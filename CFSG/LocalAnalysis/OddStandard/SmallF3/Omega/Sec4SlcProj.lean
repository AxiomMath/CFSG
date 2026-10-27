module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

lemma sec4_mem_sup_of_commute {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hnorm : A ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    have h : a * b * a⁻¹ = b := by rw [hcomm a ha b hb]; group
    rwa [h]
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hnorm
  change x ∈ (↑(A ⊔ B) : Set G) at hx
  rw [hset, Set.mem_mul] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  exact ⟨a, ha, b, hb, hab.symm⟩

lemma sec4_natCard_sup_of_commute_of_inf_bot [Finite G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hbot : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  let f : ↥A × ↥B → ↥(A ⊔ B) := fun p => ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective f := fun p q hpq =>
    Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hbot) (congrArg Subtype.val hpq)
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := sec4_mem_sup_of_commute hcomm hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm, Nat.card_prod]

lemma sec4_isPGroup_inf_eq_bot_of_odd_orderOf [Finite G] {H K : Subgroup G}
    (hodd : ∀ x ∈ H, Odd (orderOf x)) (hK : IsPGroup 2 K) : H ⊓ K = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (fun x hx => ?_) bot_le
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := (isPGroup_iff_orderOf_dvd_pow.mp hK) ⟨x, hx.2⟩
  rw [Subgroup.orderOf_mk] at hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    (Nat.coprime_two_left.mpr (hodd x hx.1)).pow_left k
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hk dvd_rfl)

lemma sec4_mem_centerIn_iff {K : Subgroup G} (a : G) :
    a ∈ centerIn K ↔ a ∈ K ∧ ∀ k ∈ K, a * k = k * a := by
  rw [centerIn, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, fun k hk => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨k, hk⟩)).symm⟩
  · rintro ⟨haK, hcent⟩
    exact ⟨⟨a, haK⟩, Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (hcent (y : G) y.2).symm, rfl⟩

lemma sec4_inf_le_centerIn {K K' : Subgroup G}
    (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) : K ⊓ K' ≤ centerIn K := by
  intro a ha
  exact (sec4_mem_centerIn_iff a).mpr ⟨ha.1, fun k hk => (hcomm k hk a ha.2).symm⟩

lemma sec4_quotient_center_eq_one_iff {K : Subgroup G} (a : ↥K) :
    (a : ↥K ⧸ Subgroup.center ↥K) = 1 ↔ (a : G) ∈ centerIn K := by
  rw [QuotientGroup.eq_one_iff]
  exact ⟨fun h => (sec4_mem_centerIn_iff (a : G)).mpr
      ⟨a.2, fun k hk => (congrArg Subtype.val (Subgroup.mem_center_iff.mp h ⟨k, hk⟩)).symm⟩,
    fun h => Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (((sec4_mem_centerIn_iff (a : G)).mp h).2 y y.2).symm⟩

theorem sec4_exists_proj_center_quotient {L C : Subgroup G}
    (hcomm : ∀ a ∈ L, ∀ b ∈ C, a * b = b * a) (hZC : centerIn L ≤ C) :
    ∃ π : ↥(L ⊔ C) →* ↥L ⧸ Subgroup.center ↥L,
      (∀ j : ↥(L ⊔ C), π j = 1 ↔ (j : G) ∈ C) ∧
      (∀ l : ↥L, π (Subgroup.inclusion le_sup_left l) = QuotientGroup.mk l) := by
  classical
  let f : ↥L × ↥C →* ↥(L ⊔ C) :=
    { toFun := fun x => ⟨(x.1 : G) * (x.2 : G), mul_mem_sup x.1.2 x.2.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
          ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
        calc ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G))
            = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by group
          _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by
                rw [hcomm y.1 y.1.2 x.2 x.2.2]
          _ = ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)) := by group) }
  have hf : Function.Surjective f := by
    have htop : L.subgroupOf (L ⊔ C) ⊔ C.subgroupOf (L ⊔ C) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    apply MonoidHom.range_eq_top.mp
    rw [eq_top_iff, ← htop]
    apply sup_le
    · rintro a ha
      exact ⟨(⟨(a : G), ha⟩, 1), Subtype.ext (by simp [f])⟩
    · rintro b hb
      exact ⟨(1, ⟨(b : G), hb⟩), Subtype.ext (by simp [f])⟩
  let g : ↥L × ↥C →* ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.mk' (Subgroup.center ↥L)).comp (MonoidHom.fst ↥L ↥C)
  have hker : f.ker ≤ g.ker := by
    rintro ⟨a, b⟩ hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hmem : (a : G) * (b : G) = 1 := by
      have := congrArg Subtype.val hx
      simpa [f] using this
    have hbL : (b : G) ∈ L := by
      rw [eq_inv_of_mul_eq_one_right hmem]
      exact L.inv_mem a.2
    have hbZ : (b : G) ∈ centerIn L := sec4_inf_le_centerIn hcomm ⟨hbL, b.2⟩
    have haZ : (a : G) ∈ centerIn L := by
      rw [eq_inv_of_mul_eq_one_left hmem]
      exact (centerIn L).inv_mem hbZ
    change (a : ↥L ⧸ Subgroup.center ↥L) = 1
    exact (sec4_quotient_center_eq_one_iff a).mpr haZ
  let π : ↥(L ⊔ C) →* ↥L ⧸ Subgroup.center ↥L :=
    f.liftOfRightInverseAux (Function.invFun f) (Function.rightInverse_invFun hf) g hker
  have hπf : ∀ x : ↥L × ↥C, π (f x) = (x.1 : ↥L ⧸ Subgroup.center ↥L) :=
    fun x => MonoidHom.liftOfRightInverseAux_comp_apply (f := f) (f_inv := Function.invFun f)
      (Function.rightInverse_invFun hf) g hker x
  refine ⟨π, ?_, ?_⟩
  · intro j
    constructor
    · intro hj
      obtain ⟨⟨a, b⟩, hab⟩ := hf j
      have hjab : (j : G) = (a : G) * (b : G) := by
        have := congrArg Subtype.val hab
        simpa [f] using this.symm
      have hja : (a : ↥L ⧸ Subgroup.center ↥L) = 1 := by
        rw [← hab, hπf] at hj
        exact hj
      have haZ : (a : G) ∈ centerIn L := (sec4_quotient_center_eq_one_iff a).mp hja
      have haC : (a : G) ∈ C := hZC haZ
      rw [hjab]
      exact C.mul_mem haC b.2
    · intro hj
      have hfj : j = f (1, ⟨(j : G), hj⟩) :=
        Subtype.ext (by simp [f])
      rw [hfj, hπf]
      rfl
  · intro l
    have hfl : Subgroup.inclusion le_sup_left l = f (l, 1) :=
      Subtype.ext (by simp [f])
    rw [hfl, hπf]

end CFSG.OddStandard.SmallF3.Omega
