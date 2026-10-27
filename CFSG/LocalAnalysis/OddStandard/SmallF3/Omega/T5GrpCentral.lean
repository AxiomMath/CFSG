module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

open scoped commutatorElement

variable {G : Type} [Group G]

private def oddOrderGen (H : Type*) [Group H] : Subgroup H :=
  Subgroup.closure {g : H | Odd (orderOf g)}

private def twoOrderGen (H : Type*) [Group H] : Subgroup H :=
  Subgroup.closure {g : H | ∃ k : ℕ, orderOf g = 2 ^ k}

private lemma closure_conj_mem {H : Type*} [Group H] {s : Set H}
    (hs : ∀ g ∈ s, ∀ x : H, x * g * x⁻¹ ∈ s) {x : H}
    (hx : x ∈ Subgroup.closure s) (y : H) : y * x * y⁻¹ ∈ Subgroup.closure s := by
  induction hx using Subgroup.closure_induction with
  | mem z hz => exact Subgroup.subset_closure (hs z hz y)
  | one => simpa using Subgroup.one_mem (Subgroup.closure s)
  | mul a b _ _ iha ihb =>
      have h : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
      have h : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ iha

private lemma oddOrderGen_normal (H : Type*) [Group H] : (oddOrderGen H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  exact closure_conj_mem (s := {a : H | Odd (orderOf a)})
    (fun a ha x => by
      have h : orderOf a = orderOf (x * a * x⁻¹) :=
        SemiconjBy.orderOf_eq x (show x * a = (x * a * x⁻¹) * x from by group)
      change Odd (orderOf (x * a * x⁻¹))
      rw [← h]
      exact ha) hn g

private lemma twoOrderGen_normal (H : Type*) [Group H] : (twoOrderGen H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  exact closure_conj_mem (s := {a : H | ∃ k : ℕ, orderOf a = 2 ^ k})
    (fun a ha x => by
      obtain ⟨k, hk⟩ := ha
      refine ⟨k, ?_⟩
      have h : orderOf a = orderOf (x * a * x⁻¹) :=
        SemiconjBy.orderOf_eq x (show x * a = (x * a * x⁻¹) * x from by group)
      rw [← h]
      exact hk) hn g

private theorem oddOrderGen_eq_top (H : Type*) [Group H] [Finite H]
    (hperf : Group.IsPerfect H) : oddOrderGen H = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : (oddOrderGen H).Normal := oddOrderGen_normal H
  haveI : Group.IsPerfect H := hperf
  have hpg : IsPGroup 2 (H ⧸ oddOrderGen H) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (oddOrderGen H) x
    have hn : orderOf g ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite g)
    obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
    refine ⟨k, ?_⟩
    have hpow : (g ^ 2 ^ k) ^ m = 1 := by
      rw [← pow_mul, ← hnm, pow_orderOf_eq_one]
    have hodd : Odd (orderOf (g ^ 2 ^ k)) :=
      Odd.of_dvd_nat hm (orderOf_dvd_iff_pow_eq_one.mpr hpow)
    have hmem : g ^ 2 ^ k ∈ oddOrderGen H := Subgroup.subset_closure hodd
    rw [← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  have hnil : Group.IsNilpotent (H ⧸ oddOrderGen H) := IsPGroup.isNilpotent (p := 2) hpg
  have hsub : Subsingleton (H ⧸ oddOrderGen H) := by
    by_contra h
    haveI : Nontrivial (H ⧸ oddOrderGen H) := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isNilpotent (H ⧸ oddOrderGen H) hnil
  exact (QuotientGroup.subsingleton_iff).mp hsub

private theorem twoOrderGen_eq_top (H : Type*) [Group H] [Finite H]
    (hperf : Group.IsPerfect H) (hsimple : IsSimpleGroup (H ⧸ Subgroup.center H))
    {t : H} (ht : t ∈ Subgroup.center H) (ht2 : orderOf t = 2) :
    twoOrderGen H = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Group.IsPerfect H := hperf
  haveI : IsSimpleGroup (H ⧸ Subgroup.center H) := hsimple
  let R : Subgroup H := twoOrderGen H
  have hRnorm : R.Normal := twoOrderGen_normal H
  haveI : R.Normal := hRnorm
  have hnormmap : (R.map (QuotientGroup.mk' (Subgroup.center H))).Normal :=
    hRnorm.map (QuotientGroup.mk' (Subgroup.center H))
      (QuotientGroup.mk'_surjective (Subgroup.center H))
  haveI : (R.map (QuotientGroup.mk' (Subgroup.center H))).Normal := hnormmap
  change R = ⊤
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (R.map (QuotientGroup.mk' (Subgroup.center H))) with hbot | htop
  ·
    exfalso
    have hRZle : R ≤ Subgroup.center H := by
      have h := (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' (Subgroup.center H))
        (H := R)).mp hbot
      rwa [QuotientGroup.ker_mk'] at h
    let P : Sylow 2 H := default
    have hPZ : (P : Subgroup H) ≤ Subgroup.center H := by
      intro x hx
      obtain ⟨k, hk⟩ := P.isPGroup'.exists_orderOf_eq_pow
        (⟨x, hx⟩ : ↥(P : Subgroup H))
      exact hRZle (Subgroup.subset_closure
        ⟨k, (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥(P : Subgroup H))).trans hk⟩)
    have hPodd : Odd (P : Subgroup H).index := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact P.not_dvd_index
    have hZodd : Odd (Subgroup.center H).index :=
      Odd.of_dvd_nat hPodd (Subgroup.index_dvd_of_le hPZ)
    have htriv : MonoidHom.transferCenterPow H t = 1 := by
      have hker : (MonoidHom.transferCenterPow H).ker = ⊤ := by
        rw [eq_top_iff, ← hperf.commutator_eq_top]
        exact Abelianization.commutator_subset_ker (MonoidHom.transferCenterPow H)
      exact MonoidHom.mem_ker.mp (by rw [hker]; exact Subgroup.mem_top t)
    have htpow : t ^ (Subgroup.center H).index = 1 := by
      have h := congrArg Subtype.val htriv
      simpa [MonoidHom.transferCenterPow_apply] using h
    have h2dvd : 2 ∣ (Subgroup.center H).index := by
      rw [← ht2]
      exact orderOf_dvd_iff_pow_eq_one.mpr htpow
    exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr h2dvd)
  ·
    have hRZ : R ⊔ Subgroup.center H = ⊤ := by
      have h := Subgroup.comap_map_eq (f := QuotientGroup.mk' (Subgroup.center H)) (H := R)
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
      exact h.symm
    have hcomm : commutator H ≤ R := by
      change ⁅(⊤ : Subgroup H), ⊤⁆ ≤ R
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨r₁, hr₁, z₁, hz₁, rfl⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := R) (t := Subgroup.center H)).mp
          (show g₁ ∈ R ⊔ Subgroup.center H by rw [hRZ]; trivial)
      obtain ⟨r₂, hr₂, z₂, hz₂, rfl⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := R) (t := Subgroup.center H)).mp
          (show g₂ ∈ R ⊔ Subgroup.center H by rw [hRZ]; trivial)
      have hcz₁ : ⁅z₁, r₂ * z₂⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_center_iff.mp hz₁ (r₂ * z₂)).symm
      have hcz₂ : ⁅r₁, z₂⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz₂ r₁)
      have heq : ⁅r₁ * z₁, r₂ * z₂⁆ = ⁅r₁, r₂⁆ := by
        calc ⁅r₁ * z₁, r₂ * z₂⁆
            = r₁ * ⁅z₁, r₂ * z₂⁆ * r₁⁻¹ * ⁅r₁, r₂ * z₂⁆ :=
                commutatorElement_mul_left_eq_conj_mul r₁ z₁ (r₂ * z₂)
          _ = ⁅r₁, r₂ * z₂⁆ := by rw [hcz₁]; group
          _ = ⁅r₁, r₂⁆ * r₂ * ⁅r₁, z₂⁆ * r₂⁻¹ :=
                commutatorElement_mul_right_eq_mul_conj r₁ r₂ z₂
          _ = ⁅r₁, r₂⁆ := by rw [hcz₂]; group
      rw [heq]
      simpa [commutatorElement_def] using
        R.mul_mem (R.mul_mem (R.mul_mem hr₁ hr₂) (R.inv_mem hr₁)) (R.inv_mem hr₂)
    exact le_antisymm le_top (by rw [← hperf.commutator_eq_top]; exact hcomm)

private lemma comap_closure_eq_of_injective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (s : Set B) (hs : s ⊆ Set.range f) :
    (Subgroup.closure s).comap f = Subgroup.closure (f ⁻¹' s) := by
  have himg : (f ⁻¹' s).image f = s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, hx⟩ := hs hy
      exact ⟨x, by rw [Set.mem_preimage, hx]; exact hy, hx⟩
  have hmap : (Subgroup.closure (f ⁻¹' s)).map f = Subgroup.closure s := by
    rw [MonoidHom.map_closure, himg]
  rw [← hmap, Subgroup.comap_map_eq, MonoidHom.ker_eq_bot f hf, sup_bot_eq]

private lemma comap_twoRes_eq (L : Subgroup G) :
    (twoRes L).comap L.subtype = Subgroup.closure {g : ↥L | Odd (orderOf g)} := by
  have h := comap_closure_eq_of_injective L.subtype Subtype.coe_injective
    ({y : G | y ∈ L ∧ Odd (orderOf y)})
    (by rintro y ⟨hyL, -⟩; exact ⟨⟨y, hyL⟩, rfl⟩)
  rw [twoRes, h]
  congr 1
  ext g
  constructor
  · rintro ⟨-, hodd⟩
    simpa [Subgroup.orderOf_coe] using hodd
  · intro hodd
    exact ⟨g.2, by simpa [Subgroup.orderOf_coe] using hodd⟩

private lemma comap_twoPrimeRes_eq (L : Subgroup G) :
    (twoPrimeRes L).comap L.subtype =
      Subgroup.closure {g : ↥L | ∃ k : ℕ, orderOf g = 2 ^ k} := by
  have h := comap_closure_eq_of_injective L.subtype Subtype.coe_injective
    ({y : G | y ∈ L ∧ ∃ k : ℕ, orderOf y = 2 ^ k})
    (by rintro y ⟨hyL, -⟩; exact ⟨⟨y, hyL⟩, rfl⟩)
  rw [twoPrimeRes, h]
  congr 1
  ext g
  constructor
  · rintro ⟨-, k, hk⟩
    exact ⟨k, by simpa [Subgroup.orderOf_coe] using hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨g.2, k, by simpa [Subgroup.orderOf_coe] using hk⟩

theorem t5_xout_central [Finite G] {L : Subgroup G} (hL : CFSG.IsQuasisimple ↥L) {t : G}
    (ht : t ∈ centerIn L) (ht2 : orderOf t = 2) : twoPrimeRes (twoRes L) = L := by
  have htwoRes_le : twoRes L ≤ L := (Subgroup.closure_le L).mpr fun _ hg => hg.1
  have htwoPrimeRes_le : twoPrimeRes L ≤ L := (Subgroup.closure_le L).mpr fun _ hg => hg.1
  have hO2 : (twoRes L).comap L.subtype = ⊤ := by
    rw [comap_twoRes_eq]
    exact oddOrderGen_eq_top ↥L hL.1
  have htwoRes : twoRes L = L := by
    have h := congrArg (Subgroup.map L.subtype) hO2
    rw [Subgroup.comap_subtype, Subgroup.map_subgroupOf_eq_of_le htwoRes_le,
      Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  rw [htwoRes]
  rw [centerIn, Subgroup.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  have ht2' : orderOf t' = 2 := by simpa [Subgroup.orderOf_coe] using ht2
  have hO2' : (twoPrimeRes L).comap L.subtype = ⊤ := by
    rw [comap_twoPrimeRes_eq]
    exact twoOrderGen_eq_top ↥L hL.1 hL.2.1 ht' ht2'
  have htwoPrimeRes : twoPrimeRes L = L := by
    have h := congrArg (Subgroup.map L.subtype) hO2'
    rw [Subgroup.comap_subtype, Subgroup.map_subgroupOf_eq_of_le htwoPrimeRes_le,
      Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  exact htwoPrimeRes

end CFSG.OddStandard.SmallF3.Omega
