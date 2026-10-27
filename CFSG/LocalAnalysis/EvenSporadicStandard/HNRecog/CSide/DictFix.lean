module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

private lemma dictFix_centerOf_eq_map_center :
    centerOf Q = (Subgroup.center ↥Q).map Q.subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (g : C) g.2)
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx]
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)

private lemma dictFix_card_centerOf (hE : IsExtraspecialPGroup 2 Q) :
    Nat.card ↥(centerOf Q) = 2 := by
  rw [dictFix_centerOf_eq_map_center, Subgroup.card_map_of_injective Q.subtype_injective,
    hE.2.2.2]

private lemma dictFix_card_ker_of (hE : IsExtraspecialPGroup 2 Q) :
    Nat.card (Abelianization.of (G := Q)).ker = 2 := by
  rw [Abelianization.ker_of, hE.2.1, hE.2.2.2]

private theorem dictFix_card_comap_of_surjective {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (f : G →* H) (hf : Function.Surjective f) (N : Subgroup H) :
    Nat.card (N.comap f) = Nat.card f.ker * Nat.card N := by
  have h1 := Subgroup.card_mul_index (N.comap f)
  rw [Subgroup.index_comap_of_surjective _ hf] at h1
  have h2 := Subgroup.card_ker_mul_card_range f
  rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top] at h2
  have h3 := Subgroup.card_mul_index N
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, ← h2, ← h3]
  ring

private def dictFix_fixedSubgroup (g : C) : Subgroup (Abelianization Q) where
  carrier := {v | conjLinEquiv hQn g (Additive.ofMul v) = Additive.ofMul v}
  one_mem' := by
    change conjLinEquiv hQn g (Additive.ofMul (1 : Abelianization Q)) = Additive.ofMul 1
    rw [ofMul_one, map_zero]
  mul_mem' := by
    intro a b ha hb
    change conjLinEquiv hQn g (Additive.ofMul (a * b)) = Additive.ofMul (a * b)
    rw [ofMul_mul, map_add, ha, hb]
  inv_mem' := by
    intro a ha
    change conjLinEquiv hQn g (Additive.ofMul a⁻¹) = Additive.ofMul a⁻¹
    rw [ofMul_inv, map_neg, ha]

private lemma dictFix_conj_mem_centerOf (ρ : C) {z : C} (hz : z ∈ centerOf Q) :
    ρ * z * ρ⁻¹ ∈ centerOf Q := by
  obtain ⟨hzQ, hzc⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨(inferInstance : Q.Normal).conj_mem z hzQ ρ, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : ρ⁻¹ * y * ρ ∈ Q := by
    simpa using (inferInstance : Q.Normal).conj_mem y hy ρ⁻¹
  have hcomm : (ρ⁻¹ * y * ρ) * z = z * (ρ⁻¹ * y * ρ) :=
    Subgroup.mem_centralizer_iff.mp hzc _ hy'
  calc y * (ρ * z * ρ⁻¹) = ρ * ((ρ⁻¹ * y * ρ) * z) * ρ⁻¹ := by group
    _ = ρ * (z * (ρ⁻¹ * y * ρ)) * ρ⁻¹ := by rw [hcomm]
    _ = (ρ * z * ρ⁻¹) * y := by group

private lemma dictFix_centerOf_le_centralizer_singleton (hE : IsExtraspecialPGroup 2 Q) (ρ : C) :
    centerOf Q ≤ Subgroup.centralizer ({ρ} : Set C) := by
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hz1 : z = 1
  · subst hz1
    group
  · have hzQ : z ∈ Q := (Subgroup.mem_inf.mp hz).1
    have hconj_mem : ρ * z * ρ⁻¹ ∈ centerOf Q := dictFix_conj_mem_centerOf ρ hz
    have hconjQ : ρ * z * ρ⁻¹ ∈ Q := (Subgroup.mem_inf.mp hconj_mem).1
    have hz'c : (⟨z, hzQ⟩ : Q) ∈ Subgroup.center Q := (mem_centerOf_iff ⟨z, hzQ⟩).mp hz
    have hw'c : (⟨ρ * z * ρ⁻¹, hconjQ⟩ : Q) ∈ Subgroup.center Q :=
      (mem_centerOf_iff ⟨ρ * z * ρ⁻¹, hconjQ⟩).mp hconj_mem
    have hz1' : (⟨z, hzQ⟩ : Q) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    have hw1 : (⟨ρ * z * ρ⁻¹, hconjQ⟩ : Q) ≠ 1 := by
      intro h
      apply hz1
      have h' : ρ * z * ρ⁻¹ = 1 := congrArg Subtype.val h
      calc z = ρ⁻¹ * (ρ * z * ρ⁻¹) * ρ := by group
        _ = ρ⁻¹ * 1 * ρ := by rw [h']
        _ = 1 := by group
    have hval : z = ρ * z * ρ⁻¹ :=
      congrArg Subtype.val (eq_of_mem_center hE hz'c hw'c hz1' hw1)
    calc z * ρ = (ρ * z * ρ⁻¹) * ρ := by rw [← hval]
      _ = ρ * z := by group

private lemma dictFix_centerOf_le_inf_centralizer_singleton (hE : IsExtraspecialPGroup 2 Q)
    (ρ : C) : centerOf Q ≤ Q ⊓ Subgroup.centralizer ({ρ} : Set C) :=
  fun z hz => Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_inf.mp hz).1, dictFix_centerOf_le_centralizer_singleton hE ρ hz⟩

theorem cSide_card_comm_eq [Finite Q] (hE : IsExtraspecialPGroup 2 Q) (g : C) :
    Nat.card {q : C // q ∈ Q ∧ ⁅q, g⁆ ∈ centerOf Q} =
      2 * Nat.card {v : Additive (Abelianization Q) // conjLinEquiv hQn g v = v} := by
  let K : Subgroup (Abelianization Q) := dictFix_fixedSubgroup (Q := Q) g
  have hiff : ∀ x : Q, (⁅(x : C), g⁆ ∈ centerOf Q) ↔ Abelianization.of x ∈ K := by
    intro x
    show (⁅(x : C), g⁆ ∈ centerOf Q) ↔
      conjLinEquiv hQn g (Additive.ofMul (Abelianization.of x)) =
        Additive.ofMul (Abelianization.of x)
    rw [show ⁅(x : C), g⁆ = ⁅g, (x : C)⁆⁻¹ from
      (commutatorElement_inv (g₁ := g) (g₂ := (x : C))).symm, Subgroup.inv_mem_iff]
    exact (extraspecialConjOrth_apply_eq_iff hE g x).symm
  have hK : Nat.card ↥K =
      Nat.card {v : Additive (Abelianization Q) // conjLinEquiv hQn g v = v} := by
    refine Nat.card_congr ?_
    refine { toFun := fun v => ⟨Additive.ofMul v.1, v.2⟩
             invFun := fun v => ⟨Additive.toMul v.1, v.2⟩
             left_inv := fun v => Subtype.ext rfl
             right_inv := fun v => Subtype.ext rfl }
  have hsurj : Function.Surjective (Abelianization.of (G := Q)) :=
    fun v => QuotientGroup.mk_surjective v
  calc Nat.card {q : C // q ∈ Q ∧ ⁅q, g⁆ ∈ centerOf Q}
      = Nat.card ↥(K.comap (Abelianization.of (G := Q))) := by
        refine Nat.card_congr ?_
        refine { toFun := fun q => ⟨⟨q.1, q.2.1⟩, (hiff ⟨q.1, q.2.1⟩).1 q.2.2⟩
                 invFun := fun x => ⟨x.1.1, x.1.2, (hiff x.1).2 x.2⟩
                 left_inv := fun q => Subtype.ext rfl
                 right_inv := fun x => Subtype.ext rfl }
    _ = Nat.card (Abelianization.of (G := Q)).ker * Nat.card ↥K :=
        dictFix_card_comap_of_surjective (Abelianization.of (G := Q)) hsurj K
    _ = 2 * Nat.card ↥K := by rw [dictFix_card_ker_of hE]
    _ = 2 * Nat.card {v : Additive (Abelianization Q) // conjLinEquiv hQn g v = v} := by
        rw [hK]

theorem cSide_comm_mem_centerOf_iff_of_odd [Finite Q] (hE : IsExtraspecialPGroup 2 Q) {ρ : C}
    (hρ : Odd (orderOf ρ)) {q : C} (hq : q ∈ Q) :
    ⁅q, ρ⁆ ∈ centerOf Q ↔ q ∈ Subgroup.centralizer ({ρ} : Set C) := by
  constructor
  · intro hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzρ : Commute (⁅q, ρ⁆) ρ :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (dictFix_centerOf_le_centralizer_singleton hE ρ hz)
    have hqconj : q * ρ * q⁻¹ = (⁅q, ρ⁆) * ρ := by
      rw [commutatorElement_def]
      group
    have hρpow : ρ ^ orderOf ρ = 1 := pow_orderOf_eq_one ρ
    have hL : (q * ρ * q⁻¹) ^ orderOf ρ = 1 := by
      rw [conj_pow, hρpow, mul_one, mul_inv_cancel]
    have hR : ((⁅q, ρ⁆) * ρ) ^ orderOf ρ = (⁅q, ρ⁆) ^ orderOf ρ := by
      rw [hzρ.mul_pow, hρpow, mul_one]
    have hzn : (⁅q, ρ⁆) ^ orderOf ρ = 1 := by
      rw [← hR, ← hqconj]
      exact hL
    have hz2 : (⁅q, ρ⁆) ^ 2 = 1 := by
      have hzQ : ⁅q, ρ⁆ ∈ Q := (Subgroup.mem_inf.mp hz).1
      have hzc : (⟨⁅q, ρ⁆, hzQ⟩ : Q) ∈ Subgroup.center Q :=
        (mem_centerOf_iff ⟨⁅q, ρ⁆, hzQ⟩).mp hz
      simpa using congrArg Subtype.val (sq_eq_one_of_mem_center hE hzc)
    obtain ⟨m, hm⟩ := hρ
    have hzn_eq : (⁅q, ρ⁆) ^ orderOf ρ = ⁅q, ρ⁆ := by
      rw [hm, pow_succ, pow_mul, hz2, one_pow, one_mul]
    rw [← commutatorElement_eq_one_iff_mul_comm, ← hzn_eq]
    exact hzn
  · intro hqcent
    rw [Subgroup.mem_centralizer_singleton_iff] at hqcent
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hqcent]
    exact Subgroup.one_mem _

theorem cSide_card_cent_of_odd [Finite Q] (hE : IsExtraspecialPGroup 2 Q) {ρ : C}
    (hρ : Odd (orderOf ρ)) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({ρ} : Set C)) =
      2 * Nat.card {v : Additive (Abelianization Q) // conjLinEquiv hQn ρ v = v} := by
  refine (Nat.card_congr ?_).trans (cSide_card_comm_eq hE ρ)
  refine { toFun := fun q => ⟨q.1, (Subgroup.mem_inf.mp q.2).1,
              (cSide_comm_mem_centerOf_iff_of_odd hE hρ (Subgroup.mem_inf.mp q.2).1).mpr
                (Subgroup.mem_inf.mp q.2).2⟩
           invFun := fun q => ⟨q.1, Subgroup.mem_inf.mpr ⟨q.2.1,
              (cSide_comm_mem_centerOf_iff_of_odd hE hρ q.2.1).mp q.2.2⟩⟩
           left_inv := fun q => Subtype.ext rfl
           right_inv := fun q => Subtype.ext rfl }

theorem cSide_cent_eq_centerOf_iff [Finite Q] (hE : IsExtraspecialPGroup 2 Q) {ρ : C}
    (hρ : Odd (orderOf ρ)) :
    Q ⊓ Subgroup.centralizer ({ρ} : Set C) = centerOf Q ↔
      ∀ v : Additive (Abelianization Q), conjLinEquiv hQn ρ v = v → v = 0 := by
  constructor
  · intro heq
    have hcardF : Nat.card {v : Additive (Abelianization Q) // conjLinEquiv hQn ρ v = v} = 1 := by
      have h := cSide_card_cent_of_odd (Q := Q) hE hρ
      rw [congrArg (fun S : Subgroup C => Nat.card ↥S) heq, dictFix_card_centerOf hE] at h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (by simpa using h.symm)
    haveI : Subsingleton {v : Additive (Abelianization Q) // conjLinEquiv hQn ρ v = v} :=
      (Nat.card_eq_one_iff_unique.mp hcardF).1
    intro v hv
    have h0 : (⟨v, hv⟩ : {v // conjLinEquiv hQn ρ v = v}) = ⟨0, by simp⟩ :=
      Subsingleton.elim _ _
    exact congrArg Subtype.val h0
  · intro hfix
    have hcardF : Nat.card {v : Additive (Abelianization Q) // conjLinEquiv hQn ρ v = v} = 1 := by
      refine Nat.card_eq_one_iff_exists.mpr ⟨⟨0, by simp⟩, ?_⟩
      intro y
      exact Subtype.ext (hfix y.1 y.2)
    haveI : Finite ↥(Q ⊓ Subgroup.centralizer ({ρ} : Set C)) :=
      Finite.of_injective (Subgroup.inclusion (inf_le_left : Q ⊓ _ ≤ Q))
        (Subgroup.inclusion_injective _)
    have hcard : Nat.card ↥(Q ⊓ Subgroup.centralizer ({ρ} : Set C)) = Nat.card ↥(centerOf Q) := by
      rw [cSide_card_cent_of_odd hE hρ, hcardF, mul_one, dictFix_card_centerOf hE]
    exact (Subgroup.eq_of_le_of_card_ge (dictFix_centerOf_le_inf_centralizer_singleton hE ρ)
      (le_of_eq hcard)).symm

end CFSG.EvenSporadicStandard.HNRecog.CSide
