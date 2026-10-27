module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupAlternatingFour
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public section

namespace CFSG.Semidihedral.OddLinearNormals

open Matrix
open scoped MatrixGroups

universe u v

section SpecialLinear

variable (F : Type u) [Field F]

@[expose] def quarterTurn : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem quarterTurn_square_matrix :
    ((quarterTurn F) ^ 2 : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quarterTurn, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem quarterTurn_square_mem_center :
    (quarterTurn F) ^ 2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  exact ⟨-1, by simp, (quarterTurn_square_matrix F).symm⟩

theorem quarterTurn_not_mem_center :
    quarterTurn F ∉ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  intro h
  obtain ⟨a, _, ha⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) ha
  simp [quarterTurn] at hentry

theorem projective_quarterTurn_order :
    orderOf (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))
      (quarterTurn F)) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (quarterTurn_square_mem_center F)
  · intro h
    exact quarterTurn_not_mem_center F ((QuotientGroup.eq_one_iff _).mp h)

theorem two_dvd_projective_card :
    2 ∣ Nat.card (ProjectiveSpecialLinearGroup (Fin 2) F) := by
  have h := orderOf_dvd_natCard
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F)) (quarterTurn F))
  simpa only [projective_quarterTurn_order] using h

theorem center_square_eq_one (g : SpecialLinearGroup (Fin 2) F)
    (hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) : g ^ 2 = 1 := by
  obtain ⟨a, ha, hmatrix⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have ha2 : a ^ 2 = 1 := by simpa using ha
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hmatrix]
  rw [← map_pow, ha2, map_one]

end SpecialLinear

theorem normal_odd_alternating_four_eq_bot
    (R : Subgroup (alternatingGroup (Fin 4))) (hR : R.Normal)
    (hodd : Odd (Nat.card R)) : R = ⊥ := by
  have hcard : Nat.card R ∣ 12 := by
    have hA : Nat.card (alternatingGroup (Fin 4)) = 12 :=
      alternatingGroup.card_of_card_eq_four (by simp)
    simpa only [hA] using Subgroup.card_subgroup_dvd_card R
  have hcoprime : Nat.Coprime (Nat.card R) 4 := by
    simpa using hodd.coprime_two_right.pow_right 2
  have hthree : Nat.card R ∣ 3 := by
    exact hcoprime.dvd_of_dvd_mul_left (by simpa using hcard)
  rcases (Nat.dvd_prime Nat.prime_three).mp hthree with hone | hthree
  · exact Subgroup.card_eq_one.mp hone
  · exact CFSG.GorensteinWalter.normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup_four
      ⟨MulEquiv.refl _⟩ 3 Nat.prime_three (by decide) R hR
      (IsPGroup.of_card (n := 1) (by simpa using hthree))

section FiniteField

variable (F : Type u) [Field F] [Finite F]

theorem normal_odd_projective_three_eq_bot (hF : Nat.card F = 3)
    (R : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) F))
    (hR : R.Normal) (hodd : Odd (Nat.card R)) : R = ⊥ := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let eF : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e : ProjectiveSpecialLinearGroup (Fin 2) F ≃* alternatingGroup (Fin 4) :=
    (CFSG.GorensteinWalter.psl2RingEquiv eF).symm.trans
      CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup
  have hmap : R.map e.toMonoidHom = ⊥ :=
    normal_odd_alternating_four_eq_bot _ (hR.map e.toMonoidHom e.surjective)
      (hodd.of_dvd_nat (R.card_map_dvd e.toMonoidHom))
  exact (Subgroup.map_eq_bot_iff_of_injective R e.injective).mp hmap

omit [Finite F] in
theorem normal_odd_projective_large_eq_bot (hF : 4 ≤ Nat.card F)
    (R : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) F))
    (hR : R.Normal) (hodd : Odd (Nat.card R)) : R = ⊥ := by
  let : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    ProjectiveSpecialLinearGroup.rank_two_simple hF
  let : R.Normal := hR
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with hbot | htop
  · exact hbot
  · have hquotodd : Odd (Nat.card (ProjectiveSpecialLinearGroup (Fin 2) F)) := by
      simpa only [htop, Subgroup.card_top] using hodd
    exact (hquotodd.not_two_dvd_nat (two_dvd_projective_card F)).elim

theorem normal_odd_specialLinear_eq_bot (hFodd : Odd (Nat.card F)) (hF : 3 ≤ Nat.card F)
    (R : Subgroup (SpecialLinearGroup (Fin 2) F)) (hR : R.Normal)
    (hodd : Odd (Nat.card R)) : R = ⊥ := by
  let q : SpecialLinearGroup (Fin 2) F →* ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hnormal : (R.map q).Normal := hR.map q hq
  have himageodd : Odd (Nat.card (R.map q)) := hodd.of_dvd_nat (R.card_map_dvd q)
  have himage : R.map q = ⊥ := by
    by_cases hthree : Nat.card F = 3
    · exact normal_odd_projective_three_eq_bot F hthree _ hnormal himageodd
    · have hfive : 5 ≤ Nat.card F := by
        obtain ⟨k, hk⟩ := hFodd
        omega
      exact normal_odd_projective_large_eq_bot F (by omega) _ hnormal himageodd
  apply le_antisymm _ bot_le
  intro g hg
  have hqg : q g = 1 := by
    have hm : q g ∈ R.map q := ⟨g, hg, rfl⟩
    simpa only [himage, Subgroup.mem_bot] using hm
  have hcenter : g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) :=
    (QuotientGroup.eq_one_iff g).mp hqg
  have hsquare : g ^ 2 = 1 := center_square_eq_one F g hcenter
  have hpow : g ^ Nat.card R = 1 := by
    exact congrArg (fun x : R => (x : SpecialLinearGroup (Fin 2) F))
      (pow_card_eq_one' (x := (⟨g, hg⟩ : R)))
  exact Subgroup.mem_bot.mpr
    ((pow_eq_one_iff_of_coprime hodd.coprime_two_left).mp ⟨hsquare, hpow⟩)

end FiniteField

section MatrixCopies

variable {F : Type u} {E : Type v} [Field F] [Field E]

@[expose] def entrywiseSL (i : F →+* E) :
    Matrix.SpecialLinearGroup (Fin 2) F →* GeneralLinearGroup (Fin 2) E :=
  Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map i)

@[expose] def imageSL (i : F →+* E) : Subgroup (GeneralLinearGroup (Fin 2) E) :=
  (entrywiseSL i).range

theorem entrywiseSL_matrix (i : F →+* E) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (entrywiseSL i g : Matrix (Fin 2) (Fin 2) E) =
      (g : Matrix (Fin 2) (Fin 2) F).map i := rfl

theorem entrywiseSL_injective (i : F →+* E) (hi : Function.Injective i) :
    Function.Injective (entrywiseSL i) := by
  intro g h heq
  apply Matrix.SpecialLinearGroup.ext
  intro j k
  apply hi
  exact congrArg (fun a : GeneralLinearGroup (Fin 2) E => a j k) heq

theorem entrywiseSL_transvection_one (i : F →+* E) {j k : Fin 2} (hjk : j ≠ k) :
    (entrywiseSL i (Matrix.SpecialLinearGroup.transvection hjk 1) :
      Matrix (Fin 2) (Fin 2) E) = 1 + Matrix.single j k 1 := by
  rw [entrywiseSL_matrix, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.map_add i i.map_add, Matrix.map_one i i.map_zero i.map_one,
    Matrix.map_single, i.map_one]

theorem scalar_of_centralizes_entrywiseSL (i : F →+* E)
    (g : GeneralLinearGroup (Fin 2) E)
    (hg : ∀ x : Matrix.SpecialLinearGroup (Fin 2) F, Commute g (entrywiseSL i x)) :
    (g : Matrix (Fin 2) (Fin 2) E) ∈ Set.range (Matrix.scalar (Fin 2)) := by
  apply Matrix.mem_range_scalar_iff_commute_single.mpr
  intro j k hjk
  have hmul := congrArg Units.val (hg (Matrix.SpecialLinearGroup.transvection hjk 1)).symm.eq
  have hcomm : Commute (1 + Matrix.single j k 1) (g : Matrix (Fin 2) (Fin 2) E) := by
    change (1 + Matrix.single j k 1) * (g : Matrix (Fin 2) (Fin 2) E) =
      (g : Matrix (Fin 2) (Fin 2) E) * (1 + Matrix.single j k 1)
    simpa only [GeneralLinearGroup.coe_mul, entrywiseSL_transvection_one] using hmul
  simpa only [add_sub_cancel_left] using hcomm.sub_left (Commute.one_left _)

@[expose] def conjugatedEntrywiseSL (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E) :
    Matrix.SpecialLinearGroup (Fin 2) F →* GeneralLinearGroup (Fin 2) E :=
  (MulAut.conj b).toMonoidHom.comp (entrywiseSL i)

@[expose] def conjugatedImageSL (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E) :
    Subgroup (GeneralLinearGroup (Fin 2) E) :=
  (imageSL i).map (MulAut.conj b).toMonoidHom

theorem conjugatedImageSL_eq_range (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E) :
    conjugatedImageSL i b = (conjugatedEntrywiseSL i b).range := by
  exact (MonoidHom.range_comp _ _).symm

theorem conjugatedEntrywiseSL_injective (i : F →+* E) (hi : Function.Injective i)
    (b : GeneralLinearGroup (Fin 2) E) : Function.Injective (conjugatedEntrywiseSL i b) :=
  (MulAut.conj b).injective.comp (entrywiseSL_injective i hi)

theorem scalar_of_centralizes_conjugatedEntrywiseSL (i : F →+* E)
    (b g : GeneralLinearGroup (Fin 2) E)
    (hg : ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
      Commute g (conjugatedEntrywiseSL i b x)) :
    (g : Matrix (Fin 2) (Fin 2) E) ∈ Set.range (Matrix.scalar (Fin 2)) := by
  let e : GeneralLinearGroup (Fin 2) E ≃* GeneralLinearGroup (Fin 2) E := MulAut.conj b
  have hbase : ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
      Commute (e.symm g) (entrywiseSL i x) := by
    intro x
    have h : Commute g (e (entrywiseSL i x)) := hg x
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      h.map e.symm.toMonoidHom
  have hc : e.symm g ∈ Subgroup.center (GeneralLinearGroup (Fin 2) E) :=
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
      (scalar_of_centralizes_entrywiseSL i _ hbase)
  apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
  apply Subgroup.mem_center_iff.mpr
  intro a
  have h := congrArg e (Subgroup.mem_center_iff.mp hc (e.symm a))
  simpa only [map_mul, MulEquiv.apply_symm_apply] using h

end MatrixCopies

section MatrixOvergroups

variable {F : Type u} {E : Type v} [Field F] [Finite F] [Field E]

theorem normal_odd_centralizes_conjugated_image
    (hFodd : Odd (Nat.card F)) (hF : 3 ≤ Nat.card F)
    (i : F →+* E) (hi : Function.Injective i) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    (hSnormal : ((conjugatedImageSL i b).subgroupOf B).Normal)
    (R : Subgroup B) [Finite R] (hRnormal : R.Normal) (hRodd : Odd (Nat.card R)) :
    ∀ r : B, r ∈ R → ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
      Commute (r : GeneralLinearGroup (Fin 2) E) (conjugatedEntrywiseSL i b x) := by
  let f := conjugatedEntrywiseSL i b
  have hf : Function.Injective f := conjugatedEntrywiseSL_injective i hi b
  let fB : Matrix.SpecialLinearGroup (Fin 2) F →* B := f.codRestrict B (by
    intro x
    apply hSB
    rw [conjugatedImageSL_eq_range]
    exact ⟨x, rfl⟩)
  have hfB : Function.Injective fB := by
    intro x y hxy
    exact hf (congrArg Subtype.val hxy)
  have hrange : fB.range = (conjugatedImageSL i b).subgroupOf B := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      change f x ∈ conjugatedImageSL i b
      rw [conjugatedImageSL_eq_range]
      exact ⟨x, rfl⟩
    · intro hg
      change (g : GeneralLinearGroup (Fin 2) E) ∈ conjugatedImageSL i b at hg
      rw [conjugatedImageSL_eq_range] at hg
      obtain ⟨x, hx⟩ := hg
      exact ⟨x, Subtype.ext hx⟩
  have hintersection : R.comap fB = ⊥ :=
    normal_odd_specialLinear_eq_bot F hFodd hF _ (hRnormal.comap fB)
      (hRodd.of_dvd_nat (R.card_comap_dvd_of_injective fB hfB))
  have hdisjoint : Disjoint R ((conjugatedImageSL i b).subgroupOf B) := by
    rw [← hrange]
    apply Subgroup.disjoint_def.mpr
    intro g hgR hgS
    obtain ⟨x, rfl⟩ := hgS
    have hx : x ∈ R.comap fB := hgR
    have hxone : x = 1 := by simpa only [hintersection, Subgroup.mem_bot] using hx
    simp only [hxone, map_one]
  intro r hr x
  have hx : fB x ∈ (conjugatedImageSL i b).subgroupOf B := by
    rw [← hrange]
    exact ⟨x, rfl⟩
  have hcomm : Commute r (fB x) :=
    Subgroup.commute_of_normal_of_disjoint R _ hRnormal hSnormal hdisjoint r (fB x) hr hx
  exact hcomm.map B.subtype

theorem normal_odd_conjugated_matrix_overgroup_scalar
    (hFodd : Odd (Nat.card F)) (hF : 3 ≤ Nat.card F)
    (i : F →+* E) (hi : Function.Injective i) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    (hSnormal : ((conjugatedImageSL i b).subgroupOf B).Normal)
    (R : Subgroup B) [Finite R] (hRnormal : R.Normal) (hRodd : Odd (Nat.card R)) :
    ∀ r : B, r ∈ R →
      (r.val : Matrix (Fin 2) (Fin 2) E) ∈ Set.range (Matrix.scalar (Fin 2)) := by
  intro r hr
  exact scalar_of_centralizes_conjugatedEntrywiseSL i b _
    (normal_odd_centralizes_conjugated_image hFodd hF i hi b B hSB hSnormal
      R hRnormal hRodd r hr)

omit [Finite F] in
theorem conjugatedImageSL_one (i : F →+* E) : conjugatedImageSL i 1 = imageSL i := by
  ext g
  simp [conjugatedImageSL, MulAut.conj]

theorem normal_odd_matrix_overgroup_scalar
    (hFodd : Odd (Nat.card F)) (hF : 3 ≤ Nat.card F)
    (i : F →+* E) (hi : Function.Injective i)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : imageSL i ≤ B)
    (hSnormal : ((imageSL i).subgroupOf B).Normal)
    (R : Subgroup B) [Finite R] (hRnormal : R.Normal) (hRodd : Odd (Nat.card R)) :
    ∀ r : B, r ∈ R →
      (r.val : Matrix (Fin 2) (Fin 2) E) ∈ Set.range (Matrix.scalar (Fin 2)) := by
  apply normal_odd_conjugated_matrix_overgroup_scalar hFodd hF i hi 1 B
    (by simpa only [conjugatedImageSL_one] using hSB)
    (by simpa only [conjugatedImageSL_one] using hSnormal) R hRnormal hRodd

theorem normal_odd_conjugated_specialLinear_eq_bot
    (hFodd : Odd (Nat.card F)) (hF : 3 ≤ Nat.card F)
    (i : F →+* E) (hi : Function.Injective i) (b : GeneralLinearGroup (Fin 2) E)
    (R : Subgroup (conjugatedImageSL i b)) (hRnormal : R.Normal)
    (hRodd : Odd (Nat.card R)) : R = ⊥ := by
  let f := conjugatedEntrywiseSL i b
  let fS : Matrix.SpecialLinearGroup (Fin 2) F →* conjugatedImageSL i b :=
    f.codRestrict _ (by
      intro x
      rw [conjugatedImageSL_eq_range]
      exact ⟨x, rfl⟩)
  have hfS : Function.Injective fS := by
    intro x y hxy
    exact conjugatedEntrywiseSL_injective i hi b (congrArg Subtype.val hxy)
  have hcomap : R.comap fS = ⊥ :=
    normal_odd_specialLinear_eq_bot F hFodd hF _ (hRnormal.comap fS)
      (hRodd.of_dvd_nat (R.card_comap_dvd_of_injective fS hfS))
  apply le_antisymm _ bot_le
  intro g hg
  have hgrange : (g : GeneralLinearGroup (Fin 2) E) ∈ f.range := by
    simpa only [conjugatedImageSL_eq_range] using g.property
  obtain ⟨x, hx⟩ := hgrange
  have hxg : fS x = g := Subtype.ext hx
  have hxmem : x ∈ R.comap fS := by
    change fS x ∈ R
    rw [hxg]
    exact hg
  have hxone : x = 1 := by simpa only [hcomap, Subgroup.mem_bot] using hxmem
  exact Subgroup.mem_bot.mpr (by simpa only [hxone, map_one] using hxg.symm)

end MatrixOvergroups

theorem odd_linear_two_normal_subgroups_are_scalar
    (F : Type u) [Field F] [Finite F]
    (hFodd : Odd (Nat.card F)) (hF : 3 ≤ Nat.card F) :
    (∀ R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F),
      R.Normal → Odd (Nat.card R) → R = ⊥) ∧
    (∀ (E : Type v) [Field E] (i : F →+* E), Function.Injective i →
      ∀ B : Subgroup (GeneralLinearGroup (Fin 2) E), imageSL i ≤ B →
      ((imageSL i).subgroupOf B).Normal → ∀ (R : Subgroup B) [Finite R],
      R.Normal → Odd (Nat.card R) → ∀ r : B, r ∈ R →
      (r.val : Matrix (Fin 2) (Fin 2) E) ∈ Set.range (Matrix.scalar (Fin 2))) ∧
    (∀ (E : Type v) [Field E] (i : F →+* E), Function.Injective i →
      ∀ (b : GeneralLinearGroup (Fin 2) E) (R : Subgroup (conjugatedImageSL i b)),
      R.Normal → Odd (Nat.card R) → R = ⊥) ∧
    (∀ (E : Type v) [Field E] (i : F →+* E), Function.Injective i →
      ∀ (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E)),
      conjugatedImageSL i b ≤ B → ((conjugatedImageSL i b).subgroupOf B).Normal →
      ∀ (R : Subgroup B) [Finite R], R.Normal → Odd (Nat.card R) → ∀ r : B, r ∈ R →
      (r.val : Matrix (Fin 2) (Fin 2) E) ∈ Set.range (Matrix.scalar (Fin 2))) := by
  refine ⟨normal_odd_specialLinear_eq_bot F hFodd hF, ?_, ?_, ?_⟩
  · intro E _ i hi B hSB hSnormal R _ hRnormal hRodd
    exact normal_odd_matrix_overgroup_scalar hFodd hF i hi B hSB hSnormal
      R hRnormal hRodd
  · intro E _ i hi b R hRnormal hRodd
    exact normal_odd_conjugated_specialLinear_eq_bot hFodd hF i hi b R hRnormal hRodd
  · intro E _ i hi b B hSB hSnormal R _ hRnormal hRodd
    exact normal_odd_conjugated_matrix_overgroup_scalar hFodd hF i hi b B hSB hSnormal
      R hRnormal hRodd

end CFSG.Semidihedral.OddLinearNormals
