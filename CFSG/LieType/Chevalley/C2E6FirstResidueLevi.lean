module

public import CFSG.LieType.Chevalley.C2E6FirstResiduePanels
public import CFSG.LieType.Chevalley.C2E6StandardLeviFactors

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap Matrix Module
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley.ExteriorCube
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def firstJ : Set (Fin 4) := {1, 2, 3}

theorem two_mem_firstJ : (2 : Fin 4) ∈ firstJ := by
  simp [firstJ]

theorem nativeUnion_firstJ : nativeUnion firstJ = setA := by
  have key1 : ∀ i : Fin 4, (i = 1 ∨ i = 2 ∨ i = 3) → ∀ x : Fin 6, x ∈ nativeOrbit i →
      x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
    decide
  have key2 : ∀ x : Fin 6, (x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5) →
      ∃ i : Fin 4, (i = 1 ∨ i = 2 ∨ i = 3) ∧ x ∈ nativeOrbit i := by
    decide
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact key1 i hi x hxi
  · intro hx
    obtain ⟨i, hi, hxi⟩ := key2 x hx
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩

theorem stdLevi_firstJ
    : stdLevi firstJ = groupA ⊓ stdFixedGroup := by
  rw [stdLevi, nativeUnion_firstJ]

theorem stdLeviUnipotent_firstJ
    : stdLeviUnipotent firstJ = unipotentA ⊓ stdFixedGroup := by
  rw [stdLeviUnipotent, nativeUnion_firstJ]

theorem stdLevi_firstJ_le_groupA
    : stdLevi firstJ ≤ groupA := by
  rw [stdLevi_firstJ]
  exact inf_le_left

theorem liftA_mem_stdLevi
    (h : SU6) :
    ((liftA (h : SpecialLinearGroup (Fin 6) K) : groupA) : ModGL Tag.E6 K) ∈ stdLevi firstJ := by
  rw [stdLevi_firstJ]
  exact ⟨(liftA (h : SpecialLinearGroup (Fin 6) K)).2,
    (mem_stdFixedGroup_iff (psiA_liftA (h : SpecialLinearGroup (Fin 6) K))).mpr h.2⟩

@[expose] def liftSU :
    SU6 →* stdLevi firstJ :=
  ((groupA.subtype.comp liftA).comp SU6.subtype).codRestrict (stdLevi firstJ) liftA_mem_stdLevi

theorem coe_liftSU
    (h : SU6) :
    ((liftSU h : stdLevi firstJ) : ModGL Tag.E6 K) =
      ((liftA (h : SpecialLinearGroup (Fin 6) K) : groupA) : ModGL Tag.E6 K) :=
  rfl

theorem psiA_liftSU
    (h : SU6) :
    psiA ⟨((liftSU h : stdLevi firstJ) : ModGL Tag.E6 K),
      stdLevi_firstJ_le_groupA (liftSU h).2⟩ = cubeHom (h : SpecialLinearGroup (Fin 6) K) :=
  psiA_liftA _

theorem liftSU_eq_iff
    {h : SU6} {l : stdLevi firstJ} :
    liftSU h = l ↔ psiA ⟨(l : ModGL Tag.E6 K), stdLevi_firstJ_le_groupA l.2⟩ =
      cubeHom (h : SpecialLinearGroup (Fin 6) K) := by
  constructor
  · rintro rfl
    exact psiA_liftSU h
  · intro e
    have e2 := congrArg Subtype.val (liftA_eq_of_psiA_eq e)
    exact Subtype.ext e2

theorem liftSU_surjective :
    Function.Surjective liftSU := by
  intro l
  obtain ⟨h, hh⟩ : psiA ⟨(l : ModGL Tag.E6 K), stdLevi_firstJ_le_groupA l.2⟩ ∈
      (cubeHom (K := K)).range := by
    rw [← range_psiA]
    exact ⟨_, rfl⟩
  have hl : (l : ModGL Tag.E6 K) ∈ stdFixedGroup :=
    (Subgroup.mem_inf.mp (stdLevi_firstJ.le l.2)).2
  have hSU : h ∈ SU6 := (mem_stdFixedGroup_iff hh.symm).mp hl
  exact ⟨⟨h, hSU⟩, liftSU_eq_iff.mpr hh.symm⟩

theorem liftSU_eq_one_iff
    (h : SU6) :
    liftSU h = 1 ↔ (h : SpecialLinearGroup (Fin 6) K) ∈ LinearFlag.scalars 6 K := by
  rw [← ker_cubeHom, MonoidHom.mem_ker]
  constructor
  · intro e
    have := psiA_liftSU h
    rw [e] at this
    rw [← this]
    exact map_one psiA
  · intro e
    refine liftSU_eq_iff.mpr ?_
    rw [e]
    exact map_one psiA

theorem ker_liftSU
    : liftSU.ker = (LinearFlag.scalars 6 K).subgroupOf SU6 := by
  ext h
  rw [MonoidHom.mem_ker, liftSU_eq_one_iff, Subgroup.mem_subgroupOf]

@[expose] def leviSUEquiv
    : stdLevi firstJ ≃* SU6 ⧸ (LinearFlag.scalars 6 K).subgroupOf SU6 :=
  ((QuotientGroup.quotientMulEquivOfEq ker_liftSU).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective liftSU liftSU_surjective)).symm

theorem leviSUEquiv_liftSU
    (h : SU6) : leviSUEquiv (liftSU h) = (h : SU6 ⧸ _) := by
  rw [leviSUEquiv, MulEquiv.symm_apply_eq]
  rfl

theorem leviSUEquiv_apply
    {l : stdLevi firstJ} {h : SU6}
    (e : psiA ⟨(l : ModGL Tag.E6 K), stdLevi_firstJ_le_groupA l.2⟩ =
      cubeHom (h : SpecialLinearGroup (Fin 6) K)) :
    leviSUEquiv l = (h : SU6 ⧸ _) := by
  rw [← liftSU_eq_iff.mpr e, leviSUEquiv_liftSU]

@[expose] def suOf
    (l : stdLevi firstJ) : SU6 :=
  Function.surjInv liftSU_surjective l

theorem liftSU_suOf
    (l : stdLevi firstJ) : liftSU (suOf l) = l :=
  Function.surjInv_eq liftSU_surjective l

theorem psiA_suOf
    (l : stdLevi firstJ) :
    psiA ⟨(l : ModGL Tag.E6 K), stdLevi_firstJ_le_groupA l.2⟩ =
      cubeHom (suOf l : SpecialLinearGroup (Fin 6) K) :=
  liftSU_eq_iff.mp (liftSU_suOf l)

theorem smul_eq_of_liftSU_eq
    {h h' : SU6} (e : liftSU h = liftSU h') (F : IsoFlag6) :
    h • F = h' • F := by
  have hz : liftSU (h⁻¹ * h') = 1 := by rw [map_mul, map_inv, e, inv_mul_cancel]
  rw [liftSU_eq_one_iff] at hz
  have := smul_eq_of_mem_scalars hz F
  rw [mul_smul, inv_smul_eq_iff] at this
  exact this.symm

theorem suOf_mul_smul
    (l l' : stdLevi firstJ) (F : IsoFlag6) :
    suOf (l * l') • F = suOf l • suOf l' • F := by
  rw [← mul_smul]
  exact smul_eq_of_liftSU_eq (by rw [map_mul, liftSU_suOf, liftSU_suOf, liftSU_suOf]) F

theorem suOf_liftSU_smul
    (h : SU6) (F : IsoFlag6) : suOf (liftSU h) • F = h • F :=
  smul_eq_of_liftSU_eq (liftSU_suOf _) F

theorem bar_mul_rev_of_upper {h : SpecialLinearGroup (Fin 6) K} (hh : h ∈ SU6)
    (hup : ∀ i j : Fin 6, j < i → (h : Matrix (Fin 6) (Fin 6) K) i j = 0) (i : Fin 6) :
    bar ((h : Matrix (Fin 6) (Fin 6) K) i i) *
      (h : Matrix (Fin 6) (Fin 6) K) (Fin.rev i) (Fin.rev i) = 1 := by
  set M := (h : Matrix (Fin 6) (Fin 6) K) with hM
  have e := congrFun (congrFun ((mem_SU6_iff h).mp hh) i) (Fin.rev i)
  change ((M.map bar)ᵀ * J6 * M) i (Fin.rev i) = J6 i (Fin.rev i) at e
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i), mul_J6_apply, transpose_apply,
    map_apply, Fin.rev_rev, J6_apply, ite_eq_left rfl] at e
  · exact e
  · intro k _ hk
    rw [mul_J6_apply, transpose_apply, map_apply]
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have hik : i < Fin.rev k := by
        have := Fin.rev_lt_rev.mpr hlt
        rwa [Fin.rev_rev] at this
      rw [hup (Fin.rev k) i hik, bar_zero, zero_mul]
    · rw [hup k (Fin.rev i) hgt, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem exists_diag_mul {h : SpecialLinearGroup (Fin 6) K} (hh : h ∈ SU6)
    (hup : ∀ i j : Fin 6, j < i → (h : Matrix (Fin 6) (Fin 6) K) i j = 0) :
    ∃ d u : SpecialLinearGroup (Fin 6) K, d ∈ diagSL ∧ d ∈ SU6 ∧
      u ∈ LinearFlag.unitriangular 6 K ∧ u ∈ SU6 ∧ h = d * u := by
  set M := (h : Matrix (Fin 6) (Fin 6) K) with hM
  set f : Fin 6 → K := fun i => M i i with hf
  have hunit := bar_mul_rev_of_upper hh hup
  have hf0 : ∀ i, f i ≠ 0 := fun i h0 => by
    have := hunit (Fin.rev i)
    rw [Fin.rev_rev] at this
    change bar (M (Fin.rev i) (Fin.rev i)) * f i = 1 at this
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hdet : (diagonal f).det = 1 := by
    rw [det_diagonal]
    have := Matrix.det_of_isUpperTriangular (M := M) fun i j hij => hup i j hij
    rw [← this]
    exact h.2
  have hdet' : (diagonal (fun i => (f i)⁻¹) * M).det = 1 := by
    rw [det_mul, det_diagonal, h.2, mul_one, Finset.prod_inv_distrib, ← det_diagonal, hdet,
      inv_one]
  let d : SpecialLinearGroup (Fin 6) K := ⟨diagonal f, hdet⟩
  let u : SpecialLinearGroup (Fin 6) K := ⟨diagonal (fun i => (f i)⁻¹) * M, hdet'⟩
  have hdu : h = d * u := by
    apply Subtype.ext
    change M = diagonal f * (diagonal (fun i => (f i)⁻¹) * M)
    rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
    have : (fun i => f i * (f i)⁻¹) = fun _ => (1 : K) := funext fun i => mul_inv_cancel₀ (hf0 i)
    rw [this, diagonal_one, Matrix.one_mul]
  have hd : d ∈ SU6 := by
    refine (mem_SU6_iff d).mpr ?_
    change ((diagonal f).map bar)ᵀ * J6 * diagonal f = J6
    ext i j
    rw [mul_diagonal, Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · rw [transpose_apply, map_apply, diagonal_apply_eq]
      change (bar (f i) * (if j = Fin.rev i then 1 else 0)) * f j = (if j = Fin.rev i then 1 else 0)
      by_cases hj : j = Fin.rev i
      · rw [ite_eq_left hj, mul_one, hj]
        exact hunit i
      · rw [ite_eq_right hj, mul_zero, zero_mul]
    · intro k _ hk
      rw [transpose_apply, map_apply, diagonal_apply_ne f hk, bar_zero, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  refine ⟨d, u, mem_diagSL.mpr ⟨f, rfl⟩, hd, ⟨fun i j hij => ?_, fun i => ?_⟩, ?_, hdu⟩
  · change (diagonal (fun i => (f i)⁻¹) * M) i j = 0
    rw [diagonal_mul, hup i j hij, mul_zero]
  · change (diagonal (fun i => (f i)⁻¹) * M) i i = 1
    rw [diagonal_mul]
    exact inv_mul_cancel₀ (hf0 i)
  · have : u = d⁻¹ * h := by rw [hdu, inv_mul_cancel_left]
    rw [this]
    exact mul_mem (inv_mem hd) hh

theorem stdTorus_le_torusA :
    stdTorus ≤ torusA := by
  rw [← stdTorus0_eq_stdTorus, stdTorus0_eq_zpowers]
  exact Subgroup.zpowers_le.mpr fixedTorusGen_mem_torusA

theorem mem_stdTorus_of_mem_torusA
    {t : ModGL Tag.E6 K} (ht : t ∈ torusA)
    (hΓ : t ∈ stdFixedGroup) : t ∈ stdTorus := by
  rw [← stdTorus0_eq_stdTorus]
  exact ⟨subsystemTorus_le_torusGroup ht, hΓ⟩

theorem liftA_mem_torusA
    {d : SpecialLinearGroup (Fin 6) K} (hd : d ∈ diagSL) :
    ((liftA d : groupA) : ModGL Tag.E6 K) ∈ torusA := by
  have hmem : cubeHom d ∈ (torusA.subgroupOf groupA).map psiA := by
    rw [map_psiA_torusA]
    exact ⟨d, hd, rfl⟩
  obtain ⟨t, ht, hte⟩ := hmem
  rw [liftA_eq_of_psiA_eq hte]
  exact ht

theorem liftA_mem_unipotentA
    {u : SpecialLinearGroup (Fin 6) K}
    (hu : u ∈ LinearFlag.unitriangular 6 K) :
    ((liftA u : groupA) : ModGL Tag.E6 K) ∈ unipotentA := by
  have hmem : cubeHom u ∈ (unipotentA.subgroupOf groupA).map psiA := by
    rw [map_psiA_unipotentA]
    exact ⟨u, hu, rfl⟩
  obtain ⟨v, hv, hve⟩ := hmem
  rw [liftA_eq_of_psiA_eq hve]
  exact hv

theorem exists_diagSL_of_mem_torusA
    {t : groupA} (ht : (t : ModGL Tag.E6 K) ∈ torusA) :
    ∃ d ∈ diagSL, cubeHom d = psiA t := by
  have hmem : psiA t ∈ (torusA.subgroupOf groupA).map psiA := ⟨t, ht, rfl⟩
  rw [map_psiA_torusA] at hmem
  exact hmem

theorem exists_unitri_of_mem_unipotentA
    {v : groupA} (hv : (v : ModGL Tag.E6 K) ∈ unipotentA) :
    ∃ u ∈ LinearFlag.unitriangular 6 K, cubeHom u = psiA v := by
  have hmem : psiA v ∈ (unipotentA.subgroupOf groupA).map psiA := ⟨v, hv, rfl⟩
  rw [map_psiA_unipotentA] at hmem
  exact hmem

theorem mem_upperTriangular_of_mem_diagSL {d : SpecialLinearGroup (Fin 6) K} (hd : d ∈ diagSL) :
    d ∈ LinearFlag.upperTriangular 6 K := by
  obtain ⟨f, hf⟩ := mem_diagSL.mp hd
  intro i j hij
  rw [hf, diagonal_apply_ne _ (ne_of_gt hij)]

theorem liftSU_mem_stdLeviBorel_iff
    (h : SU6) :
    ((liftSU h : stdLevi firstJ) : ModGL Tag.E6 K) ∈ stdLeviBorel firstJ ↔
      h • baseFlag = baseFlag := by
  constructor
  · intro hB
    have hB' : ((liftSU h : stdLevi firstJ) : ModGL Tag.E6 K) ∈
        (stdTorus : Set (ModGL Tag.E6 K)) * (stdLeviUnipotent firstJ : Set (ModGL Tag.E6 K)) := by
      rw [← coe_stdLeviBorel]
      exact hB
    obtain ⟨t, ht, v, hv, htv⟩ := Set.mem_mul.mp hB'
    rw [SetLike.mem_coe, stdLeviUnipotent_firstJ] at hv
    have htA : t ∈ torusA := stdTorus_le_torusA ht
    obtain ⟨d, hd, hdt⟩ := exists_diagSL_of_mem_torusA (t := ⟨t, torusA_le_groupA htA⟩) htA
    obtain ⟨u, hu, huv⟩ := exists_unitri_of_mem_unipotentA (v := ⟨v, unipotentA_le_groupA hv.1⟩)
      hv.1
    have hl : (⟨((liftSU h : stdLevi firstJ) : ModGL Tag.E6 K),
        stdLevi_firstJ_le_groupA (liftSU h).2⟩ : groupA) =
          ⟨t, torusA_le_groupA htA⟩ * ⟨v, unipotentA_le_groupA hv.1⟩ := Subtype.ext htv.symm
    have e := psiA_liftSU h
    rw [hl, map_mul, ← hdt, ← huv, ← map_mul, cubeHom_eq_cubeHom_iff] at e
    refine (smul_baseFlag_eq_iff h).mpr ?_
    have hz := LinearFlag.mem_scalars.mp e
    have hupper : (h : SpecialLinearGroup (Fin 6) K) ∈ LinearFlag.upperTriangular 6 K := by
      have : (h : SpecialLinearGroup (Fin 6) K) = d * u * ((d * u)⁻¹ * h) := by
        rw [mul_inv_cancel_left]
      rw [this]
      refine mul_mem (mul_mem (mem_upperTriangular_of_mem_diagSL hd) hu.1)
        (mem_upperTriangular_of_mem_diagSL (scalars_le_diagSL e))
    exact hupper
  · intro hF
    obtain ⟨d, u, hd, hdSU, hu, huSU, hdu⟩ :=
      exists_diag_mul h.2 ((smul_baseFlag_eq_iff h).mp hF)
    rw [coe_liftSU, hdu, map_mul, Subgroup.coe_mul]
    refine mul_mem (Subgroup.mem_sup_left (mem_stdTorus_of_mem_torusA (liftA_mem_torusA hd)
      ((mem_stdFixedGroup_iff (psiA_liftA d)).mpr hdSU))) (Subgroup.mem_sup_right ?_)
    rw [stdLeviUnipotent_firstJ]
    exact ⟨liftA_mem_unipotentA hu, (mem_stdFixedGroup_iff (psiA_liftA u)).mpr huSU⟩

theorem neg_one_units_K : (-1 : Kˣ) = 1 :=
  Units.ext (CharTwo.neg_eq (1 : K))

theorem weylElt_mul_canonicalRep_charTwo
    (i : Fin Tag.E6.rank) (w : WeylGroup Tag.E6) :
    weylElt Tag.E6 K i 1 * canonicalRep (coxeterSystem Tag.E6) K w =
      canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).simple i * w) := by
  rw [weylElt_mul_canonicalRep]
  split_ifs
  · rfl
  · rw [neg_one_units_K, torusElt_one, one_mul]

theorem canonicalRep_wordProd_mul_charTwo
    (ω : List (Fin Tag.E6.rank)) (v : WeylGroup Tag.E6) :
    canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).wordProd ω * v) =
      (ω.map fun i => weylElt Tag.E6 K i 1).prod * canonicalRep (coxeterSystem Tag.E6) K v := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_mul, List.map_nil, List.prod_nil, one_mul]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_assoc, ← weylElt_mul_canonicalRep_charTwo, ih,
      List.map_cons, List.prod_cons, mul_assoc]

theorem canonicalRep_wordProd_charTwo
    (ω : List (Fin Tag.E6.rank)) :
    canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).wordProd ω) =
      (ω.map fun i => weylElt Tag.E6 K i 1).prod := by
  have h := canonicalRep_wordProd_mul_charTwo ω 1
  rwa [mul_one, canonicalRep_one, mul_one] at h

theorem canonicalRep_mul_charTwo
    (w v : WeylGroup Tag.E6) :
    canonicalRep (coxeterSystem Tag.E6) K (w * v) =
      canonicalRep (coxeterSystem Tag.E6) K w * canonicalRep (coxeterSystem Tag.E6) K v := by
  obtain ⟨ω, -, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  rw [canonicalRep_wordProd_mul_charTwo, canonicalRep_wordProd_charTwo]

theorem weylElt_mem_groupA
    (t : Fin 5) : weylElt Tag.E6 K (jA t) 1 ∈ groupA :=
  weylElt_mem_subsystemGroup (jA_mem_setA t) 1

theorem psiA_weylElt (t : Fin 5) :
    psiA ⟨weylElt Tag.E6 K (jA t) 1, weylElt_mem_groupA t⟩ = cubeHom (wAdj t) := by
  have e : (⟨weylElt Tag.E6 K (jA t) 1, weylElt_mem_groupA t⟩ : groupA) =
      ⟨xUnit Tag.E6 K (jA t) 1, xUnit_mem_groupA t 1⟩ *
        ⟨yUnit Tag.E6 K (jA t) (-1), yUnit_mem_groupA t (-1)⟩ *
          ⟨xUnit Tag.E6 K (jA t) 1, xUnit_mem_groupA t 1⟩ := by
    apply Subtype.ext
    change weylElt Tag.E6 K (jA t) 1 =
      xUnit Tag.E6 K (jA t) 1 * yUnit Tag.E6 K (jA t) (-1) * xUnit Tag.E6 K (jA t) 1
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, inv_one, Units.val_one]
  rw [e, map_mul, map_mul, psiA_xUnit, psiA_yUnit, ← map_mul, ← map_mul]

theorem orbitWord_one : TwistTag.E6.orbitWord (foldedIndex 1) =
    ([⟨3, by decide⟩] : List (Fin TwistTag.E6.tag.rank)) := by
  decide

theorem orbitWord_two : TwistTag.E6.orbitWord (foldedIndex 2) =
    ([⟨2, by decide⟩, ⟨4, by decide⟩] : List (Fin TwistTag.E6.tag.rank)) := by
  decide

theorem orbitWord_three : TwistTag.E6.orbitWord (foldedIndex 3) =
    ([⟨0, by decide⟩, ⟨5, by decide⟩] : List (Fin TwistTag.E6.tag.rank)) := by
  decide

theorem orbitReflection_one
    : TwistTag.E6.orbitReflection (foldedIndex 1) =
    (coxeterSystem TwistTag.E6.tag).simple ⟨3, by decide⟩ := by
  rw [TwistTag.orbitReflection, orbitWord_one, CoxeterSystem.wordProd_singleton]

theorem orbitReflection_two
    : TwistTag.E6.orbitReflection (foldedIndex 2) =
    (coxeterSystem TwistTag.E6.tag).simple ⟨2, by decide⟩ *
      (coxeterSystem TwistTag.E6.tag).simple ⟨4, by decide⟩ := by
  rw [TwistTag.orbitReflection, orbitWord_two, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_singleton]

theorem orbitReflection_three
    : TwistTag.E6.orbitReflection (foldedIndex 3) =
    (coxeterSystem TwistTag.E6.tag).simple ⟨0, by decide⟩ *
      (coxeterSystem TwistTag.E6.tag).simple ⟨5, by decide⟩ := by
  rw [TwistTag.orbitReflection, orbitWord_three, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_singleton]

theorem nativeRep_one
    : nativeRep 1 = weylElt Tag.E6 K (jA 2) 1 := by
  have e : nativeRefl 1 = (coxeterSystem Tag.E6).simple (jA 2) :=
    (nativeRefl_eq 1).trans orbitReflection_one
  rw [nativeRep, e, canonicalRep_simple]

theorem nativeRep_two
    : nativeRep 2 = weylElt Tag.E6 K (jA 1) 1 * weylElt Tag.E6 K (jA 3) 1 := by
  have e : nativeRefl 2 =
      (coxeterSystem Tag.E6).simple (jA 1) * (coxeterSystem Tag.E6).simple (jA 3) :=
    (nativeRefl_eq 2).trans orbitReflection_two
  rw [nativeRep, e, canonicalRep_mul_charTwo, canonicalRep_simple, canonicalRep_simple]

theorem nativeRep_three :
    nativeRep 3 = weylElt Tag.E6 K (jA 0) 1 * weylElt Tag.E6 K (jA 4) 1 := by
  have e : nativeRefl 3 =
      (coxeterSystem Tag.E6).simple (jA 0) * (coxeterSystem Tag.E6).simple (jA 4) :=
    (nativeRefl_eq 3).trans orbitReflection_three
  rw [nativeRep, e, canonicalRep_mul_charTwo, canonicalRep_simple, canonicalRep_simple]

@[expose] def typeDim : Fin 4 → Fin 3 := ![0, 2, 1, 0]

theorem nativeRep_mem_groupA
    {i : Fin 4} (hi : i ∈ firstJ) : nativeRep i ∈ groupA :=
  stdLevi_firstJ_le_groupA (nativeRep_mem_stdLevi hi)

theorem psiA_nativeRep
    {i : Fin 4} (hi : i ∈ firstJ) :
    psiA ⟨nativeRep i, nativeRep_mem_groupA hi⟩ = cubeHom (weylMat (typeDim i)) := by
  rcases hi with rfl | rfl | rfl
  · have e : (⟨nativeRep 1, nativeRep_mem_groupA (by simp [firstJ])⟩ : groupA) =
        ⟨weylElt Tag.E6 K (jA 2) 1, weylElt_mem_groupA 2⟩ := Subtype.ext nativeRep_one
    rw [e, psiA_weylElt]
    rfl
  · have e : (⟨nativeRep 2, nativeRep_mem_groupA (by simp [firstJ])⟩ : groupA) =
        ⟨weylElt Tag.E6 K (jA 1) 1, weylElt_mem_groupA 1⟩ *
          ⟨weylElt Tag.E6 K (jA 3) 1, weylElt_mem_groupA 3⟩ := Subtype.ext nativeRep_two
    rw [e, map_mul, psiA_weylElt, psiA_weylElt, ← map_mul]
    rfl
  · have e : (⟨nativeRep 3, nativeRep_mem_groupA (by simp [firstJ])⟩ : groupA) =
        ⟨weylElt Tag.E6 K (jA 0) 1, weylElt_mem_groupA 0⟩ *
          ⟨weylElt Tag.E6 K (jA 4) 1, weylElt_mem_groupA 4⟩ := Subtype.ext nativeRep_three
    rw [e, map_mul, psiA_weylElt, psiA_weylElt, ← map_mul]
    rfl

theorem liftSU_weylSU
    {i : Fin 4} (hi : i ∈ firstJ) :
    liftSU (weylSU (typeDim i)) = ⟨nativeRep i, nativeRep_mem_stdLevi hi⟩ :=
  liftSU_eq_iff.mpr (psiA_nativeRep hi)

end CFSG.LieType.Chevalley.C2E6Std
