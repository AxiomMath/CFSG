module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BBlk
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrthPc
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSL3F
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOOrth2
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCore
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSL3X

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

namespace P58b3L

variable {K : Type} [Field K]

theorem not_isSquare_neg_one_of_card_three [Finite K] (hK3 : Nat.card K = 3) :
    ¬ IsSquare (-1 : K) := by
  rintro ⟨s, hs⟩
  have h2 := Foote5.OddLieCore.two_ne_zero_of_card hK3
  rcases Foote5.OddLieCore.eq_zero_or_one_or_neg_one hK3 s with h | h | h
  · rw [h, mul_zero] at hs
    exact one_ne_zero (neg_eq_zero.mp hs)
  · rw [h, mul_one] at hs
    exact h2 (by linear_combination -hs)
  · rw [h, neg_one_mul, neg_neg] at hs
    exact h2 (by linear_combination -hs)

theorem pow_four_eq_one_of_commute_unitarySU {E : Type} [Field E] (h : UnitaryFieldData 3 1 E)
    {n : ℕ} (hn : 2 ≤ n) {Y : GL (Fin n) E} (hY : Y ∈ uGrp h.bar (1 : Matrix (Fin n) (Fin n) E))
    (hc : ∀ g ∈ unitarySU 3 1 E n, Y * g = g * Y) : Y ^ 4 = 1 := by
  have hcm : ∀ g ∈ Burgoyne.U.uBlock 3 1 E (Finset.univ : Finset (Fin n)),
      (Y : Matrix (Fin n) (Fin n) E) * ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * Y := by
    intro g _
    have e := congrArg Units.val (hc (g : GL (Fin n) E) g.2)
    simpa only [Units.val_mul] using e
  obtain ⟨hoff, hdiag⟩ := Burgoyne.U.eq_of_commute_uBlock h
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hn) hcm
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set l := (Y : Matrix (Fin n) (Fin n) E) i₀ i₀ with hl
  have hYl : (Y : Matrix (Fin n) (Fin n) E) = l • 1 := by
    ext i j
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, mul_one, hdiag i (Finset.mem_univ _) i₀ (Finset.mem_univ _)]
    · rw [ite_eq_right hij, mul_zero]
      exact (hoff i (Finset.mem_univ _) j (Ne.symm hij)).1
  have hU := (mem_uGrp h.bar 1 Y).1 hY
  rw [Matrix.mul_one, hYl, Matrix.map_smul' _ _ _ (map_mul h.bar),
    Matrix.map_one _ (map_zero _) (map_one _), transpose_smul, transpose_one, Matrix.smul_mul,
    Matrix.one_mul, smul_smul] at hU
  have e := congrFun (congrFun hU i₀) i₀
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, h.bar_apply, pow_one] at e
  have hl4 : l ^ 4 = 1 := by linear_combination e
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hYl, smul_pow, one_pow, hl4, one_smul, Units.val_one]

theorem eq_one_of_odd_of_pc [Finite K] (hK3 : Nat.card K = 3) {n : ℕ} (hn : 3 ≤ n)
    {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(-1 : K))))
    {A : matrixDerived (oQ R)}
    (hA : ((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat (-1 : K)))
    {R₁ : Subgroup (StatedProj (matrixDerived (oQ R)))}
    (hR₁x : R₁ ≤ centralizer ({projH _ A} : Set _))
    (hR₁s : (R₁.subgroupOf (centralizer ({projH _ A} : Set _))).IsSubnormal)
    (hR₁solv : Group.IsSolvable ↥R₁) {r : StatedProj (matrixDerived (oQ R))} (hr : r ∈ R₁)
    (hro : Odd (orderOf r)) : r = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hKc : Nat.card K = 3 ^ 1 := by rw [hK3, pow_one]
  have hc0 : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hsq := not_isSquare_neg_one_of_card_three hK3
  have : Fact (Irreducible (sqPoly (-1 : K))) := ⟨irreducible_sqPoly hsq⟩
  have hu := unitaryFieldData_EAlg hc0 Nat.prime_three hKc
  have : Finite (EAlg (-1 : K)) := hu.finite
  have : CharP (EAlg (-1 : K)) 3 := hu.charP
  have hσ : ∀ x : EAlg (-1 : K), hu.bar x = x ^ Nat.card K := fun x => by
    rw [hu.bar_apply, hKc]
  have hW : ∀ x, ((phiE (-1 : K)).toRingHom x)ᵀ * wMat 1 (-(-1 : K)) =
      wMat 1 (-(-1 : K)) * (phiE (-1 : K)).toRingHom (hu.bar x) := fun x => by
    rw [hσ]
    exact transpose_phiE_mul_wNeg hK hsq x
  have hRG : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 (-(-1 : K))) * resMat (phiE (-1 : K)).toRingHom n 1 := by
    rw [map_one, Matrix.mul_one, hR]
  have hZeq := iso_inf_centralizer_eq (φ := (phiE (-1 : K)).toRingHom) (σ := hu.bar)
    (r := AdjoinRoot.root (sqPoly (-1 : K))) (phiE_injective (-1 : K)) (wMat_inv_mul hc0) hW
    (phiE_root (-1 : K)) (fun M hM => phiE_mem_range hc0 hM) 1 hRG hA
  have hZZeq : ⁅isoCent R (A : GL (Fin (2 * n)) K), isoCent R (A : GL (Fin (2 * n)) K)⁆ =
      (unitarySU 3 1 (EAlg (-1 : K)) n).map (resGL (phiE (-1 : K)).toRingHom n) := by
    rw [commutator_iso_inf_centralizer_eq (phiE_injective (-1 : K)) (wMat_inv_mul hc0) hW
      (phiE_root (-1 : K)) (fun M hM => phiE_mem_range hc0 hM) 1 hRG hA,
      commutator_uGrp_eq_unitarySU hu hn (by norm_num)]
  have hq := Burgoyne.C.isQuasisimple_isoCent_pc hK Nat.prime_three hKc hc0 hn hR hA
  set Z := isoCent R (A : GL (Fin (2 * n)) K) with hZdef
  have hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R := by
    rw [hR, blkDiag_transpose, wMat, diagonal_transpose]
  have hHeq : matrixDerived (oQ R) = ⁅CatalogueBGraphForm.isometryGroup (2 * n) K R,
      CatalogueBGraphForm.isometryGroup (2 * n) K R⁆ := matrixDerived_oQ h2 R hRs
  have hZΩ : ⁅Z, Z⁆ ≤ matrixDerived (oQ R) := by
    rw [hHeq]
    exact commutator_mono inf_le_left inf_le_left
  have hΩI : ∀ g : matrixDerived (oQ R),
      (g : GL (Fin (2 * n)) K) ∈ CatalogueBGraphForm.isometryGroup (2 * n) K R := fun g =>
    Subgroup.commutator_le_self _ (by rw [← hHeq]; exact g.2)
  set N := ((⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R))).map (projH _) with hN
  set C := centralizer ({projH (matrixDerived (oQ R)) A} :
    Set (StatedProj (matrixDerived (oQ R)))) with hC
  have hNC : N ≤ C := by
    rintro _ ⟨g, hg, rfl⟩
    replace hg : (g : GL (Fin (2 * n)) K) ∈ ⁅Z, Z⁆ := hg
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hgZ : (g : GL (Fin (2 * n)) K) ∈ Z := commutator_le_self _ hg
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 hgZ).2
  set φ := (projH (matrixDerived (oQ R))).comp
    (((⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R))).subtype.comp
      (subgroupOfEquivOfLe hZΩ).symm.toMonoidHom) with hφ
  have hφr : φ.range = N := by
    rw [hφ, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      (subgroupOfEquivOfLe hZΩ).symm.surjective, Subgroup.map_top, Subgroup.range_subtype]
  have hNq : IsQuasisimple N := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hq φ with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hq.2.2
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      have hφa : φ a = 1 := by
        have : φ a ∈ φ.range := ⟨a, rfl⟩
        rw [h] at this
        exact this
      have h1 : projH (matrixDerived (oQ R)) ⟨a, hZΩ a.2⟩ = 1 := hφa
      obtain ⟨u, hu'⟩ := mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      change (a : GL (Fin (2 * n)) K) * (b : GL (Fin (2 * n)) K) = (b : GL (Fin (2 * n)) K) * a
      rw [← hu']
      exact (Burgoyne.O.commute_scalar u _).eq.symm
    · rwa [hφr] at h
  set a : GL (Fin (2 * n)) K := (A : GL (Fin (2 * n)) K) with ha
  have hconjA : ∀ B₀ : matrixDerived (oQ R), projH _ B₀ ∈ C →
      ∃ ε : Kˣ, a * (B₀ : GL (Fin (2 * n)) K) * a⁻¹ =
        GeneralLinearGroup.scalar (Fin (2 * n)) ε * (B₀ : GL (Fin (2 * n)) K) := by
    intro B₀ hB₀
    have h1 : projH _ (B₀ * A) = projH _ (A * B₀) := by
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.mp hB₀
    rw [projH_eq_projH_iff] at h1
    obtain ⟨ε, hε⟩ := mem_subgroupOf.mp h1
    refine ⟨ε, ?_⟩
    set b : GL (Fin (2 * n)) K := (B₀ : GL (Fin (2 * n)) K) with hb
    set s : GL (Fin (2 * n)) K := GeneralLinearGroup.scalar (Fin (2 * n)) ε with hs_def
    have hs : ∀ x : GL (Fin (2 * n)) K, s * x = x * s := fun x =>
      (Burgoyne.O.commute_scalar ε x).eq.symm
    have e : a * b = b * a * s := by
      rw [hε]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← ha, ← hb]
      group
    calc a * b * a⁻¹ = b * a * (s * a⁻¹) := by rw [e, mul_assoc]
      _ = b * a * (a⁻¹ * s) := by rw [hs]
      _ = s * b := by rw [← mul_assoc, mul_inv_cancel_right, hs]
  have hNn : ∀ g ∈ C, ∀ y ∈ N, g * y * g⁻¹ ∈ N := by
    intro g hg y hy
    obtain ⟨B₀, rfl⟩ := projH_surjective g
    obtain ⟨Y, hY, rfl⟩ := hy
    obtain ⟨ε, hε⟩ := hconjA B₀ hg
    refine ⟨B₀ * Y * B₀⁻¹, mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_commutator_isoCent (hΩI B₀) hε (mem_subgroupOf.mp hY)
  have hNcomp : CFSG.IsComponent (N.subgroupOf C) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hNC).symm hNq,
      Burgoyne.PSL.isSubnormal_subgroupOf_of_normalizes hNC hNn
        (by rw [Subgroup.subgroupOf_self]; exact Subgroup.Normal.isSubnormal inferInstance)⟩
  have hRs' : Group.IsSolvable (R₁.subgroupOf C) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hR₁x).toMonoidHom)
      (subgroupOfEquivOfLe hR₁x).injective
  have hcommN := (LocalCores.component_solvable_centralizer hRs' hR₁s).1 _ hNcomp
  have hrc : ∀ y ∈ N, r * y = y * r := by
    intro y hy
    have h := Subgroup.commutator_mem_commutator
      (show (⟨y, hNC hy⟩ : ↥C) ∈ N.subgroupOf C from mem_subgroupOf.mpr hy)
      (show (⟨r, hR₁x hr⟩ : ↥C) ∈ R₁.subgroupOf C from mem_subgroupOf.mpr hr)
    rw [hcommN, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact (congrArg Subtype.val h).symm
  obtain ⟨B₀, rfl⟩ := projH_surjective r
  obtain ⟨ε, hε⟩ := hconjA B₀ (hR₁x hr)
  set b : GL (Fin (2 * n)) K := (B₀ : GL (Fin (2 * n)) K) with hb
  set s : GL (Fin (2 * n)) K := GeneralLinearGroup.scalar (Fin (2 * n)) ε with hs_def
  have hs : ∀ x : GL (Fin (2 * n)) K, s * x = x * s := fun x =>
    (Burgoyne.O.commute_scalar ε x).eq.symm
  have hAA : a * a = GeneralLinearGroup.scalar (Fin (2 * n)) (-1) := by
    apply Units.ext
    rw [Units.val_mul, ha, hA, blkDiag_mul, jMat_mul_self, blkDiag_smul_one,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      Units.val_neg, Units.val_one]
  have hε2 : s * s = 1 := by
    have e1 : b = (a * a) * b * (a * a)⁻¹ := by
      rw [hAA, (Burgoyne.O.commute_scalar (-1) b).eq.symm, mul_inv_cancel_right]
    have e2 : (a * a) * b * (a * a)⁻¹ = s * s * b := by
      calc (a * a) * b * (a * a)⁻¹ = a * (a * b * a⁻¹) * a⁻¹ := by group
        _ = a * (s * b) * a⁻¹ := by rw [hε]
        _ = s * (a * b * a⁻¹) := by
          rw [← mul_assoc a, ← hs a]
          group
        _ = s * s * b := by rw [hε, mul_assoc]
    calc s * s = s * s * b * b⁻¹ := by rw [mul_inv_cancel_right]
      _ = 1 := by rw [← e2, ← e1, mul_inv_cancel]
  set m := orderOf (projH (matrixDerived (oQ R)) B₀) with hm
  obtain ⟨k, hk⟩ := hro
  set B : matrixDerived (oQ R) := B₀ ^ (m + 1) with hBdef
  have hBr : projH (matrixDerived (oQ R)) B = projH _ B₀ := by
    rw [hBdef, map_pow, pow_succ, hm, pow_orderOf_eq_one, one_mul]
  have hBA : a * (B : GL (Fin (2 * n)) K) * a⁻¹ = B := by
    have hmk : m + 1 = 2 * (k + 1) := by omega
    have hsB : Commute s b := (Burgoyne.O.commute_scalar ε b).symm
    rw [hBdef, Subgroup.coe_pow, ← hb, ← conj_pow, hε, hsB.mul_pow, hmk, pow_mul, pow_two, hε2,
      one_pow, one_mul]
  have hBZ : (B : GL (Fin (2 * n)) K) ∈ Z :=
    Subgroup.mem_inf.mpr ⟨hΩI B, mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp hBA).symm⟩
  have hFperf : ⁅(⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R)),
      (⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R))⁆ =
      (⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R)) := by
    apply Subgroup.map_injective (matrixDerived (oQ R)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hZΩ,
      Burgoyne.PSL.commutator_eq_self_of_isQuasisimple hq]
  have hψ : ∀ g, MulAut.conj (projH (matrixDerived (oQ R)) B) (projH _ g) =
      projH _ ((MulAut.conj B).toMonoidHom g) := fun g => by
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  have hfixF : ∀ g ∈ (⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R)),
      MulAut.conj (projH (matrixDerived (oQ R)) B) (projH _ g) = projH _ g := by
    intro g hg
    rw [MulAut.conj_apply, hBr, hrc _ ⟨g, hg, rfl⟩, mul_inv_cancel_right]
  have hcB : ∀ y ∈ ⁅Z, Z⁆, (B : GL (Fin (2 * n)) K) * y = y * B := by
    intro y hy
    have h1 := lift_eq_of_commutator_eq (MulAut.conj B).toMonoidHom hψ hFperf hfixF
      (g := ⟨y, hZΩ hy⟩) (mem_subgroupOf.mpr hy)
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hBZ' : (B : GL (Fin (2 * n)) K) ∈ (uGrp hu.bar (1 : Matrix (Fin n) (Fin n)
      (EAlg (-1 : K)))).map (resGL (phiE (-1 : K)).toRingHom n) := by
    rw [← hZeq]
    exact hBZ
  obtain ⟨Y, hY, hYB⟩ := hBZ'
  have hYc : ∀ g ∈ unitarySU 3 1 (EAlg (-1 : K)) n, Y * g = g * Y := by
    intro g hg
    have hgZ : resGL (phiE (-1 : K)).toRingHom n g ∈ ⁅Z, Z⁆ := by
      rw [hZZeq]
      exact ⟨g, hg, rfl⟩
    have h1 := hcB _ hgZ
    rw [← hYB, ← map_mul, ← map_mul] at h1
    exact resGL_injective (phiE_injective (-1 : K)) n h1
  have hY4 := pow_four_eq_one_of_commute_unitarySU hu (by omega : 2 ≤ n) hY hYc
  have hB4 : B ^ 4 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, ← hYB, ← map_pow, hY4, map_one, Subgroup.coe_one])
  have hr4 : projH (matrixDerived (oQ R)) B₀ ^ 4 = 1 := by
    rw [← hBr, ← map_pow, hB4, map_one]
  have h2' : Nat.Coprime m 2 := Nat.coprime_two_right.mpr ⟨k, hk⟩
  have hcop : Nat.Coprime m 4 := Nat.Coprime.mul_right h2' h2'
  exact orderOf_eq_one_iff.1
    (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (orderOf_dvd_of_pow_eq_one hr4))

end P58b3L

end CFSG.ComponentClassification.HarrisLit.T1
