module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusNode
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusCore
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusCover

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.SeitzReduction.LinearPilot (upperUnit lowerUnit diagUnit coe_upperUnit)
open scoped MatrixGroups

section Involution

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_mul_self_eq_inv {c : K} : ∃ μ : K, μ * μ = c⁻¹ := by
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c⁻¹
  exact ⟨μ, hμ.symm⟩

theorem exists_conj_eq_upperUnit_of_involution {A : SL(2, K)} (hA1 : A ≠ 1) (hA2 : A * A = 1) :
    ∃ g : SL(2, K), g * upperUnit 1 * g⁻¹ = A := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K, M = (A : Matrix (Fin 2) (Fin 2) K) := ⟨_, rfl⟩
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two, hM]; exact A.2
  have hsq : M * M = 1 := by
    have h := congrArg (fun X : SL(2, K) => (X : Matrix (Fin 2) (Fin 2) K)) hA2
    change (A : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) = 1 at h
    rw [hM]; exact h
  have e00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 1 := by
    have := congrFun (congrFun hsq 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 = 1 := by
    have := congrFun (congrFun hsq 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hda : M 1 1 = M 0 0 := by
    have h1 : (M 0 0 - M 1 1) * (M 0 0 - M 1 1) = 0 := by
      linear_combination e00 + e11 - 2 * hdet - 2 * M 0 1 * M 1 0 * h2
    exact (sub_eq_zero.mp (mul_self_eq_zero.mp h1)).symm
  have hbc : M 0 1 * M 1 0 = M 0 0 * M 0 0 + 1 := by
    linear_combination e00 - M 0 0 * M 0 0 * h2
  have key : ∀ g : SL(2, K), M * (g : Matrix (Fin 2) (Fin 2) K) =
      (g : Matrix (Fin 2) (Fin 2) K) * (upperUnit (1 : K) : Matrix (Fin 2) (Fin 2) K) →
      g * upperUnit 1 * g⁻¹ = A := by
    intro g hg
    have h : A * g = g * upperUnit 1 := by
      apply Subtype.ext
      change (A : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) =
        (g : Matrix (Fin 2) (Fin 2) K) * (upperUnit (1 : K) : Matrix (Fin 2) (Fin 2) K)
      rw [← hM, hg]
    rw [← h]; group
  by_cases hb0 : M 0 1 = 0
  · have ha1 : M 0 0 = 1 := by
      have h1 : (M 0 0 - 1) * (M 0 0 - 1) = 0 := by
        rw [hb0, zero_mul] at hbc
        linear_combination -hbc - M 0 0 * h2
      exact sub_eq_zero.mp (mul_self_eq_zero.mp h1)
    have hc0 : M 1 0 ≠ 0 := by
      intro hc0
      apply hA1
      ext i j
      rw [← hM]
      fin_cases i <;> fin_cases j <;> simp [ha1, hb0, hc0, hda]
    obtain ⟨μ, hμ⟩ := exists_mul_self_eq_inv (c := M 1 0)
    have hμc : μ * μ * M 1 0 = 1 := by rw [hμ, inv_mul_cancel₀ hc0]
    refine ⟨⟨!![0, μ; μ * M 1 0, 0], by
      rw [Matrix.det_fin_two_of]; linear_combination -hμc - h2⟩, key _ ?_⟩
    rw [coe_upperUnit]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha1, hb0, hda]
    ring
  · obtain ⟨μ, hμ⟩ := exists_mul_self_eq_inv (c := M 0 1)
    have hμb : μ * μ * M 0 1 = 1 := by rw [hμ, inv_mul_cancel₀ hb0]
    refine ⟨⟨!![μ * M 0 1, 0; μ * (M 0 0 + 1), μ], by
      rw [Matrix.det_fin_two_of]; linear_combination hμb⟩, key _ ?_⟩
    rw [coe_upperUnit]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hda]
    · linear_combination μ * M 0 1 * M 0 0 * h2
    · ring
    · linear_combination μ * hbc + μ * M 0 0 * M 0 0 * h2
    · linear_combination (-μ) * h2

end Involution

section Fixed

variable {K F : Type} [Field K] [Field F]

theorem exists_map_eq_of_fixed (ι : K →+* F) {σ : F ≃+* F}
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {A : SL(2, F)}
    (hA : SpecialLinearGroup.map σ.toRingHom A = A) :
    ∃ A' : SL(2, K), SpecialLinearGroup.map ι A' = A := by
  have hent : ∀ i j, ∃ c : K, ι c = (A : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    have h := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F) i j) hA
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at h
    exact (hfix _).1 h
  choose c hc using hent
  have hMA : ι.mapMatrix (Matrix.of c) = (A : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    simp [hc]
  have hdet : (Matrix.of c).det = 1 := by
    apply ι.injective
    rw [RingHom.map_det, hMA, A.2, map_one]
  exact ⟨⟨Matrix.of c, hdet⟩, Subtype.ext hMA⟩

theorem eq_range_of_card_le {G : Type*} [Group G] [Finite G] [Finite K] {U Y : Subgroup G}
    {t : G} (φ : SL(2, F) ≃* U) (ι : K →+* F) {σ : F ≃+* F}
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hφt : ∀ A, t * (φ A : G) * t⁻¹ = φ (SpecialLinearGroup.map σ.toRingHom A))
    (hYU : Y ≤ U) (hYt : Y ≤ centralizer ({t} : Set G)) (hY : Nat.card SL(2, K) ≤ Nat.card Y) :
    Y = (U.subtype.comp (φ.toMonoidHom.comp (SpecialLinearGroup.map ι))).range := by
  have hYX : Y ≤ (U.subtype.comp (φ.toMonoidHom.comp (SpecialLinearGroup.map ι))).range := by
    intro y hy
    have hfixA : SpecialLinearGroup.map σ.toRingHom (φ.symm ⟨y, hYU hy⟩) = φ.symm ⟨y, hYU hy⟩ := by
      apply φ.injective
      apply Subtype.ext
      rw [← hφt, MulEquiv.apply_symm_apply]
      change t * y * t⁻¹ = y
      rw [← mem_centralizer_singleton_iff.mp (hYt hy), mul_inv_cancel_right]
    obtain ⟨A', hA'⟩ := exists_map_eq_of_fixed ι hfix hfixA
    refine ⟨A', ?_⟩
    change ((φ (SpecialLinearGroup.map ι A') : U) : G) = y
    rw [hA', MulEquiv.apply_symm_apply]
  exact Subgroup.eq_of_le_of_card_ge hYX
    ((Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)).trans hY)

end Fixed

section Scale

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

theorem inW_apply_of_scale {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (g1 : g P₁.e = a • P₁.e) (g2 : g P₂.e = a • P₂.e)
    (g3 : g P₁.f = b • P₁.f) (g4 : g P₂.f = b • P₂.f) {x : V} (hx : InW P₁ P₂ x) :
    InW P₁ P₂ (g x) := by
  obtain ⟨x1, x2, x3, x4⟩ := hx
  have key : ∀ {v : V} {c : K}, c ≠ 0 → g v = c • v → polar Q v x = 0 →
      polar Q v (g x) = 0 := by
    intro v c hc hv hvx
    have h := polar_map_of_mem hgO v x
    rw [hv, polar_smul_left_eq, hvx] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  exact ⟨key ha g1 x1, key hb g3 x2, key ha g2 x3, key hb g4 x4⟩

theorem leviFix_commute_of_scale (h₁₂ : P₁.Orth P₂) {H : Subgroup (V ≃ₗ[K] V)}
    {g h : V ≃ₗ[K] V} (hh : h ∈ leviFix H P₁ P₂) {a b : K} (g1 : g P₁.e = a • P₁.e)
    (g2 : g P₂.e = a • P₂.e) (g3 : g P₁.f = b • P₁.f) (g4 : g P₂.f = b • P₂.f)
    (gW : ∀ x, InW P₁ P₂ x → InW P₁ P₂ (g x)) : g * h = h * g := by
  obtain ⟨-, hL, hW⟩ := mem_leviFix.mp hh
  obtain ⟨he1, he2⟩ := planeCoeff_apply_e h₁₂ (leviFix_commute_e hh)
  have hcf : h * eichler Q (flipPair P₁).e (flipPair P₂).e =
      eichler Q (flipPair P₁).e (flipPair P₂).e * h :=
    mem_centralizer_singleton_iff.mp hL.2
  obtain ⟨hf1, hf2⟩ := planeCoeff_apply_e (orth_flipPair_left (orth_flipPair_right h₁₂)) hcf
  have g3' : g (flipPair P₁).e = b • (flipPair P₁).e := g3
  have g4' : g (flipPair P₂).e = b • (flipPair P₂).e := g4
  have k1 : g (h P₁.e) = a • h P₁.e := by
    rw [he1, map_add, map_smul, map_smul, g1, g2]; module
  have k2 : g (h P₂.e) = a • h P₂.e := by
    rw [he2, map_add, map_smul, map_smul, g1, g2]; module
  have k3 : g (h P₁.f) = b • h P₁.f := by
    have k : g (h (flipPair P₁).e) = b • h (flipPair P₁).e := by
      rw [hf1, map_add, map_smul, map_smul, g3', g4']; module
    exact k
  have k4 : g (h P₂.f) = b • h P₂.f := by
    have k : g (h (flipPair P₂).e) = b • h (flipPair P₂).e := by
      rw [hf2, map_add, map_smul, map_smul, g3', g4']; module
    exact k
  refine LinearEquiv.ext fun x => ?_
  have hx := inW_sub_uPart h₁₂ x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, eq_sub_uPart_add (P₁ := P₁) (P₂ := P₂) x]
  simp only [map_add]
  rw [hW _ hx, hW _ (gW _ hx)]
  congr 1
  simp only [uPart, map_add, map_smul, g1, g2, g3, g4, k1, k2, k3, k4]

end Scale


section Coord

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  regular_coordinateQuadPlus)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem frameLin_single_eq_smul {ι : Type*} [DecidableEq ι] {m : ℕ} (a b : Fin m → ι)
    (t : Fin m → Kˣ) (u : ι) :
    frameLin a b t (Pi.single u 1) = (frameEntry a b t u : K) • Pi.single u 1 := by
  funext i
  rw [frameLin_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hiu : i = u
  · subst hiu
    simp
  · rw [Pi.single_eq_of_ne hiu, mul_zero, mul_zero]

omit [Finite K] [CharP K 2] in
theorem frameLin_plusPair_e (t : Fin 4 → Kˣ) (i : Fin 4) :
    frameLin (plusFrameLeft 4) (plusFrameRight 4) t (plusPair K i).e =
      (t i : K) • (plusPair K i).e := by
  change frameLin (plusFrameLeft 4) (plusFrameRight 4) t (Pi.single (plusFrameLeft 4 i) 1) =
    (t i : K) • Pi.single (plusFrameLeft 4 i) 1
  rw [frameLin_single_eq_smul, (isHypFrame_plus K 4).frameEntry_left]

omit [Finite K] [CharP K 2] in
theorem frameLin_plusPair_f (t : Fin 4 → Kˣ) (i : Fin 4) :
    frameLin (plusFrameLeft 4) (plusFrameRight 4) t (plusPair K i).f =
      (((t i)⁻¹ : Kˣ) : K) • (plusPair K i).f := by
  change frameLin (plusFrameLeft 4) (plusFrameRight 4) t (Pi.single (plusFrameRight 4 i) 1) =
    (((t i)⁻¹ : Kˣ) : K) • Pi.single (plusFrameRight 4 i) 1
  rw [frameLin_single_eq_smul, (isHypFrame_plus K 4).frameEntry_right]

omit [Finite K] [CharP K 2] in
theorem leviFixBar_le_centralizer_plusFrameTorus {P₁ P₂ : HypPair (coordinateQuadPlus 4 K)}
    (h₁₂ : P₁.Orth P₂) {T : Subgroup (Fin 4 → Kˣ)}
    (hT : ∀ t ∈ T, ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧
      frameLin (plusFrameLeft 4) (plusFrameRight 4) t P₁.e = a • P₁.e ∧
      frameLin (plusFrameLeft 4) (plusFrameRight 4) t P₂.e = a • P₂.e ∧
      frameLin (plusFrameLeft 4) (plusFrameRight 4) t P₁.f = b • P₁.f ∧
      frameLin (plusFrameLeft 4) (plusFrameRight 4) t P₂.f = b • P₂.f) :
    leviFixBar P₁ P₂ ≤
      centralizer (plusFrameTorus K T : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
  have hfr := isHypFrame_plus K 4
  have key : leviFix (orthDerived (coordinateQuadPlus 4 K)) P₁ P₂ ≤
      centralizer (T.map (frameLin (plusFrameLeft 4) (plusFrameRight 4)) :
        Set ((Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) := by
    intro h hh
    rw [mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨a, b, ha, hb, g1, g2, g3, g4⟩ := hT t ht
    exact leviFix_commute_of_scale h₁₂ hh g1 g2 g3 g4
      (fun x hx => inW_apply_of_scale (hfr.frameLin_mem_orthogonalGroup t) ha hb g1 g2 g3 g4 hx)
  exact map_projHom_le_centralizer key

omit [Finite K] [CharP K 2] in
theorem leviFixBar_le_centralizer_plusSignedLevelTorus {i j : Fin 4} (hij : i ≠ j)
    {P : Finset (Fin 4)} (hi : i ∉ P) (hj : j ∉ P) :
    leviFixBar (plusPair K i) (plusPair K j) ≤ centralizer (plusSignedLevelTorus K {i, j} P :
      Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
  refine leviFixBar_le_centralizer_plusFrameTorus (plusPair_orth hij) fun t ht => ?_
  have ht' : flipParam K P t ∈ levelParam ({i, j} : Finset (Fin 4)) := ht
  have htij : flipParam K P t i = flipParam K P t j :=
    mem_levelParam.mp ht' i (by simp) j (by simp)
  simp only [flipParam_apply, hi, hj, ↓reduceIte] at htij
  refine ⟨(t i : K), (((t i)⁻¹ : Kˣ) : K), Units.ne_zero _, Units.ne_zero _,
    frameLin_plusPair_e t i, ?_, frameLin_plusPair_f t i, ?_⟩
  · rw [frameLin_plusPair_e, htij]
  · rw [frameLin_plusPair_f, htij]

omit [Finite K] [CharP K 2] in
theorem leviFixBar_flip_le_centralizer_plusSignedLevelTorus {i j : Fin 4} (hij : i ≠ j)
    {P : Finset (Fin 4)} (hi : i ∉ P) (hj : j ∈ P) :
    leviFixBar (plusPair K i) (flipPair (plusPair K j)) ≤
      centralizer (plusSignedLevelTorus K {i, j} P :
        Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
  refine leviFixBar_le_centralizer_plusFrameTorus (plusPair_orth_flip hij) fun t ht => ?_
  have ht' : flipParam K P t ∈ levelParam ({i, j} : Finset (Fin 4)) := ht
  have htij : flipParam K P t i = flipParam K P t j :=
    mem_levelParam.mp ht' i (by simp) j (by simp)
  simp only [flipParam_apply, hi, hj, ↓reduceIte] at htij
  refine ⟨(t i : K), (((t i)⁻¹ : Kˣ) : K), Units.ne_zero _, Units.ne_zero _,
    frameLin_plusPair_e t i, ?_, frameLin_plusPair_f t i, ?_⟩
  · change frameLin _ _ t (plusPair K j).f = (t i : K) • (plusPair K j).f
    rw [frameLin_plusPair_f, htij]
  · change frameLin _ _ t (plusPair K j).e = (((t i)⁻¹ : Kˣ) : K) • (plusPair K j).e
    rw [frameLin_plusPair_e, htij, inv_inv]

theorem commutator_leviFixBar_plus (hq : 4 ≤ Nat.card K)
    {P₁ P₂ : HypPair (coordinateQuadPlus 4 K)} (h₁₂ : P₁.Orth P₂) :
    ⁅leviFixBar P₁ P₂, leviFixBar P₁ P₂⁆ = leviFixBar P₁ P₂ := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hQ' := (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0).exists_ne_zero
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hq
  have : Group.IsPerfect (leviFixBar P₁ P₂) :=
    Group.IsPerfect.ofSurjective (f := (leviFixBarEquiv h₁₂ hQ hT hQ').symm.toMonoidHom)
      (leviFixBarEquiv h₁₂ hQ hT hQ').symm.surjective
  exact Subgroup.isPerfect_iff.mp this

theorem plusNodeSet_four_zero : plusNodeSet 4 0 = {0, 1} := by decide
theorem plusNodeFlip_four_zero : plusNodeFlip 4 0 = ∅ := by decide
theorem plusNodeSet_four_two : plusNodeSet 4 2 = {2, 3} := by decide
theorem plusNodeFlip_four_two : plusNodeFlip 4 2 = ∅ := by decide
theorem plusNodeSet_four_three : plusNodeSet 4 3 = {2, 3} := by decide
theorem plusNodeFlip_four_three : plusNodeFlip 4 3 = {3} := by decide

variable {G : Type} [Group G] {L : Subgroup G}

theorem modelToG_leviFixBar_le_plusNode_zero (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) :
    modelToG e (leviFixBar (plusPair K 0) (plusPair K 1)) ≤ plusNode e 0 := by
  rw [plusNode, plusNodeSet_four_zero, plusNodeFlip_four_zero]
  exact UnitaryPilot.modelToG_le_centralizerPerfectCore e
    (leviFixBar_le_centralizer_plusSignedLevelTorus (by decide) (by decide) (by decide))
    (commutator_leviFixBar_plus hq (plusPair_orth (by decide)))

theorem modelToG_leviFixBar_le_plusNode_two (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) :
    modelToG e (leviFixBar (plusPair K 2) (plusPair K 3)) ≤ plusNode e 2 := by
  rw [plusNode, plusNodeSet_four_two, plusNodeFlip_four_two]
  exact UnitaryPilot.modelToG_le_centralizerPerfectCore e
    (leviFixBar_le_centralizer_plusSignedLevelTorus (by decide) (by decide) (by decide))
    (commutator_leviFixBar_plus hq (plusPair_orth (by decide)))

theorem modelToG_leviFixBar_le_plusNode_three (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) :
    modelToG e (leviFixBar (plusPair K 2) (flipPair (plusPair K 3))) ≤ plusNode e 3 := by
  rw [plusNode, plusNodeSet_four_three, plusNodeFlip_four_three]
  exact UnitaryPilot.modelToG_le_centralizerPerfectCore e
    (leviFixBar_flip_le_centralizer_plusSignedLevelTorus (by decide) (by decide) (by decide))
    (commutator_leviFixBar_plus hq (plusPair_orth_flip (by decide)))

theorem plusZ_mul_self : plusZ K * plusZ K = 1 := by
  have hQ' := (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0).exists_ne_zero
  apply projLiftHom_injective hQ'
  rw [map_mul, map_one]
  change projLift hQ' (plusZ K) * projLift hQ' (plusZ K) = 1
  have h0 : polar (coordinateQuadPlus 4 K) (plusPair K 0).e (flipPair (plusPair K 1)).e = 0 :=
    (plusPair_orth_flip (K := K) (show (0 : Fin 4) ≠ 1 by decide)).ee
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hw : (flipPair (plusPair K 1)).e + (flipPair (plusPair K 1)).e = 0 := by
    rw [← two_smul K, h2, zero_smul]
  rw [projLift_plusZ, eichler_mul h0 h0, hw, eichler_zero_right]

end Coord


section StepA

open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  regular_coordinateQuadPlus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.LinearPilot (SLmCatalogueClausesAt)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem plusNode_zero_le_centralizer_stabTwoBar (hset : SeitzSetting G L)
    (hcat : SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hR5 : ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot (coordinateQuadPlus 4 K) (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot (coordinateQuadPlus 4 K) (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)))
    (hnn : ¬ (((modelToG e (pairPerp (K := K) 2)).subgroupOf
          (centralizer (modelToG e (pairTorus (K := K) 2) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) 2) :
            Set G))))).Normal)
    (hrow : OmegaRowAt t (modelToG e (pairTorus (K := K) 2)) (modelToG e (pairPerp (K := K) 2))
      .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    plusNode e 0 ≤ centralizer (modelToG e (stabTwoBar K 0 1) : Set G) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hQ' := (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0).exists_ne_zero
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hσσ : σ * σ = 1 := by rw [← _root_.sq, ← hσ, pow_orderOf_eq_one]
  have hσι : ∀ c : K, σ.toRingHom (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  have hFK : Nat.card F = Nat.card K ^ 2 := by
    obtain ⟨ω, hω⟩ := LinearPilot.exists_trace_one_of_involution hσ1 hσσ
    exact LinearPilot.natCard_eq_sq_of_trace_one ι hσσ hfix hω
  have hF16 : 16 ≤ Nat.card F := by rw [hFK]; nlinarith
  obtain ⟨C, hC3⟩ := exists_plusFieldCover_conj_four hset hcat hdet hKc hq 2 e htC ht hnn hrow ι
    hσ hfix
  obtain ⟨φ₀, -, hφ₀t⟩ := exists_nodeParam_of_cover C htC hC3 hq (by omega) (by omega)
    (J := plusNodeSet 4 0) (plusNodeFlip 4 0) (by decide) (by decide)
  set Y₀ := modelToG e (leviFixBar (plusPair K 0) (plusPair K 1)) with hY₀
  have hY₀U : Y₀ ≤ (plusSignedLevelCore e (plusNodeSet 4 0) (plusNodeFlip 4 0)) := modelToG_leviFixBar_le_plusNode_zero hq e
  have hY₀t : Y₀ ≤ centralizer ({t} : Set G) := fun y hy => mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp htC y (UnitaryPilot.modelToG_le e _ hy))
  have hcardY₀ : Nat.card SL(2, K) ≤ Nat.card Y₀ := by
    rw [hY₀, UnitaryPilot.card_modelToG e, card_leviFixBar (plusPair_orth (by decide)) hQ hT hQ']
  set ψ₀ : SL(2, K) →* G := (plusSignedLevelCore e (plusNodeSet 4 0) (plusNodeFlip 4 0)).subtype.comp (φ₀.toMonoidHom.comp (SpecialLinearGroup.map ι))
    with hψ₀
  have hrange : Y₀ = ψ₀.range := eq_range_of_card_le φ₀ ι hfix hφ₀t hY₀U hY₀t hcardY₀
  have hψinj : Function.Injective ψ₀ :=
    (plusSignedLevelCore e (plusNodeSet 4 0) (plusNodeFlip 4 0)).subtype_injective.comp (φ₀.injective.comp (LinearPilot.specialLinearGroup_map_injective ι))
  have hz₀ : ((e.symm (plusZ K) : L) : G) ∈ Y₀ :=
    UnitaryPilot.symm_mem_modelToG e plusZ_mem_leviFixBar
  rw [hrange] at hz₀
  obtain ⟨A₀, hA₀⟩ := hz₀
  have hz1 : plusZ K ≠ 1 := rootPairElt_ne_one hQ _ _ _
  have hA₀2 : A₀ * A₀ = 1 := hψinj (by
    rw [map_mul, map_one, hA₀, ← Subgroup.coe_mul, ← map_mul, plusZ_mul_self, map_one,
      Subgroup.coe_one])
  have hA₀1 : A₀ ≠ 1 := by
    rintro rfl
    rw [map_one] at hA₀
    have h1 : e.symm (plusZ K) = 1 := Subtype.ext hA₀.symm
    exact hz1 (by rw [← e.apply_symm_apply (plusZ K), h1, map_one])
  obtain ⟨g₀, hg₀⟩ := exists_conj_eq_upperUnit_of_involution hA₀1 hA₀2
  set c₀ : SL(2, F) := SpecialLinearGroup.map ι g₀ with hc₀
  set φ : SL(2, F) →* G := (plusSignedLevelCore e (plusNodeSet 4 0) (plusNodeFlip 4 0)).subtype.comp (φ₀.toMonoidHom.comp (MulAut.conj c₀).toMonoidHom)
    with hφ
  have hφapp : ∀ A, φ A = φ₀ (c₀ * A * c₀⁻¹) := fun A => rfl
  have hφι : ∀ A' : SL(2, K), φ (SpecialLinearGroup.map ι A') = ψ₀ (g₀ * A' * g₀⁻¹) := by
    intro A'
    rw [hφapp, hc₀, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hφu : φ (LinearPilot.upperUnit 1) = ((e.symm (plusZ K) : L) : G) := by
    rw [← map_one ι, ← LinearPilot.map_upperUnit, hφι, hg₀, hA₀]
  have hφt : ∀ A : SL(2, F), t * φ A * t⁻¹ = φ (SpecialLinearGroup.map σ.toRingHom A) := by
    intro A
    rw [hφapp, hφapp, hφ₀t]
    congr 2
    rw [map_mul, map_mul, map_inv, hc₀, LinearPilot.map_map_of_forall_eq ι σ.toRingHom hσι]
  have hUY : (plusSignedLevelCore e (plusNodeSet 4 0) (plusNodeFlip 4 0)) ≤ centralizer (modelToG e (plusLevelTorus K ({0, 1} : Finset (Fin 4))) :
      Set G) := by
    rw [plusNodeSet_four_zero, plusNodeFlip_four_zero,
      plusSignedLevelCore_of_disjoint e (Finset.disjoint_empty_right _)]
    exact F4Pilot.centralizerPerfectCore_le_centralizer _
  have hφU : φ.range ≤ (plusSignedLevelCore e (plusNodeSet 4 0) (plusNodeFlip 4 0)) := by
    rintro _ ⟨A, rfl⟩
    exact (φ₀ (c₀ * A * c₀⁻¹)).2
  have hR : Y₀ ≤ centralizer (modelToG e (stabTwoBar K 0 1) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e fun j hj => mem_centralizer_iff.mpr fun b hb =>
      (leviFixBar_commute_stabTwoBar_zero_one (Or.inl rfl) hj hb).symm
  obtain ⟨g, hg, hS⟩ := exists_conj_eq_mul_forall_le_centralizer_plus_four hset hKc hq e ht hKt hR5
  have hmain := range_le_centralizer_of_fieldTwist hq ι hσ1 hσσ hfix φ hφt (hφU.trans hUY)
    (fun A' => hR (by rw [hφι, hrange]; exact ⟨_, rfl⟩))
    (fun S hSp hSs hSt hSY hzS => hS S hSp hSs (by rw [hg, ← hφu]; exact hSt) hSY
      (by rw [← hφu]; exact hzS))
  change (plusSignedLevelCore e (plusNodeSet 4 0) (plusNodeFlip 4 0)) ≤ _
  intro u hu
  refine hmain ⟨c₀⁻¹ * φ₀.symm ⟨u, hu⟩ * c₀, ?_⟩
  rw [hφapp, show c₀ * (c₀⁻¹ * φ₀.symm ⟨u, hu⟩ * c₀) * c₀⁻¹ = φ₀.symm ⟨u, hu⟩ by group,
    MulEquiv.apply_symm_apply]

end StepA


end CFSG.SeitzReduction.OmegaPilot
