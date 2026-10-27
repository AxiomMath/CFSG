module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightOut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightMat

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups commutatorElement

section Centralizer

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤}

theorem exists_isLeftRight_of_commute
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega Q₂, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K} (hw₀ : Q₂ w₀ ≠ 0)
    {ω : K} (hω0 : ω ≠ 0) {g : StatedOmega Q}
    (hL : ∀ Z : StatedOmega Q₂, g * oKappa oe hQ Z = oKappa oe hQ Z * g)
    (h5 : g * oRhoOne oe hQ hSL (fiveSL ω) = oRhoOne oe hQ hSL (fiveSL ω) * g) :
    ∃ (X : GL (Fin 2 ⊕ Fin 2) K) (A B : GL (Fin 2) K), (g : GL ι K) = oblkGL oe (1, X) ∧
      IsLeftRight X A B ∧ (A : Matrix (Fin 2) (Fin 2) K) * fiveM ω = fiveM ω * A := by
  have hm5 : (g : GL ι K).val * oblk oe 1 (rhoOneShape (fiveM ω)) =
      oblk oe 1 (rhoOneShape (fiveM ω)) * (g : GL ι K).val := by
    have := congrArg (fun x : StatedOmega Q => ((x : GL ι K) : Matrix ι ι K)) h5
    simp only [Subgroup.coe_mul, Units.val_mul, coe_oRhoOne] at this
    exact this
  obtain ⟨Y, X, hYX⟩ := eq_oblk_of_commute (isUnit_det_rhoOneShape_fiveM_sub_one hω0) hm5
  obtain ⟨d, hd⟩ := hcomm Y fun Z hZ => by
    have h := congrArg (fun x : StatedOmega Q => ((x : GL ι K) : Matrix ι ι K)) (hL ⟨Z, hZ⟩)
    simp only [Subgroup.coe_mul, Units.val_mul, coe_oKappa] at h
    rw [hYX, oblk_mul, oblk_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact (oblk_injective h).1
  have hiso := quad_mulVec_of_mem_statedOmega g.2
  have hQ0 : Q₂ 0 = 0 := by simpa using hsm 0 w₀
  have hd1 : d = 1 := by
    refine eq_one_of_quad_smul hsm hw₀ ?_
    have h := hiso (oVec oe w₀ 0)
    rw [hYX, hd, quad_oblk_mulVec hQ, oVec_inl, oVec_inr, hQ, oVec_inl, oVec_inr,
      Matrix.mulVec_zero, smul_mulVec, Matrix.one_mulVec, add_left_inj] at h
    exact h
  have hXiso : ∀ u, StatedQuadPlus 2 K (X *ᵥ u) = StatedQuadPlus 2 K u := fun u => by
    have h := hiso (oVec oe 0 u)
    rw [hYX, quad_oblk_mulVec hQ, oVec_inl, oVec_inr, hQ, oVec_inl, oVec_inr,
      Matrix.mulVec_zero, add_right_inj] at h
    exact h
  have hXdet : X.det ≠ 0 := by
    have h3 := ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g : GL ι K))).ne_zero
    rw [hYX, det_oblk] at h3
    exact right_ne_zero_of_mul h3
  have hXc : X * rhoOneShape (fiveM ω) = rhoOneShape (fiveM ω) * X := by
    rw [hYX, oblk_mul, oblk_mul, Matrix.mul_one, Matrix.one_mul] at hm5
    exact (oblk_injective hm5).2
  obtain ⟨A, B, -, hAX, hX⟩ := exists_leftRight_of_commute_five
    (X := Matrix.GeneralLinearGroup.mkOfDetNeZero X hXdet) hXiso hXc
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero X hXdet, A, B, Units.ext ?_, hX, hAX⟩
  rw [coe_oblkGL, hYX, hd, hd1, one_smul]
  rfl

omit [CharP K 2] in
theorem oblkGL_one_inv (X : GL (Fin 2 ⊕ Fin 2) K) :
    (oblkGL oe ((1 : GL ι₂ K), X))⁻¹ = oblkGL oe (1, X⁻¹) := by
  rw [← map_inv, Prod.inv_mk, inv_one]

theorem oProj_mem_normalizer_oBarTwo {g : StatedOmega Q} {X : GL (Fin 2 ⊕ Fin 2) K}
    {A B : GL (Fin 2) K} (hg : (g : GL ι K) = oblkGL oe (1, X)) (hX : IsLeftRight X A B) :
    oProj Q g ∈ normalizer (oBarTwo oe hQ hSL : Set (StatedProj (StatedOmega Q))) := by
  have key : ∀ {g' : StatedOmega Q} {X' : GL (Fin 2 ⊕ Fin 2) K} {A' B' : GL (Fin 2) K},
      (g' : GL ι K) = oblkGL oe (1, X') → IsLeftRight X' A' B' →
      ∀ y ∈ oBarTwo oe hQ hSL, oProj Q g' * y * (oProj Q g')⁻¹ ∈ oBarTwo oe hQ hSL := by
    rintro g' X' A' B' hg' hX' _ ⟨C, rfl⟩
    obtain ⟨C', hC'⟩ := hX'.conj_rhoTwo C
    refine ⟨C', ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change oblk oe 1 (rhoTwoMat C') = ((g' : GL ι K) * (oRhoTwo oe hQ hSL C : GL ι K) *
      ((g' : GL ι K))⁻¹ : GL ι K).val
    rw [hg', oblkGL_one_inv, Units.val_mul, Units.val_mul, coe_oblkGL, coe_oblkGL]
    change oblk oe 1 (rhoTwoMat C') = oblk oe 1 (X' : Matrix _ _ K) * oblk oe 1 (rhoTwoMat C) *
      oblk oe 1 ((X'⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K)
    rw [oblk_mul, oblk_mul, Matrix.one_mul, Matrix.one_mul, hC']
  have hgi : ((g⁻¹ : StatedOmega Q) : GL ι K) = oblkGL oe (1, X⁻¹) := by
    rw [Subgroup.coe_inv, hg, oblkGL_one_inv]
  refine mem_normalizer_iff.mpr fun y => ⟨key hg hX y, fun hy => ?_⟩
  have h1 := key hgi hX.inv _ hy
  rwa [map_inv, inv_inv, show (oProj Q g)⁻¹ * (oProj Q g * y * (oProj Q g)⁻¹) * oProj Q g = y by
    group] at h1

theorem commutatorElement_mem_oBarTwo {g g' : StatedOmega Q} {X X' : GL (Fin 2 ⊕ Fin 2) K}
    {A B A' B' : GL (Fin 2) K} (hg : (g : GL ι K) = oblkGL oe (1, X)) (hX : IsLeftRight X A B)
    (hg' : (g' : GL ι K) = oblkGL oe (1, X')) (hX' : IsLeftRight X' A' B')
    (hAA : A * A' = A' * A) : ⁅oProj Q g, oProj Q g'⁆ ∈ oBarTwo oe hQ hSL := by
  obtain ⟨C, hC⟩ := hX.commutator hX' hAA
  refine ⟨C, ?_⟩
  simp only [MonoidHom.comp_apply]
  rw [← map_commutatorElement]
  congr 1
  apply Subtype.ext
  apply Units.ext
  have h : ((⁅g, g'⁆ : StatedOmega Q) : GL ι K) = oblkGL oe (1, ⁅X, X'⁆) := by
    rw [commutatorElement_def, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hg, hg', ← map_inv, ← map_inv,
      ← map_mul, ← map_mul, ← map_mul]
    congr 1
    simp
  rw [h, coe_oblkGL, coe_oRhoTwo, hC]
  rfl

end Centralizer

section Lift

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂]
  [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}
  {Q : (ι → K) → K} {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤} {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedOmega Q)}

omit [CharP K 2] in
theorem isQuasisimple_oBarTwo (hK : 4 ≤ Nat.card K) (hinj : Function.Injective (oProj Q)) :
    CFSG.IsQuasisimple ↥(oBarTwo oe hQ hSL) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (oBarTwoEquiv hinj)
    (CFSG.RankThree.Classical.isQuasisimple_SL2 (exists_finset_four hK))

omit [Finite K] in
theorem oLeviW_le_centralizer (hker : θ.ker = center ↥A) :
    levLift θ (oBarTwo oe hQ hSL) ≤ A ⊓ centralizer
      ((levLift θ (oBarL oe hQ) ⊔ levLift θ (oBarOne oe hQ hSL) : Subgroup G) : Set G) := by
  refine le_inf levLift_le ?_
  rw [le_centralizer_iff]
  exact sup_le
    (levLift_le_centralizer_levLift hker fun _ hs _ hs' => (oBarTwo_commute_oBarL hs' hs).symm)
    (levLift_le_centralizer_levLift hker fun _ hs _ hs' => oBarOne_commute_oBarTwo hs hs')

theorem layerCentralizer_eq_oLeviW_five (hK : 4 ≤ Nat.card K) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hinj : Function.Injective (oProj Q))
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega Q₂, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K} (hw₀ : Q₂ w₀ ≠ 0)
    (hperf : commutator (StatedOmega Q₂) = ⊤) {ω : K} (hω0 : ω ≠ 0) {x : G}
    (hxL : x ∈ levLift θ (oBarOne oe hQ hSL)) (hxA : x ∈ A)
    (hxθ : θ ⟨x, hxA⟩ = oProj Q (oRhoOne oe hQ hSL (fiveSL ω))) :
    AS76b.layerCentralizer A (levLift θ (oBarL oe hQ) ⊔ zpowers x) =
      levLift θ (oBarTwo oe hQ hSL) := by
  set Y := levLift θ (oBarL oe hQ) ⊔ zpowers x
  have hstr : ∀ m ∈ A ⊓ centralizer (Y : Set G), ∀ hm : m ∈ A, ∃ g : StatedOmega Q,
      oProj Q g = θ ⟨m, hm⟩ ∧ ∃ (X : GL (Fin 2 ⊕ Fin 2) K) (A' B' : GL (Fin 2) K),
        (g : GL ι K) = oblkGL oe (1, X) ∧ IsLeftRight X A' B' ∧
          (A' : Matrix (Fin 2) (Fin 2) K) * fiveM ω = fiveM ω * A' := by
    intro m hmM hm
    obtain ⟨g, hg⟩ := oProj_surjective Q (θ ⟨m, hm⟩)
    refine ⟨g, hg, exists_isLeftRight_of_commute (hQ := hQ) (hSL := hSL) hcomm hsm hw₀ hω0
      (fun Z => hinj ?_) (hinj ?_)⟩
    · rw [map_mul, map_mul, hg]
      obtain ⟨w', hw', hw'θ⟩ := exists_mem_levLift hθ (commutator_oBarL (oe := oe) (hQ := hQ)
        hperf) (s := oProj Q (oKappa oe hQ Z)) ⟨Z, rfl⟩
      have h1 := (mem_centralizer_iff.mp (mem_inf.mp hmM).2 w' (mem_sup_left hw')).symm
      rw [← hw'θ, ← map_mul, ← map_mul]
      exact congrArg θ (Subtype.ext h1)
    · rw [map_mul, map_mul, hg, ← hxθ]
      have h1 := (mem_centralizer_iff.mp (mem_inf.mp hmM).2 x
        (mem_sup_right (mem_zpowers x))).symm
      rw [← map_mul, ← map_mul]
      exact congrArg θ (Subtype.ext h1)
  refine layerCentralizer_eq_levLift hker hθ commutator_oBarTwo (isQuasisimple_oBarTwo hK hinj)
    ((oLeviW_le_centralizer hker).trans (inf_le_inf_left _ (centralizer_le
      (SetLike.coe_subset_coe.mpr (sup_le_sup_left (zpowers_le.mpr hxL) _))))) ?_ ?_
  · intro m hmM hm
    obtain ⟨g, hg, X, A', B', hgX, hX, -⟩ := hstr m hmM hm
    rw [← hg]
    exact oProj_mem_normalizer_oBarTwo hgX hX
  · intro a ha b hb haA hbA
    obtain ⟨g, hg, X, A₁, B₁, hgX, hX, hA₁⟩ := hstr a ha haA
    obtain ⟨g', hg', X', A₂, B₂, hgX', hX', hA₂⟩ := hstr b hb hbA
    rw [← hg, ← hg']
    exact commutatorElement_mem_oBarTwo hgX hX hgX' hX'
      (Units.ext (by rw [Units.val_mul, Units.val_mul]; exact commute_of_mul_fiveM hA₁ hA₂))

omit [Finite K] in
theorem noInv_oEight_five (hA : commutator ↥A = ⊤) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hinj : Function.Injective (oProj Q))
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega Q₂, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K} (hw₀ : Q₂ w₀ ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hperf : commutator (StatedOmega Q₂) = ⊤)
    (hsemi : ∀ β : MulAut (StatedProj (StatedOmega Q)), (∀ x ∈ oBarTwo oe hQ hSL, β x = x) →
      (∀ x ∈ oBarL oe hQ, β x = x) → ∃ (σ : K ≃+* K) (A' : GL ι K) (μ : K), μ ≠ 0 ∧
        (∀ v, Q ((A' : Matrix ι ι K) *ᵥ fun i => σ (v i)) = μ * σ (Q v)) ∧
        ∀ g : StatedOmega Q, ∃ hg : A' * glAut σ (g : GL ι K) * A'⁻¹ ∈ StatedOmega Q,
          β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    {ω : K} (hω0 : ω ≠ 0) {x : G} (hxA : x ∈ A)
    (hxθ : θ ⟨x, hxA⟩ = oProj Q (oRhoOne oe hQ hSL (fiveSL ω))) :
    NoInvolutoryCentralizing A (levLift θ (oBarL oe hQ) ⊔ zpowers x ⊔
      levLift θ (oBarTwo oe hQ hSL)) := by
  intro σ hσ hfix
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hL := inducedAut_fix_of_levLift hθ (commutator_oBarL hperf)
    (le_sup_left.trans le_sup_left) hfix hα
  have hW := inducedAut_fix_of_levLift hθ commutator_oBarTwo le_sup_right hfix hα
  have hx : α (θ ⟨x, hxA⟩) = θ ⟨x, hxA⟩ := by
    rw [hα, hfix ⟨x, hxA⟩ (mem_sup_left (mem_sup_right (mem_zpowers x)))]
  obtain ⟨σ', A', μ, hμ0, hAQ, hβ⟩ := hsemi α hW hL
  obtain ⟨B, hB⟩ := exists_eq_conj_oRhoOne hinj hcomm hsm hw₀ ht0 ht1 hμ0 hAQ hβ hW hL
  have hconj : ∀ C : SL(2, K), α (oProj Q (oRhoOne oe hQ hSL C)) =
      oProj Q (oRhoOne oe hQ hSL (B * C * B⁻¹)) := fun C => by
    rw [hB, map_mul (oRhoOne oe hQ hSL), map_mul (oRhoOne oe hQ hSL), map_inv (oRhoOne oe hQ hSL),
      map_mul (oProj Q), map_mul (oProj Q), map_inv (oProj Q)]
  have hinjρ : Function.Injective ((oProj Q).comp (oRhoOne oe hQ hSL)) :=
    hinj.comp oRhoOne_injective
  have hB5 : B * fiveSL ω = fiveSL ω * B := by
    have h := hconj (fiveSL ω)
    rw [← hxθ, hx, hxθ] at h
    have h2 := hinjρ h
    calc B * fiveSL ω = B * fiveSL ω * B⁻¹ * B := by group
      _ = fiveSL ω * B := by rw [← h2]
  have hα2 := inducedAut_sq hθ hσ hα
  have hB2 : ∀ C : SL(2, K), B * B * C = C * (B * B) := fun C => by
    have h := congrArg (fun φ : MulAut (StatedProj (StatedOmega Q)) =>
      φ (oProj Q (oRhoOne oe hQ hSL C))) hα2
    simp only [MulAut.mul_apply, MulAut.one_apply, hconj] at h
    have h2 := hinjρ h
    calc B * B * C = B * (B * C * B⁻¹) * B⁻¹ * (B * B) := by group
      _ = C * (B * B) := by rw [h2]
  set b : Matrix (Fin 2) (Fin 2) K := (B : Matrix (Fin 2) (Fin 2) K)
  have hb2 : ∀ (i j : Fin 2) (hij : i ≠ j),
      b * b * (1 + single i j 1) = (1 + single i j 1) * (b * b) :=
    fun i j hij => by
      have := congrArg (fun C : SL(2, K) => (C : Matrix (Fin 2) (Fin 2) K)) (hB2 (tr₂ i j hij))
      simp only [Matrix.SpecialLinearGroup.coe_mul] at this
      exact this
  have hBm : b * b = (b * b) 0 0 • 1 := eq_smul_one_of_commute_tr (hb2 0 1 (by decide))
    (hb2 1 0 (by decide))
  have hb5 : b * fiveM ω = fiveM ω * b := by
    have := congrArg (fun C : SL(2, K) => (C : Matrix (Fin 2) (Fin 2) K)) hB5
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  have hBs := eq_smul_one_of_mul_fiveM hω0 hb5 hBm
  have hB1 : B = 1 := by
    have hdet : b.det = 1 := B.2
    rw [hBs, det_smul, Fintype.card_fin, det_one, mul_one, sq] at hdet
    have hb := eq_of_mul_self_eq (hdet.trans (mul_one 1).symm)
    apply Subtype.ext
    change b = 1
    rw [hBs, hb, one_smul]
  have h1 : α = 1 := by
    ext y
    rw [hB, hB1, map_one, map_one, one_mul, inv_one, mul_one, MulAut.one_apply]
  exact eq_one_of_theta_eq hker hA σ fun a => by rw [← hα, h1, MulAut.one_apply]

end Lift

end CFSG.ComponentClassification.RankTwoClassical
