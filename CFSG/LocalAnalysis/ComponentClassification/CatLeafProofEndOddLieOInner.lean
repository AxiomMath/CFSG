module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieOLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieOSplit
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdReduction
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieQuat
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddO

open Subgroup Matrix Module CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.OddClassSelector CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FooteLit
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare (orthogonalOmega)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.Burgoyne.O (linPair linPair_left linPair_right)

variable {K : Type} [Field K] {d : ℕ}

theorem derivedLinear_eq (Q : QuadraticForm K (Fin d → K)) (X : matrixDerived Q) :
    derivedLinear Q X = matrixLinearEquiv X.val :=
  rfl

theorem proj_eq_one_of_smul (Q : QuadraticForm K (Fin d → K)) (X : matrixDerived Q) (a : Kˣ)
    (h : ∀ v, derivedLinear Q X v = (a : K) • v) : matrixProjectiveProjection Q X = 1 := by
  have h1 : X ∈ matrixDerivedScalars Q := by
    refine (mem_matrixDerivedScalars_iff Q X).mpr ⟨a, ?_⟩
    apply matrixLinearIso.injective
    refine LinearEquiv.ext fun v => ?_
    change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) a) v = matrixLinearEquiv X.val v
    rw [LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar,
      ← derivedLinear_apply, h]
  have h2 : X ∈ (matrixProjectiveProjection Q).ker := by
    rw [matrixProjectiveProjection, QuotientGroup.ker_mk']
    exact h1
  exact MonoidHom.mem_ker.mp h2

theorem isComponentOf_of_isTwoComponentAt [Finite K] {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ e) (hd : 2 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate) (W : matrixDerived Q)
    {L : Subgroup (matrixProjectiveDerived Q)}
    (hL : IsTwoComponentAt (matrixProjectiveProjection Q W) L) :
    CFSG.Assembly.IsComponentOf L
        (centralizer ({matrixProjectiveProjection Q W} : Set (matrixProjectiveDerived Q))) ∧
      CFSG.IsQuasisimple L := by
  obtain ⟨hord, hLC, hLp⟩ := hL
  have hw2 : matrixProjectiveProjection Q W * matrixProjectiveProjection Q W = 1 := by
    rw [← pow_two, ← hord, pow_orderOf_eq_one]
  have hw1 : matrixProjectiveProjection Q W ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  obtain ⟨c, hc⟩ := exists_scalar_sq Q W hw2
  have key := CatalogueBOrthogonalFixedTransfer.fixed_pComponent_quasisimple_of_matrix ℓ e hℓ hℓ2
    he hK hd Q hQ (linPair W.val (matrixDerived_le_isometries Q W.2))
    (by rw [linPair_right, one_pow]) c
    (by rw [linPair_left, linPair_right, map_one, MulAut.one_apply]; exact hc)
    (fun _ a => scalar_ne_of_ne_one Q W hw1 a)
  have hfix : fixedSubgroup (matrixProjectiveConjugation Q
      (linPair W.val (matrixDerived_le_isometries Q W.2))) =
      centralizer ({matrixProjectiveProjection Q W} : Set (matrixProjectiveDerived Q)) := by
    change fixedSubgroup (matrixProjectiveConjugationHom Q _) = _
    rw [matrixProjectiveConjugationHom_linPair, fixedSubgroup_conj_eq]
  have hq : ∀ L' : Subgroup (centralizer
      ({matrixProjectiveProjection Q W} : Set (matrixProjectiveDerived Q))),
      CFSG.IsPComponent 2 L' → CFSG.IsQuasisimple L' :=
    CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv 2
      (MulEquiv.subgroupCongr hfix.symm) (key 2 Nat.prime_two)
  have hLc : CFSG.IsComponent (L.subgroupOf (centralizer
      ({matrixProjectiveProjection Q W} : Set (matrixProjectiveDerived Q)))) :=
    ⟨hq _ hLp, by obtain ⟨_, _, h, _⟩ := hLp; exact h⟩
  have hLC' := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLC).mpr
    hLc
  exact ⟨hLC', (AssemblyBPredicates.isQuasisimple_iff_native _).1 hLC'.2.2⟩

theorem smallSource_of_quot {X : Type} [Group X] [Finite X] {L K₀ : Subgroup X}
    (hL : CFSG.IsQuasisimple L) (φ : L ⧸ pPrimeCore 2 L ≃* K₀ ⧸ pPrimeCore 2 K₀)
    (hs : IsSimpleGroup (K₀ ⧸ pPrimeCore 2 K₀)) (hF : FooteFamilyType K₀) : SmallSource L := by
  have hZ := center_quotient_pPrimeCore_eq_bot_of_footeFamilyType hs hF
  have hZ' : Open.fusionZStar K₀ = pPrimeCore 2 K₀ := (Sol78.fusionZStar_eq_iff K₀).2 hZ
  let e : L ⧸ pPrimeCore 2 L ≃* K₀ ⧸ Open.fusionZStar K₀ :=
    φ.trans (QuotientGroup.quotientMulEquivOfEq hZ'.symm)
  refine smallSource_of_type hL ?_
  rcases hF with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hm⟩
  · exact Or.inr (Or.inl ⟨e.trans e7⟩)
  · exact Or.inl ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm⟩

theorem inner_split_data [Finite K] {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate) (W : matrixDerived Q)
    (hw2 : matrixProjectiveProjection Q W * matrixProjectiveProjection Q W = 1)
    (hw1 : matrixProjectiveProjection Q W ≠ 1) {X : Subgroup (matrixProjectiveDerived Q)}
    (hX : CFSG.Assembly.IsComponentOf X
      (centralizer ({matrixProjectiveProjection Q W} : Set (matrixProjectiveDerived Q))))
    (hs : SmallSource X) :
    ∃ (s : K) (M F : Submodule K (Fin d → K)), s * s = 1 ∧
      M = Module.End.eigenspace (matrixLinearEquiv W.val).toLinearMap s ∧
      F = Module.End.eigenspace (matrixLinearEquiv W.val).toLinearMap (-s) ∧ IsCompl M F ∧
      (∀ m ∈ M, ∀ f ∈ F, QuadraticMap.polar Q m f = 0) ∧
      (LinearMap.BilinForm.restrict Q.polarBilin M).Nondegenerate ∧
      (LinearMap.BilinForm.restrict Q.polarBilin F).Nondegenerate ∧
      (∀ y ∈ (liftHat Q X).map (derivedLinear Q), ∀ f ∈ F, y f = f) ∧
      ∃ ρ : (liftHat Q X).map (derivedLinear Q) →*
          TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype),
        Function.Injective ρ ∧ CFSG.IsComponent ρ.range ∧
        (∀ (y : (liftHat Q X).map (derivedLinear Q)) (m : M),
          (((ρ y).val m : M) : Fin d → K) = (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) m) ∧
        3 ≤ finrank K M ∧ finrank K M ≤ 4 := by
  classical
  obtain ⟨-, -, hYc, -, σ, hσs, hσk⟩ := inner_lift Q W hw2 hX
  obtain ⟨c, hc⟩ := exists_scalar_sq Q W hw2
  have hdV : finrank K (Fin d → K) = d := Module.finrank_fin_fun K
  have hAO : matrixLinearEquiv W.val ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
      ((mem_matrixIsometries_iff Q W.val).mp (matrixDerived_le_isometries Q W.2))
  have hsquare : ∀ x, matrixLinearEquiv W.val (matrixLinearEquiv W.val x) = (c : K) • x := by
    intro x
    rw [← LinearEquiv.mul_apply, ← matrixLinearEquiv_mul, hc]
    exact LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar c x
  have hnonscalar : ∀ a : K,
      (matrixLinearEquiv W.val).toLinearMap ≠ a • (1 : Module.End K (Fin d → K)) := by
    intro a h
    have hc0 : a ≠ 0 := by
      rintro rfl
      have h0 := LinearMap.congr_fun h (Pi.single ⟨0, by omega⟩ 1)
      rw [zero_smul, LinearMap.zero_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_eq_zero_iff] at h0
      simpa using congrFun h0 ⟨0, by omega⟩
    apply scalar_ne_of_ne_one Q W hw1 (Units.mk0 a hc0)
    apply matrixLinearIso.injective
    refine LinearEquiv.ext fun v => ?_
    change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) (Units.mk0 a hc0)) v =
      matrixLinearEquiv W.val v
    rw [LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar]
    have := LinearMap.congr_fun h v
    rw [LinearEquiv.coe_coe] at this
    rw [this]
    rfl
  exact split_data_of_component hℓ hℓ2 he hK (by omega) hQ _ hAO c hsquare hnonscalar hYc σ hσs
    hσk hs

theorem false_of_quasisimple_commuting [Finite K] (Q : QuadraticForm K (Fin d → K))
    (W : matrixDerived Q) {Yh : Subgroup (matrixDerived Q)}
    {X : Subgroup (matrixProjectiveDerived Q)} (hYX : Yh.map (matrixProjectiveProjection Q) = X)
    (hsol : Group.IsSolvable ↥(centralizer
      ({matrixProjectiveProjection Q W} : Set (matrixProjectiveDerived Q)) ⊓
        centralizer (X : Set (matrixProjectiveDerived Q))))
    {G : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))} (hG : CFSG.IsQuasisimple G)
    (hGO : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hGW : ∀ g ∈ G, g * derivedLinear Q W = derivedLinear Q W * g)
    (hGY : ∀ g ∈ G, ∀ y ∈ Yh, g * derivedLinear Q y = derivedLinear Q y * g)
    {v : Fin d → K} (hv : v ≠ 0) (hGv : ∀ g ∈ G, g v = v) : False := by
  classical
  have hGG : ⁅G, G⁆ = G := LocalAnalysis.ComponentInitial.commutator_self_of_isQuasisimple
    ((AssemblyBPredicates.isQuasisimple_iff_native _).2 hG)
  have hGΩ : G ≤ (derivedLinear Q).range := by
    rw [range_derivedLinear, ← hGG]
    exact Subgroup.commutator_mono hGO hGO
  let θ : G →* matrixDerived Q :=
    (MonoidHom.ofInjective (derivedLinear_injective Q)).symm.toMonoidHom.comp
      (Subgroup.inclusion hGΩ)
  have hθ : ∀ g : G, derivedLinear Q (θ g) = g := fun g =>
    congrArg Subtype.val
      ((MonoidHom.ofInjective (derivedLinear_injective Q)).apply_symm_apply
        (Subgroup.inclusion hGΩ g))
  let φ : G →* matrixProjectiveDerived Q := (matrixProjectiveProjection Q).comp θ
  have hφi : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have h1 : θ g ∈ matrixDerivedScalars Q := by
      have h0 : θ g ∈ (matrixProjectiveProjection Q).ker := hg
      rwa [matrixProjectiveProjection, QuotientGroup.ker_mk'] at h0
    obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q _).mp h1
    have h2 : ∀ u, (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) u = (c : K) • u := fun u => by
      rw [← hθ g, derivedLinear_apply, ← hc,
        LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar]
    have h3 : (c : K) = 1 := by
      have h4 := hGv g g.2
      rw [h2] at h4
      have h5 : ((c : K) - 1) • v = 0 := by rw [sub_smul, h4, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right hv)
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine LinearEquiv.ext fun u => ?_
    rw [h2, h3, one_smul]
    rfl
  have hφr : ∀ g, φ g ∈ centralizer
      ({matrixProjectiveProjection Q W} : Set (matrixProjectiveDerived Q)) ⊓
        centralizer (X : Set (matrixProjectiveDerived Q)) := by
    intro g
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      have h1 : θ g * W = W * θ g := by
        apply derivedLinear_injective Q
        rw [map_mul, map_mul, hθ g]
        exact hGW g g.2
      change matrixProjectiveProjection Q (θ g) * matrixProjectiveProjection Q W =
        matrixProjectiveProjection Q W * matrixProjectiveProjection Q (θ g)
      rw [← map_mul, ← map_mul, h1]
    · rw [mem_centralizer_iff]
      intro x hx
      rw [← hYX] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have h1 : y * θ g = θ g * y := by
        apply derivedLinear_injective Q
        rw [map_mul, map_mul, hθ g]
        exact (hGY g g.2 y hy).symm
      change matrixProjectiveProjection Q y * matrixProjectiveProjection Q (θ g) =
        matrixProjectiveProjection Q (θ g) * matrixProjectiveProjection Q y
      rw [← map_mul, ← map_mul, h1]
  let ψ : G →* ↥(centralizer
      ({matrixProjectiveProjection Q W} : Set (matrixProjectiveDerived Q)) ⊓
        centralizer (X : Set (matrixProjectiveDerived Q))) := φ.codRestrict _ hφr
  have hψ : Function.Injective ψ := fun a b h => hφi (congrArg Subtype.val h)
  exact LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hG
    (Group.isSolvable_of_isSolvable_injective hψ)

end CFSG.ComponentClassification.CatLeafProof.EndOddO
