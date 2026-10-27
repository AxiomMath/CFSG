module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalPartsSO
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019SpModels
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019FixTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalReduceSO
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019SympOuter
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019LinInner
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open scoped commutatorElement

section Pull

variable {r : ℕ} {K : Type} [Field K] [NeZero r]

theorem exists_quadratic_of_modelPair {R : Type*} [CommRing R]
    {W : Submodule K (Fin r ⊕ Fin r → K)} [Module R W]
    {Γ : Subgroup (LinearMap.GeneralLinearGroup R W)}
    {A : Subgroup (StatedSp r K)} (φ : A ≃* Γ)
    (hφ : ∀ (g : A) (v : Fin r ⊕ Fin r → K) (hv : v ∈ W),
      ((((φ g : Γ) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) ⟨v, hv⟩ : Fin r ⊕ Fin r → K) =
        spEnd (g : StatedSp r K) v)
    (hpair : SpBlock.ModelPair Γ) :
    ∃ uA u'A : A, (uA : StatedSp r K) ∈ ⁅A, A⁆ ∧ (u'A : StatedSp r K) ∈ ⁅A, A⁆ ∧
      ((((φ uA : Γ) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) - 1) ^ 2 = 0 ∧
      (∀ v ∈ W, ((spEnd (uA : StatedSp r K) - 1) ^ 2 : Module.End K (Fin r ⊕ Fin r → K)) v = 0) ∧
      proj r K (u'A : StatedSp r K) * proj r K (uA : StatedSp r K) ≠
        proj r K (uA : StatedSp r K) * proj r K (u'A : StatedSp r K) := by
  obtain ⟨d, hd, τ, hτ, τ', hτ', hsq, m, hne1, hne2⟩ := hpair
  set dA := φ.symm ⟨d, hd⟩
  set τA := φ.symm ⟨τ, hτ⟩
  set τ'A := φ.symm ⟨τ', hτ'⟩
  set uA : A := ⁅dA, τA⁆ with huA
  set u'A : A := ⁅dA, τ'A⁆ with hu'A
  have hφu : ((φ uA : Γ) : LinearMap.GeneralLinearGroup R W) = ⁅d, τ⁆ := by
    rw [huA, map_commutatorElement, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  have hφu' : ((φ u'A : Γ) : LinearMap.GeneralLinearGroup R W) = ⁅d, τ'⁆ := by
    rw [hu'A, map_commutatorElement, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  have hact : ∀ (g : A) (v : W), spEnd (g : StatedSp r K) (v : Fin r ⊕ Fin r → K) =
      ((((φ g : Γ) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) v : Fin r ⊕ Fin r → K) := by
    intro g v
    rw [← hφ g v v.2]
  have hsub : ∀ (g : A) (v : W), (spEnd (g : StatedSp r K) - 1) (v : Fin r ⊕ Fin r → K) =
      (((((φ g : Γ) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) - 1) v :
        Fin r ⊕ Fin r → K) := by
    intro g v
    rw [LinearMap.sub_apply, Module.End.one_apply, hact, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.coe_sub]
  refine ⟨uA, u'A, Subgroup.commutator_mem_commutator dA.2 τA.2,
    Subgroup.commutator_mem_commutator dA.2 τ'A.2, by rw [hφu]; exact hsq, ?_, ?_⟩
  · intro v hv
    rw [sq, Module.End.mul_apply, hsub uA ⟨v, hv⟩, hsub uA, ← Module.End.mul_apply, ← sq, hφu, hsq,
      LinearMap.zero_apply, Submodule.coe_zero]
  · intro hcomm
    rw [← map_mul, ← map_mul] at hcomm
    have hmem : ((uA : StatedSp r K) * (u'A : StatedSp r K))⁻¹ *
        ((u'A : StatedSp r K) * (uA : StatedSp r K)) ∈
        SymplecticHigher.spScalars r K := by
      rw [← SymplecticHigher.ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hcomm, inv_mul_cancel]
    obtain ⟨c, hc2, hc⟩ := CFSG.RankThree.PartOne.KCSpComm.exists_scalar_of_mem_spScalars hmem
    set X := ((uA : StatedSp r K) * (u'A : StatedSp r K))⁻¹ *
      ((u'A : StatedSp r K) * (uA : StatedSp r K)) with hX
    have hprod : (u'A : StatedSp r K) * (uA : StatedSp r K) =
        ((uA : StatedSp r K) * (u'A : StatedSp r K)) * X := by
      rw [hX]
      group
    have hXv : ∀ v : Fin r ⊕ Fin r → K, spEnd X v = (c : K) • v := by
      intro v
      rw [spEnd_apply, hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      ext i
      simp [Matrix.mulVec_diagonal]
    have hmul : ∀ a b : StatedSp r K, spEnd (a * b) = spEnd a * spEnd b := fun a b => by
      change ((spLin r K (a * b) : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) = _
      rw [map_mul, Units.val_mul]
    have h1 : spEnd ((u'A : StatedSp r K) * (uA : StatedSp r K)) (m : Fin r ⊕ Fin r → K) =
        (c : K) • spEnd ((uA : StatedSp r K) * (u'A : StatedSp r K)) (m : Fin r ⊕ Fin r → K) := by
      rw [hprod, hmul, Module.End.mul_apply, hXv, map_smul]
    have hcomp : ∀ g g' : A,
        spEnd ((g : StatedSp r K) * (g' : StatedSp r K)) (m : Fin r ⊕ Fin r → K) =
        (((((φ g : Γ) : LinearMap.GeneralLinearGroup R W) * ((φ g' : Γ) :
          LinearMap.GeneralLinearGroup R W) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) m :
            Fin r ⊕ Fin r → K) := by
      intro g g'
      rw [hmul, Module.End.mul_apply, hact g' m, hact g ⟨_, _⟩, Units.val_mul, Module.End.mul_apply]
    rw [hcomp u'A uA, hcomp uA u'A, hφu, hφu'] at h1
    have hc' : (c : K) = 1 ∨ (c : K) = -1 := by
      have : (c : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hc2, Units.val_one]
      exact sq_eq_one_iff.1 this
    rcases hc' with h | h
    · rw [h, one_smul] at h1
      exact hne1 (Subtype.ext h1.symm)
    · rw [h, neg_one_smul] at h1
      apply hne2
      apply Subtype.ext
      rw [Submodule.coe_neg, h1, neg_neg]

theorem exists_quadratic_of_modelPair_top {R : Type*} [CommRing R]
    {W : Submodule K (Fin r ⊕ Fin r → K)} [Module R W] {A : Subgroup (StatedSp r K)}
    (φ : A ≃* LinearMap.GeneralLinearGroup R W)
    (hφ : ∀ (g : A) (v : Fin r ⊕ Fin r → K) (hv : v ∈ W),
      (((φ g : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) ⟨v, hv⟩ : Fin r ⊕ Fin r → K) =
        spEnd (g : StatedSp r K) v)
    (hpair : SpBlock.ModelPair (⊤ : Subgroup (LinearMap.GeneralLinearGroup R W))) :
    ∃ uA u'A : A, (uA : StatedSp r K) ∈ ⁅A, A⁆ ∧ (u'A : StatedSp r K) ∈ ⁅A, A⁆ ∧
      (((φ uA : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) - 1) ^ 2 = 0 ∧
      (∀ v ∈ W, ((spEnd (uA : StatedSp r K) - 1) ^ 2 : Module.End K (Fin r ⊕ Fin r → K)) v = 0) ∧
      proj r K (u'A : StatedSp r K) * proj r K (uA : StatedSp r K) ≠
        proj r K (uA : StatedSp r K) * proj r K (u'A : StatedSp r K) := by
  obtain ⟨uA, u'A, h1, h2, h3, h4, h5⟩ :=
    exists_quadratic_of_modelPair (φ.trans Subgroup.topEquiv.symm) (fun g v hv => hφ g v hv) hpair
  exact ⟨uA, u'A, h1, h2, h3, h4, h5⟩

end Pull

section Blocks

variable {r : ℕ} {K : Type} [Field K] [NeZero r]

open _root_.Classical in
theorem eq_zero_of_forall_primaryComponent {x : StatedSp r K}
    (hint : DirectSum.IsInternal
      (fun h : primaryFactors (spEnd x) => primaryComponent (spEnd x) (h : K[X])))
    {g : Module.End K (Fin r ⊕ Fin r → K)}
    (hg : ∀ k ∈ primaryFactors (spEnd x), ∀ v ∈ primaryComponent (spEnd x) k, g v = 0) :
    g = 0 := by
  have hle : (⨆ h : primaryFactors (spEnd x), primaryComponent (spEnd x) (h : K[X])) ≤
      LinearMap.ker g := iSup_le fun h v hv => LinearMap.mem_ker.2 (hg h h.2 v hv)
  rw [hint.submodule_iSup_eq_top, top_le_iff, LinearMap.ker_eq_top] at hle
  exact hle

theorem sq_apply_eq_zero_of_not_mem {x g : StatedSp r K} {O : Set K[X]}
    (hg : g ∈ spSupported x O) {k : K[X]} (hk : k ∈ primaryFactors (spEnd x)) (hkO : k ∉ O)
    {v : Fin r ⊕ Fin r → K} (hv : v ∈ primaryComponent (spEnd x) k) :
    ((spEnd g - 1) ^ 2 : Module.End K (Fin r ⊕ Fin r → K)) v = 0 := by
  have h1 : spEnd g v = v := (mem_spSupported.1 hg).2 k hk hkO v hv
  have h0 : (spEnd g - 1) v = 0 := by
    rw [LinearMap.sub_apply, h1, Module.End.one_apply, sub_self]
  rw [sq, Module.End.mul_apply, h0, map_zero]

private theorem matrix_mul_comm_of_le_one {E : Type*} [CommRing E] {m : ℕ} (hm : m ≤ 1)
    (M N : Matrix (Fin m) (Fin m) E) : M * N = N * M := by
  haveI : Subsingleton (Fin m) := Fin.subsingleton_iff_le_one.2 hm
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_subsingleton _ i,
    Fintype.sum_subsingleton _ i, Subsingleton.elim j i, mul_comm]

private theorem not_comm_of_isQuasisimple {G : Type*} [Group G] {A : Subgroup G}
    (hA : CFSG.IsQuasisimple ↥⁅A, A⁆) : ¬ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro hc
  have hbot : ⁅A, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hc a ha b hb).symm
  obtain ⟨-, -, a, b, hab⟩ := hA
  apply hab
  haveI : Subsingleton ↥⁅A, A⁆ := by
    rw [hbot]
    infer_instance
  haveI : Subsingleton (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) := Quotient.instSubsingletonQuotient _
  exact Subsingleton.elim _ _

@[expose] def SpBlockQuad (A : Subgroup (StatedSp r K)) : Prop :=
  ∃ u ∈ ⁅A, A⁆, ∃ u' ∈ ⁅A, A⁆,
    (spEnd u - 1) ^ 2 = 0 ∧ proj r K u' * proj r K u ≠ proj r K u * proj r K u'

variable {ℓ f p : ℕ} {x : StatedSp r K} {a : StatedProj (StatedSp r K)}

theorem spBlockQuad_fixed [FiniteDimensional K (Fin r ⊕ Fin r → K)]
    (blocks : SpPrimaryBlocks ℓ f p x a) (hsq : Squarefree (minpoly K (spEnd x)))
    (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1)
    (hX1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)) :
    SpBlockQuad (spSupported x {X - 1}) := by
  obtain ⟨φ, hφ⟩ := blocks.fixedFactor hX1
  have hB₁ : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt := fun z =>
    spForm_isAlt (z : Fin r ⊕ Fin r → K)
  have hsep := blocks.fixed_nondegenerate.1
  unfold LinearMap.SeparatingLeft at hsep
  obtain ⟨v₀, hv₀W, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq hX1)
  obtain ⟨w₀, hw₀⟩ : ∃ w : primaryComponent (spEnd x) (X - 1),
      (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)) ⟨v₀, hv₀W⟩ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hv₀ (congrArg Subtype.val (hsep ⟨v₀, hv₀W⟩ h))
  have hvw : (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)) ⟨v₀, hv₀W⟩
      (((spForm r K).restrict (primaryComponent (spEnd x) (X - 1)) ⟨v₀, hv₀W⟩ w₀)⁻¹ • w₀) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw₀]
  have hpair := SpBlock.modelPair_alt hB₁ h2 hvw hl hl2
  obtain ⟨uA, u'A, hu, hu', -, hWq, hnc⟩ :=
    exists_quadratic_of_modelPair (R := K) φ (fun g v hv => hφ g ⟨v, hv⟩) hpair
  refine ⟨uA, hu, u'A, hu', ?_, hnc⟩
  apply eq_zero_of_forall_primaryComponent blocks.isInternal
  intro k hk v hv
  by_cases hkX : k = X - 1
  · subst hkX
    exact hWq v hv
  · exact sq_apply_eq_zero_of_not_mem uA.2 hk (by simpa using hkX) hv

private theorem sq_inv_sub_one_eq_zero {R : Type*} [Ring R] (u : Rˣ) (hu : ((u : R) - 1) ^ 2 = 0) :
    (((u⁻¹ : Rˣ) : R) - 1) ^ 2 = 0 := by
  have hab : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
  have hba : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := u.inv_mul
  have e1 : ((u⁻¹ : Rˣ) : R) - 1 = -(((u : R) - 1) * ((u⁻¹ : Rˣ) : R)) := by
    rw [sub_mul, hab, one_mul, neg_sub]
  have e2 : ((u⁻¹ : Rˣ) : R) * ((u : R) - 1) = ((u : R) - 1) * ((u⁻¹ : Rˣ) : R) := by
    rw [mul_sub, sub_mul, hba, hab, mul_one, one_mul]
  calc (((u⁻¹ : Rˣ) : R) - 1) ^ 2
      = ((u : R) - 1) * (((u⁻¹ : Rˣ) : R) * ((u : R) - 1)) * ((u⁻¹ : Rˣ) : R) := by
        rw [sq, e1, neg_mul_neg, mul_assoc, mul_assoc, mul_assoc]
    _ = ((u : R) - 1) ^ 2 * (((u⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R)) := by
        rw [e2, sq, mul_assoc, mul_assoc, mul_assoc]
    _ = 0 := by rw [hu, zero_mul]

private theorem sq_inv_sub_one_eq_zero_gl {E M : Type*} [CommRing E] [AddCommGroup M] [Module E M]
    (u : LinearMap.GeneralLinearGroup E M) (hu : ((u : M →ₗ[E] M) - 1) ^ 2 = 0) :
    (((u⁻¹ : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) - 1) ^ 2 = 0 :=
  sq_inv_sub_one_eq_zero u hu

private theorem gl_comm_of_le_one {E : Type*} [Field E] {m : ℕ} (hm : m ≤ 1) (g g' : GL (Fin m) E) :
    g * g' = g' * g :=
  Units.ext (matrix_mul_comm_of_le_one hm _ _)

open CFSG.RankThree.PartOne.KCUnitary (blockApply blockApply_mem blockApply_blockApply
  blockApply_one blockGL)

theorem spBlockQuad_paired [FiniteDimensional K (Fin r ⊕ Fin r → K)]
    (blocks : SpPrimaryBlocks ℓ f p x a) (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    (hl2 : l ^ 2 ≠ 1) (h : primaryFactors (spEnd x))
    (hne : (h : K[X]) ≠ reciprocalPolynomial (h : K[X]))
    (hnc : ¬ ∀ g ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      ∀ g' ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}, g * g' = g' * g) :
    SpBlockQuad (spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  have P := blocks.paired h hne
  obtain ⟨φ, hφ1, hφ2⟩ := P.factor
  haveI : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
  obtain ⟨ψ⟩ := P.matrixFactor
  have hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) := by
    by_contra hlt
    push Not at hlt
    apply hnc
    intro g hg g' hg'
    have h1 := gl_comm_of_le_one (by omega) (ψ ⟨g, hg⟩) (ψ ⟨g', hg'⟩)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (ψ.injective h1)
  let b : Module.Basis (Fin (primaryMultiplicity (spEnd x) (h : K[X]))) (AdjoinRoot (h : K[X]))
      (primaryComponent (spEnd x) (h : K[X])) := Module.finBasisOfFinrankEq _ _ rfl
  have hij : (⟨0, by omega⟩ : Fin (primaryMultiplicity (spEnd x) (h : K[X]))) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  have h2E : (2 : AdjoinRoot (h : K[X])) ≠ 0 := by
    have := (algebraMap K (AdjoinRoot (h : K[X]))).injective.ne h2
    rwa [map_ofNat, map_zero] at this
  have hlE : algebraMap K (AdjoinRoot (h : K[X])) l ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap K _).injective]
    exact hl
  have hl2E : (algebraMap K (AdjoinRoot (h : K[X])) l) ^ 2 ≠ 1 := by
    rw [← map_pow, Ne, ← map_one (algebraMap K (AdjoinRoot (h : K[X]))),
      (algebraMap K _).injective.eq_iff]
    exact hl2
  have hpair := SpBlock.modelPair_lin b h2E hij hlE hl2E
  obtain ⟨uA, u'A, hu, hu', hγ', hWq, hnc'⟩ :=
    exists_quadratic_of_modelPair_top φ (fun g v hv => hφ1 g v hv) hpair
  refine ⟨uA, hu, u'A, hu', ?_, hnc'⟩
  have hcommx : Commute (spEnd (uA : StatedSp r K)) (spEnd x) := by
    have h1 := (mem_spSupported.1 uA.2).1
    change spEnd (uA : StatedSp r K) * spEnd x = spEnd x * spEnd (uA : StatedSp r K)
    have hmul : ∀ a b : StatedSp r K, spEnd (a * b) = spEnd a * spEnd b := fun a b => by
      change ((spLin r K (a * b) : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) = _
      rw [map_mul, Units.val_mul]
    rw [← hmul, ← hmul, h1]
  have hGi : ((((φ uA)⁻¹ : blockGL (spEnd x) (h : K[X])) :
      Module.End (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))) - 1) ^ 2 = 0 :=
    sq_inv_sub_one_eq_zero_gl (φ uA) hγ'
  have key : ∀ y ∈ primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])),
      ∀ v' : primaryComponent (spEnd x) (h : K[X]),
      spForm r K (v' : Fin r ⊕ Fin r → K) ((spEnd (uA : StatedSp r K) - 1) y) =
        spForm r K ((((((φ uA)⁻¹ : blockGL (spEnd x) (h : K[X])) :
          Module.End (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))) - 1) v' :
            primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K) y := by
    intro y hy v'
    have h1 := hφ2 uA (blockApply (φ uA)⁻¹ v' v'.2) y (blockApply_mem _ _ _) hy
    rw [blockApply_blockApply, mul_inv_cancel, blockApply_one] at h1
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, h1, LinearMap.sub_apply,
      Module.End.one_apply, Submodule.coe_sub, map_sub, LinearMap.sub_apply]
    rfl
  apply eq_zero_of_forall_primaryComponent blocks.isInternal
  intro k hk w hw
  by_cases hkh : k = h
  · subst hkh
    exact hWq w hw
  by_cases hks : k = reciprocalPolynomial (h : K[X])
  · subst hks
    have hpres : ∀ y ∈ primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])),
        (spEnd (uA : StatedSp r K) - 1) y ∈
          primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])) := by
      intro y hy
      exact Submodule.sub_mem _ (apply_mem_primaryComponent hcommx hy) hy
    apply P.perfect_right _ (by rw [sq, Module.End.mul_apply]; exact hpres _ (hpres w hw))
    intro v hv
    rw [sq, Module.End.mul_apply, key _ (hpres w hw) ⟨v, hv⟩, key w hw, ← Module.End.mul_apply,
      ← sq, hGi, LinearMap.zero_apply, Submodule.coe_zero, map_zero, LinearMap.zero_apply]
  · exact sq_apply_eq_zero_of_not_mem uA.2 hk (by simp [hkh, hks]) hw

theorem spBlockQuad_selfDual [FiniteDimensional K (Fin r ⊕ Fin r → K)]
    (blocks : SpPrimaryBlocks ℓ f p x a) (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    (hl2 : l ^ 2 ≠ 1) (h : primaryFactors (spEnd x)) (hX : (h : K[X]) ≠ X - 1)
    (hsd : reciprocalPolynomial (h : K[X]) = h)
    (hnc : ¬ ∀ g ∈ spSupported x {(h : K[X])}, ∀ g' ∈ spSupported x {(h : K[X])},
      g * g' = g' * g) :
    SpBlockQuad (spSupported x {(h : K[X])}) := by
  haveI : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
  obtain ⟨d, -, -, σ, -, -, -, -, -, hE, hbar, Hf, hHs, -, ⟨η, hη0, hη, -⟩, ⟨e, he⟩, φ, hφ⟩ :=
    (blocks.selfDual h hX hsd).exists_half
  have hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) := by
    by_contra hlt
    push Not at hlt
    apply hnc
    intro g hg g' hg'
    have hcommEnd : ∀ F F' : Module.End (AdjoinRoot (h : K[X]))
        (primaryComponent (spEnd x) (h : K[X])), F * F' = F' * F := by
      intro F F'
      apply (LinearMap.toMatrixAlgEquiv e).injective
      rw [map_mul, map_mul]
      exact matrix_mul_comm_of_le_one (by omega) _ _
    have h1 : (φ ⟨g, hg⟩ : LinearMap.GeneralLinearGroup (AdjoinRoot (h : K[X]))
        (primaryComponent (spEnd x) (h : K[X]))) * φ ⟨g', hg'⟩ = φ ⟨g', hg'⟩ * φ ⟨g, hg⟩ :=
      Units.ext (hcommEnd _ _)
    have h2' : φ (⟨g, hg⟩ * ⟨g', hg'⟩) = φ (⟨g', hg'⟩ * ⟨g, hg⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h1
    exact congrArg Subtype.val (φ.injective h2')
  have hm1 : (-1 : AdjoinRoot (h : K[X])) ∈ hE.fixedField := by
    rw [hE.mem_fixedField, map_neg, map_one]
  obtain ⟨μ, hμ'⟩ := hE.normHom_surjective ⟨-1, hm1⟩
  have hμ : μ * hE.bar μ = -1 := congrArg Subtype.val hμ'
  set i₀ : Fin (primaryMultiplicity (spEnd x) (h : K[X])) := ⟨0, by omega⟩
  set i₁ : Fin (primaryMultiplicity (spEnd x) (h : K[X])) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h00 : Hf (e i₀) (e i₀) = 1 := by rw [he, if_pos rfl]
  have h11 : Hf (e i₁) (e i₁) = 1 := by rw [he, if_pos rfl]
  have h01' : Hf (e i₀) (e i₁) = 0 := by rw [he, if_neg h01]
  have h10' : Hf (e i₁) (e i₀) = 0 := by rw [he, if_neg h01.symm]
  have h2E : (2 : AdjoinRoot (h : K[X])) ≠ 0 := by
    have := (algebraMap K (AdjoinRoot (h : K[X]))).injective.ne h2
    rwa [map_ofNat, map_zero] at this
  have hvv : Hf (e i₀ + μ • e i₁) (e i₀ + μ • e i₁) = 0 := by
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul,
      smul_eq_mul, h00, h11, h01', h10', RingHom.id_apply]
    linear_combination hμ
  have hww : Hf ((2 : AdjoinRoot (h : K[X]))⁻¹ • (e i₀ - μ • e i₁))
      ((2 : AdjoinRoot (h : K[X]))⁻¹ • (e i₀ - μ • e i₁)) = 0 := by
    simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul,
      smul_eq_mul, h00, h11, h01', h10', RingHom.id_apply]
    linear_combination (hE.bar (2 : AdjoinRoot (h : K[X]))⁻¹ * (2 : AdjoinRoot (h : K[X]))⁻¹) * hμ
  have hvw : Hf (e i₀ + μ • e i₁) ((2 : AdjoinRoot (h : K[X]))⁻¹ • (e i₀ - μ • e i₁)) = 1 := by
    simp only [map_add, map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, map_smul, smul_eq_mul, h00, h11, h01', h10', RingHom.id_apply]
    field_simp
    linear_combination -hμ
  have hlE : algebraMap K (AdjoinRoot (h : K[X])) l ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap K _).injective]
    exact hl
  have hl2E : (algebraMap K (AdjoinRoot (h : K[X])) l) ^ 2 ≠ 1 := by
    rw [← map_pow, Ne, ← map_one (algebraMap K (AdjoinRoot (h : K[X]))),
      (algebraMap K _).injective.eq_iff]
    exact hl2
  have hσl : hE.bar (algebraMap K (AdjoinRoot (h : K[X])) l) =
      algebraMap K (AdjoinRoot (h : K[X])) l := by
    rw [hbar, σ.commutes]
  have hpair := SpBlock.modelPair_herm hHs hvv hww hvw h2E hlE hl2E hσl hη0 hη
  obtain ⟨uA, u'A, hu, hu', -, hWq, hnc'⟩ :=
    exists_quadratic_of_modelPair φ (fun g v hv => hφ g v hv) hpair
  refine ⟨uA, hu, u'A, hu', ?_, hnc'⟩
  apply eq_zero_of_forall_primaryComponent blocks.isInternal
  intro k hk w hw
  by_cases hkh : k = h
  · subst hkh
    exact hWq w hw
  · exact sq_apply_eq_zero_of_not_mem uA.2 hk (by simpa using hkh) hw

end Blocks

section Main

variable {r : ℕ} {K : Type} [Field K] [Finite K]

private theorem exists_ne_zero_sq_ne_one (hK : 4 ≤ Nat.card K) : ∃ l : K, l ≠ 0 ∧ l ^ 2 ≠ 1 := by
  classical
  by_contra h
  push Not at h
  haveI := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1, -1} := by
    intro l _
    by_cases hl : l = 0
    · simp [hl]
    · rcases sq_eq_one_iff.1 (h l hl) with h1 | h1 <;> simp [h1]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h3 : ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
  omega

private theorem not_dvd_orderOf_of_isPGroup_two' {G : Type*} [Group G] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {T : Subgroup G} (hT : IsPGroup 2 T) : ∀ t ∈ T, ¬ q ∣ orderOf t := by
  intro t ht hdvd
  obtain ⟨j, hj⟩ := hT ⟨t, ht⟩
  have h1 : orderOf t ∣ 2 ^ j := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hj
    simpa using this
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow (hdvd.trans h1)))

private theorem sq_eq_one_of_mem_ker_proj [NeZero r] {s : StatedSp r K}
    (hs : s ∈ (proj r K).ker) : s ^ 2 = 1 := by
  rw [SymplecticHigher.ker_proj] at hs
  obtain ⟨c, hc2, hc⟩ := CFSG.RankThree.PartOne.KCSpComm.exists_scalar_of_mem_spScalars hs
  apply Subtype.ext
  rw [Subgroup.coe_pow, hc, ← map_pow, hc2, map_one, Subgroup.coe_one]

theorem s2019FixCentralizes_conj_proj_sp {q f : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hf : 1 ≤ f)
    (hK : Nat.card K = q ^ f) (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q)
    (x : StatedSp r K) (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    S2019FixCentralizes p (MulAut.conj (proj r K x)) := by
  classical
  haveI : NeZero r := ⟨by omega⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite K
  haveI : CharP K q := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hq2 : q ≠ 2 := by omega
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K q] at h'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h')
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ q := by omega
      _ ≤ q ^ f := Nat.le_self_pow (by omega) q
  obtain ⟨l, hl, hl2⟩ := exists_ne_zero_sq_ne_one hK4
  intro L hL T hT hLT
  have hperf : ⁅L, L⁆ = L := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hL
  have hle := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_sp hq hf
    hK hr hp hp2 hpq x hx L hL.1 hperf
  obtain ⟨hcomp, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hL hle
  have hZc : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have ha1 : proj r K x ≠ 1 := by
    intro h
    apply hx1
    have h2x := sq_eq_one_of_mem_ker_proj (MonoidHom.mem_ker.2 h)
    have hdvd : orderOf x ∣ Nat.gcd 2 p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2x) (orderOf_dvd_of_pow_eq_one hx)
    rw [(Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2), Nat.dvd_one, orderOf_eq_one_iff]
      at hdvd
    exact hdvd
  have ha : orderOf (proj r K x) = p := orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
  have hxp : orderOf x = p := orderOf_eq_prime hx hx1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks hq hf hK hp hp2 hpq hr _
    ha).2 x rfl hxp
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K q] at h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hqf : 2 ≤ q ^ f := le_trans (by omega) (Nat.le_self_pow (by omega) q)
  obtain ⟨O, hOq, hLO⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_conj_of_orbit_family
    (proj r K) SymplecticHigher.proj_surjective hZc x
    (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
    hjoin (fun O =>
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported
        hp3 hqf hsq blocks O) L hcomp
  have hnc := not_comm_of_isQuasisimple hOq
  obtain ⟨u, hu, u', hu', hsq', hnc'⟩ : SpBlockQuad (spSupported x (O : Set K[X])) := by
    obtain ⟨O, h, hh, rfl⟩ := O
    have hh' : h ∈ primaryFactors (spEnd x) := Finset.mem_coe.1 hh
    by_cases hX : h = X - 1
    · subst hX
      have hO : ({X - 1, reciprocalPolynomial (X - 1)} : Set K[X]) = {X - 1} := by
        rw [reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
      change SpBlockQuad (spSupported x {X - 1, reciprocalPolynomial (X - 1)})
      rw [hO]
      exact spBlockQuad_fixed blocks hsq h2 hl hl2 hh'
    · by_cases hsd : reciprocalPolynomial h = h
      · have hO : ({h, reciprocalPolynomial h} : Set K[X]) = {h} := by
          rw [hsd, Set.pair_eq_singleton]
        change SpBlockQuad (spSupported x {h, reciprocalPolynomial h})
        have hnc2 : ¬ ∀ g ∈ spSupported x {h, reciprocalPolynomial h},
            ∀ g' ∈ spSupported x {h, reciprocalPolynomial h}, g * g' = g' * g := hnc
        rw [hO] at hnc2 ⊢
        exact spBlockQuad_selfDual blocks h2 hl hl2 ⟨h, hh'⟩ hX hsd hnc2
      · exact spBlockQuad_paired blocks h2 hl hl2 ⟨h, hh'⟩ (Ne.symm hsd) hnc
  have huL : proj r K u ∈ L := by
    rw [hLO]
    exact Subgroup.mem_map_of_mem _ hu
  have hu'L : proj r K u' ∈ L := by
    rw [hLO]
    exact Subgroup.mem_map_of_mem _ hu'
  have hker : ∀ s ∈ (proj r K).ker, ¬ q ∣ orderOf s := by
    intro s hs hdvd
    have h1 : q ∣ 2 := hdvd.trans (orderOf_dvd_of_pow_eq_one (sq_eq_one_of_mem_ker_proj hs))
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h1)
  have huq : u ^ q = 1 := by
    apply spLin_injective
    rw [map_pow, map_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact pow_char_eq_one_of_sq_sub_one_eq_zero (F := K) hsq'
  exact commutator_eq_bot_of_quadratic_lift hq5 hcomp.2.2 hLT
    (not_dvd_orderOf_of_isPGroup_two' hq hq2 hT) (proj r K) SymplecticHigher.proj_surjective hker
    (spLin r K) spLin_injective huL ⟨_, hu'L, hnc'⟩ huq hsq'

theorem s2019FixCentralizes_one_of_isSimpleGroup {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hperf : Group.IsPerfect G) {p : ℕ} (hp : p.Prime) :
    S2019FixCentralizes p (1 : MulAut G) := by
  intro L hL T hT hLT
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (1 : MulAut G) = ⊤ := by
    ext g
    simp [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
  have hsn : IsSubnormal L ⊤ := hfix ▸ hL.2.1
  have hLne : L ≠ ⊥ := by
    haveI := CFSG.LocalAnalysis.GLTheoremA.AltDown.nontrivial_of_glaPComponent hp hL
    exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance
  have hLtop : L = ⊤ := (CFSG.Open.IsSubnormal.eq_bot_or_top hsn).resolve_left hLne
  subst hLtop
  have hTn : T.Normal := by
    refine ⟨fun t ht g => ?_⟩
    have hg := hLT (Subgroup.mem_top g)
    rw [Subgroup.mem_normalizer_iff] at hg
    exact (hg t).1 ht
  haveI := hs
  haveI := hTn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with h | h
  · rw [h, Subgroup.commutator_bot_left]
  · exfalso
    subst h
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hG2 : IsPGroup 2 G := hT.of_equiv Subgroup.topEquiv
    haveI : Group.IsNilpotent G := hG2.isNilpotent
    obtain ⟨n, hn⟩ := (isSolvable_def G).1 inferInstance
    have htop : ∀ m, derivedSeries G m = ⊤ := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, hperf.commutator_eq_top]
    rw [htop n] at hn
    haveI := hs.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne G
    have ha : a ∈ (⊥ : Subgroup G) := hn ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup G) := hn ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    exact hab (ha.trans hb.symm)

theorem s2019SympInner_five : S2019SympInner (5 ≤ ·) := by
  intro p q hp hp2 hq hq2 hqp hq5 G _ n f hG a ha
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hG
  haveI : Finite G := Finite.of_equiv _ e.toEquiv.symm
  refine s2019FixCentralizes_of_congr hp e (MulAut.conj a) ?_
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  have hea : (e a) ^ p = 1 := by rw [← map_pow, ha, map_one]
  obtain ⟨x, hx, hxp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
      (by omega) hp hp2 hea
  rw [← hx]
  by_cases hx1 : x = 1
  · subst hx1
    rw [map_one, map_one]
    have hne : ¬(n = 2 ∧ Nat.card K = 2) := by
      rintro ⟨-, h2⟩
      rw [hK] at h2
      have h1 : q ∣ 2 := by
        rw [← h2]
        exact dvd_pow_self q (by omega)
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h1)
    obtain ⟨hs, hperf⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hn hne
    exact s2019FixCentralizes_one_of_isSimpleGroup hs hperf hp
  · exact s2019FixCentralizes_conj_proj_sp hq hq5 hf hK (by omega) hp hp2 hqp.symm x hxp hx1

theorem s2019FactClassicalOn_symplectic_of_three (hI3 : S2019SympInner (· = 3)) :
    S2019FactClassicalOn .symplectic :=
  s2019FactClassicalOn_symplectic s2019SympInner_five hI3 (s2019SympOuter _) (s2019SympOuter _)

end Main

end CFSG.LocalAnalysis.GLTheoremA.S2019
