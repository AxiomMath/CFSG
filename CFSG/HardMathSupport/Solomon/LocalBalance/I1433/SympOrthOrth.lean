module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthGeneric
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthOrthBlock
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates
import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
open scoped commutatorElement

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.RankThree.PartOne.KCOrthogonalNoninner (mem_of_pow_eq_one_of_relIndex_eq_two_pow)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)

theorem inner_of_mem_commutator_gates {K : Type} [Field K] [Finite K] {d f : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hg : OrthogonalGates Q f)
    (htop : projectivePointFamilyAut Q = ⊤) {β : MulAut (matrixProjectiveDerived Q)}
    (hβ : β ∈ commutator (MulAut (matrixProjectiveDerived Q))) (hβ3 : β ^ 3 = 1) :
    ∃ t : matrixProjectiveDerived Q, MulAut.conj t = β := by
  obtain ⟨-, ⟨ψ, -, hker, hcyc⟩, ⟨-, k, hk⟩, -, -, hE, -⟩ := hg
  have hEall : ∀ γ : MulAut (matrixProjectiveDerived Q), γ ∈ matrixProjectiveImage Q := fun γ => by
    rw [← hE, htop]; exact Subgroup.mem_top γ
  have hD : β ∈ (linearConjugationHom Q).range := by
    have hle : commutator (MulAut (matrixProjectiveDerived Q)) ≤
        (linearConjugationHom Q).range := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      have h1 : (⟨⁅a, b⁆, hEall _⟩ : ↥(matrixProjectiveImage Q)) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        have : (⟨⁅a, b⁆, hEall _⟩ : ↥(matrixProjectiveImage Q)) =
            ⁅(⟨a, hEall a⟩ : ↥(matrixProjectiveImage Q)),
              (⟨b, hEall b⟩ : ↥(matrixProjectiveImage Q))⁆ := rfl
        rw [this, map_commutatorElement]
        haveI := hcyc
        have hcomm : ∀ x y : ↥ψ.range, x * y = y * x := fun x y =>
          (IsCyclic.commGroup (α := ↥ψ.range)).mul_comm x y
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (congrArg Subtype.val (hcomm ⟨ψ ⟨a, hEall a⟩, ⟨_, rfl⟩⟩ ⟨ψ ⟨b, hEall b⟩, ⟨_, rfl⟩⟩))
      rw [hker, Subgroup.mem_subgroupOf] at h1
      exact h1
    exact hle hβ
  have : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  exact mem_of_pow_eq_one_of_relIndex_eq_two_pow hk Nat.prime_three (by norm_num) hD hβ3

theorem orth_inner_of_mem_commutator {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S]
    {n ℓ f : ℕ} (hG : StatedClassicalModel S t n ℓ f) (hD4 : t = .POmegaPlus → n ≠ 4)
    {β : MulAut S} (hβ : β ∈ commutator (MulAut S)) (hβ3 : β ^ 3 = 1) :
    ∃ s : S, MulAut.conj s = β := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaOdd
      (Or.inl rfl) n ℓ f hG K hK e
    have htop : projectivePointFamilyAut (coordinateQuadOdd n K) = ⊤ :=
      ((orthogonal_geometry_tail_model_point_family_invariant S .POmegaOdd
        (.inl rfl) n ℓ f hG) K hK).2
    exact inner_of_mem_commutator_of_equiv (coordinateOddWitnessEquiv K e)
      (fun β hβ hβ3 => inner_of_mem_commutator_gates hgates htop hβ hβ3) hβ hβ3
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
    obtain ⟨-, -, hn4⟩ := hG.1
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ f hG K hK e
    have h5 : 5 ≤ n := by have := hD4 rfl; omega
    have htop : projectivePointFamilyAut (coordinateQuadPlus n K) = ⊤ :=
      (orthogonal_geometry_plus_point_family_orbit hG hK e).2.2.2.2.1 h5
    exact inner_of_mem_commutator_of_equiv (coordinatePlusWitnessEquiv K e)
      (fun β hβ hβ3 => inner_of_mem_commutator_gates hgates htop hβ hβ3) hβ hβ3
  · obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
    obtain ⟨-, -, hn4⟩ := hG.1
    have hn1 : 1 ≤ n := by omega
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ f hG hn1 K hK b c hirr e
    have htop : projectivePointFamilyAut (coordinateQuadMinus n K hn1 b c) = ⊤ :=
      ((orthogonal_geometry_tail_model_point_family_invariant S .POmegaMinus
        (.inr rfl) n ℓ f hG) hn1 K hK b c hirr).2
    exact inner_of_mem_commutator_of_equiv (coordinateMinusWitnessEquiv K hn1 b c e)
      (fun β hβ hβ3 => inner_of_mem_commutator_gates hgates htop hβ hβ3) hβ hβ3

theorem orth_exists_blockModel {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S]
    {n ℓ f : ℕ} (hG : StatedClassicalModel S t n ℓ f) (hℓ3 : ℓ ≠ 3) :
    ∃ (G : Type) (_ : Group G) (π : G →* S), Function.Surjective π ∧
      π.ker ≤ Subgroup.center G ∧ (∀ z ∈ π.ker, z ^ 2 = 1) ∧
      ∀ X : G, X ^ 3 = 1 → π X ≠ 1 → ∀ J : Subgroup S,
        IsComponentOf J (Subgroup.centralizer ({π X} : Set S)) → π X ∈ J →
          HasLowRankBlock π X J :=
  orth_exists_blockModel' ht hG hℓ3

theorem orth_contra {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) {n ℓ f : ℕ}
    (hG : StatedClassicalModel S t n ℓ f) (hℓ3 : ℓ ≠ 3) (hD4 : t = .POmegaPlus → n ≠ 4)
    {Q : Subgroup (MulAut S)} {x : S} {J : Subgroup S} {q : ℕ} (c : I1433SCfg Q x J q) :
    False := by
  haveI := hs
  have hS : Subgroup.center S = ⊥ := b3Lie_center_eq_bot hna
  have hinn : ∀ β ∈ Q, ∃ s : S, MulAut.conj s = β := fun β hβ =>
    orth_inner_of_mem_commutator ht hG hD4 (c.derived hβ) (c.exponent β hβ)
  obtain ⟨G, _, π, hπ, hker, hker2, hblock⟩ := orth_exists_blockModel ht hG hℓ3
  refine c.false_of_lowRank π hπ hker hker2 hS (fun y hy => ?_) hblock hinn
  exact LieSemisimple.perfectInLayer_conj_omega ht hG Nat.prime_three (by norm_num)
    (Ne.symm hℓ3) y hy

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
