module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaOddCoreLemmas
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaInvolutionConjugacy

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace OmegaRadical

variable {K : Type} [Field K] {d : ℕ}

@[expose] def FieldInvolutionOddCore (Q : QuadraticForm K (Fin d → K)) : Prop :=
  ∀ H : Subgroup (MulAut (matrixProjectiveDerived Q)), inner (matrixProjectiveDerived Q) ≤ H →
    H ≤ matrixProjectiveImage Q → ∀ g : similarityPairs Q, g.val.right ≠ 1 →
      matrixProjectiveConjugationHom Q g ∈ H →
      orderOf (matrixProjectiveConjugationHom Q g) = 2 →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {matrixProjectiveConjugationHom Q g}) = ⊥

theorem fieldInvolutionOddCore_of_regular {f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) : FieldInvolutionOddCore Q := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have := finite_mulAut_matrixProjectiveDerived Q
  intro H hInn hHE g hg1 hgH hg2
  set α := matrixProjectiveConjugationHom Q g with hαdef
  obtain ⟨b, hb⟩ := exists_scalarPair_mul_mem Q g
  set S : similarityPairs Q := ⟨_, scalarPair_mem Q b⟩ * g with hSdef
  have hSα : matrixProjectiveConjugationHom Q S = α := by
    rw [hSdef, map_mul, kappa_scalarPair, one_mul]
  have hS1 : S.val.right ≠ 1 := by
    change (SemidirectProduct.inl _ * g.val).right ≠ 1
    rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]
    exact hg1
  obtain ⟨-, -, hsimple, heven, ext, -, -, hinj, hinn, hNC, hnormal, hcent⟩ :=
    evenOrthogonalFieldCentralizer_of_regular hf hK hn Q hQ hT hE α (hHE hgH) hg2 S hb hSα hS1
  set N := (extKappa Q ext).range with hNdef
  have : Finite ↥(pairDescentDerived hb) := Finite.of_injective _ hinj
  have hN : CFSG.oddCore ↥N = ⊥ :=
    EvenCatalog.oddCore_eq_bot_of_mulEquiv (MonoidHom.ofInjective hinj)
      (EvenCatalog.oddCore_eq_bot_of_isSimpleGroup heven)
  refine oddCore_eq_bot_of_normal (N := N) (fun x hx => ?_) (fun x hx n hn => ?_) hN
    (fun x hx hxN => ?_)
  · exact Subgroup.mem_inf.mpr ⟨hInn (hinn hx), (Subgroup.mem_inf.mp (hNC hx)).2⟩
  · obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxE : x ∈ matrixProjectiveImage Q ⊓ Subgroup.centralizer {α} :=
      Subgroup.mem_inf.mpr ⟨hHE hxH, hxC⟩
    have h1 := hnormal.conj_mem ⟨n, hNC hn⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨x, hxE⟩
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  · obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxZ : x ∈ matrixProjectiveImage Q ⊓ Subgroup.centralizer {α} ⊓
        Subgroup.centralizer (N : Set (MulAut (matrixProjectiveDerived Q))) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hHE hxH, hxC⟩,
        Subgroup.mem_centralizer_iff.mpr fun n hn => (hxN n hn).symm⟩
    rw [hcent] at hxZ
    have h2 : x ^ orderOf α = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_of_mem_zpowers hxZ)
    rw [hg2] at h2
    exact ⟨1, by rw [pow_one]; exact h2⟩

end OmegaRadical

open OmegaRadical in
theorem even_orthogonal_field_involution_semilinear_odd_core (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ)
    (h : StatedClassicalModel G t n 2 f) :
    match t with
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)),
          FieldInvolutionOddCore (coordinateQuadPlus n K) ∧
            (5 ≤ n → matrixProjectiveImage (coordinateQuadPlus n K) = ⊤)
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)),
          FieldInvolutionOddCore (coordinateQuadMinus n K hn b c) ∧
            matrixProjectiveImage (coordinateQuadMinus n K hn b c) = ⊤
    | _ => False := by
  have htop := semilinearImageEqTop G t ht h
  rcases ht with rfl | rfl
  · obtain ⟨-, hf, hn⟩ := h.1
    intro K _ _ hK e
    have hreg := regular_coordinateQuadPlus n K (by omega)
    exact ⟨fieldInvolutionOddCore_of_regular hf hK hn hreg.1 hreg.2
      (commutator_coordinateQuadPlus n K (by omega)), fun h5 => htop h5 K hK e⟩
  · obtain ⟨-, hf, hn⟩ := h.1
    intro hn1 K _ _ hK b c hirr e
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    exact ⟨fieldInvolutionOddCore_of_regular hf hK hn hreg.1 hreg.2
      (commutator_coordinateQuadMinus n K b c hn hirr), htop hn1 K hK b c hirr e⟩

end CFSG.ComponentClassification.UnbalancedCatalog
