module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8e
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Corr
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Low
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowOData

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup Module Matrix
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
open CFSG.ComponentClassification.OddSelector (rowOAction)

attribute [local instance] GSThmB.Catalog7Std.Om8.finite_linearEquiv

variable {K : Type} [Field K] [Finite K] {b c : K}

omit [Finite K] in
theorem card_extension (c₀ : K) : Nat.card (extension c₀) = Nat.card K ^ 2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd c₀ 0), Nat.card_prod, sq]

theorem finite_extension (c₀ : K) : Finite (extension c₀) :=
  Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd c₀ 0).symm

theorem image_eq_commutator {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (μ c₀ : Kˣ)
    (hsim : ∀ x, Q8 K b c (A x) = (μ : K) * Q8 K b c x) (hsq : ∀ x, A (A x) = (c₀ : K) • x)
    [Fact (¬ IsSquare (c₀ : K))]
    (hadj : ∀ x y, (Q8 K b c).polarBilin (A.toLinearMap x) y =
      (Q8 K b c).polarBilin x (A.toLinearMap y)) (h2K : (2 : K) ≠ 0)
    (M : Subgroup ((orthogonalDerived (Q8 K b c)).subgroupOf
      (fixedSubgroup (similarityConjugation (Q8 K b c) A μ hsim)))) (hM : IsPComponent 2 M) :
    letI := modE A (c₀ : K) hsq
    ∀ g, g ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup
        (formE A (c₀ : K) hsq (Q8 K b c) (Units.ne_zero c₀) hadj)) ↔
      ∃ m ∈ M, centEquivE A (c₀ : K) hsq (Q8 K b c) (Units.ne_zero c₀) hadj h2K
        (fixedCentralizerEquiv (Q8 K b c) A μ hsim m.val) = g := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have hstated := stated K b c hp he hK hirr
  obtain ⟨-, hnd, -⟩ := CatalogueBOrthogonalPointData.coordinate_model_witness_minus hstated K hK
    b c hirr (MulEquiv.refl _)
  have hnp := GSThmB.Catalog7Std.Om8.not_isPlusType_coordinateQuadMinus 4 (by norm_num) hirr
  let := modE A (c₀ : K) hsq
  let := isScalarTower A (c₀ : K) hsq
  let := finite_extension (c₀ : K)
  let : FiniteDimensional (extension (c₀ : K)) (Fin (2 * 4) → K) :=
    Module.Finite.of_restrictScalars_finite K _ _
  have hc₀ : (c₀ : K) ≠ 0 := Units.ne_zero c₀
  have hQE := formE_nondegenerate A (c₀ : K) hsq (Q8 K b c) hc₀ hadj h2K hnd
  have hdim : finrank K (Fin (2 * 4) → K) = 8 := by simp
  have hdimE : finrank (extension (c₀ : K)) (Fin (2 * 4) → K) = 4 := by
    have := finrank_E A (c₀ : K) hsq
    omega
  have hno := formE_not_split A (c₀ : K) hsq (Q8 K b c) hc₀ hadj h2K hdim hnp
  have hE : Nat.card (extension (c₀ : K)) = p ^ (2 * e) := by
    rw [card_extension, hK, ← pow_mul, mul_comm]
  have hM' := CatalogueBAlternating.pComponent_map_equiv 2
    ((fixedCentralizerEquiv (Q8 K b c) A μ hsim).trans
      (centEquivE A (c₀ : K) hsq (Q8 K b c) hc₀ hadj h2K)) _
    ((GSThmB.Catalog7Std.Om8.chain_normal_iff (orthogonalDerived (Q8 K b c))
      (similarityConjugation (Q8 K b c) A μ hsim) M).mp hM)
  have hMc := (GSThmB.Catalog7Std.Om8.pComponent_nonsplit_four hp hp2 (by omega) hE hQE hdimE
    hno hM').1
  intro g
  rw [← hMc]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨_, ⟨m, hm, rfl⟩, rfl⟩

theorem exists_hom_of_image {X T H S : Type*} [Group X] [Group T] [Group H] [Group S]
    {Ω Fx C : Subgroup X} (fcE : Fx ≃* C) (hfcE : ∀ g, ((fcE g : C) : X) = g)
    (cE : C ≃* T) (e' : T ≃* H) (ρ : S →* H) (M : Subgroup (Ω.subgroupOf Fx))
    (himage : ∀ g, g ∈ ρ.range.map e'.symm.toMonoidHom ↔ ∃ m ∈ M, cE (fcE m.val) = g) :
    ∃ y : S →* Ω, (∀ h, ((y h : Ω) : X) = ((cE.symm (e'.symm (ρ h)) : C) : X)) ∧
      (∀ m ∈ M, ∃ h, y h = ⟨m.val.val, m.property⟩) ∧
      ∀ h, ∃ m ∈ M, y h = ⟨m.val.val, m.property⟩ := by
  have hmem : ∀ h, ∃ m ∈ M, cE (fcE m.val) = e'.symm (ρ h) := fun h =>
    (himage _).mp (mem_map_of_mem _ ⟨h, rfl⟩)
  have hy : ∀ h, ((C.subtype.comp (cE.symm.toMonoidHom.comp (e'.symm.toMonoidHom.comp ρ))) h) ∈
      Ω := fun h => by
    obtain ⟨m, -, hm⟩ := hmem h
    change ((cE.symm (e'.symm (ρ h)) : C) : X) ∈ Ω
    rw [← hm, MulEquiv.symm_apply_apply, hfcE]
    exact m.property
  refine ⟨(C.subtype.comp (cE.symm.toMonoidHom.comp (e'.symm.toMonoidHom.comp ρ))).codRestrict
    Ω hy, fun h => rfl, fun m hm => ?_, fun h => ?_⟩
  · obtain ⟨_, ⟨h, rfl⟩, hh⟩ := (himage (cE (fcE m.val))).mpr ⟨m, hm, rfl⟩
    refine ⟨h, Subtype.ext ?_⟩
    change ((cE.symm (e'.symm (ρ h)) : C) : X) = m.val.val
    change e'.symm (ρ h) = _ at hh
    rw [hh, MulEquiv.symm_apply_apply, hfcE]
  · obtain ⟨m, hm, hme⟩ := hmem h
    refine ⟨m, hm, Subtype.ext ?_⟩
    change ((cE.symm (e'.symm (ρ h)) : C) : X) = m.val.val
    rw [← hme, MulEquiv.symm_apply_apply, hfcE]

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
