module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QCov
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionEigen

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

theorem evenCentInv_of_cover' {S X : Type} [Group S] [Group X] [Finite S] (π : S →* X)
    (hπ : Function.Surjective π) (hker : ∀ s, π s = 1 → s ∈ center S) (a : S)
    (𝓜 : Set (Subgroup S)) (hC : ∀ M ∈ 𝓜, M ≤ centralizer ({a} : Set S))
    (hN : ∀ M ∈ 𝓜, ∀ x ∈ centralizer ({a} : Set S), ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hQ : ∀ M ∈ 𝓜, IsQuasisimple M) (hE : ∀ M ∈ 𝓜, ∃ m ∈ M, π m ≠ 1 ∧ m ^ 4 = 1)
    (hinv : ∀ g : S, (∀ M ∈ 𝓜, ∀ m ∈ M, g * m = m * g) → π (g * g) = 1 →
      π g = 1 ∨ π g = π a) :
    EvenCentInv X (π a) := by
  intro g _ hg hgg
  obtain ⟨ĝ, hĝ⟩ := hπ g
  rcases hinv ĝ (lift_commute_of_cover π hπ hker a 𝓜 hC hN hQ hE g hg ĝ hĝ)
    (by rw [map_mul, hĝ, hgg]) with h | h
  · exact Or.inl (hĝ ▸ h)
  · exact Or.inr (hĝ ▸ h)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] def psuCover {X : Type*} [Group X] (e₀ : X ≃* primeFormP h (idGram K n)) :
    gramSU h (idGram K n) →* X :=
  e₀.symm.toMonoidHom.comp (QuotientGroup.mk' _)

theorem psuCover_surjective {X : Type*} [Group X] (e₀ : X ≃* primeFormP h (idGram K n)) :
    Function.Surjective (psuCover h e₀) :=
  e₀.symm.surjective.comp (QuotientGroup.mk'_surjective _)

theorem psuCover_eq_one_iff {X : Type*} [Group X] (e₀ : X ≃* primeFormP h (idGram K n))
    (s : gramSU h (idGram K n)) :
    psuCover h e₀ s = 1 ↔ s ∈ normOneScalars h (gramSU h (idGram K n)) n := by
  change e₀.symm (QuotientGroup.mk' _ s) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem normOneScalars_le_center :
    normOneScalars h (gramSU h (idGram K n)) n ≤ center (gramSU h (idGram K n)) := by
  rintro z ⟨c, -, -, hz⟩
  refine mem_center_iff.mpr fun g => Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
  exact (commute_scalar c _).eq

theorem toLin_scalar_eq (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.toLin (GeneralLinearGroup.scalar (Fin n) c) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) = (c : K) • 1 := by
  rw [Matrix.GeneralLinearGroup.coe_toLin, GeneralLinearGroup.coe_scalar]
  ext v i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

@[expose] def suOp (a : gramSU h (idGram K n)) : sesqUnitaryGroup (idForm h n) :=
  ⟨Matrix.GeneralLinearGroup.toLin (a : GL (Fin n) K),
    (toLin_mem_sesqUnitaryGroup_iff _).mpr ((mem_gramSU_iff_unitary h).mp a.2).1⟩

theorem orderOf_mk_suOp (a : gramSU h (idGram K n))
    (ha2 : a * a ∈ normOneScalars h (gramSU h (idGram K n)) n)
    (ha1 : a ∉ normOneScalars h (gramSU h (idGram K n)) n) :
    orderOf (QuotientGroup.mk (suOp h a) : sesqProjUnitary h (idForm h n)) = 2 := by
  have hT2 : suOp h a * suOp h a ∈ sesqNormOneScalars h (idForm h n) := by
    obtain ⟨c, hcN, -, hc⟩ := ha2
    refine ⟨(c : K), hcN, ?_⟩
    have h1 : ((suOp h a * suOp h a : sesqUnitaryGroup (idForm h n)) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) =
        Matrix.GeneralLinearGroup.toLin ((a * a : gramSU h (idGram K n)) : GL (Fin n) K) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul]
      rfl
    rw [h1, hc, toLin_scalar_eq]
  have hT1 : (QuotientGroup.mk (suOp h a) : sesqProjUnitary h (idForm h n)) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨c, hcN, hc⟩ := h1
    apply ha1
    have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one h hcN
    have ha : (a : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0) := by
      apply Matrix.GeneralLinearGroup.toLin.injective
      apply Units.ext
      rw [toLin_scalar_eq]
      exact hc
    refine ⟨Units.mk0 c hc0, hcN, ?_, ha⟩
    have hdet := ((mem_gramSU_iff_unitary h).mp a.2).2
    rw [ha, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext hdet
  refine orderOf_eq_prime ?_ hT1
  rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  exact hT2

theorem isQuasisimple_gramSU_one {m : ℕ} (hm : 2 ≤ m) (hq : 4 ≤ p ^ f) :
    IsQuasisimple (gramSU h (1 : Matrix (Fin m) (Fin m) K)) := by
  have hS : (gramForm h (1 : Matrix (Fin m) (Fin m) K)).IsSymm :=
    gramForm_isSymm h (by simp)
  have hL : (gramForm h (1 : Matrix (Fin m) (Fin m) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  have hfin : Module.finrank K (Fin m → K) = m := Module.finrank_fin_fun K
  have hQ := RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le h hS hL
    (by omega) ⟨fun _ => hq, fun _ => by omega⟩
  obtain ⟨φ⟩ := RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU h
    (B := gramForm h (1 : Matrix (Fin m) (Fin m) K))
    (Pi.basisFun K (Fin m)) (G := (1 : Matrix (Fin m) (Fin m) K)) (fun i j => by
      simp [gramForm_apply, Pi.single_apply, Matrix.one_apply, dotProduct, eq_comm])
  exact LocalCores.isQuasisimple_of_mulEquiv φ hQ

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
