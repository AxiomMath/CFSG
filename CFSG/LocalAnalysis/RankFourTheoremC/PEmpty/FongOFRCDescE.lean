module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieExc
import CFSG.HardMathSupport.Lang.E6Descent.OuterDescentE
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Lang.E6Descent (prime_dvd_of_diag_noninner
  exists_conj_entrywise_of_not_innerDiag)

theorem not_prime_dvd_cartan_det_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp5 : 5 ≤ p) : ¬ p ∣ τ.cartan.det.natAbs := by
  intro hdvd
  have hpos : 0 < τ.cartan.det.natAbs := by
    rcases hτ with rfl | rfl | rfl
    · rw [det_cartan_E6]; norm_num
    · rw [det_cartan_E7]; norm_num
    · rw [det_cartan_E8]; norm_num
  have hle : τ.cartan.det.natAbs ≤ 3 := by
    rcases hτ with rfl | rfl | rfl
    · rw [det_cartan_E6]; norm_num
    · rw [det_cartan_E7]; norm_num
    · rw [det_cartan_E8]; norm_num
  have := Nat.le_of_dvd hpos hdvd
  omega

section


theorem pRank_adjoint_le_fixed_entrywise_anychar_E {p : ℕ} (hp1 : 1 < p) (τ : Tag) {M : Type}
    [Field M] [Finite M] (σ : M ≃+* M) :
    CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ (fixSubfield σ))) ≤
      CFSG.Open.pRank p (fixedSubgroup (entrywiseAdjointAut τ σ)) := by
  classical
  obtain ⟨-, -, -, hJΓ, -, -, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ M σ
  have hJA : fixedFieldImage τ σ ≤ adjointGroup τ M := hJΓ.trans inf_le_left
  set J : Subgroup ↥(adjointGroup τ M) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ M)
  have hmemJ : ∀ x : ↥(adjointGroup τ M), x ∈ J ↔ (x : ModGL τ M) ∈ fixedFieldImage τ σ :=
    fun x => Iff.rfl
  have hJC : J ≤ fixedSubgroup (entrywiseAdjointAut τ σ) := fun x hx => by
    refine Subtype.ext ?_
    change ((entrywiseAdjointAut τ σ x : ↥(adjointGroup τ M)) : ModGL τ M) = (x : ModGL τ M)
    rw [coe_entrywiseAdjointAut]
    exact (hJΓ ((hmemJ x).1 hx)).2
  let eJ : ↥J ≃* adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv σ).symm
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ (fixSubfield σ))) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥J) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 eJ).symm
  have h2 : CFSG.Open.pRank p J = CFSG.Open.pRank p (⊤ : Subgroup ↥J) :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_eq_pRank_top J
  have h3 := CFSG.SectionRank.pRank_mono (p := p) hp1 hJC
  omega

theorem descent_fixed_adjoint_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime) (hp5 : 5 ≤ p) (hne : ℓ ≠ p) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f) (α : MulAut (adjointGroup τ K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup τ K)) :
    p ∣ f ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = ℓ ^ (f / p) ∧
      CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ k)) ≤
        CFSG.Open.pRank p (fixedSubgroup α) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hnd : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      α ≠ MulAut.conj g * rootDiagAut τ K a := fun g a h =>
    not_prime_dvd_cartan_det_E hτ hp5 (prime_dvd_of_diag_noninner τ hτ K hp g a α h hαp hα).1
  obtain ⟨d, T, r, j, ψ, hd, -, hcard, -, -, hαβ, hψ⟩ :=
    exists_conj_entrywise_of_not_innerDiag τ hτ hf K hK hp (by omega) α hαp hnd
  have hfp : f / p = d := by rw [hd, Nat.mul_div_cancel_left d hp.pos]
  refine ⟨⟨d, hd⟩, ↥(fixSubfield T), inferInstance, inferInstance, ?_, ?_⟩
  · rw [hfp]
    exact hcard
  · have h1 := pRank_adjoint_le_fixed_entrywise_anychar_E hp.one_lt τ T
    have h2 := pRank_fixed_le_of_intertwine hp.one_lt ψ (α ^ r) (entrywiseAdjointAut τ T)
      (intertwine_of_conj hψ)
    have h3 : fixedSubgroup (α ^ r) ≤ fixedSubgroup α := by
      have := fixedSubgroup_le_pow (α ^ r) j
      rwa [hαβ] at this
    have h4 := CFSG.SectionRank.pRank_mono (p := p) hp.one_lt h3
    exact h1.trans (h2.trans h4)

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

end
