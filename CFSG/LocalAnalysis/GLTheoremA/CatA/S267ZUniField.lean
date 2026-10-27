module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniBound
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUDescent
import CFSG.GH74.Uniqueness.SU.SU7Gen3
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem inner_le_innDiag (h : UnitaryFieldData ℓ f K) : inner (PU h) ≤ innDiag h := by
  intro α hα
  obtain ⟨s, rfl⟩ := (mem_inner_primeFormP h _ α).1 hα
  exact ⟨_, rfl⟩

theorem exists_fieldAut_mem [Finite K] (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (PU h))}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) :
    ∃ α ∈ E, α ∉ innDiag h ∧ ∃ σ : K ≃+* K, orderOf σ = p ∧ fieldFactor h hℓ α = σ ∧
      p ∣ f ∧ p ∣ ℓ ^ (f / p) + 1 ∧
      Nat.card (semilinearFixedSubfield σ) = (ℓ ^ (f / p)) ^ 2 ∧
      (∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ (f / p))) ∧
      ∃ M : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
        (primeFormConjHom h _ M)⁻¹ * α * primeFormConjHom h _ M =
          primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker (fieldFactor h hℓ) E
  rw [ker_fieldFactor, hcard] at h1
  have hmap := card_map_fieldFactor_le h hℓ hp hE
  have hinf := card_inf_innDiag_le h hp hp2 hpℓ hE
  have hinf2 : p ^ 2 ≤ Nat.card ↥(E ⊓ innDiag h) := by
    refine Nat.le_of_mul_le_mul_left ?_ hp.pos
    calc p * p ^ 2 = p ^ 3 := by ring
      _ = _ := h1.symm
      _ ≤ p * Nat.card ↥(E ⊓ innDiag h) := Nat.mul_le_mul_right _ hmap
  have hne : ¬ E ≤ innDiag h := by
    intro hle
    rw [inf_eq_left.2 hle, hcard] at hinf
    exact absurd hinf (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  obtain ⟨α, hαE, hαD⟩ := Set.not_subset.1 hne
  have hαp : α ^ p = 1 := hE.2 α hαE
  have hα1 : α ≠ 1 := fun h1 => hαD (h1 ▸ (innDiag h).one_mem)
  have hαord : orderOf α = p := orderOf_eq_prime hαp hα1
  set σ := fieldFactor h hℓ α with hσdef
  have hσ1 : σ ≠ 1 := fun h1 => hαD (by
    have hk : α ∈ (fieldFactor h hℓ).ker := MonoidHom.mem_ker.2 h1
    rw [ker_fieldFactor] at hk
    exact hk)
  have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hαp, map_one]
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨hpf, hK0, hbar, -, -, M, hM⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h (n := 3)
      (le_refl 3) (not_three_two_of_ne_two h.prime hℓ) hp hp2 α hαord σ rfl hσord
  have hq1 : p ∣ ℓ ^ f + 1 := dvd_add_one_of_le_card_inf_innDiag h hℓ hp hp2 hpℓ hE hinf2
  have hfp : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by
    rw [← pow_mul, Nat.div_mul_cancel hpf]
  rw [hfp] at hq1
  exact ⟨α, hαE, hαD, σ, hσord, rfl, hpf,
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC.dvd_pow_prime_add_one_iff.1 hq1, hK0,
    hbar, M, hM⟩

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
