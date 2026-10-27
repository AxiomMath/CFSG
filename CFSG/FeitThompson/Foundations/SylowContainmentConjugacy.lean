module

public import Mathlib.GroupTheory.Sylow
import CFSG.FeitThompson.Foundations.PGroupFixedPointCongruence
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

open MulAction Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] {p : ℕ}

theorem natCard_conj_smul (g : G) (P : Subgroup G) :
    Nat.card (MulAut.conj g • P : Subgroup G) = Nat.card P :=
  (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) P).toEquiv).symm

theorem not_dvd_index_of_natCard_eq_pow_factorization [Finite G] (hp : p.Prime) {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) : ¬ p ∣ P.index := by
  intro h
  have hG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hdvd : p ^ ((Nat.card G).factorization p + 1) ∣ P.index * Nat.card P := by
    rw [hP, pow_succ']
    exact mul_dvd_mul h dvd_rfl
  rw [Subgroup.index_mul_card] at hdvd
  have := (Nat.Prime.pow_dvd_iff_le_factorization hp hG).mp hdvd
  omega

theorem not_dvd_natCard_range_leftCoset [Finite G] (hp : p.Prime) {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) :
    ¬ p ∣ Nat.card (Set.range fun g : G => g • (P : Set G)) := by
  rw [natCard_range_leftCoset]
  exact not_dvd_index_of_natCard_eq_pow_factorization hp hP

variable [Fact p.Prime]

theorem natCard_eq_pow_factorization_iff [Finite G] {P : Subgroup G} :
    Nat.card P = p ^ (Nat.card G).factorization p ↔ IsPGroup p P ∧ ¬ p ∣ P.index := by
  refine ⟨fun h => ⟨IsPGroup.of_card h,
    not_dvd_index_of_natCard_eq_pow_factorization Fact.out h⟩, fun ⟨h1, h2⟩ => ?_⟩
  simpa [IsPGroup.toSylow_coe] using (h1.toSylow h2).card_eq_multiplicity

theorem exists_le_conj_smul_of_isPGroup [Finite G] {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    {S : Subgroup G} (hS : IsPGroup p S) :
    ∃ g : G, S ≤ MulAut.conj g • P := by
  obtain ⟨b, hb⟩ := hS.exists_card_eq
  have hidx : ¬ p ∣ Nat.card (G ⧸ P) := by
    rw [← Subgroup.index_eq_card, ← natCard_range_leftCoset (H := P)]
    exact not_dvd_natCard_range_leftCoset Fact.out hP
  obtain ⟨x, hx⟩ := nonempty_fixedPoints_of_not_dvd_natCard (P := S) (X := G ⧸ P) hb hidx
  induction x using QuotientGroup.induction_on with
  | H g =>
    refine ⟨g, fun s hs => ?_⟩
    have hfix : (s : G) • (g : G ⧸ P) = (g : G ⧸ P) := hx ⟨s, hs⟩
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at hfix
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    refine ⟨g⁻¹ * s * g, ?_, by simp [MulAut.conj]; group⟩
    have := P.inv_mem hfix
    simpa [mul_assoc] using this

theorem exists_forall_inv_mul_mul_mem [Finite G] {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    {S : Subgroup G} (hS : IsPGroup p S) :
    ∃ g : G, ∀ s ∈ S, g⁻¹ * s * g ∈ P := by
  obtain ⟨g, hg⟩ := exists_le_conj_smul_of_isPGroup hP hS
  refine ⟨g, fun s hs => ?_⟩
  obtain ⟨t, ht, hts⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mp (hg hs)
  have : g⁻¹ * s * g = t := by
    rw [← hts]; simp [MulAut.conj]; group
  rwa [this]

theorem exists_le_conj_smul_sylow [Finite G] (P : Sylow p G) {S : Subgroup G}
    (hS : IsPGroup p S) : ∃ g : G, S ≤ MulAut.conj g • (P : Subgroup G) :=
  exists_le_conj_smul_of_isPGroup P.card_eq_multiplicity hS

theorem exists_conj_smul_eq [Finite G] {P Q : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hQ : Nat.card Q = p ^ (Nat.card G).factorization p) :
    ∃ g : G, MulAut.conj g • P = Q := by
  obtain ⟨g, hg⟩ := exists_le_conj_smul_of_isPGroup hP (IsPGroup.of_card hQ)
  exact ⟨g, (Subgroup.eq_of_le_of_card_ge hg (by rw [natCard_conj_smul, hP, hQ])).symm⟩

end

end CFSG.FeitThompson
