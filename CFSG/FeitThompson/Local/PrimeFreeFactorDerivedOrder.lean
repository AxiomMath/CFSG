module

public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Foundations.FiniteHomImageOrder
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.DerivedSubgroupCharacteristic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

variable {X : Type*} [Group X]

theorem map_mk'_eq_top_of_sup_eq_top {D J : Subgroup X} [D.Normal] (hX : D ⊔ J = ⊤) :
    J.map (QuotientGroup.mk' D) = ⊤ := by
  have h := congrArg (Subgroup.map (QuotientGroup.mk' D)) hX
  rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective D)] at h

theorem coe_mul_coe_eq_univ_iff_sup_eq_top {D J : Subgroup X} [D.Normal] :
    (D : Set X) * (J : Set X) = Set.univ ↔ D ⊔ J = ⊤ := by
  rw [← Subgroup.normal_mul D J, ← Subgroup.coe_top]
  exact ⟨fun h => SetLike.coe_injective h, fun h => by rw [h]⟩

theorem natCard_commutator_subgroup_eq [Finite X] (J : Subgroup X) :
    Nat.card (⁅J, J⁆ : Subgroup X) = Nat.card (commutator ↥J) := by
  rw [← Subgroup.map_subtype_commutator, Subgroup.card_subtype]

theorem natCard_commutator_dvd_mul [Finite X] {D J : Subgroup X} [D.Normal] (hX : D ⊔ J = ⊤) :
    Nat.card (commutator X) ∣ Nat.card (commutator ↥J) * Nat.card D := by
  set f : (commutator X) →* X ⧸ D := (QuotientGroup.mk' D).comp (commutator X).subtype with hf
  rw [← natCard_range_mul_natCard_ker f]
  refine Nat.mul_dvd_mul ?_ ?_
  · have hrange : f.range = ⁅J, J⁆.map (QuotientGroup.mk' D) := by
      rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, map_commutator_eq,
        Subgroup.map_commutator, map_mk'_eq_top_of_sup_eq_top hX,
        MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective D)]
    rw [hrange, ← natCard_commutator_subgroup_eq]
    exact Subgroup.card_map_dvd _ _
  · rw [← Subgroup.card_subtype (commutator X) f.ker]
    refine Subgroup.card_dvd_of_le ?_
    rintro x ⟨y, hy, rfl⟩
    exact (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hy)

theorem not_dvd_natCard_commutator [Finite X] {p : ℕ} (hp : p.Prime)
    {D J : Subgroup X} [D.Normal] (hX : D ⊔ J = ⊤)
    (hD : ¬ p ∣ Nat.card D) (hJ : ¬ p ∣ Nat.card (commutator ↥J)) :
    ¬ p ∣ Nat.card (commutator X) := fun h => by
  rcases (Nat.Prime.dvd_mul hp).1 (h.trans (natCard_commutator_dvd_mul hX)) with h | h
  · exact hJ h
  · exact hD h

theorem not_dvd_natCard_commutator_of_coe_mul_coe_eq_univ [Finite X] {p : ℕ} (hp : p.Prime)
    {D J : Subgroup X} [D.Normal] (hX : (D : Set X) * (J : Set X) = Set.univ)
    (hD : ¬ p ∣ Nat.card D) (hJ : ¬ p ∣ Nat.card (commutator ↥J)) :
    ¬ p ∣ Nat.card (commutator X) :=
  not_dvd_natCard_commutator hp (coe_mul_coe_eq_univ_iff_sup_eq_top.1 hX) hD hJ

theorem not_dvd_natCard_closure_of_sup_eq_top [Finite X] {p : ℕ} (hp : p.Prime)
    {D J : Subgroup X} [D.Normal] (hX : D ⊔ J = ⊤) (hD : ¬ p ∣ Nat.card D)
    (hJ : ¬ p ∣ Nat.card
      (Subgroup.closure {g : X | ∃ a ∈ J, ∃ b ∈ J, a⁻¹ * b⁻¹ * a * b = g})) :
    ¬ p ∣ Nat.card (Subgroup.closure {g : X | ∃ a b : X, a⁻¹ * b⁻¹ * a * b = g}) := by
  rw [closure_setOf_inv_mul_inv_mul_mul_eq_commutator]
  refine not_dvd_natCard_commutator hp hX hD ?_
  rwa [closure_setOf_inv_mul_inv_mul_mul, natCard_commutator_subgroup_eq] at hJ

theorem notMem_primeFactors_iff_not_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ∉ n.primeFactors ↔ ¬ p ∣ n := by
  simp [Nat.mem_primeFactors, hp, hn]

theorem notMem_primeFactors_natCard_commutator [Finite X] {p : ℕ} (hp : p.Prime)
    {D J : Subgroup X} [D.Normal] (hX : D ⊔ J = ⊤)
    (hD : p ∉ (Nat.card D).primeFactors)
    (hJ : p ∉ (Nat.card (commutator ↥J)).primeFactors) :
    p ∉ (Nat.card (commutator X)).primeFactors :=
  (notMem_primeFactors_iff_not_dvd hp Nat.card_pos.ne').2
    (not_dvd_natCard_commutator hp hX
      ((notMem_primeFactors_iff_not_dvd hp Nat.card_pos.ne').1 hD)
      ((notMem_primeFactors_iff_not_dvd hp Nat.card_pos.ne').1 hJ))

theorem isPiSubgroup_compl_singleton_iff {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (N : Subgroup Y) :
    IsPiSubgroup {q : ℕ | q.Prime ∧ q ≠ p} N ↔ p ∉ (Nat.card N).primeFactors := by
  rw [isPiSubgroup_iff]
  exact ⟨fun h hmem => (h p hmem).2 rfl,
    fun h q hq => ⟨Nat.prime_of_mem_primeFactors hq, fun hqp => h (hqp ▸ hq)⟩⟩

theorem isPiSubgroup_compl_singleton_commutator [Finite X] {p : ℕ} (hp : p.Prime)
    {D J : Subgroup X} [D.Normal] (hX : D ⊔ J = ⊤)
    (hD : IsPiSubgroup {q : ℕ | q.Prime ∧ q ≠ p} D)
    (hJ : IsPiSubgroup {q : ℕ | q.Prime ∧ q ≠ p} (commutator ↥J)) :
    IsPiSubgroup {q : ℕ | q.Prime ∧ q ≠ p} (commutator X) :=
  (isPiSubgroup_compl_singleton_iff _).2
    (notMem_primeFactors_natCard_commutator hp hX
      ((isPiSubgroup_compl_singleton_iff _).1 hD)
      ((isPiSubgroup_compl_singleton_iff _).1 hJ))

end

end CFSG.FeitThompson
