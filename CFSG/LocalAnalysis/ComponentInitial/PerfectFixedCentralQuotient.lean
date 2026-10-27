module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_map_center_iff {E : Subgroup G} {x : G} :
    x ∈ (center E).map E.subtype ↔ x ∈ E ∧ ∀ e ∈ E, e * x = x * e := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun e he => congrArg Subtype.val (mem_center_iff.1 hy ⟨e, he⟩)⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.2 fun e => Subtype.ext (h e e.2), rfl⟩

@[expose] def fixedCentralQuotient (E : Subgroup G) (t : G) : Subgroup G where
  carrier := {e | e ∈ E ∧ e⁻¹ * (t⁻¹ * e * t) ∈ (center E).map E.subtype}
  one_mem' := ⟨E.one_mem, by
    simp only [inv_one, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _⟩
  mul_mem' := by
    rintro e f ⟨he, hze⟩ ⟨hf, hzf⟩
    refine ⟨E.mul_mem he hf, ?_⟩
    have hc : f * (e⁻¹ * (t⁻¹ * e * t)) = (e⁻¹ * (t⁻¹ * e * t)) * f :=
      (mem_map_center_iff.1 hze).2 f hf
    have key : (e * f)⁻¹ * (t⁻¹ * (e * f) * t) =
        (e⁻¹ * (t⁻¹ * e * t)) * (f⁻¹ * (t⁻¹ * f * t)) := by
      calc (e * f)⁻¹ * (t⁻¹ * (e * f) * t)
          = f⁻¹ * ((e⁻¹ * (t⁻¹ * e * t)) * f) * (f⁻¹ * (t⁻¹ * f * t)) := by group
        _ = f⁻¹ * (f * (e⁻¹ * (t⁻¹ * e * t))) * (f⁻¹ * (t⁻¹ * f * t)) := by rw [hc]
        _ = (e⁻¹ * (t⁻¹ * e * t)) * (f⁻¹ * (t⁻¹ * f * t)) := by group
    rw [key]
    exact mul_mem hze hzf
  inv_mem' := by
    rintro e ⟨he, hze⟩
    refine ⟨E.inv_mem he, ?_⟩
    have hc : Commute e (e⁻¹ * (t⁻¹ * e * t)) := (mem_map_center_iff.1 hze).2 e he
    have key : e⁻¹⁻¹ * (t⁻¹ * e⁻¹ * t) = (e⁻¹ * (t⁻¹ * e * t))⁻¹ := by
      calc e⁻¹⁻¹ * (t⁻¹ * e⁻¹ * t) = e * (e⁻¹ * (t⁻¹ * e * t))⁻¹ * e⁻¹ := by group
        _ = (e⁻¹ * (t⁻¹ * e * t))⁻¹ * e * e⁻¹ := by rw [hc.inv_right.eq]
        _ = (e⁻¹ * (t⁻¹ * e * t))⁻¹ := by rw [mul_inv_cancel_right]
    rw [key]
    exact inv_mem hze

theorem coe_fixedCentralQuotient (E : Subgroup G) (t : G) :
    (fixedCentralQuotient E t : Set G) =
      {e | e ∈ E ∧ e⁻¹ * (t⁻¹ * e * t) ∈ (center E).map E.subtype} :=
  rfl

theorem unique_perfect_fixed_central_quotient_centralization {E A : Subgroup G} {t : G}
    (_ht : t ∈ normalizer (E : Set G))
    (hA : A ≤ normalizer (E : Set G) ⊓ centralizer ({t} : Set G)) (hperf : Group.IsPerfect A)
    (hAZ : ⁅A, (center E).map E.subtype⁆ = ⊥)
    (hAD : ⁅A, E ⊓ centralizer ({t} : Set G)⁆ = ⊥) :
    ∃ P : Subgroup G,
      (P : Set G) = {e | e ∈ E ∧ e⁻¹ * (t⁻¹ * e * t) ∈ (center E).map E.subtype} ∧
        ⁅A, P⁆ = ⊥ := by
  refine ⟨fixedCentralQuotient E t, rfl, ?_⟩
  have hAc : A ≤ centralizer ((center E).map E.subtype : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 hAZ
  have hle : ⁅A, fixedCentralQuotient E t⁆ ≤ E ⊓ centralizer ({t} : Set G) := by
    rw [commutator_le]
    intro a ha e he
    obtain ⟨heE, hz⟩ := he
    obtain ⟨haN, hat⟩ := mem_inf.1 (hA ha)
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact E.mul_mem ((mem_normalizer_iff.1 haN e).1 heE) (E.inv_mem heE)
    · rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.1 hw]
      obtain ⟨z, hzZ, het⟩ : ∃ z ∈ (center E).map E.subtype, t⁻¹ * e * t = e * z :=
        ⟨_, hz, (mul_inv_cancel_left e _).symm⟩
      have hta : t * a = a * t := mem_centralizer_iff.1 hat t rfl
      have hta' : t⁻¹ * a * t = a := by rw [mul_assoc, ← hta, inv_mul_cancel_left]
      have hza : Commute z a := mem_centralizer_iff.1 (hAc ha) z hzZ
      have hconj : t⁻¹ * ⁅a, e⁆ * t = ⁅a, e⁆ := by
        rw [commutatorElement_def]
        calc t⁻¹ * (a * e * a⁻¹ * e⁻¹) * t
            = (t⁻¹ * a * t) * (t⁻¹ * e * t) * (t⁻¹ * a * t)⁻¹ * (t⁻¹ * e * t)⁻¹ := by group
          _ = a * e * (z * a⁻¹) * z⁻¹ * e⁻¹ := by rw [hta', het]; group
          _ = a * e * (a⁻¹ * z) * z⁻¹ * e⁻¹ := by rw [hza.inv_right.eq]
          _ = a * e * a⁻¹ * e⁻¹ := by group
      calc t * ⁅a, e⁆ = t * (t⁻¹ * ⁅a, e⁆ * t) := by rw [hconj]
        _ = ⁅a, e⁆ * t := by group
  have hdouble : ⁅⁅A, fixedCentralQuotient E t⁆, A⁆ = ⊥ := by
    refine eq_bot_iff.2 ((commutator_mono hle le_rfl).trans ?_)
    rw [commutator_comm, hAD]
  exact perfect_double_commutator (isPerfect_iff.mp hperf) hdouble

end CFSG.LocalAnalysis.ComponentInitial
