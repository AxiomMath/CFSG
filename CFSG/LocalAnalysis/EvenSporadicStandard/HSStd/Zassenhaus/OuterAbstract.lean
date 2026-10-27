module

public import CFSG.Open.Defs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Open
open scoped commutatorElement

theorem isQuasisimple_of_equiv_alt8 {A : Type*} [Group A]
    (e : A ≃* alternatingGroup (Fin 8)) : IsQuasisimple A := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hsA : IsSimpleGroup A := e.isSimpleGroup
  have hc : Subgroup.center (alternatingGroup (Fin 8)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  have hcA : Subgroup.center A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center A) with h | h
    · exact h
    · exfalso
      have hcomm : ∀ a b : A, a * b = b * a := fun a b =>
        (mem_center_iff.1 (h ▸ mem_top b) a)
      have : (⊤ : Subgroup (alternatingGroup (Fin 8))) ≤
          Subgroup.center (alternatingGroup (Fin 8)) := by
        intro x _
        rw [mem_center_iff]
        intro g
        apply e.symm.injective
        simpa using (hcomm (e.symm g) (e.symm x))
      rw [hc, top_le_iff] at this
      have hnt8 : Nontrivial (alternatingGroup (Fin 8)) := hs.toNontrivial
      exact bot_ne_top this
  have hnt : Nontrivial A := hsA.toNontrivial
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator A) with h | h
    · exfalso
      have htop : (⊤ : Subgroup A) ≤ Subgroup.centralizer ((⊤ : Subgroup A) : Set A) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact h
      rw [Subgroup.coe_top, Subgroup.centralizer_univ, hcA, top_le_iff] at htop
      exact bot_ne_top htop
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hcA).trans QuotientGroup.quotientBot).isSimpleGroup

variable {X : Type*} [Group X]

theorem mem_normalizer_of_map_le [Finite X] {A : Subgroup X} {x : X}
    (hle : A.map (MulAut.conj x).toMonoidHom ≤ A) : x ∈ normalizer (A : Set X) := by
  have hcard : Nat.card (A.map (MulAut.conj x).toMonoidHom) = Nat.card A :=
    Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj x).injective).symm.toEquiv
  have heq : A.map (MulAut.conj x).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  rw [mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : x * h * x⁻¹ ∈ A.map (MulAut.conj x).toMonoidHom := ⟨h, hh, by simp [MulAut.conj_apply]⟩
    rwa [heq] at this
  · intro hh
    rw [← heq] at hh
    obtain ⟨y, hy, hyh⟩ := hh
    have : y = h := by
      have h' : x * y * x⁻¹ = x * h * x⁻¹ := by simpa [MulAut.conj_apply] using hyh
      simpa using h'
    exact this ▸ hy

theorem commutator_eq_self_of_equiv_alt8 {A : Subgroup X}
    (e : ↥A ≃* alternatingGroup (Fin 8)) : ⁅A, A⁆ = A := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hq := isQuasisimple_of_equiv_alt8 e
  have hperf : commutator ↥A = ⊤ := hq.1
  have h2 : (commutator ↥A).map A.subtype = ⁅A, A⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← h2, hperf, Subgroup.map_top, Subgroup.range_subtype]

section Good

variable [Finite X] {A : Subgroup X} {τ : X}

structure GoodData (A : Subgroup X) (τ : X) : Prop where
  sq : τ * τ = 1
  ne : τ ≠ 1
  cent : τ ∈ centralizer (A : Set X)
  H1 : ∀ y : X, y * τ = τ * y → y ∈ normalizer (A : Set X)
  H2 : ∀ w w' : X, w * τ = τ * w → w' * τ = τ * w' → ⁅w, w'⁆ ∈ A
  H3 : ∀ y ∈ centralizer (A : Set X), y * τ = τ * y → y ∈ zpowers τ

end Good

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
