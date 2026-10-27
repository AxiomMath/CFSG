module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterTransfer
public import CFSG.Sporadic.NativeFinite
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.ComponentClassification.OuterAutomorphisms

theorem OddCover.finite {s : TauCeti.SporadicName} (hs : s ≠ .M) {H : Type} [Group H]
    {M : Subgroup H} (h : OddCover s M) : Finite ↥M := by
  have hZ : Finite ↥(center ↥M) := Nat.finite_of_card_ne_zero h.2.1.pos.ne'
  obtain ⟨e⟩ := h.2.2
  have : Finite (Carrier s) := CFSG.Sporadic.finite_carrier_of_ne_M s hs
  have : Finite (↥M ⧸ center ↥M) := Finite.of_equiv _ e.symm.toEquiv
  exact Finite.of_subgroup_quotient (center ↥M)

theorem exists_noncommute_of_center_eq_bot {Y : Type} [Group Y] [Nontrivial Y]
    (hZ : center Y = ⊥) : ∃ a b : Y, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := exists_ne (1 : Y)
  have : x ∈ center Y := Subgroup.mem_center_iff.2 fun g => (hcon x g).symm
  rw [hZ, Subgroup.mem_bot] at this
  exact hx this

theorem outTwo_of_card_outer_dvd_two {Y : Type} [Group Y] (h : Nat.card (Outer Y) ∣ 2) :
    OutTwo Y := by
  classical
  have hne : Nat.card (Outer Y) ≠ 0 := fun h0 => by
    rw [h0] at h
    exact absurd (Nat.eq_zero_of_zero_dvd h) (by norm_num)
  have : Finite (Outer Y) := Nat.finite_of_card_ne_zero hne
  have hle : Nat.card (Outer Y) ≤ 2 := Nat.le_of_dvd (by norm_num) h
  have hinner : ∀ γ : MulAut Y, (γ : Outer Y) = 1 → ∃ l : Y, γ = MulAut.conj l := by
    intro γ hγ
    obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff γ).1 hγ
    exact ⟨l, hl.symm⟩
  intro α β
  by_cases ha : (α : Outer Y) = 1
  · exact Or.inl (hinner α ha)
  by_cases hb : (β : Outer Y) = 1
  · exact Or.inr (Or.inl (hinner β hb))
  refine Or.inr (Or.inr (hinner (α⁻¹ * β) ?_))
  have hab : (α : Outer Y) = β := by
    by_contra hab
    have : Fintype (Outer Y) := Fintype.ofFinite _
    have h3 : ({1, (α : Outer Y), (β : Outer Y)} : Finset (Outer Y)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h1 => ha h1.symm, fun h1 => hb h1.symm⟩
    have h4 := Finset.card_le_univ ({1, (α : Outer Y), (β : Outer Y)} : Finset (Outer Y))
    rw [h3, ← Nat.card_eq_fintype_card] at h4
    omega
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hab, inv_mul_cancel]

end CFSG.EvenSporadicStandard.Induction
