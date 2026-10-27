module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderShape
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderSwaps
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SwapGenerated

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

open Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (Wr OmegaE exists_omegaEquiv_Wr_of_swaps)

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def SwapType (E : Subgroup (Perm Ω)) : Prop :=
  (∀ i : Ω, Nat.card (orbit E i) ≤ 2) ∧ E = orbitStab E

theorem eq_or_eq_of_card_orbit_le_two {E : Subgroup (Perm Ω)} {a b : Ω}
    (hc : Nat.card (orbit E a) ≤ 2) (hb : b ∈ orbit E a) (hab : a ≠ b) {x : Ω}
    (hx : x ∈ orbit E a) : x = a ∨ x = b := by
  by_contra h
  push Not at h
  have hsub : ({a, b, x} : Set Ω) ⊆ orbit E a := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact mem_orbit_self _
    · exact hb
    · exact hx
  have hcard : ({a, b, x} : Set Ω).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair h.2.symm]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hab, h.1.symm⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard] at this
  have h2 : (orbit E a).ncard ≤ 2 := by
    rw [← Nat.card_coe_set_eq]; exact hc
  omega

theorem le_closure_swaps_of_swapType {E : Subgroup (Perm Ω)} (h : SwapType E) :
    E ≤ Subgroup.closure {t : Perm Ω | t ∈ E ∧ t.IsSwap} := by
  obtain ⟨hsmall, hE⟩ := h
  suffices H : ∀ n : ℕ, ∀ g : Perm Ω, g.support.card = n → g ∈ E →
      g ∈ Subgroup.closure {t : Perm Ω | t ∈ E ∧ t.IsSwap} from
    fun g hg => H _ g rfl hg
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hn hg
    by_cases hg1 : g = 1
    · rw [hg1]; exact one_mem _
    obtain ⟨a, ha⟩ : ∃ a, g a ≠ a := by
      by_contra hno
      push Not at hno
      exact hg1 (Equiv.ext hno)
    set b := g a with hb
    have hab : a ≠ b := fun h => ha h.symm
    have hbo : b ∈ orbit E a := ⟨⟨g, hg⟩, rfl⟩
    have hgb : g b = a := by
      have hmem : g b ∈ orbit E a := by
        have : g b ∈ orbit E b := ⟨⟨g, hg⟩, rfl⟩
        have h3 : orbit E b = orbit E a := orbit_eq_iff.2 hbo
        rwa [h3] at this
      rcases eq_or_eq_of_card_orbit_le_two (hsmall a) hbo hab hmem with h | h
      · exact h
      · exact absurd (g.injective (h.trans hb)) hab.symm
    have hsw : swap a b ∈ E := by
      rw [hE]
      intro i
      by_cases h1 : i = a
      · rw [h1, swap_apply_left]; exact hbo
      by_cases h2 : i = b
      · rw [h2, swap_apply_right]
        have h3 : orbit E b = orbit E a := orbit_eq_iff.2 hbo
        rw [h3]; exact mem_orbit_self _
      · rw [swap_apply_of_ne_of_ne h1 h2]; exact mem_orbit_self _
    have hswc : swap a b ∈ Subgroup.closure {t : Perm Ω | t ∈ E ∧ t.IsSwap} :=
      Subgroup.subset_closure ⟨hsw, a, b, hab, rfl⟩
    have hg' : swap a b * g ∈ E := E.mul_mem hsw hg
    have hlt : (swap a b * g).support.card < n := by
      rw [← hn]
      apply Finset.card_lt_card
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Equiv.Perm.mem_support] at hx ⊢
        intro hgx
        apply hx
        rw [Perm.mul_apply, hgx]
        have hxa : x ≠ a := fun h => by
          rw [h] at hgx; exact ha hgx
        have hxb : x ≠ b := fun h => by
          rw [h] at hgx
          exact hab (g.injective (hgx.trans hb)).symm
        exact swap_apply_of_ne_of_ne hxa hxb
      · intro hsub
        have := hsub (Equiv.Perm.mem_support.2 ha)
        rw [Equiv.Perm.mem_support, Perm.mul_apply, ← hb, swap_apply_right] at this
        exact this rfl
    have := ih _ hlt (swap a b * g) rfl hg'
    have hgeq : g = swap a b * (swap a b * g) := by
      rw [← mul_assoc, swap_mul_self, one_mul]
    rw [hgeq]
    exact Subgroup.mul_mem _ hswc this

theorem exists_omegaEquiv_Wr_of_swapType {P : Subgroup (Perm Ω)} (hP : IsPGroup 2 P) {ι : Type*}
    (E : ι → Subgroup (Perm Ω)) (hEP : ∀ i, E i ≤ P) (hE : ∀ i, SwapType (E i)) :
    ∃ (r s : ℕ) (e : Ω ≃ OmegaE r s),
      (⨆ i, E i).map e.permCongrHom.toMonoidHom = Wr r s := by
  have hA : ∀ i, ∃ T : Set (Perm Ω), (∀ t ∈ T, t.IsSwap) ∧ E i = Subgroup.closure T := fun i =>
    ⟨{t | t ∈ E i ∧ t.IsSwap}, fun t ht => ht.2,
      le_antisymm (le_closure_swaps_of_swapType (hE i))
        ((Subgroup.closure_le _).2 fun t ht => ht.1)⟩
  obtain ⟨T, hTs, -, hTP, hsup⟩ := iSup_eq_closure_disjoint_swaps hP E hEP hA
  have hWP : (⨆ i, E i) ≤ P := iSup_le hEP
  refine exists_omegaEquiv_Wr_of_swaps (hP.to_le hWP) ?_
  rw [hsup]
  exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, hTs t ht⟩

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender
