module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux11
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_two_of_le {E F : Subgroup G} (hFE : F ≤ E) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem exists_isUGroup_of_two_le_pRank_centerOf {T : Subgroup G}
    (h2 : 2 ≤ pRank 2 (centerOf T)) : ∃ U : Subgroup G, IsUGroup 2 T U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup G, E ≤ centerOf T ∧ IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E, -, -, hk⟩
    have h1 : 2 ^ k ≤ Nat.card G := hk ▸ Subgroup.card_le_card_group E
    exact le_trans (Nat.lt_two_pow_self).le h1
  have hne : {k : ℕ | ∃ E : Subgroup G, E ≤ centerOf T ∧ IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : pRank 2 (centerOf T) = 0 := by
      unfold pRank
      rw [hne]
      simp
    omega
  obtain ⟨E, hEC, hE, hEcard⟩ := Nat.sSup_mem hne hbdd
  have hk2 : 2 ≤ sSup {k : ℕ | ∃ E : Subgroup G, E ≤ centerOf T ∧ IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := h2
  have hdvd : 2 ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow 2 hk2
  obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2 hdvd
  set U : Subgroup G := K.map E.subtype with hU_def
  have hUE : U ≤ E := by
    rintro x ⟨e, -, rfl⟩
    exact e.2
  have hUcard : Nat.card U = 2 ^ 2 := by
    rw [hU_def, Subgroup.card_map_of_injective (f := E.subtype) Subtype.val_injective]
    exact hKcard
  have hEU : IsElemAbelian 2 U := isElemAbelian_two_of_le hUE hE
  have hUC : U ≤ centerOf T := hUE.trans hEC
  have hUT : U ≤ T := fun u hu => (mem_centerOf_iff.mp (hUC hu)).1
  have hfix : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ = u := fun g hg u hu => by
    rw [(mem_centerOf_iff.mp (hUC hu)).2 g hg, mul_inv_cancel_right]
  have hN : T ≤ Subgroup.normalizer (U : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hfix g hg h hh]
      exact hh
    · intro hx
      have e := hfix g⁻¹ (inv_mem hg) _ hx
      have e2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rw [e2] at e
      rw [e]
      exact hx
  exact ⟨U, hUT, hN, ⟨hEU, hUcard⟩, fun _ => hUC⟩

end CFSG.HardMathSupport.Solomon.Proving

end
