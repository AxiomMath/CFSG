module

public import CFSG.GH74.GLS.C3.Statements
public import CFSG.GH74.GLS.C3.Layer3.OrderStep
public import CFSG.GH74.GLS.C3.Layer3.Moore

public section

namespace CFSG.GH74.GLS.Layer3

@[expose] def S_prop121 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ n ∈ ({9, 10, 11} : Finset ℕ),
    IsApproxTo G (alternatingGroup (Fin n)) →
      ∃ G₀ : Subgroup G, Nonempty (G₀ ≃* alternatingGroup (Fin n))

@[expose] def S_mooreElements : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ n ∈ ({9, 10, 11} : Finset ℕ),
    IsApproxTo G (alternatingGroup (Fin n)) →
      ∃ x : ℕ → G, CFSG.Sporadic.SchreierLemmas.IsMooreFamily (n - 2) x ∧
        ∃ i ∈ Set.Icc 1 (n - 2), x i ≠ 1

theorem S_prop121_of_moore (h : S_mooreElements) : S_prop121 := by
  intro G _ _ hG n hn hA
  have hn5 : 5 ≤ n := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  obtain ⟨x, hx, hne⟩ := h G hG n hn hA
  exact exists_subgroup_alt_of_moore hn5 x hx hne

theorem s_layerIII_of (h : S_prop121) :
    ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ n ∈ ({9, 10, 11} : Finset ℕ),
      IsApproxTo G (alternatingGroup (Fin n)) → Nonempty (G ≃* alternatingGroup (Fin n)) := by
  intro G _ _ hG n hn hA
  have hn' : 9 ≤ n ∧ n ≤ 11 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  obtain ⟨G₀, ⟨e⟩⟩ := h G hG n hn hA
  exact nonempty_mulEquiv_of_subgroup_alt hn'.1 hn'.2 hA.1 G₀ e

end CFSG.GH74.GLS.Layer3
