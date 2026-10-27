module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Block
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.QuasithinUnique.DoubleA3

variable {G : Type} [Group G] [Finite G]

theorem list_length_le_four {U : Subgroup G} (hU : Nat.card U = 4) (l : List G) (hl : l.Nodup)
    (hmem : ∀ x ∈ l, x ∈ U) : l.length ≤ 4 := by
  classical
  have h1 : l.toFinset.card = l.length := List.toFinset_card_of_nodup hl
  have h2 : (↑l.toFinset : Set G) ⊆ (U : Set G) := fun x hx => hmem x (by simpa using hx)
  have h3 : (↑l.toFinset : Set G).ncard ≤ (U : Set G).ncard := Set.ncard_le_ncard h2
  rw [Set.ncard_coe_finset] at h3
  have h4 : (U : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hU
  omega

theorem klein_conj_transitive {U : Subgroup G} (hcard : Nat.card U = 4) {c : G}
    (hc3 : c ^ 3 = 1) (hcN : c ∈ Subgroup.normalizer (U : Set G))
    (hcfp : ∀ u ∈ U, u ≠ 1 → c * u * c⁻¹ ≠ u) {a b : G} (haU : a ∈ U) (hbU : b ∈ U)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : ∃ n : ℕ, b = (c ^ n)⁻¹ * a * c ^ n := by
  have hmem : ∀ u ∈ U, c⁻¹ * u * c ∈ U := by
    intro u hu
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hcN)) u
    simpa using this.mp hu
  have hne1 : ∀ u ∈ U, u ≠ 1 → c⁻¹ * u * c ≠ 1 := by
    intro u hu hu1 h
    apply hu1
    have := congrArg (fun y => c * y * c⁻¹) h
    simpa [mul_assoc] using this
  have hfp : ∀ u ∈ U, u ≠ 1 → c⁻¹ * u * c ≠ u := by
    intro u hu hu1 h
    apply hcfp u hu hu1
    have := congrArg (fun y => c * y * c⁻¹) h
    simpa [mul_assoc] using this.symm
  have hc3' : c * c * c = 1 := by simpa [pow_succ] using hc3
  set a1 := c⁻¹ * a * c with ha1def
  set a2 := c⁻¹ * a1 * c with ha2def
  have ha1U : a1 ∈ U := hmem a haU
  have ha2U : a2 ∈ U := hmem a1 ha1U
  have ha1ne1 : a1 ≠ 1 := hne1 a haU ha1
  have ha2ne1 : a2 ≠ 1 := hne1 a1 ha1U ha1ne1
  have hne_a1 : a1 ≠ a := hfp a haU ha1
  have hne_a2 : a2 ≠ a1 := hfp a1 ha1U ha1ne1
  have hne_a2a : a2 ≠ a := by
    intro h
    apply hne_a1
    have e3 : c⁻¹ * a2 * c = a := by
      have : c⁻¹ * (c⁻¹ * (c⁻¹ * a * c) * c) * c = (c * c * c)⁻¹ * a * (c * c * c) := by group
      rw [hc3'] at this
      simpa [ha2def, ha1def] using this
    rw [h] at e3
    exact e3
  by_contra hcon
  have hcon' : ∀ n : ℕ, b ≠ (c ^ n)⁻¹ * a * c ^ n := fun n h => hcon ⟨n, h⟩
  have hbne_a : b ≠ a := by
    have := hcon' 0; simpa using this
  have hbne_a1 : b ≠ a1 := by
    have := hcon' 1; simpa [ha1def] using this
  have hbne_a2 : b ≠ a2 := by
    have := hcon' 2
    simpa [ha2def, ha1def, pow_two, mul_assoc] using this
  have hlist : ([1, a, a1, a2, b] : List G).Nodup := by
    simp [List.nodup_cons, ha1.symm, ha1ne1.symm, ha2ne1.symm, hb1.symm, hne_a1.symm,
      hne_a2a.symm, hbne_a.symm, hne_a2.symm, hbne_a1.symm, hbne_a2.symm]
  have hlen := list_length_le_four hcard _ hlist (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact haU
    · exact ha1U
    · exact ha2U
    · exact hbU)
  simp at hlen

theorem alt3_conj_transitive {L : Subgroup G} (hs : IsShort2 L) (ha : IsAltType L 3)
    {a b : G} (haU : a ∈ blockU L) (hbU : b ∈ blockU L) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ l ∈ L, b = l⁻¹ * a * l := by
  obtain ⟨-, hcard, -, -, -, -, c, hcL, hc3, hcN, hcfp, -⟩ := hs.alt3_structure ha
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  obtain ⟨n, hn⟩ := klein_conj_transitive hcard hc3' hcN hcfp haU hbU ha1 hb1
  exact ⟨c ^ n, pow_mem hcL n, hn⟩

end CFSG.QuasithinUnique.DoubleA3
