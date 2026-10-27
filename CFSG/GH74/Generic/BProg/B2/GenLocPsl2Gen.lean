module

public import CFSG.Walter.PSL2Facts.OddMaximal
public import CFSG.Walter.Defs

public section

namespace CFSG.GH74.Generic.BProg.B2

open Subgroup CFSG.Walter CFSG.BenderSuzuki.MatrixGroups

namespace GenLocPsl2Gen

theorem mem_zpowers_two {X : Type*} [Group X] {u a : X} (hu : orderOf u = 2) (ha : a ∈ zpowers u) :
    a = 1 ∨ a = u := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
  have h2 : (orderOf u : ℤ) = 2 := by rw [hu]; rfl
  rw [← zpow_mod_orderOf, h2]
  have : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases this with h | h
  · rw [h]; exact Or.inl (zpow_zero u)
  · rw [h]; exact Or.inr (zpow_one u)

theorem centralizer_ne_of_center {X : Type*} [Group X] {u u' : X} (hu : orderOf u = 2)
    (hu' : orderOf u' = 2) (hne : u ≠ u')
    (hZ : (center (centralizer ({u} : Set X))).map (centralizer ({u} : Set X)).subtype = zpowers u) :
    centralizer ({u} : Set X) ≠ centralizer ({u'} : Set X) := by
  intro h
  have h1 : u' ∈ centralizer ({u} : Set X) := by
    rw [h]; exact mem_centralizer_singleton_iff.2 rfl
  have h2 : (⟨u', h1⟩ : centralizer ({u} : Set X)) ∈ center (centralizer ({u} : Set X)) := by
    rw [mem_center_iff]
    intro x
    have hx : (x : X) ∈ centralizer ({u'} : Set X) := h ▸ x.2
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hx)
  have h3 : u' ∈ zpowers u := by
    rw [← hZ]
    exact ⟨_, h2, rfl⟩
  rcases mem_zpowers_two hu h3 with h4 | h4
  · rw [h4, orderOf_one] at hu'
    omega
  · exact hne h4.symm

end GenLocPsl2Gen

theorem psl2_sup_centralizer_eq_top_mod_eight {F : Type} [Field F]
    [Finite F] {p f : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq : 11 ≤ p ^ f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {u u' : PSL2MatrixGroup F} (hu : orderOf u = 2)
    (hu' : orderOf u' = 2) (hne : u ≠ u') :
    centralizer ({u} : Set (PSL2MatrixGroup F)) ⊔ centralizer ({u'} : Set (PSL2MatrixGroup F)) =
      ⊤ := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hq; omega
    · exact h
  have hq7 : 7 ≤ p ^ f := by omega
  refine (psl2_centralizer_involution_isCoatom F hF hpodd hf hq h8 hu).sup_eq_top_of_ne
    (psl2_centralizer_involution_isCoatom F hF hpodd hf hq h8 hu') ?_
  exact GenLocPsl2Gen.centralizer_ne_of_center hu hu' hne
    (psl2_center_centralizer_involution F hF hpodd hf hq7 hu)

end CFSG.GH74.Generic.BProg.B2
