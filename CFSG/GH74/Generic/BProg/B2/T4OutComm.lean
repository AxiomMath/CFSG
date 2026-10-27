module

public import CFSG.GH74.Generic.BProg.B2.PumpupTable
public import CFSG.GH74.Generic.BProg.B2.T4OutCore

public section

namespace CFSG.GH74.Generic.BProg.B2.T4

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

section Elim

@[expose] def PuL4SD (H : Type) [Group H] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 3 < p ^ f ∧
    ((p ^ f % 4 = 3 ∧ LieModel H .PSL 4 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel H .PSU 4 p f))

@[expose] def PuL4W (H : Type) [Group H] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 3 < p ^ f ∧
    ((p ^ f % 8 = 5 ∧ LieModel H .PSL 4 p f) ∨ (p ^ f % 8 = 3 ∧ LieModel H .PSU 4 p f))

theorem puL4_cases {H : Type} [Group H] (h : PuL4 H) : PuL4SD H ∨ PuL4W H := by
  obtain ⟨p, f, hp, hp2, hf, h3, ⟨h8, hm⟩ | ⟨h8, hm⟩⟩ := h
  · have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
    have hcases : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 ∨ p ^ f % 8 = 7 := by omega
    rcases hcases with h | h | h
    · exact Or.inl ⟨p, f, hp, hp2, hf, h3, Or.inl ⟨by omega, hm⟩⟩
    · exact Or.inr ⟨p, f, hp, hp2, hf, h3, Or.inl ⟨h, hm⟩⟩
    · exact Or.inl ⟨p, f, hp, hp2, hf, h3, Or.inl ⟨by omega, hm⟩⟩
  · have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
    have hcases : p ^ f % 8 = 1 ∨ p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 := by omega
    rcases hcases with h | h | h
    · exact Or.inl ⟨p, f, hp, hp2, hf, h3, Or.inr ⟨by omega, hm⟩⟩
    · exact Or.inr ⟨p, f, hp, hp2, hf, h3, Or.inr ⟨h, hm⟩⟩
    · exact Or.inl ⟨p, f, hp, hp2, hf, h3, Or.inr ⟨by omega, hm⟩⟩

@[expose] def ShapeS3 {N : Type} [Group N] (L : Subgroup N) : Prop :=
  ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal, QShape3 (↥L ⧸ Z)

namespace T4OutComm

theorem conjNormal_mem_commutator {N : Type} [Group N] {H : Subgroup N} [H.Normal] {t : N}
    (ht : t ∈ commutator N) : (MulAut.conjNormal t : MulAut ↥H) ∈ commutator (MulAut ↥H) := by
  have h : (commutator N).map (MulAut.conjNormal : N →* MulAut ↥H) ≤ commutator (MulAut ↥H) := by
    change (⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆).map _ ≤
      ⁅(⊤ : Subgroup (MulAut ↥H)), (⊤ : Subgroup (MulAut ↥H))⁆
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact h ⟨t, ht, rfl⟩

end T4OutComm

theorem commutator_le_of_puL4SD {N : Type} [Group N] [Finite N] {H : Subgroup N} (hHn : H.Normal)
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) (hL : PuL4SD ↥H) :
    commutator N ≤ H := by
  have := hHn
  have key : ∀ α β : MulAut ↥H, α * β * α⁻¹ * β⁻¹ ∈
      (MulAut.conj : ↥H →* MulAut ↥H).range := by
    obtain ⟨p, f, hp, hp2, hf, h3, ⟨hq, hm⟩ | ⟨hq, hm⟩⟩ := hL
    · exact T4OutCore.commutator_inner_of_psl4 hq hm
    · exact T4OutCore.commutator_inner_of_psu4 hp2 hq hm
  intro t ht
  exact T4OutCore.mem_of_conjNormal_mem_inner hfaith
    (T4OutCore.mem_of_commutator_mem key (T4OutComm.conjNormal_mem_commutator ht))

theorem mem_of_commutator_puL5 {N : Type} [Group N] [Finite N] {H : Subgroup N} (hHn : H.Normal)
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) (hL : PuL5 ↥H) {t : N}
    (ht : t ∈ commutator N) (ht2 : orderOf t = 2) : t ∈ H := by
  have := hHn
  have hc := T4OutComm.conjNormal_mem_commutator (H := H) ht
  have ht2' : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2] at this
  have h2 : (MulAut.conjNormal t : MulAut ↥H) ^ 2 = 1 := by
    rw [← map_pow, ht2', map_one]
  apply T4OutCore.mem_of_conjNormal_mem_inner hfaith
  obtain ⟨p, f, hp, hp2, hf, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hL
  · exact T4OutCore.inner_of_involution_psl5 hm hc h2
  · exact T4OutCore.inner_of_involution_psu5 hm hc h2

end Elim

end CFSG.GH74.Generic.BProg.B2.T4
