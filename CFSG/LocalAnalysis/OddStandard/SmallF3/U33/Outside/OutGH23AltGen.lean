module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.Permutation.SymmetricCoxeter

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.Permutation.SymmetricCoxeter
open CFSG.ComponentClassification.PresentationLocal

theorem gh23_alt_equiv_of_rels {n : ℕ} (hn : 3 ≤ n) {H : Type*} [Group H] [Finite H]
    (y : ℕ → H) (h3 : ∀ i, i < n - 2 → y i ^ 3 = 1)
    (h2 : ∀ i j, i < n - 2 → j < n - 2 → i ≠ j → (y i * y j) ^ 2 = 1)
    (hgen : Subgroup.closure {h | ∃ i, i < n - 2 ∧ y i = h} = ⊤)
    (hcard : Nat.card H = n.factorial / 2) :
    Nonempty (H ≃* alternatingGroup (Fin n)) := by
  let x : CarmichaelIndex n → H := fun k => y ((k.1 : ℕ) - 2)
  have hxle : ∀ k : CarmichaelIndex n, (k.1 : ℕ) - 2 < n - 2 := by
    intro k
    have hk := k.1.isLt
    have hk2 := k.2
    omega
  have hx : ∀ k, x k ^ 3 = 1 := fun k => h3 _ (hxle k)
  have hxx : ∀ k l, k ≠ l → (x k * x l) ^ 2 = 1 := by
    intro k l hkl
    refine h2 _ _ (hxle k) (hxle l) ?_
    intro h
    exact hkl (Subtype.ext (Fin.ext (by omega)))
  obtain ⟨φ, hφ⟩ := exists_hom_carmichaelCycle hn x hx hxx
  have hrange : Set.range x = {h : H | ∃ i, i < n - 2 ∧ y i = h} := by
    ext h
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨(k.1 : ℕ) - 2, hxle k, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨⟨i + 2, by omega⟩, by simp⟩, by simp [x]⟩
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine (Subgroup.closure_le _).2 ?_
    intro h hh
    rw [← hrange] at hh
    obtain ⟨k, rfl⟩ := hh
    exact ⟨carmichaelCycle k, hφ k⟩
  have hcardA : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin]
  have hbij : Function.Bijective φ :=
    hsurj.bijective_of_nat_card_le (by rw [hcardA, hcard])
  exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

theorem gh23_sym_equiv_of_rels {n : ℕ} {H : Type*} [Group H] [Finite H] (y : ℕ → H)
    (hy : IsCoxeterA n y) (hgen : Subgroup.closure {h | ∃ i, i < n ∧ y i = h} = ⊤)
    (hcard : Nat.card H = (n + 1).factorial) :
    Nonempty (H ≃* Equiv.Perm (Fin (n + 1))) := by
  obtain ⟨ψ, hψ⟩ := exists_hom_perm n y hy
  have hrange : Set.range (fun i : Fin n => y i) = {h : H | ∃ i, i < n ∧ y i = h} := by
    ext h
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine (Subgroup.closure_le _).2 ?_
    intro h hh
    rw [← hrange] at hh
    obtain ⟨i, rfl⟩ := hh
    exact ⟨adjSwap n i, hψ i i.2⟩
  have hcardP : Nat.card (Equiv.Perm (Fin (n + 1))) = (n + 1).factorial := by
    rw [Nat.card_perm, Nat.card_fin]
  have hbij : Function.Bijective ψ :=
    hsurj.bijective_of_nat_card_le (by rw [hcardP, hcard])
  exact ⟨(MulEquiv.ofBijective ψ hbij).symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
