module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootData

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal CFSG.ComponentClassification.RestrictedStd.Spor

section Nontrivial

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (e : L ≃* alternatingGroup (Fin n))

theorem exists_ne_one_of_card_ge_three {S : Finset (Fin n)} (hS : 3 ≤ S.card) :
    ∃ r ∈ corr (X := G) e (altSub S), r ≠ 1 := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (by omega : 2 < S.card)
  have hmem := cyc3_mem_altSub ha hb hc hab hbc hac
  have hA : cyc3 a b c ∈ alternatingGroup (Fin n) := altSub_le_alternatingGroup S hmem
  refine ⟨((e.symm ⟨cyc3 a b c, hA⟩ : L) : G), mem_corr_of_mem (by simpa using hmem), ?_⟩
  intro h1
  have h2 : e.symm ⟨cyc3 a b c, hA⟩ = 1 := Subtype.ext h1
  have h3 : (⟨cyc3 a b c, hA⟩ : alternatingGroup (Fin n)) = 1 := by
    simpa using congrArg e h2
  have h4 : cyc3 a b c = 1 := congrArg Subtype.val h3
  have := congrArg (fun f : Equiv.Perm (Fin n) => f a) h4
  simp only [cyc3_apply_left hab hac, Equiv.Perm.coe_one, id_eq] at this
  exact hab this.symm

end Nontrivial

section S1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem rootData_of_card_three_or_four (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (e : L ≃* alternatingGroup (Fin n)) {S : Finset (Fin n)} (hS : S.card = 3 ∨ S.card = 4)
    (hSc : 5 ≤ n - S.card) :
    RootData L z (rootGroup e S) (corr (X := G) e (altSub Sᶜ)) (n - S.card) := by
  rcases hS with hS | hS
  · exact rootData_of_card_three h d hQ2 e hS hSc
  · exact rootData_of_card_ge_four h d hQ2 e (by omega) hSc

theorem zstar_or_wreath (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (e : L ≃* alternatingGroup (Fin n))
    {S : Finset (Fin n)} (hS : S.card = 3 ∨ S.card = 4) (hm : 9 ≤ n - S.card) :
    IsZStar (rootGroup e S) z ∨
      ∃ ht : z ∈ centralizer (rootGroup (G := G) e S : Set G),
        WreathOutcome (QuotientGroup.mk
          (⟨z, ht⟩ : ↥(centralizer (rootGroup (G := G) e S : Set G))) : Sec G (rootGroup e S))
          (secImage (rootGroup e S) (corr (X := G) e (altSub Sᶜ))) (n - S.card) := by
  have hRD := rootData_of_card_three_or_four h d hQ2 e hS (by omega)
  rcases zstar_or_wreath_of_rootData hlookup hHN hFour h d hQ2 hE hRD hm
    (exists_ne_one_of_card_ge_three e (by omega)) with h1 | h2
  · exact Or.inl h1
  · exact Or.inr ⟨hRD.hz, h2⟩

theorem zstar_or_fusion (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (e : L ≃* alternatingGroup (Fin n)) {k : ℕ}
    (hk : 3 ≤ k) (hk' : k ≤ 4) (hm : 9 ≤ n - k) (S : Finset (Fin n)) (hS : S.card = k) :
    IsZStar (rootGroup e S) z ∨
      ∀ b ∈ L, b ∈ centralizer (rootGroup e S : Set G) → orderOf b = 2 →
        ∃ h' ∈ centralizer (rootGroup e S : Set G), h' * z * h'⁻¹ = z * b := by
  have hS' : S.card = 3 ∨ S.card = 4 := by omega
  have hm' : 9 ≤ n - S.card := by rw [hS]; exact hm
  rcases zstar_or_wreath hlookup hHN hFour h d hQ2 hE e hS' hm' with h1 | ⟨ht, hW⟩
  · exact Or.inl h1
  · right
    have hRD := rootData_of_card_three_or_four h d hQ2 e hS' (by omega)
    intro b hbL hbC hb2
    exact wreath_fusion_of_rootData h d hRD (by omega) hW hbL hbC hb2

end S1
end CFSG.OddStandard.AltStdSec
