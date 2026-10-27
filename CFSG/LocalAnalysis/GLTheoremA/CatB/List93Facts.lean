module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

namespace List93

theorem catalogIs_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    {Q : TauCeti.CFSGIndex → Prop} (h : catalogIs S Q) : catalogIs T Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem catalogIs_mono {S : Type} [Group S] {P Q : TauCeti.CFSGIndex → Prop}
    (hPQ : ∀ i, P i → Q i) (h : catalogIs S P) : catalogIs S Q := by
  obtain ⟨i, hi, hf⟩ := h
  exact ⟨i, hPQ i hi, hf⟩

theorem isChevSimple_of_mulEquiv {r : ℕ} {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : IsChevSimple r S) : IsChevSimple r T :=
  h.imp (catalogIs_of_mulEquiv e) (catalogIs_of_mulEquiv e)

theorem card_mod_three_of_even {q : TauCeti.PrimePower} (h2 : q.p = 2) (he : Even q.exponent) :
    q.card % 3 = 1 := by
  obtain ⟨k, hk⟩ := he
  rw [TauCeti.PrimePower.card_def, h2, hk, ← two_mul, pow_mul]
  norm_num [Nat.pow_mod]

theorem card_mod_three_of_odd {q : TauCeti.PrimePower} (h2 : q.p = 2) (ho : Odd q.exponent) :
    q.card % 3 = 2 := by
  obtain ⟨k, hk⟩ := ho
  rw [TauCeti.PrimePower.card_def, h2, hk, pow_succ, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

@[expose] def l2Two : TauCeti.CFSGIndex → Prop :=
  onLie fun d => match d with | .A 1 q => q.p = 2 | _ => False

@[expose] def titsIdx : TauCeti.CFSGIndex → Prop :=
  onLie fun d => d = TauCeti.LieTypeIndex.tits

@[expose] def szIdx : TauCeti.CFSGIndex → Prop :=
  onLie fun d => d = TauCeti.LieTypeIndex.suzuki 2

@[expose] def l33Idx : TauCeti.CFSGIndex → Prop :=
  onLie fun d => match d with | .A 2 q => q.card = 3 | _ => False

@[expose] def NotChev2Idx (j : TauCeti.CFSGIndex) : Prop :=
  (∃ s : TauCeti.SporadicName, j = .sporadic s ∧ ∃ p : ℕ, CFSG.Yardstones.Md0ec50421ce4.k2Spor p s) ∨
    (∃ h : 5 ≤ 7, j = .alternating 7 h) ∨ (∃ h : 5 ≤ 9, j = .alternating 9 h) ∨ l33Idx j

structure I9List93Residual : Prop where
  chevOdd : ∀ (S : Type) [Group S] [Finite S] (q : ℕ), q.Prime → q ≠ 2 → q ≠ 3 →
    IsChevSimple q S → IsChevSimple 2 S → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian p E → Nat.card E < p ^ 3
  chev23 : ∀ (S : Type) [Group S] [Finite S], IsChevSimple 2 S → IsChevSimple 3 S →
    catalogIs S S9.isU4two ∨
      ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 3 E → Nat.card E < 3 ^ 3
  l2Two : ∀ (S : Type) [Group S] [Finite S], catalogIs S l2Two →
    ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 3 E → Nat.card E < 3 ^ 3
  tits : ∀ (S : Type) [Group S] [Finite S], catalogIs S titsIdx →
    (∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 3 E → Nat.card E < 3 ^ 3) ∧
      ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 5 E → Nat.card E < 5 ^ 3
  suzuki : ∀ (S : Type) [Group S] [Finite S], catalogIs S szIdx →
    ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 5 E → Nat.card E < 5 ^ 3
  notChev2 : ∀ (S : Type) [Group S] (j : TauCeti.CFSGIndex), NotChev2Idx j →
    Nonempty (S ≃* j.Group) → ¬ IsChevSimple 2 S

end List93

abbrev I9List93Residual : Prop := List93.I9List93Residual

end CFSG.LocalAnalysis.GLTheoremA

end
