module

public import CFSG.Certificates.Kernel.Spor.ONLin
public import CFSG.Certificates.Kernel.Spor.TabWords

public section

namespace CFSG.KS.ONLin

open CFSG.KS.TW

variable {n : Nat} {key : Nat → Nat}

theorem lin_word {TT UU : Nat → Nat → Nat} {m : Nat}
    (hl : ∀ h < m, Lin n key (TT h) ∧ Lin n key (UU h)) :
    ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) →
      Lin n key fun x => w.foldr (fun z y => GZ TT UU z y) x
  | [], _ => Lin.id
  | l :: w, hw => by
    have ih := lin_word hl w fun z hz => hw z (List.mem_cons_of_mem l hz)
    obtain ⟨h0, hm⟩ := hw l List.mem_cons_self
    simp only [List.foldr_cons]
    unfold GZ
    by_cases hp : 0 < l
    · simp only [hp, ↓reduceIte]
      exact Lin.comp (hl _ (by omega)).1 ih
    · simp only [hp, ↓reduceIte]
      exact Lin.comp (hl _ (by omega)).2 ih

theorem lin_strong {P : Nat → Nat} (hS : Spans n key P) {TT UU : Nat → Nat → Nat}
    {words : Array (List Int)} {nT : Nat} (h0 : Lin n key (TT 0)) (h1 : Lin n key (TT 1))
    (hperm : ∀ x < n, ∀ h < nT, TT h x < n ∧ UU h x < n ∧ UU h (TT h x) = x)
    (hw : ∀ j < nT, 2 ≤ j → (∀ l ∈ words[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      ∀ x < n, TT j x = words[j]!.foldr (fun z y => GZ TT UU z y) x) :
    ∀ h < nT, Lin n key (TT h) ∧ Lin n key (UU h) := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro hh
    have hT : Lin n key (TT h) := by
      rcases Nat.lt_or_ge h 2 with a | a
      · interval_cases h
        · exact h0
        · exact h1
      · obtain ⟨hlet, htr⟩ := hw h hh a
        exact (lin_word (m := h) (fun k hk => ih k hk (by omega)) _ hlet).congr
          fun x hx => (htr x hx).symm
    exact ⟨hT, Lin.inv hS hT fun x hx => ⟨(hperm x hx h hh).2.1, (hperm x hx h hh).2.2⟩⟩

end CFSG.KS.ONLin

end
