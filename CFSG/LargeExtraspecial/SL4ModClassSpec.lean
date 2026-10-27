module

public import CFSG.LargeExtraspecial.SL4ModClassCheck
public import CFSG.LargeExtraspecial.SL4ModSpinSpec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Module Native CFSG.Sporadic.SmallF2.Native Matrix

@[expose] def refMat (d : ℕ) (rows : Array ℕ) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  Matrix.of fun m k => if (rows[k.val]!).testBit m.val then 1 else 0

@[expose] def IsIrredTau (taus : Array (Array ℕ)) (X : Submodule (ZMod 2) (Fin 105 → ZMod 2))
    (d : ℕ) : Prop :=
  IsTauInv taus X ∧ finrank (ZMod 2) X = d ∧
    ∀ Y : Submodule (ZMod 2) (Fin 105 → ZMod 2), IsTauInv taus Y → Y ≤ X → Y ≠ ⊥ → X ≤ Y

theorem forall_of_closedC {taus : Array (Array ℕ)} {B coef : Array ℕ}
    (h : closedC taus B coef = true) :
    ∀ t < B.size, ∀ s < 6, xorSel coef[6 * t + s]! B = actV taus[s]! B[t]! := by
  intro t ht s hs
  rw [closedC, List.all_eq_true] at h
  have h1 := h t (List.mem_range.mpr ht)
  rw [List.all_eq_true] at h1
  exact beq_iff_eq.mp (h1 s (List.mem_range.mpr hs))

theorem forall_of_refOK {taus : Array (Array ℕ)} {L : Array ℕ} {rows : Array (Array ℕ)}
    (h : refOK taus L rows = true) :
    rows.size = 6 ∧ (∀ s < 6, (rows[s]!).size = L.size) ∧
      ∀ s < 6, ∀ k < L.size, xorSel ((rows[s]!)[k]!) L = actV taus[s]! L[k]! := by
  rw [refOK, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, fun s hs => ?_, fun s hs k hk => ?_⟩
  · have h1 := (List.all_eq_true.mp h.2) s (List.mem_range.mpr hs)
    rw [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.1
  · have h1 := (List.all_eq_true.mp h.2) s (List.mem_range.mpr hs)
    rw [Bool.and_eq_true] at h1
    have h2 := (List.all_eq_true.mp h1.2) k (List.mem_range.mpr hk)
    exact beq_iff_eq.mp h2

theorem isTauInv_spanB_of_forall {taus : Array (Array ℕ)} {B : Array ℕ}
    (h : ∀ t < B.size, ∀ s < 6, ∃ mask, xorSel mask B = actV taus[s]! B[t]!) :
    IsTauInv taus (spanB B) := by
  intro s hs F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨i, rfl⟩ := hF
    obtain ⟨mask, hmask⟩ := h i.val i.isLt s hs
    have hmem := xorSel_mem (X := spanB B) mask
      (fun j hj => Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    rwa [hmask, vec_actV] at hmem
  | zero => exact (spanB B).zero_mem
  | add F G _ _ hF hG => exact (spanB B).add_mem hF hG
  | smul c F _ hF => exact (spanB B).smul_mem c hF

theorem kind_cases {d : ℕ} {refs : Array (Array (Array ℕ))} {taus : Array (Array ℕ)} {m : ℕ}
    {c : ClassCert} (hc : validClass d refs taus m c = true) :
    c.kind = 0 ∨ c.kind = 1 ∨ c.kind = 2 := by
  rw [validClass, Bool.and_eq_true] at hc
  have h := hc.2
  by_cases h0 : c.kind = 0
  · exact Or.inl h0
  by_cases h1 : c.kind = 1
  · exact Or.inr (Or.inl h1)
  by_cases h2 : c.kind = 2
  · exact Or.inr (Or.inr h2)
  exfalso
  simp only [beq_iff_eq, h0, h1, h2, if_false] at h
  exact absurd h (by decide)

end CFSG.LargeExtraspecial.SL4Mod
