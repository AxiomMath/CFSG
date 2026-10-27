module

public import Certificates.Data.Kernel.FiveStdKTree
public import CFSG.Certificates.Kernel.FiveStdKSound
public import CFSG.GH74.GLS.LU.Local.FiveStdDict

public section

namespace CFSG.KC.FiveStdK

open CFSG.GH74.GLS.LU.Local.FiveStd

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem ifB_true {c t e : Bool} (h : ifB c t e = true) : (c = true → t = true) ∧ (c = false → e = true) := by
  revert h
  cases c <;> cases t <;> cases e <;> decide

theorem blt_iff (a b : Nat) : Nat.blt a b = true ↔ a < b := by
  rw [Nat.blt_eq]

theorem tPt_spec {T G nG N i : Nat} (h : tPt T G nG N i = true) :
    (i + 1 < N → rCode (f64 T i) < rCode (f64 T (i + 1))) ∧
    (rDep (f64 T i) = 0 → rCode (f64 T i) = oneK) ∧
    (rDep (f64 T i) ≠ 0 → rPar (f64 T i) < N ∧ rLet (f64 T i) < nG ∧
      rDep (f64 T (rPar (f64 T i))) < rDep (f64 T i) ∧
      mulK (rCode (f64 T (rPar (f64 T i)))) (f20 G (rLet (f64 T i))) = rCode (f64 T i)) := by
  unfold tPt at h
  rw [letB_eq, letB_eq] at h
  obtain ⟨h1, h2⟩ := andB_true h
  have h2' := ifB_true h2
  refine ⟨fun hi => (blt_iff _ _).1 ((ifB_true h1).1 ((blt_iff _ _).2 hi)), fun hz => ?_, fun hz => ?_⟩
  · exact Nat.eq_of_beq_eq_true (h2'.1 (by rw [hz]; rfl))
  · have hb : Nat.beq (rDep (f64 T i)) 0 = false := by
      cases hb : Nat.beq (rDep (f64 T i)) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hz
    have h3 := h2'.2 hb
    rw [letB_eq, letB_eq] at h3
    obtain ⟨ha, h4⟩ := andB_true h3
    obtain ⟨hl, h5⟩ := andB_true h4
    obtain ⟨hd, hm⟩ := andB_true h5
    exact ⟨(blt_iff _ _).1 ha, (blt_iff _ _).1 hl, (blt_iff _ _).1 hd, Nat.eq_of_beq_eq_true hm⟩

variable {Gp : Type} [Group Gp]

theorem tree_sound {ι : E → Gp} (hM : Model ι) {T G nG N : Nat} (gE : Nat → E)
    (hg : ∀ l < nG, validE (gE l) = true ∧ codeE (gE l) = f20 G l)
    (h : ∀ i < N, tPt T G nG N i = true) :
    (∀ i < N, ∃ x, validE x = true ∧ codeE x = rCode (f64 T i) ∧
      ι x ∈ Subgroup.closure {g | ∃ l < nG, ι (gE l) = g}) ∧
    (∀ i j, i < j → j < N → rCode (f64 T i) < rCode (f64 T j)) := by
  have hpt := fun i hi => tPt_spec (h i hi)
  refine ⟨fun i hi => ?_, fun i j hij hj => ?_⟩
  · suffices H : ∀ n, ∀ i < N, rDep (f64 T i) = n → ∃ x, validE x = true ∧
        codeE x = rCode (f64 T i) ∧ ι x ∈ Subgroup.closure {g | ∃ l < nG, ι (gE l) = g} from
      H _ i hi rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi hn
      by_cases hz : rDep (f64 T i) = 0
      · refine ⟨oneE, hM.valid_one, ?_, ?_⟩
        · rw [codeE_oneE, (hpt i hi).2.1 hz]
        · rw [hM.map_one]
          exact Subgroup.one_mem _
      · obtain ⟨hp, hl, hd, hm⟩ := (hpt i hi).2.2 hz
        obtain ⟨x, hx, hxc, hxm⟩ := ih _ (hn ▸ hd) _ hp rfl
        obtain ⟨hgv, hgc⟩ := hg _ hl
        refine ⟨mulE x (gE (rLet (f64 T i))), hM.valid_mul _ _ hx hgv, ?_, ?_⟩
        · rw [codeE_mulE, hxc, hgc, hm]
        · rw [hM.map_mul _ _ hx hgv]
          exact Subgroup.mul_mem _ hxm (Subgroup.subset_closure ⟨_, hl, rfl⟩)
  · induction j with
    | zero => omega
    | succ j ih =>
      have hs := (hpt j (by omega)).1 hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact (ih h' (by omega)).trans hs
      · exact hs

end CFSG.KC.FiveStdK

end
