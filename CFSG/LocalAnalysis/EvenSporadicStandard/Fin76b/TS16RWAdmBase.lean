
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWCls
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAdmCheck

@[expose] public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

@[expose] def AdmPred (π : Equiv.Perm (Fin 128)) : Prop :=
  π * π = 1 ∧ (π ⟨32, by norm_num⟩ : ℕ) = 32 ∧ (π ⟨64, by norm_num⟩ : ℕ) = 85 ∧
    (∀ c : Fin 128, (c : ℕ) < 32 → (π c : ℕ) < 32) ∧
    (Finset.univ.filter fun c : Fin 128 => (c : ℕ) < 32 ∧ π c = c).card = 8 ∧
    ∃ c : Fin 128, (c : ℕ) < 32 ∧ (c : ℕ) ≠ 0 ∧ (c : ℕ) ≠ 21 ∧ mulC (c : ℕ) (c : ℕ) = 0 ∧
      π c = c

theorem evR_point {w : List (Array ℕ)} {g : Equiv.Perm (Fin 128)} (hw : RepW 128 w g) {c : ℕ}
    (hc : c < 128) : evR w c = (g ⟨c, hc⟩ : ℕ) :=
  hw ⟨c, hc⟩

section Adm

theorem card_filter_fin_range {n m : ℕ} (hm : m ≤ n) (P : Fin n → Prop) [DecidablePred P]
    (Q : ℕ → Bool) (h : ∀ c : Fin n, P c ↔ ((c : ℕ) < m ∧ Q c = true)) :
    (Finset.univ.filter P).card = ((List.range m).filter Q).length := by
  have key : (Finset.univ.filter P).card = ((Finset.range m).filter fun c => Q c = true).card := by
    refine Finset.card_bij (fun c _ => (c : ℕ)) ?_ ?_ ?_
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      simp only [Finset.mem_filter, Finset.mem_range]
      exact (h c).1 hc
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      refine ⟨⟨b, lt_of_lt_of_le hb.1 hm⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (h ⟨b, lt_of_lt_of_le hb.1 hm⟩).2 hb
  rw [key, lenFilter_range, Finset.card_filter]

theorem sqW_iff_one {w : List (Array ℕ)} {g : Equiv.Perm (Fin 128)} (hw : RepW 128 w g)
    (hg : g ∈ Pg) : sqW w = true ↔ g * g = 1 := by
  rw [sqW_iff hw]
  constructor
  · intro h
    exact baseFaithful_Pg (g * g) (Pg.mul_mem hg hg) fun y hy => by
      rw [Equiv.Perm.mul_apply]
      exact h y hy
  · intro h x _
    have := congrArg (fun π : Equiv.Perm (Fin 128) => π x) h
    simpa [Equiv.Perm.mul_apply] using this

theorem admW_iff {w : List (Array ℕ)} {g : Equiv.Perm (Fin 128)} (hw : RepW 128 w g)
    (hg : g ∈ Pg) : admW w = true ↔ AdmPred g := by
  have h2 : (evR w 32 == 32) = true ↔ (g ⟨32, by norm_num⟩ : ℕ) = 32 := by
    rw [beq_iff_eq, evR_point hw (by norm_num : (32 : ℕ) < 128)]
  have h3 : (evR w 64 == 85) = true ↔ (g ⟨64, by norm_num⟩ : ℕ) = 85 := by
    rw [beq_iff_eq, evR_point hw (by norm_num : (64 : ℕ) < 128)]
  have h4 : ((List.range 32).all fun c => decide (evR w c < 32)) = true ↔
      ∀ c : Fin 128, (c : ℕ) < 32 → (g c : ℕ) < 32 := by
    rw [List.all_eq_true]
    constructor
    · intro h c hc
      have h' := h c (List.mem_range.2 hc)
      simp only [decide_eq_true_eq] at h'
      rw [hw c] at h'
      exact h'
    · intro h c hc
      have hc' := List.mem_range.1 hc
      simp only [decide_eq_true_eq]
      rw [evR_point hw (by omega : c < 128)]
      exact h ⟨c, by omega⟩ hc'
  have hP5 : ∀ c : Fin 128, ((c : ℕ) < 32 ∧ g c = c) ↔
      ((c : ℕ) < 32 ∧ (evR w c == c) = true) := by
    intro c
    rw [beq_iff_eq, hw c, Fin.ext_iff]
  have h5 : (((List.range 32).filter fun c => evR w c == c).length == 8) = true ↔
      (Finset.univ.filter fun c : Fin 128 => (c : ℕ) < 32 ∧ g c = c).card = 8 := by
    rw [card_filter_fin_range (m := 32) (Q := fun c => evR w c == c) (by norm_num) _ hP5,
      beq_iff_eq]
  have h6 : ((List.range 32).any fun c => c != 0 && c != 21 && mulC c c == 0 && evR w c == c) =
      true ↔ ∃ c : Fin 128, (c : ℕ) < 32 ∧ (c : ℕ) ≠ 0 ∧ (c : ℕ) ≠ 21 ∧
        mulC (c : ℕ) (c : ℕ) = 0 ∧ g c = c := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨c, hc, hp⟩
      have hc' := List.mem_range.1 hc
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
      obtain ⟨⟨⟨h0, h21⟩, hm⟩, he⟩ := hp
      exact ⟨⟨c, by omega⟩, hc', h0, h21, hm,
        Fin.ext ((evR_point hw (by omega : c < 128)).symm.trans he)⟩
    · rintro ⟨c, hc, h0, h21, hm, hg'⟩
      refine ⟨(c : ℕ), List.mem_range.2 hc, ?_⟩
      have he : evR w (c : ℕ) = (c : ℕ) := (hw c).trans (congrArg Fin.val hg')
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      exact ⟨⟨⟨h0, h21⟩, hm⟩, he⟩
  unfold admW AdmPred
  simp only [Bool.and_eq_true]
  rw [sqW_iff_one hw hg, h2, h3, h4, h5, h6]
  simp only [and_assoc]

end Adm

end CFSG.EvenSporadicStandard.Fin76b.W16
