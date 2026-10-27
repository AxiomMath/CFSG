module

public import Certificates.Data.Kernel.FF81P51Wit

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.P51

def CfgImp (c : CfgD) : Prop := C1D c → C3D c → C4D c 2 → C4D c 4 → GoodD c

section

variable (hnz : ∀ x : V4, x ≠ V4.zero → x ∈ nonzeroD)
include hnz

theorem mem_nonzeroD_of_memOmD {c : CfgD} {x : V4} (h : memOmD c x = true) : x ∈ nonzeroD := by
  unfold memOmD at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact hnz x h.1

theorem c4aD_of_c4aB {c : CfgD} {k : ℕ} (h : c4aB c k = true) : C4aD c k := by
  intro w _ hw
  have := List.all_eq_true.1 h w ‹_›
  simpa [hw] using this

theorem not_c4D_of {c : CfgD} {k : ℕ} {w w' : V4} (ha : c4aB c k = true)
    (hb : c4bFail c k w w' = true) : ¬C4D c k := by
  intro h4
  unfold c4bFail at hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hb
  obtain ⟨⟨hw, hw'⟩, hne⟩ := hb
  exact hne (h4 (c4aD_of_c4aB hnz ha) w (mem_nonzeroD_of_memOmD hnz hw) hw w'
    (mem_nonzeroD_of_memOmD hnz hw') hw')

theorem fwitOK_sound (c : CfgD) (t : FWit) (h : fwitOK c t = true) : CfgImp c := by
  intro h1 h3 h42 h44
  cases t with
  | c1 w w' =>
    simp only [fwitOK, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at h
    obtain ⟨⟨hw, hw'⟩, hn⟩ := h
    have := h1 w (mem_nonzeroD_of_memOmD hnz hw) hw w' (mem_nonzeroD_of_memOmD hnz hw') hw'
    rcases hn with hn | hn
    · rw [this.1] at hn
      exact absurd hn (by decide)
    · exact absurd this.2 hn
  | c3 =>
    obtain ⟨v, hv, hm, h0⟩ := h3
    have := List.all_eq_true.1 h v hv
    simp [hm, h0] at this
  | c4two w w' =>
    simp only [fwitOK, Bool.and_eq_true] at h
    exact absurd h42 (not_c4D_of hnz h.1 h.2)
  | c4four w w' =>
    simp only [fwitOK, Bool.and_eq_true] at h
    exact absurd h44 (not_c4D_of hnz h.1 h.2)
  | triv =>
    simp only [fwitOK, decide_eq_true_eq] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  | w a b =>
    simp only [fwitOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hp, ha⟩, hb⟩, hm⟩ := h
    have hW : WD c := ⟨a, mem_nonzeroD_of_memOmD hnz ha, ha, b, mem_nonzeroD_of_memOmD hnz hb, hb, hm⟩
    rcases hp with hp | hp
    · exact Or.inr (Or.inl ⟨hp, hW⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hp, hW⟩))

theorem fwitsOK_sound : ∀ (cs : List CfgD) (ws : List FWit), fwitsOK cs ws = true →
    ∀ c ∈ cs, CfgImp c
  | [], _, _, c, hc => absurd hc List.not_mem_nil
  | c' :: cs, w :: ws, h, c, hc => by
    simp only [fwitsOK, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact fwitOK_sound hnz c w h.1
    · exact fwitsOK_sound cs ws h.2 c hc
  | _ :: _, [], h, _, _ => by simp [fwitsOK] at h

theorem classify_of_fwitsOK (h : fwitsOK cfgsD fwitsD = true) :
    ([false, true].all fun m₁ => [false, true].all fun m₂ => [false, true].all fun m₄ =>
      [false, true].all fun m₅ => [false, true].all fun m₆ => (optLD 1 m₁).all fun p₁ =>
      (optLD 2 m₂).all fun p₂ => (optLD 4 m₄).all fun p₄ => (optLD 5 m₅).all fun p₅ =>
      (optLD 6 m₆).all fun p₆ =>
      decide (C1D (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) →
        C3D (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) →
        C4D (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) 2 →
        C4D (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) 4 →
        GoodD (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆))) = true := by
  have hall := fwitsOK_sound hnz cfgsD fwitsD h
  simp only [cfgsD, List.mem_flatMap, List.mem_map] at hall
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro m₁ _ m₂ _ m₄ _ m₅ _ m₆ _ p₁ hp₁ p₂ hp₂ p₄ hp₄ p₅ hp₅ p₆ hp₆
  exact hall _ ⟨m₁, by simp, m₂, by simp, m₄, by simp, m₅, by simp, m₆, by simp, p₁, hp₁, p₂, hp₂,
    p₄, hp₄, p₅, hp₅, p₆, hp₆, rfl⟩

end

theorem ofCols_toV (a b c d : V4) :
    ofCols ![a.toV, b.toV, c.toV, d.toV] = (ofColsD a b c d).toM := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem H0L_cols_of (hH : H0L = H0D.map M16.toM) (hE : E0L = E0D.map V4.toV)
    (hS : SU = SUD.map V4.toV)
    (hD : ∀ c₀ ∈ E0D, ∀ c₁ ∈ SUD, ∀ c₂ ∈ SUD, ∀ c₃ ∈ SUD,
      c₁ = c₂ ∨ c₁ = c₂.neg ∨ c₁ = c₃ ∨ c₁ = c₃.neg ∨ c₂ = c₃ ∨ c₂ = c₃.neg ∨
        ofColsD c₀ c₁ c₂ c₃ ∈ H0D) :
    ∀ c₀ ∈ E0L, ∀ c₁ ∈ SU, ∀ c₂ ∈ SU, ∀ c₃ ∈ SU,
      ofCols ![c₀, c₁, c₂, c₃] ∈ H0L ∨ c₁ = c₂ ∨ c₁ = -c₂ ∨ c₁ = c₃ ∨ c₁ = -c₃ ∨ c₂ = c₃ ∨
        c₂ = -c₃ := by
  intro c₀ h₀ c₁ h₁ c₂ h₂ c₃ h₃
  rw [hE] at h₀
  rw [hS] at h₁ h₂ h₃
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h₀
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h₁
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h₂
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h₃
  rw [ofCols_toV, hH, ← V4.toV_neg, ← V4.toV_neg]
  rcases hD a ha b hb c hc d hd with h | h | h | h | h | h | h
  rotate_left 6
  · exact Or.inl (List.mem_map_of_mem h)
  all_goals subst h
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

end CFSG.RankThree.PartTwo.Sec21.FF81.P51
