module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitOrbit

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open CFSG.EvenSmallLie.OmegaEight.Stage2 Subgroup

@[expose] def classCertW (E : Enum) (reps good : List ℕ) (B : ℕ → List ℕ) (R Y : ℕ → ℕ) :
    Bool :=
  ((List.range E.keys.size).all fun i =>
    mulK (E.keys.getD i 0) (E.keys.getD i 0) != idK || E.keys.getD i 0 == idK ||
      (decide (8 ≤ (B i).length) && fixLB (E.keys.getD i 0) (B i)) ||
      (decide (R i < reps.length) && decide (Y i < E.keys.size) &&
        mulK (E.keys.getD (Y i) 0) (reps.getD (R i) 0) ==
          mulK (E.keys.getD i 0) (E.keys.getD (Y i) 0))) &&
    reps.all fun r => memK E.keys r && (!(candB E r) || good.contains r)

variable {gs : Array (ℕ × ℕ)} {E : Enum}

theorem cand_of_classCertW (hE : enumOK gs E = true) {reps good : List ℕ} {B : ℕ → List ℕ}
    {R Y : ℕ → ℕ} (h : classCertW E reps good B R Y = true) {s : GL12} (hs : s ∈ grpOf gs)
    (hc : IsCand (grpOf gs) s) :
    ∃ r ∈ good, ∃ rG : GL12, Rep r rG ∧ rG ∈ grpOf gs ∧ ∃ y ∈ grpOf gs, s = y * rG * y⁻¹ := by
  simp only [classCertW, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true', List.contains_iff_mem,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨i, hi, hri⟩ := Enum.exists_key hE hs
  obtain ⟨hs2, hs1, hfix, -⟩ := id hc
  rcases h1 i hi with ((h3 | h3) | ⟨h3, h4⟩) | ⟨⟨hR, hY⟩, h3⟩
  · exact absurd ((hri.mul hri).key_unique (by rw [hs2]; exact rep_one) (mulK_lt _ _) idK_lt) h3
  · rw [h3] at hri
    exact absurd (hri.unique rep_one) hs1
  · rw [← fixM_of_rep hri] at hfix
    have := (Nat.pow_le_pow_right (by norm_num) h3).trans (fixLB_sound h4)
    omega
  · set r := reps.getD (R i) 0 with hr_def
    have hr : r ∈ reps := by
      rw [hr_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hR, Option.getD_some]
      exact List.getElem_mem hR
    obtain ⟨hmem, hgood⟩ := h2 r hr
    obtain ⟨rG, hrGS, hrG⟩ := Enum.rep_of_memK hE hmem
    obtain ⟨y, hy, hry⟩ := Enum.exists_mem hE (Y i) hY
    have e : y * rG = s * y := by
      have h5 := hry.mul hrG
      rw [h3] at h5
      exact h5.unique (hri.mul hry)
    have hsy : s = y * rG * y⁻¹ := by
      calc s = s * y * y⁻¹ := by group
        _ = y * rG * y⁻¹ := by rw [← e]
    have hcr : IsCand (grpOf gs) rG := by
      have := (isCand_conj (S := grpOf gs) (le_normalizer (inv_mem hy)) (s := s)).2 hc
      have e2 : y⁻¹ * (y * rG * y⁻¹) * y⁻¹⁻¹ = rG := by group
      rwa [hsy, e2] at this
    have hcb := candB_of_isCand hE hrG hcr
    rcases hgood with hgood | hgood
    · exact absurd hcb (by rw [hgood]; decide)
    · exact ⟨r, hgood, rG, hrG, hrGS, y, hy, hsy⟩

theorem not_isCand_of_classCertW (hE : enumOK gs E = true) {reps good : List ℕ}
    {B : ℕ → List ℕ} {R Y : ℕ → ℕ} (h : classCertW E reps good B R Y = true)
    {ms : Array (ℕ × ℕ)} {EM : Enum}
    (hEM : enumOK ms EM = true) (hsz : EM.keys.size < 2 ^ 64) (hMS : grpOf ms ≤ grpOf gs)
    (hidx : (grpOf ms).relIndex (grpOf gs) = 2)
    (hgood : (good.all fun r => !(memK EM.keys r) && decide (r < 2 ^ 144)) = true) :
    ∀ s ∈ grpOf ms, ¬ IsCand (grpOf gs) s := by
  intro s hs hc
  obtain ⟨r, hr, rG, hrG, -, y, hy, hsy⟩ := cand_of_classCertW hE h (hMS hs) hc
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hgood
  have hrM : rG ∈ grpOf ms := by
    have := conj_mem_of_relIndex_two hMS hidx (inv_mem hy) hs
    have e2 : y⁻¹ * (y * rG * y⁻¹) * y⁻¹⁻¹ = rG := by group
    rwa [hsy, e2] at this
  have := Enum.memK_of_mem' hEM hsz hrM hrG (hgood r hr).2
  rw [(hgood r hr).1] at this
  exact Bool.false_ne_true this

end CFSG.EvenSmallLie.OmegaEight.N3Split
