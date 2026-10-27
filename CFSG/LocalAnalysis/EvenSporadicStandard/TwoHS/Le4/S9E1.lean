module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Sigma
public import Certificates.Certificate26751

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.HSMultiplier CFSG.LieType.Multipliers CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic

@[expose] def bet (j : ℕ) : HSCover := wordVal hsGens (betaWords.getD j [])

@[expose] def tL : HSCover := wordVal hsGens tWord

@[expose] def kapL (c : List ℕ) : HSCover :=
  bet 0 ^ c.getD 0 0 * bet 1 ^ c.getD 1 0 * tL ^ (c.getD 2 0 / 2) * bet 2 ^ c.getD 3 0

@[expose] def gamma1L : HSCover := wordVal hsGens gamma1Word

@[expose] def gamma2L : HSCover := wordVal hsGens gamma2Word

theorem betaWords_letters : ∀ w ∈ betaWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6 := by decide

theorem betaWords_getD_letters (j : ℕ) : ∀ l ∈ betaWords.getD j [], 1 ≤ l ∧ l ≤ 6 := by
  by_cases hj : j < betaWords.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact betaWords_letters _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro l hl
    simp at hl

theorem tWord_letters : ∀ l ∈ tWord, 1 ≤ l ∧ l ≤ 6 := by decide

theorem gamma1Word_letters : ∀ l ∈ gamma1Word, 1 ≤ l ∧ l ≤ 6 := by decide

theorem gamma2Word_letters : ∀ l ∈ gamma2Word, 1 ≤ l ∧ l ≤ 6 := by decide

section E1

theorem rep_bet (j : ℕ) : Rep 11200 (betaT j) (harRhoHom (bet j)) :=
  rep_rho_wordVal _ (betaWords_getD_letters j)

theorem rep_tL : Rep 11200 tT (harRhoHom tL) := rep_rho_wordVal _ tWord_letters

theorem rep_kapL (c : List ℕ) : Rep 11200 (kapT c) (harRhoHom (kapL c)) := by
  have hn : (11200 : ℕ) < 2 ^ 32 := by norm_num
  unfold kapT kapL
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
  exact Rep.compT (Rep.compT (Rep.compT (Rep.powT hn (rep_bet 0) _) (Rep.powT hn (rep_bet 1) _))
    (Rep.powT hn rep_tL _)) (Rep.powT hn (rep_bet 2) _)

theorem e1OK_true : e1OK = true ∧ realOK = true := Certificates.certificate26751

theorem e1_parts :
    (∀ j < 3, permOK 11200 (betaT j) = true ∧
      invOK 11200 (betaT j) (invT 11200 (betaT j)) = true) ∧
    (permOK 11200 tT = true ∧ invOK 11200 tT (invT 11200 tT) = true ∧ involOK 11200 tT = true) ∧
    (∀ g ∈ harYs, commTT 11200 tT g = true) ∧
    (∀ i < 3, ∀ j < 3, commTT 11200 (betaT i) (betaT j) = true) ∧
    (∀ j < 3, tblEq 11200 (powT 11200 4 (betaT j)) (idT 11200) = true) ∧
    (∀ a < 4, ∀ b < 4, ∀ c < 4, ∀ u < 2,
      (a = 0 ∧ b = 0 ∧ c = 0 ∧ u = 0) ∨ tblEq 11200 (e1T a b c u) (idT 11200) = false) := by
  have h := e1OK_true.1
  simp only [e1OK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, ⟨h2, h3, h4⟩, h5, h6, h7, ?_⟩
  intro a ha b hb c hc u hu
  have := h8 a ha b hb c hc u hu
  rcases this with h | h
  · left
    simp only [beq_iff_eq] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · exact Or.inr h

theorem s9E1_card_lt : (11200 : ℕ) < 2 ^ 32 := by norm_num

theorem HSCtx.tL_comm_gen (hΛ : HSCtx) (i : Fin 6) :
    tL * PresentedGroup.of i = PresentedGroup.of i * tL := by
  have h := e1_parts.2.2.1 (harY i) (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
  apply hΛ.rho_injective
  rw [map_mul, map_mul, harRhoHom_of]
  exact (commTT_iff rep_tL (rep_harY i).1).1 h

theorem HSCtx.tL_central (hΛ : HSCtx) (x : HSCover) : tL * x = x * tL := by
  have hx : x ∈ closure (Set.range (PresentedGroup.of : Fin 6 → HSCover)) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hΛ.tL_comm_gen i
  | one => simp
  | mul y z _ _ hy hz => rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]
  | inv y _ hy =>
    calc tL * y⁻¹ = y⁻¹ * (y * tL) * y⁻¹ := by group
      _ = y⁻¹ * (tL * y) * y⁻¹ := by rw [hy]
      _ = y⁻¹ * tL := by group

theorem tL_involution (hΛ : HSCtx) : tL * tL = 1 ∧ tL ≠ 1 := by
  have hord := orderOf_eq_two_of_involOK s9E1_card_lt rep_tL e1_parts.2.1.2.2
  have h2 : harRhoHom tL ^ 2 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  refine ⟨?_, ?_⟩
  · apply hΛ.rho_injective
    rw [map_mul, map_one, ← sq]
    exact h2
  · intro h1
    rw [h1, map_one, orderOf_one] at hord
    omega

theorem HSCtx.tL_mem_center (hΛ : HSCtx) : tL ∈ center HSCover :=
  Subgroup.mem_center_iff.2 fun x => (hΛ.tL_central x).symm

theorem HSCtx.eq_one_or_tL (hΛ : HSCtx) {z : HSCover} (hz : z ∈ center HSCover) :
    z = 1 ∨ z = tL := by
  obtain ⟨w, -, hw2⟩ := (Nat.card_eq_two_iff' (1 : center HSCover)).1 hΛ.card_center
  by_cases hz1 : z = 1
  · exact Or.inl hz1
  · right
    have h1 : (⟨z, hz⟩ : center HSCover) = w := hw2 _ (fun h => hz1 (congrArg Subtype.val h))
    have h2 : (⟨tL, hΛ.tL_mem_center⟩ : center HSCover) = w :=
      hw2 _ (fun h => (tL_involution hΛ).2 (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)

theorem HSCtx.bet_comm (hΛ : HSCtx) {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    bet i * bet j = bet j * bet i := by
  apply hΛ.rho_injective
  rw [map_mul, map_mul]
  exact (commTT_iff (rep_bet i) (rep_bet j)).1 (e1_parts.2.2.2.1 i hi j hj)

theorem HSCtx.bet_pow_four (hΛ : HSCtx) {j : ℕ} (hj : j < 3) : bet j ^ 4 = 1 := by
  apply hΛ.rho_injective
  rw [map_pow, map_one]
  exact (tblEq_idT_iff s9E1_card_lt (Rep.powT s9E1_card_lt (rep_bet j) 4)).1
    (e1_parts.2.2.2.2.1 j hj)

theorem bet_indep {a b c u : ℕ} (ha : a < 4) (hb : b < 4) (hc : c < 4)
    (hu : u < 2) (h : bet 0 ^ a * bet 1 ^ b * bet 2 ^ c * tL ^ u = 1) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ u = 0 := by
  rcases e1_parts.2.2.2.2.2 a ha b hb c hc u hu with h1 | h1
  · exact h1
  · exfalso
    have hrep : Rep 11200 (e1T a b c u)
        (harRhoHom (bet 0 ^ a * bet 1 ^ b * bet 2 ^ c * tL ^ u)) := by
      rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
      exact Rep.compT (Rep.compT (Rep.compT (Rep.powT s9E1_card_lt (rep_bet 0) _)
        (Rep.powT s9E1_card_lt (rep_bet 1) _)) (Rep.powT s9E1_card_lt (rep_bet 2) _))
        (Rep.powT s9E1_card_lt rep_tL _)
    have : tblEq 11200 (e1T a b c u) (idT 11200) = true :=
      (tblEq_idT_iff s9E1_card_lt hrep).2 (by rw [h, map_one])
    rw [this] at h1
    exact Bool.noConfusion h1

end E1

section Sig

@[expose] noncomputable def HSCtx.sigBet (hΛ : HSCtx) (b j : ℕ) : HSCover :=
  if b = 0 then bet j else hΛ.sigma (bet j)

theorem HSCtx.rep_sigBetaT (hΛ : HSCtx) (b j : ℕ) :
    Rep 11200 (sigBetaT b j) (harRhoHom (hΛ.sigBet b j)) := by
  unfold sigBetaT HSCtx.sigBet
  by_cases hb : b = 0
  · simp only [hb, ite_true]
    exact rep_bet j
  · simp only [hb, ite_false]
    have : hΛ.sigma (bet j) = wordVal hsGens (sigWord (betaWords.getD j [])) :=
      hΛ.sigma_wordVal _
    rw [this]
    exact rep_rho_wordVal _ (sigWord_letters (betaWords_getD_letters j))

theorem HSCtx.real_of_realEq (hΛ : HSCtx) {lw : List ℕ} (hlw : ∀ l ∈ lw, 1 ≤ l ∧ l ≤ 6)
    {b : ℕ} {d : List ℕ} {j : ℕ} (h : realEq lw b d j = true) :
    wordVal hsGens lw * hΛ.sigBet b j * (wordVal hsGens lw)⁻¹ =
      kapL (colOf d ([0, 1, 3].getD j 0)) := by
  simp only [realEq, Bool.and_eq_true] at h
  obtain ⟨hinv, heq⟩ := h
  have hL := rep_rho_wordVal lw hlw
  have hLi := Rep.inv_of_invOK hL hinv
  have hc := Rep.compT (Rep.compT hL (hΛ.rep_sigBetaT b j)) hLi
  have hk := rep_kapL (colOf d ([0, 1, 3].getD j 0))
  have := (tblEq_iff_eq hc hk).1 heq
  apply hΛ.rho_injective
  rw [map_mul, map_mul, map_inv]
  exact this

theorem realOK_parts : (∀ j < 3, realEq gamma1Word 0 gamma1Data j = true ∧
      realEq gamma2Word 1 gamma2Data j = true) ∧
    realShapeOK 0 gamma1Data = true ∧ realShapeOK 1 gamma2Data = true := by
  have h := e1OK_true.2
  simp only [realOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem HSCtx.real1 (hΛ : HSCtx) {j : ℕ} (hj : j < 3) :
    gamma1L * bet j * gamma1L⁻¹ = kapL (colOf gamma1Data ([0, 1, 3].getD j 0)) := by
  have := hΛ.real_of_realEq gamma1Word_letters (realOK_parts.1 j hj).1
  simp only [HSCtx.sigBet, ite_true] at this
  exact this

theorem HSCtx.real2 (hΛ : HSCtx) {j : ℕ} (hj : j < 3) :
    gamma2L * hΛ.sigma (bet j) * gamma2L⁻¹ = kapL (colOf gamma2Data ([0, 1, 3].getD j 0)) := by
  have := hΛ.real_of_realEq gamma2Word_letters (realOK_parts.1 j hj).2
  simp only [HSCtx.sigBet, one_ne_zero, ite_false] at this
  exact this

end Sig

end CFSG.EvenSporadicStandard.TwoHS
