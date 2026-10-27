module

public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.GF2Type.Smith1980Orth.Ident

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriConf

open CFSG CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.GF2Type.Smith1980Orth CFSG.Timmesfeld

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem card_G_eq_of_triality (hw : S.width = 4)
    (hM : Nat.card S.Mbar = 648 ∨ Nat.card S.Mbar = 1296)
    (hidx : Nat.card S.Mbar = 648 → S.M.index % 8 = 7) :
    ∃ e : ℕ, e ≤ 1 ∧ Nat.card G = 2 ^ (12 + e) * (81 * S.M.index) ∧
      (e = 0 → S.M.index % 8 = 7) := by
  have hQ : Nat.card S.Q = 2 ^ 9 := by
    rw [S.card_Q_eq, hw]
  have hMQ : Nat.card S.M = Nat.card S.Q * Nat.card S.Mbar := card_M_eq_card_Q_mul S
  have hG : Nat.card S.M * S.M.index = Nat.card G := S.M.card_mul_index
  rcases hM with hM | hM
  · refine ⟨0, by omega, ?_, fun _ => hidx hM⟩
    calc Nat.card G = Nat.card S.M * S.M.index := hG.symm
      _ = (2 ^ 9 * 648) * S.M.index := by rw [hMQ, hQ, hM]
      _ = 2 ^ (12 + 0) * (81 * S.M.index) := by norm_num; ring
  · refine ⟨1, by omega, ?_, fun h => absurd h (by omega)⟩
    calc Nat.card G = Nat.card S.M * S.M.index := hG.symm
      _ = (2 ^ 9 * 1296) * S.M.index := by rw [hMQ, hQ, hM]
      _ = 2 ^ (12 + 1) * (81 * S.M.index) := by norm_num; ring

theorem odd_81_mul_index (S : Setting G) : Odd (81 * S.M.index) := by
  have hi : Odd S.M.index := by
    rw [Nat.odd_iff]
    have := S14.not_two_dvd_index_M S
    omega
  exact (by decide : Odd 81).mul hi

private theorem psl_triality {n e i : ℕ} (hn : 3 ≤ n) (he : e ≤ 1) (hodd : Odd (81 * i))
    (h : 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) =
      2 ^ (12 + e) * (81 * i)) : False := by
  obtain ⟨hexp, -⟩ := two_pow_mul_odd_inj (odd_prod_two_pow_sub_one n) hodd h
  have hnn : n * (n - 1) = 2 * (12 + e) := by
    have := Nat.even_mul_pred_self n
    rw [Nat.even_iff] at this
    omega
  have hn6 : n ≤ 6 := by
    by_contra h6
    push Not at h6
    have : 7 * 6 ≤ n * (n - 1) := Nat.mul_le_mul h6 (by omega)
    omega
  interval_cases n <;> omega

private theorem psp_triality {n e : ℕ} (hn : 3 ≤ n) (he : e ≤ 1) : n * n ≠ 12 + e := by
  intro h
  have hn4 : n = 3 ∨ 4 ≤ n := by omega
  rcases hn4 with rfl | h4
  · omega
  · nlinarith [Nat.mul_le_mul h4 h4]

private theorem pomega_triality {n e i : ℕ} {b : Bool} (hn : 4 ≤ n) (he : e ≤ 1)
    (hidx : e = 0 → i % 8 = 7) (hodd : Odd (81 * i))
    (h : 2 ^ (n * (n - 1)) * omegaOdd b n = 2 ^ (12 + e) * (81 * i)) : False := by
  obtain ⟨hexp, hU⟩ := two_pow_mul_odd_inj (odd_omegaOdd b (by omega)) hodd h
  have hn4 : n = 4 := by
    by_contra hne
    have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  subst hn4
  have he0 : e = 0 := by omega
  have hi8 : i % 8 = 7 := hidx he0
  have hmod : (81 * i) % 8 = 7 := by
    rw [Nat.mul_mod, show 81 % 8 = 1 by norm_num, Nat.one_mul, Nat.mod_mod, hi8]
  cases b
  · have h1 : omegaOdd false 4 = 48195 := by decide
    rw [h1] at hU
    have hbad : (48195 : ℕ) % 8 = (81 * i) % 8 := by rw [hU]
    rw [hmod] at hbad
    norm_num at hbad
  · have h1 : omegaOdd true 4 = 42525 := by decide
    rw [h1] at hU
    have hbad : (42525 : ℕ) % 8 = (81 * i) % 8 := by rw [hU]
    rw [hmod] at hbad
    norm_num at hbad

private theorem trialityD4_triality {i : ℕ} (hi : i % 8 = 7) (hU : 51597 = 81 * i) : False := by
  have hmod : (81 * i) % 8 = 7 := by
    rw [Nat.mul_mod, show 81 % 8 = 1 by norm_num, Nat.one_mul, Nat.mod_mod, hi]
  have hbad : (51597 : ℕ) % 8 = (81 * i) % 8 := by rw [hU]
  rw [hmod] at hbad
  norm_num at hbad

private theorem outcome_triality
    {D : Set G} (hFI : DW.DW2FieldInput) (hD34 : DW.IsTransClass34 D)
    (hOut : Timmesfeld.Outcome G) {e i : ℕ} (he : e ≤ 1)
    (hi : e = 0 → i % 8 = 7) (hodd : Odd (81 * i))
    (hcard : Nat.card G = 2 ^ (12 + e) * (81 * i)) : False := by
  rcases hOut with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ |
    ⟨f, hf, h⟩ | ⟨f, hf, t, ht, h⟩ | h | h | h
  ·
    obtain rfl : f = 1 := by
      by_contra hne
      exact hFI G .PSL n f (by omega) (Or.inl ⟨rfl, hn⟩) h D hD34
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).1 rfl, ordA_two (by omega)] at hcard
    exact psl_triality hn he hodd hcard
  ·
    obtain rfl : f = 1 := by
      by_contra hne
      exact hFI G .PSp n f (by omega) (Or.inr (Or.inl ⟨rfl, hn⟩)) h D hD34
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.1 rfl] at hcard
    obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordBC (n := n) (le_refl 1)).two
    rw [hr'] at hcard
    obtain ⟨hexp, -⟩ := two_pow_mul_odd_inj hr hodd hcard
    exact psp_triality hn he (by simpa using hexp)
  ·
    obtain rfl : f = 1 := by
      by_contra hne
      exact (hFI G .POmegaPlus n f (by omega)
        (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, hn⟩))) h D hD34).elim
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.1 rfl, ordD_two (by omega)] at hcard
    exact pomega_triality hn he hi hodd hcard
  ·
    obtain rfl : f = 1 := by
      by_contra hne
      exact (hFI G .POmegaMinus n f (by omega)
        (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, hn⟩))) h D hD34).elim
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.2 rfl,
      ordTwistedD_two (by omega)] at hcard
    exact pomega_triality hn he hi hodd hcard
  ·
    exact (hFI G .G2 0 f hf (Or.inr (Or.inr (Or.inr ⟨rfl, by simp⟩))) h D hD34).elim
  ·
    have hct : t ∈ chevalleyExceptionalTags := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain rfl : f = 1 := by
      by_contra hne
      refine hFI G t 0 f (by omega) (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))) h D hD34
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
      tauto
    have hc := Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel hct h
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have hm' : Nat.card G = ordTrialityD4 (2 ^ 1) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hc
      have hval : ordTrialityD4 (2 ^ 1) = 2 ^ 12 * 51597 := by decide
      rw [hm', hval] at hcard
      obtain ⟨hexp, hU⟩ := two_pow_mul_odd_inj (by decide : Odd 51597) hodd hcard
      have he0 : e = 0 := by omega
      exact trialityD4_triality (hi he0) hU
    ·
      have hm' : Nat.card G = ordF4 (2 ^ 1) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordF4 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      obtain ⟨hexp, -⟩ := two_pow_mul_odd_inj hr hodd hcard
      omega
    ·
      have hm' : Nat.card G = ordE6 (2 ^ 1) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordE6 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      obtain ⟨hexp, -⟩ := two_pow_mul_odd_inj hr hodd hcard
      omega
    ·
      have hm' : Nat.card G = ordTwistedE6 (2 ^ 1) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordTwistedE6 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      obtain ⟨hexp, -⟩ := two_pow_mul_odd_inj hr hodd hcard
      omega
    ·
      have hm' : Nat.card G = ordE7 (2 ^ 1) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordE7 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      obtain ⟨hexp, -⟩ := two_pow_mul_odd_inj hr hodd hcard
      omega
    ·
      have hm' : Nat.card G = ordE8 (2 ^ 1) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordE8 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      obtain ⟨hexp, -⟩ := two_pow_mul_odd_inj hr hodd hcard
      omega
  ·
    have h6048 : Nat.card G = 6048 := LieModel.card_psu_three_three h
    have hdvd : 2 ^ 12 ∣ Nat.card G := by
      rw [hcard]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) (81 * i)
    rw [h6048] at hdvd
    norm_num at hdvd
  ·
    obtain ⟨e'⟩ := h
    have h360 : Nat.card G = 360 := by
      rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    have hdvd : 2 ^ 12 ∣ Nat.card G := by
      rw [hcard]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) (81 * i)
    rw [h360] at hdvd
    norm_num at hdvd
  ·
    obtain ⟨e'⟩ := h
    have hJ : Nat.card G = 604800 := (Nat.card_congr e'.toEquiv).trans Sporadic.J2.card_J2
    have hdvd : 2 ^ 12 ∣ Nat.card G := by
      rw [hcard]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) (81 * i)
    rw [hJ] at hdvd
    norm_num at hdvd


theorem false_of_threeFourPlusClass
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G} (hw : S.width = 4)
    (hD : ThreeFourPlusClass G {g | IsConj S.z g})
    (h4 : ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4)
    (hM : Nat.card S.Mbar = 648 ∨ Nat.card S.Mbar = 1296)
    (hidx : Nat.card S.Mbar = 648 → S.M.index % 8 = 7) : False := by
  obtain ⟨a, b, ha, hb, h4⟩ := h4
  have hOut := Timmesfeld.outcome (S14.hyp_of_threeFourPlusClass hD ⟨a, ha, b, hb, h4⟩)
  have hD34 : DW.IsTransClass34 {g : G | IsConj S.z g} :=
    isTransClass34_of_threeFourPlusClass hD
  obtain ⟨e, he, hcard, hi⟩ := card_G_eq_of_triality hw hM hidx
  exact outcome_triality DW.dw2FieldInput hD34 hOut he hi (odd_81_mul_index S) hcard

end CFSG.GF2Type.Smith1979.TriConf
