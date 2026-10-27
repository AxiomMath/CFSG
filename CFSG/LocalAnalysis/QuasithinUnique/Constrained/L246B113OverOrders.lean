module

public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Sporadic.Schreier.TitsOuterTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
public import CFSG.GH74.KGroups.U33
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.QuasithinUnique.Bridge.Over

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

namespace Orders2520

theorem ne_of_profile {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hN : N ≠ 3) : m ≠ 2520 := by
  have := h.ne_of_ne (a := 3) (r := 315) (by decide) hN
  simpa using this

theorem three_le_of_three_le {n : ℕ} (hn : 3 ≤ n) : 6 ≤ n * (n + 1) / 2 :=
  (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)

theorem ordA_ne {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) : ordA n (2 ^ f) ≠ 2520 := by
  by_cases hN : f * (n * (n + 1) / 2) = 3
  · have h3 : n * (n + 1) / 2 ≤ 3 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left f hN)
    have hn2 : n ≤ 2 := by
      by_contra hlt
      have := three_le_of_three_le (show 3 ≤ n by omega)
      omega
    interval_cases n
    · have hf3 : f = 3 := by simpa using hN
      subst hf3
      decide
    · have hf1 : f = 1 := by simpa using hN
      subst hf1
      decide
  · exact ne_of_profile (profile_ordA hn hf) hN

theorem ordTwistedA_ne {n g : ℕ} (hn : 2 ≤ n) (hg : 1 ≤ g) : ordTwistedA n (2 ^ g) ≠ 2520 := by
  by_cases hN : g * (n * (n + 1) / 2) = 3
  · have h3 : n * (n + 1) / 2 ≤ 3 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left g hN)
    have hn2 : n ≤ 2 := by
      by_contra hlt
      have := three_le_of_three_le (show 3 ≤ n by omega)
      omega
    have hn2' : n = 2 := by omega
    subst hn2'
    have hg1 : g = 1 := by simpa using hN
    subst hg1
    decide
  · exact ne_of_profile (profile_ordTwistedA hn hg) hN

theorem ordBC_ne {n f : ℕ} (hf : 1 ≤ f) : ordBC n (2 ^ f) ≠ 2520 := by
  by_cases hN : f * (n * n) = 3
  · have h3 : n * n ≤ 3 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left f hN)
    have hn1 : n ≤ 1 := by nlinarith
    interval_cases n
    · simp at hN
    · have hf3 : f = 3 := by simpa using hN
      subst hf3
      decide
  · exact ne_of_profile (profile_ordBC hf) hN

theorem ordD_ne {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) : ordD n (2 ^ f) ≠ 2520 := by
  refine ne_of_profile (profile_ordD hn hf) fun hN => ?_
  have : Even (f * (n * (n - 1))) := (Nat.even_mul_pred_self n).mul_left f
  rw [hN] at this
  exact absurd this (by decide)

theorem ordTwistedD_ne {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    ordTwistedD n (2 ^ f) ≠ 2520 := by
  refine ne_of_profile (profile_ordTwistedD hn hf) fun hN => ?_
  have : Even (f * (n * (n - 1))) := (Nat.even_mul_pred_self n).mul_left f
  rw [hN] at this
  exact absurd this (by decide)

theorem dvd_card_of_twistedF4
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : ReeTitsModel X .twistedF4 2 f) : 2 ^ (2 * f) + 1 ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hidx : ¬ 2 ∣ ((S : Subgroup X).subgroupOf ⊤).index := by
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup X) ⊤ := ⟨le_top, S.isPGroup', hidx⟩
  obtain ⟨-, -, -, hcov⟩ := CFSG.QuasithinUnique.Setup.X6.large_Ree_model_two_extensions h
  obtain ⟨P₁, P₂, -, -, -, -, -, h2⟩ := hcov S hS
  rw [← h2]
  exact (Subgroup.relIndex_dvd_card _ _).trans (Subgroup.card_dvd_of_le le_top) |>.trans
    (Subgroup.card_top (G := X)).dvd

theorem not_dvd_of_two_pow {f : ℕ} (hf : Odd f) (h3 : 3 ≤ f) : ¬ 2 ^ (2 * f) + 1 ∣ 2520 := by
  intro hd
  have hle := Nat.le_of_dvd (by norm_num) hd
  have hf5 : f ≤ 5 := by
    by_contra hlt
    have : 2 ^ 12 ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨k, rfl⟩ := hf
  have : k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl <;> revert hd <;> decide

end Orders2520

open Orders2520 in
theorem card_ne_of_evenLieType
    {X : Type} [Group X] (h : EvenLieType X) : Nat.card X ≠ 2520 := by
  obtain ⟨t, n, f, hadm, hmod⟩ := h
  have hf : 1 ≤ f := hadm.2.1
  rcases hmod with ⟨ht, hc⟩ | ⟨-, ht, hce⟩ | ⟨-, ht, hrt⟩ | ⟨-, -, hsz⟩
  · have hcard := card_statedClassicalModel_two hc
    cases t
    case PSL =>
      rw [hcard.1 rfl]
      exact ordA_ne (by have := hadm.2.2.1; omega) hf
    case PSU =>
      rw [hcard.2.1 rfl]
      exact ordTwistedA_ne (by have := hadm.2.2.1; omega) hf
    case PSp =>
      rw [hcard.2.2.1 rfl]
      exact ordBC_ne hf
    case POmegaOdd => exact absurd rfl hadm.2.2.2
    case POmegaPlus =>
      rw [hcard.2.2.2.1 rfl]
      exact ordD_ne (by have := hadm.2.2; omega) hf
    case POmegaMinus =>
      rw [hcard.2.2.2.2 rfl]
      exact ordTwistedD_ne (by have := hadm.2.2; omega) hf
    all_goals exact absurd ht (by decide)
  · have hcard := card_chevalleyExceptionalModel_two hce
    cases t
    case G2 =>
      rw [hcard]
      exact ne_of_profile (profile_ordG2 hf) (by omega)
    case F4 =>
      rw [hcard]
      exact ne_of_profile (profile_ordF4 hf) (by omega)
    case E6 =>
      rw [hcard]
      exact ne_of_profile (profile_ordE6 hf) (by omega)
    case E7 =>
      rw [hcard]
      exact ne_of_profile (profile_ordE7 hf) (by omega)
    case E8 =>
      rw [hcard]
      exact ne_of_profile (profile_ordE8 hf) (by omega)
    case twistedE6 =>
      rw [hcard]
      exact ne_of_profile (profile_ordTwistedE6 hf) (by omega)
    case trialityD4 =>
      rw [hcard]
      exact ne_of_profile (profile_ordTrialityD4 hf) (by omega)
    all_goals exact absurd ht (by decide)
  · cases t
    case twistedG2 => exact absurd hadm.2.2.2.1 (by decide)
    case twistedF4 =>
      intro hX
      have : Finite X := Nat.finite_of_card_ne_zero (by omega)
      have hd := dvd_card_of_twistedF4 hrt
      rw [hX] at hd
      exact not_dvd_of_two_pow hadm.2.2.2.2.1 hadm.2.2.2.2.2 hd
    case Tits =>
      intro hX
      have := (CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound X 2 f hrt).1
      omega
    all_goals exact absurd ht (by decide)
  · obtain ⟨-, a, -, K, _, _, hfa, hK, ⟨e⟩⟩ := hsz
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
    have hcard : Nat.card X = ordSuzuki (2 ^ f) := by
      rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK', hfa, ordSuzuki]
      exact Nat.mul_right_comm _ _ _
    rw [hcard]
    exact ne_of_profile (profile_ordSuzuki hf) (by omega)

theorem not_evenLieType_of_card
    {X : Type} [Group X] (hX : Nat.card X = 2520) :
    ¬ EvenLieType X := fun h => card_ne_of_evenLieType h hX

theorem card_psu_three_three
    {X : Type} [Group X] (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1) :
    Nat.card X = 6048 := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
  rw [Nat.card_congr e.toEquiv, ← CFSG.GH74.KGroups.U33.QP.orderCertificate_eq_card
    CFSG.GH74.KGroups.U33.QP_valid.1, CFSG.GH74.KGroups.U33.QP_valid.2]

theorem not_psu33_of_card
    {X : Type} [Group X] (hX : Nat.card X = 2520) :
    ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1 := fun h => by
  have := card_psu_three_three h
  omega

end CFSG.QuasithinUnique.Bridge.Over
