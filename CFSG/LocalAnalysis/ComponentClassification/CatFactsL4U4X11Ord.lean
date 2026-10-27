module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Conf
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.GH74.Orders.LieType
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple

public section

namespace CFSG.ComponentClassification.GSThmB.X11

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] {N : Subgroup G}

theorem card_of_lieModel_psp_four_three {X : Type} [Group X]
    (h : Blueprint.LieModel X .PSp 2 3 1) : Nat.card X = 25920 := by
  rw [GH74.card_of_lieModel_PSp (by norm_num) (by norm_num) h]
  decide

theorem KConf.dvd_lt [Finite G] (h : KConf G N) : 25920 ∣ Nat.card N ∧ 25920 < Nat.card N := by
  obtain ⟨-, hC, -, b, K, hb, hKN, hKb, -, hKm⟩ := h
  have h1 : 25920 ∣ Nat.card K := by
    rw [← card_of_lieModel_psp_four_three hKm]
    exact Subgroup.card_quotient_dvd_card _
  have hne : K ≠ N := by
    intro hKN'
    have hbC : b ∈ centralizer (N : Set G) := by
      rw [mem_centralizer_iff]
      intro m hm
      exact mem_centralizer_singleton_iff.mp (hKb (hKN' ▸ hm))
    rw [hC, mem_bot] at hbC
    rw [hbC, orderOf_one] at hb
    exact absurd hb (by norm_num)
  have h2 : Nat.card K < Nat.card N := Subgroup.card_lt_of_lt (lt_of_le_of_ne hKN hne)
  exact ⟨h1.trans (Subgroup.card_dvd_of_le hKN),
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos h1) h2⟩

theorem KConf.exists_dvd [Finite G] (h : KConf G N) :
    ∃ b : G, orderOf b = 2 ∧ 25920 ∣ Nat.card ↥(N ⊓ centralizer ({b} : Set G)) := by
  obtain ⟨-, -, -, b, K, hb, hKN, hKb, -, hKm⟩ := h
  refine ⟨b, hb, ?_⟩
  have h1 : 25920 ∣ Nat.card K := by
    rw [← card_of_lieModel_psp_four_three hKm]
    exact Subgroup.card_quotient_dvd_card _
  exact h1.trans (Subgroup.card_dvd_of_le (le_inf hKN hKb))

theorem KConf.not_u52 (hU52 : CF81X11U52) [Finite G] (h : KConf G N) :
    ¬ Blueprint.LieModel ↥N .PSU 5 2 1 := fun hN => by
  obtain ⟨b, hb, hd⟩ := h.exists_dvd
  rcases hU52 G N h.1 h.2.1 hN b hb with he | he | he <;> rw [he] at hd <;> norm_num at hd

theorem KConf.not_on (hON : CF81X11ON) [Finite G] (h : KConf G N) :
    ¬ Blueprint.NativeSporadic.IsSporadic ↥N .ONan := fun hN => by
  obtain ⟨b, hb, hd⟩ := h.exists_dvd
  rcases hON G N h.1 h.2.1 hN b hb with he | he <;> rw [he] at hd <;> norm_num at hd

theorem KConf.eightyOne_dvd [Finite G] (h : KConf G N) : 81 ∣ Nat.card N :=
  (by norm_num : 81 ∣ 25920).trans h.dvd_lt.1

theorem KConf.not_psp_four_three [Finite G] (h : KConf G N) :
    ¬ Blueprint.LieModel ↥N .PSp 2 3 1 := fun hN => by
  have := h.dvd_lt.2
  rw [card_of_lieModel_psp_four_three hN] at this
  exact lt_irrefl _ this

theorem three_pow_odd_mod_eight (k : ℕ) : 3 ^ (2 * k + 1) % 8 = 3 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem ordRee_mod_sixteen {q : ℕ} (hq : q % 8 = 3) : Open.ordRee q % 16 = 8 := by
  have hr : q % 16 = 3 ∨ q % 16 = 11 := by omega
  have h1 : (q - 1) % 16 = q % 16 - 1 := by omega
  have h3 : q ^ 3 % 16 = (q % 16) ^ 3 % 16 := Nat.pow_mod q 3 16
  have h4 : (q ^ 3 + 1) % 16 = (q ^ 3 % 16 + 1) % 16 := by omega
  show q ^ 3 * (q ^ 3 + 1) * (q - 1) % 16 = 8
  rw [Nat.mul_mod, Nat.mul_mod (q ^ 3), h4, h3, h1]
  rcases hr with h | h <;> (rw [h]; try norm_num)

theorem KConf.not_ree
    [Finite G] (h : KConf G N)
    (f : ℕ) : ¬ Blueprint.LieModel ↥N .twistedG2 0 3 f := fun hN => by
  obtain ⟨k, -, hcard⟩ := GH74.card_of_lieModel_twistedG2 hN
  have h64 : 16 ∣ Nat.card N := (by norm_num : 16 ∣ 25920).trans h.dvd_lt.1
  rw [hcard] at h64
  have := ordRee_mod_sixteen (three_pow_odd_mod_eight k)
  omega

theorem card_mul_divisor (hO : CatLeaf.LieOrderFormulasInput) {X : Type} [Group X]
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hadm : Assembly.LowTwoRank.StatedLieAdmissible t n p f) (h : Blueprint.LieModel X t n p f) :
    Nat.card X * CatLeaf.lieOrderDivisor t n (p ^ f) = CatLeaf.lieOrderNumerator t n (p ^ f) :=
  (hO X t n p f hadm h).2.1

theorem KConf.not_charTwo (hO : CatLeaf.LieOrderFormulasInput) [Finite G] (h : KConf G N) :
    ¬ Blueprint.LieModel ↥N .PSL 2 2 4 ∧ ¬ Blueprint.LieModel ↥N .PSL 3 2 2 ∧
      ¬ Blueprint.LieModel ↥N .PSU 3 2 2 ∧ ¬ Blueprint.LieModel ↥N .PSp 2 2 2 ∧
      ¬ Blueprint.LieModel ↥N .PSL 5 2 1 ∧ ¬ Blueprint.LieModel ↥N .PSL 3 2 4 := by
  have h81 := h.eightyOne_dvd
  refine ⟨fun hN => ?_, fun hN => ?_, fun hN => ?_, fun hN => ?_, fun hN => ?_, fun hN => ?_⟩
  · have := card_mul_divisor hO (by refine ⟨Nat.prime_two, by norm_num, ?_⟩; decide) hN
    rw [show CatLeaf.lieOrderNumerator .PSL 2 (2 ^ 4) = 4080 by decide,
      show CatLeaf.lieOrderDivisor .PSL 2 (2 ^ 4) = 1 by decide] at this
    omega
  · have := card_mul_divisor hO (by refine ⟨Nat.prime_two, by norm_num, ?_⟩; decide) hN
    rw [show CatLeaf.lieOrderNumerator .PSL 3 (2 ^ 2) = 60480 by decide,
      show CatLeaf.lieOrderDivisor .PSL 3 (2 ^ 2) = 3 by decide] at this
    omega
  · have := card_mul_divisor hO (by refine ⟨Nat.prime_two, by norm_num, ?_⟩; decide) hN
    rw [show CatLeaf.lieOrderNumerator .PSU 3 (2 ^ 2) = 62400 by decide,
      show CatLeaf.lieOrderDivisor .PSU 3 (2 ^ 2) = 1 by decide] at this
    omega
  · have := card_mul_divisor hO (by refine ⟨Nat.prime_two, by norm_num, ?_⟩; decide) hN
    rw [show CatLeaf.lieOrderNumerator .PSp 2 (2 ^ 2) = 979200 by decide,
      show CatLeaf.lieOrderDivisor .PSp 2 (2 ^ 2) = 1 by decide] at this
    omega
  · have := card_mul_divisor hO (by refine ⟨Nat.prime_two, by norm_num, ?_⟩; decide) hN
    rw [show CatLeaf.lieOrderNumerator .PSL 5 (2 ^ 1) = 9999360 by decide,
      show CatLeaf.lieOrderDivisor .PSL 5 (2 ^ 1) = 1 by decide] at this
    omega
  · have := card_mul_divisor hO (by refine ⟨Nat.prime_two, by norm_num, ?_⟩; decide) hN
    rw [show CatLeaf.lieOrderNumerator .PSL 3 (2 ^ 4) = 4277145600 by decide,
      show CatLeaf.lieOrderDivisor .PSL 3 (2 ^ 4) = 3 by decide] at this
    omega

theorem KConf.not_sporadic
    [Finite G] (h : KConf G N) :
    ¬ Blueprint.NativeSporadic.IsSporadic ↥N .J1 ∧ ¬ Blueprint.NativeSporadic.IsSporadic ↥N .J2 ∧
      ¬ Blueprint.NativeSporadic.IsSporadic ↥N .M12 ∧
      ¬ Blueprint.NativeSporadic.IsSporadic ↥N .HS ∧
      ¬ Blueprint.NativeSporadic.IsSporadic ↥N .He := by
  have h81 := h.eightyOne_dvd
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_⟩
  · have hc : Nat.card N = 175560 := (Nat.card_congr e.toEquiv).trans Sporadic.J1.card_J1
    omega
  · have hc : Nat.card N = 604800 := (Nat.card_congr e.toEquiv).trans Sporadic.J2.card_J2
    omega
  · have hc : Nat.card N = 95040 := (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M12
    omega
  · have hc : Nat.card N = 44352000 := (Nat.card_congr e.toEquiv).trans Sporadic.HS.card_HS
    omega
  · have hc : Nat.card N = 4030387200 := (Nat.card_congr e.toEquiv).trans Sporadic.He.card_He
    omega

end CFSG.ComponentClassification.GSThmB.X11
