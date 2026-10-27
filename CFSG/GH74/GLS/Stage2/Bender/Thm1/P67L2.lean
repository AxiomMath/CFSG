module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L2Cross
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.Blueprint.Multiplier


theorem exists_L2_model {Y : Type} [Group Y] (hY : FL2 Y) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), L2Field F ∧ Nonempty (Y ≃* L2 F) ∧
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F = p ^ f := by
  obtain ⟨p₀, f, hp₀, hf, hp₀2, hLie⟩ := hY
  obtain ⟨-, -, -, hpf3, F, _, _, hFcard, ⟨e0⟩⟩ :=
    ComponentClassification.AutL2Facts.lieModel_psl2_data hLie
  have hoddF : Odd (Nat.card F) := by
    rw [hFcard]; exact (hp₀.odd_of_ne_two hp₀2).pow
  have hF3 : 3 < Nat.card F := by
    have h1 : p₀ ≤ p₀ ^ f := Nat.le_self_pow (by omega) p₀
    have h2 : 3 ≤ p₀ := by have := hp₀.two_le; omega
    have h3 : Nat.card F ≠ 3 := by rw [hFcard]; exact hpf3
    have : 3 ≤ Nat.card F := by rw [hFcard]; exact h2.trans h1
    omega
  exact ⟨F, inferInstance, inferInstance, ⟨hoddF, hF3⟩, ⟨e0.trans (L2.equivPSL F).symm⟩,
    p₀, f, hp₀, hp₀2, hFcard⟩

theorem cf67CoreFull_L2 (Y : Type) [Group Y] [Finite Y] (hY : FL2 Y) : CF67CoreFull Y := by
  intro hs hn r V Z h2 h3
  obtain ⟨F, _, _, hFL, ⟨e⟩, -⟩ := exists_L2_model hY
  by_cases hrp : ringChar F = r
  · exact cf67_L2_char hFL e h2 h3 hrp
  · exact cf67_L2_cross hFL e h2 h3 hrp

theorem L2_cover_odd (hGA : CFSG.Open.GriessAllModelsStatement)
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) (hY : FL2 (J ⧸ center J)) {r : ℕ}
    (hr : r.Prime) (hr2 : Odd r) (hd : r ∣ Nat.card (center J)) :
    r = 3 ∧ Blueprint.LieModel (J ⧸ center J) .PSL 2 3 2 := by
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  have hM : Models.LieModel (J ⧸ center J) .PSL 2 p f :=
    CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hLie
  have hgen : genericOrders .PSL 2 p f = (Nat.gcd 2 (p ^ f - 1), 1) := by
    unfold genericOrders; rfl
  have hpos : 0 < Nat.gcd 2 (p ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  by_cases h32 : p = 3 ∧ f = 2
  · obtain ⟨rfl, rfl⟩ := h32
    refine ⟨?_, hLie⟩
    have hex : exceptionalOrders .PSL 2 3 2 = (3, 1) := by unfold exceptionalOrders; rfl
    have hne : (genericOrders .PSL 2 3 2).1 * (genericOrders .PSL 2 3 2).2 *
        ((exceptionalOrders .PSL 2 3 2).1 * (exceptionalOrders .PSL 2 3 2).2) ≠ 0 := by
      rw [hgen, hex]; norm_num
    have h := hd.trans (card_center_dvd_table hGA hJ hM hne)
    rw [hgen, hex] at h
    have h6 : r ∣ 6 := by norm_num at h; exact h
    have hr6 : r ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    interval_cases r <;> first
      | rfl
      | exact absurd hr (by decide)
      | exact absurd hr2 (by decide)
      | exact absurd h6 (by decide)
  · exfalso
    have hex : exceptionalOrders .PSL 2 p f = (1, 1) := by
      unfold exceptionalOrders; split <;> simp_all
    have hne : (genericOrders .PSL 2 p f).1 * (genericOrders .PSL 2 p f).2 *
        ((exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2) ≠ 0 := by
      rw [hex, hgen]; simpa using hpos.ne'
    have h := hd.trans (card_center_dvd_table hGA hJ hM hne)
    rw [hex, hgen] at h
    have h2' : r ∣ 2 := by
      have h1 : r ∣ Nat.gcd 2 (p ^ f - 1) := by simpa using h
      exact h1.trans (Nat.gcd_dvd_left 2 _)
    exact absurd (((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2') ▸ hr2) (by decide)


theorem cf67L2_of_nine (hGA : CFSG.Open.GriessAllModelsStatement)
    (hNine : ∀ (Y : Type) [Group Y] [Finite Y], Blueprint.LieModel Y .PSL 2 3 2 →
      CF67CoreDeriv Y 3) : CF67L2 :=
  cf67Fam_of_core (fun Y _ _ hY => cf67CoreFull_L2 Y hY)
    (fun J _ _ hJ hY r hr hr2 hd => by
      obtain ⟨rfl, hL⟩ := L2_cover_odd hGA hJ hY hr hr2 hd
      exact hNine _ hL)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
