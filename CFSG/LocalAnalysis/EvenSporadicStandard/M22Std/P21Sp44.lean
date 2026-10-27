module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Out
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21HSp44
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2Sp44

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std
  CFSG.EvenSporadicStandard.M23Std

theorem not_card_centralizer_one_or_two {U : Type} [Group U] [Finite U] [IsSimpleGroup U]
    (hbig : 2 < Nat.card U) (u : U) (hu : u * u = 1) (hu1 : u ≠ 1) :
    ¬ (Nat.card (centralizer ({u} : Set U)) = 1 ∨ Nat.card (centralizer ({u} : Set U)) = 2) := by
  have hord : orderOf u = 2 := orderOf_eq_prime (by rwa [sq]) hu1
  have huC : u ∈ centralizer ({u} : Set U) := mem_centralizer_singleton_iff.2 rfl
  rintro (h | h)
  · have : 1 < Nat.card (centralizer ({u} : Set U)) := by
      rw [Nat.one_lt_iff_ne_zero_and_ne_one]
      refine ⟨Nat.card_pos.ne', fun h1 => hu1 ?_⟩
      have := Subgroup.eq_bot_of_card_eq _ h1
      have hm : u ∈ (⊥ : Subgroup U) := this ▸ huC
      exact Subgroup.mem_bot.1 hm
    omega
  · have hU2 : ∀ V : Subgroup U, IsPGroup 2 V → V ≤ (⊤ : Subgroup U) →
        V ≤ centralizer ({u} : Set U) → Nat.card V ≤ 2 := fun V _ _ hV =>
      (Subgroup.card_le_of_le hV).trans h.le
    have hX : ∀ N : Subgroup U, N.Normal → Odd (Nat.card N) → N = ⊥ := by
      intro N hN hodd
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h0 | h0
      · exact h0
      · exfalso
        have hdvd : 2 ∣ Nat.card U := hord ▸ orderOf_dvd_natCard u
        rw [h0, Subgroup.card_top] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
    have htop := CResH4.normal_eq_zpowers (⊤ : Subgroup U) (Subgroup.mem_top u) hu hu1 hU2 hX
    have hc : Nat.card U = 2 := by
      rw [← Subgroup.card_top (G := U), htop, Nat.card_zpowers, hord]
    omega

theorem noBadCent_of_noNine {U : Type} [Group U] [Finite U] [IsSimpleGroup U]
    (hbig : 2 < Nat.card U) (u : U) (hu : u * u = 1) (hu1 : u ≠ 1)
    (h9 : ∀ P : Subgroup U, Nat.card P = 9 → ¬ ∀ x ∈ P, u * x = x * u) :
    ¬ (Nat.card (centralizer ({u} : Set U)) = 1 ∨ Nat.card (centralizer ({u} : Set U)) = 2 ∨
      Nat.card (centralizer ({u} : Set U)) = 360 ∨ Nat.card (centralizer ({u} : Set U)) = 720 ∨
      Nat.card (centralizer ({u} : Set U)) = 1440) := by
  have hnine : (9 : ℕ) ∣ Nat.card (centralizer ({u} : Set U)) → False := by
    intro hd
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := centralizer ({u} : Set U))
      3 (n := 2) (by simpa using hd)
    refine h9 (K.map (centralizer ({u} : Set U)).subtype) ?_ ?_
    · rw [Subgroup.card_map_of_injective (centralizer ({u} : Set U)).subtype_injective, hK]
      norm_num
    · rintro _ ⟨k, -, rfl⟩
      exact (mem_centralizer_singleton_iff.1 k.2).symm
  rintro (h | h | h | h | h)
  · exact not_card_centralizer_one_or_two hbig u hu hu1 (Or.inl h)
  · exact not_card_centralizer_one_or_two hbig u hu hu1 (Or.inr h)
  · exact hnine (by rw [h]; norm_num)
  · exact hnine (by rw [h]; norm_num)
  · exact hnine (by rw [h]; norm_num)

variable {G : Type} [Group G] [Finite G] {z : G}

theorem prop21_sp44_partial
    (hz : orderOf z = 2)
    (hC : Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)))
    (hG : Nat.card G ∣ gl8)
    (hS : LieModel (egaLayer (G ⧸ fusionOddCore G)) .PSp 2 2 2) :
    LieModel (egaLayer G) .PSp 2 2 2 ∧
      z ∉ egaLayer G ⊔ centralizer (egaLayer G : Set G) := by
  have hE := eData_Sp44 hS
  have hc := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hS
  have hbig : 1440 < Nat.card (egaLayer (G ⧸ fusionOddCore G)) := by
    rw [card_of_statedClassicalModel_psp_two_two hc]
    norm_num
  have hsimp := isSimpleGroup_of_eData hE
  obtain ⟨U, -, ⟨eU⟩, hU, hzU⟩ := prop21_simple_case hz hC hG hE hbig
    fun u hu hu1 => noBadCent_of_noNine (by omega) u hu hu1
      fun P hP => P21H.no_involution_centralizes_nine_sp44 hS u hu hu1 P hP
  subst hU
  exact ⟨CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eU.symm hS, hzU⟩

end CFSG.EvenSporadicStandard.M22Std
