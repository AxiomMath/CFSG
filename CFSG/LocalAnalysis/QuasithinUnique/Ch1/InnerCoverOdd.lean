module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.LieType.Steinberg.CentralExt.UnitaryPerfect

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem ker_eq_bot_of_card_dvd_odd {E K : Type} [Group E] [Finite E] [Group K] (η : E →* K)
    (h2 : IsPGroup 2 η.ker) {m : ℕ} (hm : Odd m) (hd : Nat.card η.ker ∣ m) : η.ker = ⊥ :=
  Subgroup.eq_bot_of_card_eq _
    (CFSG.LieType.Steinberg.card_eq_one_of_isPGroup_two_of_dvd_odd h2 hm hd)

theorem sylowCentralizerCentral_of_psl_three_odd {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel X .PSL 3 p f) : SylowCentralizerCentral X := by
  refine sylowCentralizerCentral_of_cover_trivial ?_
  intro E _ _ _ η hη hC h2
  have hcard := (CFSG.LieType.Steinberg.odd_field_higher_linear_perfect_central_two_kernel_cyclic
    hp2 inferInstance hη hC h2 (Or.inl ⟨by decide, h⟩)).2
  exact ker_eq_bot_of_card_dvd_odd η h2 (m := 3) (by decide) (hcard.trans (Nat.gcd_dvd_left 3 _))

theorem sylowCentralizerCentral_of_psu_three_odd {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel X .PSU 3 p f) : SylowCentralizerCentral X := by
  refine sylowCentralizerCentral_of_cover_trivial ?_
  intro E _ _ _ η hη hC h2
  obtain ⟨C₂⟩ : Nonempty (Sylow 2 η.ker) := inferInstance
  have hc : Nat.card (C₂ : Subgroup η.ker) = 1 :=
    CFSG.LieType.Steinberg.odd_unitary_three_perfect_central_two_kernel_cyclic hp2
      (Or.inl ⟨by decide, h⟩) hη inferInstance hC C₂
  have htop : (C₂ : Subgroup η.ker) = ⊤ := top_unique ((h2.to_subgroup ⊤).le_sylow_of_normal C₂)
  rw [htop, Subgroup.card_top] at hc
  exact Subgroup.eq_bot_of_card_eq _ hc

end CFSG.QuasithinUnique.Ch1
