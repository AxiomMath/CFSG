module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL2Res
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL2Bor
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL2Img
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL2Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1All
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L2Card
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecTransport

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ComponentClassification.OuterAutomorphisms

namespace L2V

theorem eq_five_of_mul {Q : ℕ} (h : Q * (Q ^ 2 - 1) = 120) : Q = 5 := by
  have hle : Q ≤ 5 := by
    by_contra h6
    have h6' : 6 ≤ Q := by omega
    have := Nat.mul_le_mul h6' (Nat.sub_le_sub_right (Nat.pow_le_pow_left h6' 2) 1)
    norm_num at this
    omega
  interval_cases Q <;> first | rfl | (norm_num at h)

theorem card_psl2_five {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5) :
    Nat.card (GorensteinWalter.PSL2 F) = 60 := by
  have h := card_L2_mul_two_of_odd (F := F) (by rw [hF]; decide)
  rw [Nat.card_congr (IVK.L2.equivPSL F).toEquiv, hF] at h
  omega

theorem card_outer_dvd_two {Y : Type} [Group Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (h : LieModel Y .PSL 2 r f) (hY : Nat.card Y = 60) :
    Nat.card (Outer Y) ∣ 2 := by
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := ComponentClassification.AutL2Facts.lieModel_psl2_data h
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hr.odd_of_ne_two hr2).pow
  have hc := card_L2_mul_two_of_odd (F := F) hodd
  rw [Nat.card_congr (IVK.L2.equivPSL F).toEquiv, ← Nat.card_congr e.toEquiv, hY, hF] at hc
  have hq5 : r ^ f = 5 := eq_five_of_mul (by omega)
  have hr5 : r = 5 := by
    rcases Nat.prime_five.eq_one_or_self_of_dvd r
      (hq5 ▸ dvd_pow_self r (by omega : f ≠ 0)) with h1 | h1
    · exact absurd h1 hr.one_lt.ne'
    · exact h1
  subst hr5
  have hf1 : f = 1 := Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num : 2 ≤ 5))
    (hq5.trans (pow_one 5).symm)
  subst hf1
  have hst : StatedClassicalModel Y .PSL 2 5 1 := by
    rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  exact ((LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound Y 2 5 1 hst).2.2.2.1
    rfl).trans (by norm_num)

end L2V

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}


theorem false_of_fl2_moved (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)}
    (hB : BridgeB k p H P g J) (hF : FL2 (↥J ⧸ center ↥J))
    (hI : ¬ barIn H I ≤ centralizer (J : Set (HBar H))) : False := by
  obtain ⟨Γ, _, _, V, _, _, _, ρ, K, a, P', hM, -, hL⟩ := hB
  have := hM.normal
  have hq := hM.quasi
  obtain ⟨e, -⟩ := LinkB.exists_equiv hq hL
  obtain ⟨r, f, hr, hf1, hr2, hlie⟩ := hF
  have hlieK : LieModel (↥K ⧸ center ↥K) .PSL 2 r f := Transport.lieModel_of_mulEquiv e hlie
  obtain ⟨Xi, hXperf, hXne, hXN⟩ := exists_perfect_image hd hq hL hI
  have hWp : IsPGroup p ↥(innerPart (K := K) P') :=
    isPGroup_innerPart (center_quot_eq_bot hq) hM.pgrp
  by_cases hrp : r = p
  · subst hrp
    by_cases hU : innerPart (K := K) P' = ⊥
    · exact false_of_innerPart_eq_bot hM (outerFalseNS_l2 r f hr hr2 hf1 _ hlieK) hU
    · exact hXne (L2V.perfect_eq_bot_of_le_normalizer hr hlieK hU hWp hXperf hXN)
  · obtain ⟨hp3, F₀, _, _, e0, h5, -⟩ :=
      stepL2_core crossE1_all hM.toHyp89 hr hr2 hrp ⟨f, hf1, hlieK⟩
    subst hp3
    have hs : IsSimpleGroup (↥K ⧸ center ↥K) := hq.2.1
    have hY60 : Nat.card (↥K ⧸ center ↥K) = 60 := by
      rw [Nat.card_congr e0.toEquiv]
      exact L2V.card_psl2_five h5
    by_cases hU : innerPart (K := K) P' = ⊥
    · have hO := L2V.card_outer_dvd_two hr hr2 hf1 hlieK hY60
      have hnotinn : actYHom (K := K) a ∉ inner (↥K ⧸ center ↥K) := by
        intro hin
        obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hin
        have hyU : y ∈ innerPart (K := K) P' := mem_innerPart.mpr ⟨a, hM.a_mem, hy.symm⟩
        rw [hU, Subgroup.mem_bot] at hyU
        apply hM.actYHom_ne_one
        rw [← hy, hyU, map_one]
      exact hnotinn (L2V.mem_inner_of_pow_three hO hM.actYHom_pow)
    · exact hXne (L2V.perfect_eq_bot_of_sixty hY60 hU hWp hXperf hXN)

theorem cellV_fl2 (hRes : FL2Res) : CellV FL2 := by
  intro G _ _ z k S T Tstar p H P g X Y h t q I Q₁ hd J hB hF
  by_cases hI : barIn H I ≤ centralizer (J : Set (HBar H))
  · exact hRes G z k S T Tstar p H P g X Y h t q I Q₁ hd J hB hF hI
  · exact false_of_fl2_moved hd hB hF hI

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
