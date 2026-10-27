module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4CaseA
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4B
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4C
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4HP
public import CFSG.GH74.GLS.Stage2.OddAut.SL2OddNormal
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4

theorem center_eq_bot_of_simple {Y : Type} [Group Y] (hY : IsSimpleGroup Y)
    (hn : ∃ a b : Y, a * b ≠ b * a) : Subgroup.center Y = ⊥ := by
  obtain ⟨a₀, b₀, hab₀⟩ := hn
  rcases hY.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    apply hab₀
    have ha : a₀ ∈ Subgroup.center Y := h ▸ Subgroup.mem_top a₀
    exact (Subgroup.mem_center_iff.mp ha b₀).symm

theorem cf67CoreFull_stated {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 1 ≤ n) (hK : Nat.card K = p ^ n) : CF67CoreFull (StatedProj (StatedSp 2 K)) := by
  classical
  intro hs hnab r V Z h2 h3
  have hcen := center_eq_bot_of_simple hs hnab
  have : Fintype K := Fintype.ofFinite K
  have hpf : Fact p.Prime := ⟨hp⟩
  have hcp : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hK3 : 3 ≤ Nat.card K := by
    rw [hK]
    calc 3 ≤ p := by
          have := hp.two_le
          omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
  by_cases hrp : r = p
  · exact sp4_caseA hp hp2 hK hcen h2 h3 hrp
  · by_cases hinn : ∀ v ∈ V, ∃ g : StatedProj (StatedSp 2 K), MulAut.conj g = v
    · exact caseB hp2 hK hcen
        (fun P hPd hPo r' => noOddNormal_HP
          (fun N _ hN => OddAut.sl2_eq_bot_of_normal_odd hK3 N hN) hPd hPo r') hrp h2 h3 hinn
    · exact caseC hodd hp hn hK hcen h2.1 h2 h3 hinn

theorem cf67CoreFull_Sp4 : ∀ (Y : Type) [Group Y] [Finite Y], FSp4 Y → CF67CoreFull Y := by
  intro Y _ _ hY
  obtain ⟨p, f, hp, hf, hp2, hlie⟩ := hY
  obtain ⟨-, F, iF, fF, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psp_unpack hlie
  have : Finite (StatedProj (StatedSp 2 F)) := Finite.of_equiv Y e.toEquiv
  exact CF67CoreFull.of_mulEquiv e (cf67CoreFull_stated hp hp2 hf hcard)

open CFSG.Blueprint.Multiplier in
theorem cf67Sp4_thm
    (hGA : CFSG.Open.GriessAllModelsStatement) : CF67Sp4 := by
  refine cf67Fam_of_core cf67CoreFull_Sp4 ?_
  intro J _ _ hJ hF r hr hr2 hdvd
  exfalso
  obtain ⟨p, f, hp, hf, hp2, hlie⟩ := hF
  have hm : CFSG.Models.LieModel (J ⧸ Subgroup.center J) .PSp 2 p f :=
    CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hlie
  have hg : genericOrders .PSp 2 p f = (Nat.gcd 2 (p ^ f - 1), 1) := rfl
  have he : exceptionalOrders .PSp 2 p f = (1, 1) := rfl
  have hne : (genericOrders .PSp 2 p f).1 * (genericOrders .PSp 2 p f).2 *
      ((exceptionalOrders .PSp 2 p f).1 * (exceptionalOrders .PSp 2 p f).2) ≠ 0 := by
    rw [hg, he]
    simp only [mul_one]
    exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_table hGA hJ hm hne
  rw [hg, he] at h
  have h2 : Nat.card (Subgroup.center J) ∣ 2 := by
    refine h.trans ?_
    simp only [mul_one]
    exact Nat.gcd_dvd_left _ _
  have hr2' : r ∣ 2 := hdvd.trans h2
  have hreq : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hr2'
  rw [hreq] at hr2
  exact absurd hr2 (by decide)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
