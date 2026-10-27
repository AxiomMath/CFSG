module

import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap510
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4

theorem isPGroup_center_of_core_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hO : GLAPPrimeCore 3 Y = ⊥) : IsPGroup 3 (Subgroup.center Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [IsPGroup.iff_orderOf]
  rintro ⟨z, hz⟩
  have key : ∃ k : ℕ, orderOf z = 3 ^ k := by
    obtain ⟨k, m, hm, hmk⟩ := Nat.exists_eq_pow_mul_and_not_dvd
      (orderOf_pos z).ne' 3 (by norm_num)
    set w : Y := z ^ 3 ^ k with hw
    have hord : orderOf w = m := by
      have hg : Nat.gcd (orderOf z) (3 ^ k) = 3 ^ k :=
        Nat.gcd_eq_right (by rw [hmk]; exact Dvd.intro m rfl)
      rw [hw, orderOf_pow' _ (pow_ne_zero k (by norm_num)), hg]
      conv_lhs => rw [hmk]
      exact Nat.mul_div_cancel_left m (pow_pos (by norm_num) k)
    have hwc : w ∈ Subgroup.center Y := Subgroup.pow_mem _ hz _
    have hN : (Subgroup.zpowers w).Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hcomm : ∀ g : Y, g * w = w * g := Subgroup.mem_center_iff.1 hwc
      have : g * w ^ j * g⁻¹ = w ^ j := by
        have h1 : g * w ^ j = w ^ j * g := (Commute.zpow_right (hcomm g : Commute g w) j).eq
        rw [h1, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.zpow_mem_zpowers w j
    have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers w)) := by
      rw [Nat.card_zpowers, hord]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm
    have hle : Subgroup.zpowers w ≤ GLAPPrimeCore 3 Y := le_sSup ⟨hN, hcop⟩
    rw [hO] at hle
    have hw1 : w = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers w))
    have hm1 : m = 1 := by rw [← hord, hw1, orderOf_one]
    exact ⟨k, by rw [hmk, hm1, mul_one]⟩
  obtain ⟨k, hk⟩ := key
  exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk⟩

theorem glaPPrimeCore_top_eq_bot {Y : Type} [Group Y] (hO : GLAPPrimeCore 3 Y = ⊥) :
    GLAPPrimeCore 3 ↥(⊤ : Subgroup Y) = ⊥ := by
  refine le_bot_iff.1 (sSup_le ?_)
  rintro N ⟨hN, hcop⟩
  have hN' : (N.map (Subgroup.topEquiv (G := Y)).toMonoidHom).Normal :=
    Subgroup.Normal.map hN _ (Subgroup.topEquiv (G := Y)).surjective
  have hc : Nat.Coprime 3 (Nat.card (N.map (Subgroup.topEquiv (G := Y)).toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective (Subgroup.topEquiv (G := Y)).injective]
    exact hcop
  have hle : N.map (Subgroup.topEquiv (G := Y)).toMonoidHom ≤ GLAPPrimeCore 3 Y :=
    le_sSup ⟨hN', hc⟩
  rw [hO] at hle
  intro n hn
  have h1 := hle ⟨n, hn, rfl⟩
  rw [Subgroup.mem_bot] at h1 ⊢
  exact (Subgroup.topEquiv (G := Y)).injective (by simpa using h1)

theorem center_ne_bot_of_comp_top {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) (hO : GLAPPrimeCore 3 Y = ⊥)
    (hZ : Subgroup.center Y ≠ ⊥) {S : Subgroup Y} (hS : GLAPComponent 3 (⊤ : Subgroup Y) S) :
    Subgroup.center (barOf 3 S) ≠ ⊥ := by
  have hOt := glaPPrimeCore_top_eq_bot hO
  have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup Y) :=
    isQuasisimple_open_of_mulEquiv Subgroup.topEquiv hY
  obtain ⟨-, comp, -⟩ := layer_of_normal_quasisimple (F := (⊤ : Subgroup Y))
    (S := (⊤ : Subgroup Y)) le_rfl (commutator_le_self _) (fun a _ => ⟨0, by simp⟩) hq hOt
  have hST : S = ⊤ := (comp S).1 hS
  subst hST
  intro hc
  apply hZ
  have e : barOf 3 (⊤ : Subgroup Y) ≃* Y := (barEquivOfCore hOt).symm.trans Subgroup.topEquiv
  exact center_eq_bot_of_mulEquiv' e.symm hc

theorem false_of_comp_of_solvable {Y : Type} [Group Y] [Finite Y] {X S : Subgroup Y}
    (hX : Group.IsSolvable ↥X) (hS : GLAPComponent 3 X S) : False := by
  have hSX : Group.IsSolvable ↥S :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hS.1)
      (Subgroup.inclusion_injective hS.1)
  have hQ : Group.IsSolvable (barOf 3 S) := inferInstanceAs (Group.IsSolvable (↥S ⧸ _))
  exact false_of_quasisimple_of_solvable (isQuasisimple_quotient_of_glaPComponent hS) hQ

theorem isSolvable_fixSub_of_descend {Y : Type} [Group Y] (α : MulAut Y)
    (h : Group.IsSolvable ↥(fixSub (centerDescend Y α))) : Group.IsSolvable ↥(fixSub α) := by
  let φ : ↥(fixSub α) →* ↥(fixSub (centerDescend Y α)) :=
    { toFun := fun y => ⟨(y : Y), by
        rw [mem_fixSub, centerDescend_mk, mem_fixSub.1 y.2]⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine CFSG.Quasithin.isSolvable_of_ker_le_center φ ?_
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have h1 : (QuotientGroup.mk (y : Y) : Y ⧸ Subgroup.center Y) = 1 :=
    congrArg Subtype.val hy
  have h2 : (y : Y) ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff _).1 h1
  rw [Subgroup.mem_center_iff] at h2 ⊢
  intro g
  exact Subtype.ext (h2 g)

end CFSG.HardMathSupport.Solomon.Coordinator
