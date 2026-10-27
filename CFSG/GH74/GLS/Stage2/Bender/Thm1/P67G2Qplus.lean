module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ThetaCore
public import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusInnerActor
public import CFSG.RankThree.PartOne.KGD.G2ThreeQPlusI
public import CFSG.RankThree.PartOne.KGD.PlaneBridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.Chevalley CFSG.LieType.Ree

theorem g2_false_of_qplus {p f r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = p ^ f) (hr : r.Prime) (hr3 : 3 < r)
    (hrq : r ∣ Nat.card K + 1) {V Z : Subgroup (MulAut (adjointGroup Tag.G2 K))}
    (h2 : N2Cfg (adjointGroup Tag.G2 K) r V Z) (h3 : N3Full (adjointGroup Tag.G2 K) V Z)
    (hinn : ∀ v ∈ V, v ∈
      (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range) :
    False := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hcen : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨-, -, hVe, hVc, -⟩ := id h2
  have := hVe
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP K ReeTag.G2.prime := finite_field_prime_power_characteristic hp hf hK
    exact false_of_autThetaT_eq_bot hcen h2 h3 hinn
      (autThetaT_eq_bot_of_qplus_three hf K hK hr hr3 hrq _ (conj_range_le_planeOverGroup V Z) V
        hVe hVc (fun v hv => hinn v hv))
  · set B := planeOverGroup (adjointGroup Tag.G2 K) V Z with hB
    have hVB : V ≤ B := V_le_planeOverGroup V Z
    have hE : IsElementaryAbelian r (V.subgroupOf B) := isElementaryAbelian_subgroupOf hVB hVe
    have hEcard : Nat.card (V.subgroupOf B) = r ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVB).toEquiv]
      exact hVc
    obtain ⟨t, htV, ht1⟩ : ∃ t ∈ V, t ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : V = ⊥ := by
        rw [eq_bot_iff]
        intro v hv
        exact Subgroup.mem_bot.2 (hcon v hv)
      rw [hbot, Subgroup.card_bot] at hVc
      have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hr.one_lt
      omega
    have h := odd_G2_qplus_inner_actor_local_core_product_odd hp hp2 hp3 hf K hK hr hr3 hrq B
      (conj_range_le_planeOverGroup V Z) (V.subgroupOf B) hE hEcard ⟨t, hVB htV⟩
      (Subgroup.mem_subgroupOf.2 htV) (fun h => ht1 (congrArg Subtype.val h)) (hinn t htV)
    exact false_of_thetaT_eq_bot hcen h2 h3 hinn h.1

end CFSG.GH74.GLS.Stage2.Bender.Thm1
