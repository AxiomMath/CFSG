module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E2Ord
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E8Exi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D5Model
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma zpowers_inf_eq_bot_of_notMem {G : Type} [Group G] {t : G} {C : Subgroup G}
    (ht : t ∉ C) (hcard : Nat.card ↥(zpowers t) = 2) : zpowers t ⊓ C = ⊥ := by
  haveI : Fact (Nat.card ↥(zpowers t)).Prime := ⟨by rw [hcard]; exact Nat.prime_two⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (C.subgroupOf (zpowers t)) with h | h
  · have hd : Disjoint C (zpowers t) := Subgroup.subgroupOf_eq_bot.mp h
    rw [Subgroup.disjoint_def] at hd
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    exact hd hx.2 hx.1
  · exact absurd ((Subgroup.subgroupOf_eq_top.mp h) (Subgroup.mem_zpowers t)) ht

theorem sec8t84_card_sup_le {G : Type} [Group G] [Finite G] {t : G} {P : Subgroup G}
    (ht : orderOf t = 2) (hcomm : ∀ x ∈ P, x * t = t * x) :
    Nat.card ↥(zpowers t ⊔ P) ≤ 2 * Nat.card ↥P := by
  by_cases htP : t ∈ P
  · rw [sup_eq_right.mpr (Subgroup.zpowers_le.mpr htP)]
    haveI : Nonempty ↥P := ⟨⟨1, P.one_mem⟩⟩
    have := Nat.card_pos (α := ↥P)
    omega
  · have hcard2 : Nat.card ↥(zpowers t) = 2 := by rw [Nat.card_zpowers]; exact ht
    have hbot : zpowers t ⊓ P = ⊥ := zpowers_inf_eq_bot_of_notMem htP hcard2
    have hc : ∀ a ∈ zpowers t, ∀ b ∈ P, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hbt : Commute b t := (commute_iff_eq b t).mpr (hcomm b hb)
      exact (hbt.symm.zpow_left k).eq
    rw [sec124_card_sup hc hbot, hcard2]

theorem sec8t84_T_data {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G}
    {B E : Subgroup G} (hE : Sec8E G t L S z g B E) (hCE : Asc82FinkCE)
    (hAut : Asc82FinkAut) (h89 : Asc82Lemma89) (hLM : IsOm6M L)
    (hP : IsSylow2Of (S ⊓ L) L) (hleft : S = zpowers t ⊔ (S ⊓ L)) :
    ∃ T : Subgroup G, IsSylow2Of T (normalizer (E : Set G)) ∧ t ∈ T ∧
      IsSylow2Of (T ⊓ centralizer ({t} : Set G)) (centralizer ({t} : Set G)) := by
  have ht : orderOf t = 2 := hE.ctx.involution
  have htX : t ∈ normalizer (E : Set G) := Subgroup.mem_normalizer_fintype hE.t_norm
  have htC : t ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzpY : zpowers t ≤ normalizer (E : Set G) ⊓ centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr ⟨htX, htC⟩
  have hzp2 : IsPGroup 2 (zpowers t : Subgroup G) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨R, hR, hzpR⟩ := exists_isSylow2Of_ge hzp2 hzpY
  have hcardR : Nat.card ↥R = 2 ^ 8 := sec8t84_cent_order hE hCE hAut h89 hR
  obtain ⟨T, hT, hRT, hTC⟩ := sec8t84_exists_T hR
  have hcardS : Nat.card S ≤ 2 ^ 8 := by
    have hcommSL : ∀ x ∈ S ⊓ L, x * t = t * x := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hE.ctx.toSec3SettingLB.component.le hx.2)
    rw [hleft]
    calc Nat.card ↥(zpowers t ⊔ (S ⊓ L))
        ≤ 2 * Nat.card ↥(S ⊓ L) := sec8t84_card_sup_le ht hcommSL
      _ = 2 * 2 ^ 7 := by rw [(sec8t84_sylow_model hLM hP).1]
      _ = 2 ^ 8 := by norm_num
  have hRsyl : IsSylow2Of R (centralizer ({t} : Set G)) := by
    have hRC : R ≤ centralizer ({t} : Set G) := hR.1.trans inf_le_right
    have hcardC2 : 2 ^ (Nat.card (centralizer ({t} : Set G))).factorization 2 = Nat.card S :=
      ((isSylow2Of_iff_ci.1 hE.ctx.sylow).card_eq).symm
    refine isSylow2Of_iff_ci.2 (CFSG.ClassicalInvolution.isSylow2Of_of_card hRC hR.2.1 ?_)
    rw [hcardC2, hcardR]
    exact hcardS
  exact ⟨T, hT, hRT (hzpR (Subgroup.mem_zpowers t)), by rw [hTC]; exact hRsyl⟩

end CFSG.OddStandard.SmallF3.Omega
