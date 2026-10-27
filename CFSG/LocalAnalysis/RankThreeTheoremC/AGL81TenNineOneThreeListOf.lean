module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeShapeProd
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
public import CFSG.LocalAnalysis.AGLEmbedding.G28Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCore
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeCfgHolds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open TenNineOneThree (IsWClosed)
open Subgroup

@[expose] def IsCaseIThreeG28 (Y : Type*) [Group Y] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsGTwoEightIndex d ∧
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def KFactG28RankNotNineFour : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B), IsCaseIThreeG28 K →
    2 ≤ Open.pRank 3 K ∧ ¬ NineFourListGroup 3 K

variable (G : Type) [Group G] [Finite G]

variable {G}

namespace TenNineOneThree

section Prod

variable {B : Type} [Group B] [Finite B]

theorem not_isSimpleGroup_of_isCaseIThreeProd {K : Subgroup B} (h : IsCaseIThreeProd K) :
    ¬ IsSimpleGroup K := by
  intro hs
  haveI := hs
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  set Gq := (TauCeti.CFSGIndex.lie d).Group
  have hG : IsCaseTwoGroup 3 Gq := ⟨d, Or.inl ⟨rfl, hd⟩, ⟨MulEquiv.refl _⟩⟩
  haveI : Finite Gq := Finite.of_injective (fun g : Gq => e.symm (g, 1)) fun a b h => by
    simpa using congrArg Prod.fst (e.symm.injective h)
  obtain ⟨x, hx⟩ := L28Sq.exists_ne_one hG
  set N := ((MonoidHom.snd Gq Gq).comp e.toMonoidHom).ker
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · have hm : e.symm (x, 1) ∈ N := MonoidHom.mem_ker.mpr (by simp)
    rw [h, Subgroup.mem_bot] at hm
    exact hx (by simpa using congrArg Prod.fst (congrArg e hm))
  · have hm : e.symm (1, x) ∈ N := h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hm
    exact hx (by simpa using hm)

theorem two_le_pRank_of_isCaseIThreeProd {K : Subgroup B} (h : IsCaseIThreeProd K) :
    2 ≤ Open.pRank 3 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  set Gq := (TauCeti.CFSGIndex.lie d).Group
  have hG : IsCaseTwoGroup 3 Gq := ⟨d, Or.inl ⟨rfl, hd⟩, ⟨MulEquiv.refl _⟩⟩
  haveI : Finite Gq := Finite.of_injective (fun g : Gq => e.symm (g, 1)) fun a b h => by
    simpa using congrArg Prod.fst (e.symm.injective h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3
    (by rw [L28Sq.card_eq hG]; norm_num : 3 ∣ Nat.card Gq)
  set Z := Subgroup.zpowers x
  have hZ : ∀ a b : Z, a * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact Subtype.ext (Commute.zpow_zpow_self x i j).eq
  have hZ3 : ∀ a : Z, a ^ 3 = 1 := by
    rintro ⟨a, ha⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    apply Subtype.ext
    change (x ^ i) ^ 3 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx,
      pow_orderOf_eq_one, one_zpow]
  set f : Z × Z →* B :=
    K.subtype.comp (e.symm.toMonoidHom.comp (Z.subtype.prodMap Z.subtype)) with hf
  have hfi : Function.Injective f := by
    refine K.subtype_injective.comp (e.symm.injective.comp ?_)
    rintro ⟨a, b⟩ ⟨c, d⟩ hab
    have h1 := congrArg Prod.fst hab
    have h2 := congrArg Prod.snd hab
    simp at h1 h2
    exact Prod.ext h1 h2
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num)
    (fun a b => Prod.ext (hZ _ _) (hZ _ _)) (fun a => Prod.ext (hZ3 _) (hZ3 _)) ?_ f hfi ?_
  · rw [Nat.card_prod, Nat.card_zpowers, hx]
    norm_num
  · rintro _ ⟨y, rfl⟩
    exact (e.symm _).2

theorem not_nineFourListGroup_of_isCaseIThreeProd {K : Subgroup B} (h : IsCaseIThreeProd K) :
    ¬ NineFourListGroup 3 K := fun hl => not_isSimpleGroup_of_isCaseIThreeProd h hl.1

end Prod

theorem nineThreeListGroup_of_cfg (h9 : AGL81NineCompetitorQ G) (hS : Setting G) {p : ℕ}
    {P : Sylow p G} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) : NineThreeListGroup p K := by
  have hk := hd.kbar
  subst hk
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hne : d1KBar p M H ≠ ⊥ := fun h => hd.not_le_X0 (by rw [h]; exact bot_le)
  exact (h9 (aglGlobal_of_setting hS) p P M H (muAt_of_escape hesc) hd.maxH hd.not_le
    (exists_component_of_d1KBar_ne_bot hne) Q H hd.base hd.le_H hd.maxH hd.not_le hd.le_H
    (aglCovers_self H _)).1.list hne

theorem not_hasPrimeConstraint_of_cfg {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) : ¬ HasPrimeConstraint (G := H) p := by
  have hne : d1KBar p M H ≠ ⊥ := fun h => hd.not_le_X0 (by rw [hd.kbar, h]; exact bot_le)
  obtain ⟨L, hL, -⟩ := exists_component_of_d1KBar_ne_bot hne
  exact not_hasPrimeConstraint_of_component hL

theorem not_three_dvd_card_plusCore (h94 : AGL81NineFourCfg G) (hS : Setting G)
    {P : Sylow 3 G} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hd : AGL81CfgData 3 P M H Q K) (h2 : 2 ≤ Open.pRank 3 K) (hn : ¬ NineFourListGroup 3 K) :
    ¬ 3 ∣ Nat.card (d1PlusCore 3 H K) := by
  intro h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Open.pRank 3 (d1PlusCore 3 H K) ≤ 1 :=
    agl81NineThreeRankCfg_holds hS 3 P M H Q K hd
  have hge : 1 ≤ Open.pRank 3 (d1PlusCore 3 H K) := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hx' : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
    refine CFSG.SectionRank.le_pRank (by norm_num) (E := Subgroup.zpowers (x : G)) ?_
      (CFSG.Open.isElemAbelian_zpowers
        (by have h := pow_orderOf_eq_one (x : G); rwa [hx'] at h)) ?_
    · rw [Subgroup.zpowers_le]
      exact x.2
    · rw [Nat.card_zpowers, hx', pow_one]
  exact hn (h94 hS 3 P M H Q K hd (not_hasPrimeConstraint_of_cfg hd) h2 (le_antisymm hle hge))

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
