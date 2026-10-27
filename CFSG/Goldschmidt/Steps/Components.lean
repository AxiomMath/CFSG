module

import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
import CFSG.Milestones.OO_odd_order_solvable
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.CommutingComponentFamily
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification

theorem N8a :
    ∀ (G : Type) [Group G] [Finite G] (L H : Subgroup G), IsComponentOf L ⊤ →
      CFSG.Open.IsSubnormal H ⊤ → L ≤ H ∨ ⁅L, H⁆ = ⊥ := fun _ _ _ L H hL hH =>
  LocalComponents.subnormal_contains_or_commutes L H hL hH

theorem N8b :
    ∀ (G : Type) [Group G] [Finite G] (K L : Subgroup G), IsComponentOf K ⊤ → IsComponentOf L ⊤ →
      K ≠ L → ⁅K, L⁆ = ⊥ := fun _ _ _ K L hK hL hne => LocalComponents.commute_of_ne K L hK hL hne

theorem N8c :
    ∀ (G : Type) [Group G] [Finite G] (L N : Subgroup G), IsComponentOf L ⊤ → N.Normal →
      Group.IsSolvable N → ⁅L, N⁆ = ⊥ := fun _ _ _ L N hL hN _ =>
  LocalComponents.commutes_with_solvable_subnormal L N hL
    (Components.chain_of_mathlib_subnormal hN.isSubnormal)

theorem N8d :
    ∀ (G : Type) [Group G] [Finite G], goldschmidtOddCore G = ⊥ →
      (∀ K : Subgroup G, IsComponentOf K ⊤ → IsPGroup 2 (Subgroup.center K)) ∧
      (Subgroup.center (goldschmidtLayer G)).map (goldschmidtLayer G).subtype ≤
        CFSG.Open.pCore 2 G ∧
      Subgroup.centralizer ((CFSG.Open.pCore 2 G ⊔ goldschmidtLayer G : Subgroup G) : Set G) ≤
        CFSG.Open.pCore 2 G ⊔ goldschmidtLayer G := by
  intro G _ _ hO
  have hO' : componentClassificationOddCore G = ⊥ := hO
  have hFit : Fitting.subgroup G = CFSG.Open.pCore 2 G := by
    rw [PrimeCore.fitting_eq_two_of_odd_corefree hO',
      CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup]
    rfl
  have hE : Layer.subgroup G = goldschmidtLayer G := rfl
  have hZE : (Subgroup.center (goldschmidtLayer G)).map (goldschmidtLayer G).subtype ≤
      CFSG.Open.pCore 2 G := by
    rw [← hFit, ← hE]
    exact GeneralizedFitting.layer_center_le_fitting G
  refine ⟨fun K hK => ?_, hZE, ?_⟩
  · have hle : (Subgroup.center K).map K.subtype ≤ CFSG.Open.pCore 2 G := by
      refine le_trans ?_ hZE
      rintro _ ⟨z, hz, rfl⟩
      have hzE : (z : G) ∈ goldschmidtLayer G := Layer.component_le hK z.2
      have hzc := ComponentAutomorphisms.center_le_layer_center K hK
        (Subgroup.mem_map_of_mem K.subtype hz)
      refine ⟨⟨z, hzE⟩, Subgroup.mem_center_iff.mpr fun e => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hzc e e.2
    exact ((CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2).to_le hle).of_equiv
      ((Subgroup.center K).equivMapOfInjective K.subtype K.subtype_injective).symm
  · have h := GeneralizedFitting.centralizer_le G
    rwa [GeneralizedFitting.subgroup, hFit, hE] at h

theorem N8e :
    ∀ (G : Type) [Group G] [Finite G] (Z : Subgroup G) [Z.Normal], Z ≤ Subgroup.center G →
      goldschmidtLayer (G ⧸ Z) = (goldschmidtLayer G).map (QuotientGroup.mk' Z) :=
  fun _ _ _ Z _ hZ =>
  (CentralComponentQuotients.layer_map (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
    (by rw [QuotientGroup.ker_mk']; exact hZ)).symm

theorem N8f :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ α : MulAut K,
      (∀ k : K, α k * k⁻¹ ∈ Subgroup.center K) → α = 1 := fun _ _ _ hK α hα =>
  CFSG.GorensteinWalter.perfect_central_automorphism_eq ⟨hK.1⟩ α 1 (by simpa using hα)

theorem N8g :
    ∀ (Y : Type) [Group Y] [Finite Y] (N : Subgroup Y), N.Normal → IsSimpleGroup N →
      (∃ a b : N, a * b ≠ b * a) → Subgroup.centralizer (N : Set Y) = ⊥ →
      goldschmidtOddCore Y = ⊥ ∧ CFSG.Open.pCore 2 Y = ⊥ ∧ goldschmidtLayer Y = N ∧
      ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = N := by
  intro Y _ _ N hN hsimple hnonab hcent
  have : Group.IsPerfect N := ⟨Helpers.commutator_eq_top N hnonab⟩
  have hNc : IsComponentOf N ⊤ :=
    ⟨le_top, Components.chain_of_mathlib_subnormal hN.isSubnormal,
      Quasisimple.simple_of_perfect N⟩
  have hbot : ∀ H : Subgroup Y, ⁅N, H⁆ = ⊥ → H = ⊥ := fun H h => by
    rw [← le_bot_iff, ← hcent]
    rw [Subgroup.commutator_comm] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hcomp : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = N := by
    intro K hK
    by_contra hne
    have hKbot : K = ⊥ := hbot K (by
      rw [Subgroup.commutator_comm]
      exact LocalComponents.commute_of_ne K N hK hNc hne)
    exact (K.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hK.2.2)) hKbot
  have hsolv : ∀ M : Subgroup Y, M.Normal → Group.IsSolvable M → M = ⊥ := by
    intro M hM _
    exact hbot M (LocalComponents.commutes_with_solvable_subnormal N M hNc
      (Components.chain_of_mathlib_subnormal hM.isSubnormal))
  refine ⟨?_, ?_, ?_, hcomp⟩
  · exact hsolv _ (goldschmidtOddCore_normal Y)
      (CFSG.Milestones.odd_order_solvable (OddCore.odd_card Y))
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup (G := Y) 2).isNilpotent
    exact hsolv _ (CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2) inferInstance
  · exact le_antisymm (sSup_le fun K hK => (hcomp K hK).le) (le_sSup hNc)

theorem N8h :
    ∀ (G : Type) [Group G] [Finite G] (𝒴 : Set (Subgroup G)) (L : Subgroup G),
      (∀ Y₁ ∈ 𝒴, ∀ Y₂ ∈ 𝒴, Y₁ ≠ Y₂ → ⁅Y₁, Y₂⁆ = ⊥) → CFSG.Open.IsSubnormal L (sSup 𝒴) →
      commutator L = ⊤ → CFSG.Open.IsQuasisimple (L ⧸ goldschmidtOddCore L) →
      ∃ Y ∈ 𝒴, L ≤ Y := by
  intro G _ _ 𝒴 L hcomm hsub hperf hqs
  set X := sSup 𝒴 with hXdef
  have hLX : L ≤ X := LBalance.subnormal_le hsub
  have hL'sub : IsSubnormal (L.subgroupOf X) ⊤ := by
    have h := LBalance.subnormal_subgroupOf hsub X
    rwa [Subgroup.subgroupOf_self] at h
  set O := componentClassificationOddCore X with hOdef
  set π := QuotientGroup.mk' O with hπdef
  set K := (L.subgroupOf X).map π with hKdef
  have hK : IsComponentOf K ⊤ :=
    (Components.quotient_component_iff (L.subgroupOf X) hL'sub).mpr
      (TwoComponentTransport.quasisimple_coreQuotient_of_equiv
        (Subgroup.subgroupOfEquivOfLe hLX).symm hqs)
  have hYn : ∀ Y ∈ 𝒴, (Y.subgroupOf X).Normal := fun Y hY =>
    CommutingComponentFamily.factor_normal 𝒴 hcomm Y hY
  obtain ⟨Y, hY, hKY⟩ : ∃ Y ∈ 𝒴, K ≤ (Y.subgroupOf X).map π := by
    by_contra hnone
    push Not at hnone
    have hall : ∀ Y ∈ 𝒴, (Y.subgroupOf X).map π ≤ Subgroup.centralizer (K : Set (X ⧸ O)) := by
      intro Y hY
      have : ((Y.subgroupOf X).map π).Normal :=
        (hYn Y hY).map π (QuotientGroup.mk'_surjective O)
      have h := (LocalComponents.normal_contains_or_commutes K _ hK).resolve_left (hnone Y hY)
      rw [Subgroup.commutator_comm] at h
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hcen : K ≤ Subgroup.center (X ⧸ O) := by
      intro k hk
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O g
      have hle : X ≤ ((Subgroup.centralizer (K : Set (X ⧸ O))).comap π).map X.subtype := by
        refine sSup_le fun Y hY y hy => ?_
        have hyX : y ∈ X := le_sSup hY hy
        exact ⟨⟨y, hyX⟩, hall Y hY ⟨⟨y, hyX⟩, hy, rfl⟩, rfl⟩
      obtain ⟨x', hx', hxx'⟩ := hle x.2
      rw [show x' = x from Subtype.ext hxx'] at hx'
      exact (Subgroup.mem_centralizer_iff.mp hx' k hk).symm
    have : Group.IsPerfect K := ⟨hK.2.2.1⟩
    exact (K.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hK.2.2))
      (Quasisimple.perfect_le_center_eq_bot K hcen)
  have hLY : L.subgroupOf X ≤ Y.subgroupOf X ⊔ O := by
    have h := Subgroup.map_le_iff_le_comap.mp hKY
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
  have := hYn Y hY
  set ρ := QuotientGroup.mk' (Y.subgroupOf X) with hρdef
  have hmap : (L.subgroupOf X).map ρ ≤ O.map ρ := by
    calc (L.subgroupOf X).map ρ ≤ (Y.subgroupOf X ⊔ O).map ρ := Subgroup.map_mono hLY
      _ = O.map ρ := by rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hodd : Odd (Nat.card ((L.subgroupOf X).map ρ)) :=
    (OddCore.odd_card X).of_dvd_nat
      ((Subgroup.card_dvd_of_le hmap).trans (Subgroup.card_map_dvd O ρ))
  have := CFSG.Milestones.odd_order_solvable hodd
  have : Group.IsPerfect L := ⟨hperf⟩
  have : Group.IsPerfect (L.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLX).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have : Group.IsPerfect ((L.subgroupOf X).map ρ) := Group.IsPerfect.map ρ
  have hbot : (L.subgroupOf X).map ρ = ⊥ := by
    by_contra hne
    have : Nontrivial ((L.subgroupOf X).map ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable _ ‹_›
  have hle : L.subgroupOf X ≤ Y.subgroupOf X := by
    have h := (Subgroup.map_eq_bot_iff _).mp hbot
    rwa [QuotientGroup.ker_mk'] at h
  exact ⟨Y, hY, fun x hx => hle (show (⟨x, hLX hx⟩ : X) ∈ L.subgroupOf X from hx)⟩

end CFSG.Goldschmidt
