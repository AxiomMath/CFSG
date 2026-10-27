module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotOuterFusionModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPosition

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.OuterAutomorphisms

theorem outerFusionTwoCentral {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    OuterFusionTwoCentral L t := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have hf1 : 1 ≤ f := by omega
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨5, derivedSeries_outer_eq_bot_of_mulEquiv e
      ((exceptional_ordinary_small_rank_Schreier .F4 K).2 (Or.inl rfl))⟩⟩
  have hZ : center L = ⊥ := center_eq_bot_congr e.symm center_adjointGroup_eq_bot
  exact outerFusionTwoCentral_of_twoCentralTwistedFusion hset hOut hZ
    (exists_perfect_le_of_mulEquiv e factF1 (factF3Perfect hq) (factF4b hq)) e
    (fun α hα hαo => by
      obtain ⟨ψ, hψ, -⟩ := even_F4_all_outer_involutions_canonical hf1 K hK α hα hαo
      exact ⟨ψ, hψ⟩)
    (twoCentralTwistedFusion_of_two_le hf K hK) ht hKt

theorem not_normal_map_oddCore_torusLineR_of_two_le {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hX : X = (((torusLineR K).subgroupOf (adjointGroup .F4 K)).map
      e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal :=
  not_normal_map_oddCore_torusLineR hset hf hK e ht hKt
    (outerFusionTwoCentral hset hf K hK e ht hKt) hX hDe

end CFSG.SeitzReduction.F4Pilot
