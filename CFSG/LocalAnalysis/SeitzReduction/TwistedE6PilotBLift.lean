module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotBLiftBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotBLift
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.C2E6Std
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift)

section Odd

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem odd_card_thetaTorus (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) :
    Odd (Nat.card (thetaTorus (algebraMap k K))) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hodd : Odd (Nat.card kˣ) := by
    rw [Nat.card_units, hk]
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    obtain ⟨m, hm⟩ := h2
    rw [Nat.odd_iff]
    omega
  exact hodd.of_dvd_nat (Subgroup.card_range_dvd _)

end Odd

section SettingX

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem forall_odd_mem_2E6_X (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = (((thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hLt := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hK' := inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht
  have hXo : Odd (Nat.card X) := by
    rw [hX, card_map_symm_subgroupOf (thetaTorus_le_C0 hf hk hK hσ)]
    exact odd_card_thetaTorus hf hk
  have hAut : ∀ β : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
      (∀ x ∈ (thetaTorus (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ),
        β x = x) →
      (∀ x ∈ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), β x = x) →
      ∃ w ∈ (thetaTorus (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ),
        β = MulAut.conj w := fun β hβX hβD => by
    obtain ⟨w, hw, hβw⟩ := exists_eq_conj_of_fix_su6Levi hf2 hk hK hσ β
      (fun x hx => hβX x (mem_subgroupOf.2 hx)) (fun x hx => hβD x (mem_subgroupOf.2 hx))
    exact ⟨w, mem_subgroupOf.2 hw, hβw⟩
  intro c hc hco
  subst hX hDe
  exact mem_of_forall_fix_fix_eq_conj htC ht hLt hK' hXo (forall_eq_conj_map_symm e hAut)
    hc.1.1 hc.1.2 hc.2 hco

theorem hasBLift_2E6_X (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = (((thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hE : ⁅E, E⁆ = E)
    (htE : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hEt : E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆) :
    HasBLift E := by
  obtain ⟨hD, hDq⟩ := neighbour_layer_2E6_X hf2 hk hK hσ e hX hDe
  exact LinearPilot.hasBLift_of_forall_odd_mem htC ht
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht)
    htX hD hDq (forall_odd_mem_2E6_X hset hf2 hk hK hσ e htC ht hX hDe) hE htE hEt

theorem hasBLift_sup_conj_2E6_X (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = (((thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kb : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKb : ⁅Kb, Kb⁆ = Kb)
    (hcomm : ⁅Kb, Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥) :
    HasBLift (Kb ⊔ Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom) ∧
      HasBLift Kb := by
  obtain ⟨hD, hDq⟩ := neighbour_layer_2E6_X hf2 hk hK hσ e hX hDe
  exact LinearPilot.hasBLift_sup_conj_of_forall_odd_mem htC ht
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht)
    htX hD hDq (forall_odd_mem_2E6_X hset hf2 hk hK hσ e htC ht hX hDe) hKb hcomm

end SettingX

end CFSG.SeitzReduction.TwistedE6Pilot
