module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGKind2Cover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGKind2E0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CLayer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem fg_kind2_layer_map (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (hφ : IsCoverMap L φ)
    {s : G} (hs2 : s * s = 1) {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ}
    (hty : invType g = (1, α)) (hact : CoverAct L φ s (orthToSim Q g)) :
    (CFSG.layer ↥(L ⊓ centralizer ({s} : Set G))).map (FGKind2Rho hact) =
      FGKind2E0 hQ hgg := by
  have hlie := fg_kind2_E0_lieModel hQ hφ.finrank_eq hgg hty
  obtain ⟨hsE, hnc⟩ := ff_simple_of_lieModel_psp hlie
  have hev : 2 ∣ Nat.card ↥(FGKind2E0 hQ hgg) := by rw [ff_card_model_psp hlie]; norm_num
  exact a6c_cover_layer_map (fg_kind2_rho_oddCentralCover hL hφ hs2 hact) (FGKind2E0 hQ hgg) hsE
    hnc hev (fg_kind2_E0_isPGroup_quotient hQ hgg hty)

theorem fg_kind2_chi_layer (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (hφ : IsCoverMap L φ)
    {s : G} (hs2 : s * s = 1) {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ}
    (hty : invType g = (1, α)) (hact : CoverAct L φ s (orthToSim Q g))
    {x : ↥(L ⊓ centralizer ({s} : Set G))} (hx : x ∈ CFSG.layer ↥(L ⊓ centralizer ({s} : Set G))) :
    FGKind2Chi hQ hgg (FGKind2Rho hact x) = 1 := by
  have hmem : FGKind2Rho hact x ∈ (CFSG.layer ↥(L ⊓ centralizer ({s} : Set G))).map
      (FGKind2Rho hact) := Subgroup.mem_map_of_mem _ hx
  rw [fg_kind2_layer_map hL hφ hs2 hgg hty hact] at hmem
  exact fg_kind2_chi_eq_one_of_mem_E0 hQ hgg hmem

theorem fg_kind2_chi_central (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (hφ : IsCoverMap L φ)
    {s : G} {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ} (hty : invType g = (1, α))
    (hact : CoverAct L φ s (orthToSim Q g)) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2)
    (htC : t ∈ L ⊓ centralizer ({s} : Set G)) :
    FGKind2Chi hQ hgg (FGKind2Rho hact ⟨t, htC⟩) ≠ 1 := by
  have hπ := hφ.map_central hL ht ht2 (Subgroup.mem_inf.mp htC).1
  have hval : ((FGKind2Rho hact ⟨t, htC⟩ : ↥(FGKind2D hQ g)) : OGroup Q) = piOrth Q := hπ
  have hmem : piOrth Q ∈ FGKind2D hQ g := hval ▸ (FGKind2Rho hact ⟨t, htC⟩).2
  have heq : FGKind2Rho hact ⟨t, htC⟩ = ⟨piOrth Q, hmem⟩ := Subtype.ext hval
  have hcdim : Module.finrank (ZMod 3) (commSp g) = 1 := congrArg Prod.fst hty
  rw [heq]
  exact fg_kind2_chi_piOrth_ne_one hQ hgg hmem (by omega)

theorem fg_kind2_mem_layer_of_chi (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ}
    (hφ : IsCoverMap L φ) {s : G} (hs2 : s * s = 1) {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ}
    (hty : invType g = (1, α)) (hact : CoverAct L φ s (orthToSim Q g))
    {x : ↥(L ⊓ centralizer ({s} : Set G))} (hxx : x * x = 1)
    (hχ : FGKind2Chi hQ hgg (FGKind2Rho hact x) = 1) :
    x ∈ CFSG.layer ↥(L ⊓ centralizer ({s} : Set G)) := by
  have hρx : FGKind2Rho hact x * FGKind2Rho hact x = 1 := by rw [← map_mul, hxx, map_one]
  have hE0 : FGKind2Rho hact x ∈ FGKind2E0 hQ hgg :=
    fg_kind2_mem_E0_of_involution hQ hgg hρx hχ
  rw [← fg_kind2_layer_map hL hφ hs2 hgg hty hact] at hE0
  obtain ⟨e, he, hex⟩ := Subgroup.mem_map.mp hE0
  have hpow := (fg_kind2_rho_oddCentralCover hL hφ hs2 hact).pow_card_ker_eq hxx hex
  rw [← hpow]
  exact Subgroup.pow_mem _ he _

private theorem fg_kind2_zpow_of_sq {H : Type*} [Group H] {u : H} (hu : u * u = 1) (k : ℤ) :
    u ^ k = 1 ∨ u ^ k = u := by
  have hu2 : u ^ 2 = 1 := by rw [pow_two]; exact hu
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [hm, zpow_mul]
    simp [hu2]
  · right
    rw [hm, zpow_add, zpow_mul]
    simp [hu2]

theorem fg_kind2_split_of_cover (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ}
    (hφ : IsCoverMap L φ) {s : G} (hs2 : s * s = 1) {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ}
    (hty : invType g = (1, α)) (hact : CoverAct L φ s (orthToSim Q g)) {t : G}
    (ht : t ∈ centerIn L) (ht2 : orderOf t = 2) {B : Subgroup G}
    (hB : B ≤ L ⊓ centralizer ({s} : Set G)) (hB2 : ∀ b ∈ B, b * b = 1) (htB : t ∈ B) :
    zpowers t ⊓ layerCent L s = ⊥ ∧ B = zpowers t ⊔ (B ⊓ layerCent L s) := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have htC : t ∈ L ⊓ centralizer ({s} : Set G) := hB htB
  have hcdim : Module.finrank (ZMod 3) (commSp g) = 1 := congrArg Prod.fst hty
  have hord2 : Nat.card (OGroup (Q.restrict (commSp g))) = 2 :=
    natCard_oGroup_one (nondegenerate_restrict_commSp hQ hgg) hcdim
  have hχt := fg_kind2_chi_central hL hφ hgg hty hact ht ht2 htC
  have hlc : ∀ (x : G) (hx : x ∈ L ⊓ centralizer ({s} : Set G)), x ∈ layerCent L s ↔
      (⟨x, hx⟩ : ↥(L ⊓ centralizer ({s} : Set G))) ∈
        CFSG.layer ↥(L ⊓ centralizer ({s} : Set G)) := by
    intro x hx
    unfold layerCent CFSG.inSubgroup
    constructor
    · intro h
      obtain ⟨e, he, hex⟩ := Subgroup.mem_map.mp h
      have : e = ⟨x, hx⟩ := Subtype.ext hex
      rwa [this] at he
    · intro h
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, h, rfl⟩
  constructor
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxt, hxl⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxt
    rcases fg_kind2_zpow_of_sq htt k with hk | hk
    · rw [hk]
      exact Subgroup.one_mem _
    · exfalso
      rw [hk] at hxl
      exact hχt (fg_kind2_chi_layer hL hφ hs2 hgg hty hact ((hlc t htC).mp hxl))
  · apply le_antisymm
    · intro b hb
      have hbC : b ∈ L ⊓ centralizer ({s} : Set G) := hB hb
      by_cases hχ : FGKind2Chi hQ hgg (FGKind2Rho hact ⟨b, hbC⟩) = 1
      · have hl := fg_kind2_mem_layer_of_chi hL hφ hs2 hgg hty hact
          (x := ⟨b, hbC⟩) (Subtype.ext (hB2 b hb)) hχ
        exact Subgroup.mem_sup_right ⟨hb, (hlc b hbC).mpr hl⟩
      · have hu : b * t ∈ B := Subgroup.mul_mem _ hb htB
        have huC : b * t ∈ L ⊓ centralizer ({s} : Set G) := hB hu
        have hχu : FGKind2Chi hQ hgg (FGKind2Rho hact ⟨b * t, huC⟩) = 1 := by
          have hmul : (⟨b * t, huC⟩ : ↥(L ⊓ centralizer ({s} : Set G))) =
              ⟨b, hbC⟩ * ⟨t, htC⟩ := rfl
          rw [hmul, map_mul, map_mul]
          exact fg_kind2_mul_eq_one_of_ne_one hord2 hχ hχt
        have hl := fg_kind2_mem_layer_of_chi hL hφ hs2 hgg hty hact
          (x := ⟨b * t, huC⟩) (Subtype.ext (hB2 (b * t) hu)) hχu
        have hmem : b * t ∈ B ⊓ layerCent L s := ⟨hu, (hlc _ huC).mpr hl⟩
        have hbeq : b = (b * t) * t⁻¹ := by group
        rw [hbeq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmem)
          (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)))
    · exact sup_le (Subgroup.zpowers_le.mpr htB) inf_le_left

end CFSG.OddStandard.SmallF3.Omega
