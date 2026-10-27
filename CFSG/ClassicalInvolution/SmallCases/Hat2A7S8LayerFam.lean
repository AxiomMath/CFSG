module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8LayerRes
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8LayerCol
public import CFSG.ClassicalInvolution.Uniform.UTwinSolv

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7S8.Asc77.T8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement

section Hyp

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

structure LayerHyp (Ω : Set (Subgroup G)) (x : G) : Prop where
  gen : HypOmegaGen Ω
  cls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u
  below : Hat2A7.CITBelow2A7 (Nat.card G)
  sq : x * x = 1
  nc : ¬ ({x} : Set G) ⊆ Subgroup.center G

theorem not_central_of_ne_one [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hx1 : x ≠ 1) :
    ¬ ({x} : Set G) ⊆ Subgroup.center G := by
  intro hc
  have hxc : x ∈ Subgroup.center G := hc rfl
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
  · rw [h] at hxc
    exact hx1 (by simpa using hxc)
  · obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

theorem cenZ_ne_top (hnc : ¬ ({x} : Set G) ⊆ Subgroup.center G) : cenZ x ≠ ⊤ := by
  rw [cenZ_eq_centralizer]
  exact fun h => hnc (Subgroup.centralizer_eq_top_iff_subset.mp h)

theorem card_lt_of_le_cenZ (hnc : ¬ ({x} : Set G) ⊆ Subgroup.center G) {H : Subgroup G}
    (hH : H ≤ cenZ x) : Nat.card H < Nat.card G := by
  have h1 : Nat.card H ≤ Nat.card ↥(cenZ x) := Subgroup.card_le_of_le hH
  have h3 := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr (cenZ_ne_top hnc))
  rw [Subgroup.card_top] at h3
  omega

end Hyp

section Fam

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {Λ : Set (Subgroup G)}

abbrev famJoin (Λ : Set (Subgroup G)) : Subgroup G := ⨆ L ∈ Λ, L

structure LayerFam (Ω : Set (Subgroup G)) (x : G) (Λ : Set (Subgroup G)) : Prop where
  sub : Λ ⊆ layerSet Ω x
  nonempty : Λ.Nonempty
  inv : ∀ c ∈ cenZ x, ∀ L ∈ Λ, conjSub c L ∈ Λ

omit [Finite G] in
theorem le_famJoin {L : Subgroup G} (hL : L ∈ Λ) : L ≤ famJoin Λ :=
  le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ Λ) => L) L hL

theorem LayerFam.layerSet (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : XMem Ω x K) :
    LayerFam Ω x (layerSet Ω x) where
  sub := fun _ h => h
  nonempty := ⟨layerRes x K, K, hK, rfl⟩
  inv := fun _ hc _ hL => layerSet_conj hΩ hL hc

variable (hF : LayerFam Ω x Λ)
include hF

theorem LayerFam.famJoin_le_cenZ : famJoin Λ ≤ cenZ x :=
  iSup₂_le fun _ hL => layerSet_le_cenZ (hF.sub hL)

theorem LayerFam.conjSub_famJoin {n : G} (hn : n ∈ cenZ x) :
    conjSub n (famJoin Λ) = famJoin Λ := by
  have key : ∀ d ∈ cenZ x, conjSub d (famJoin Λ) ≤ famJoin Λ := by
    intro d hd
    rw [conjSub, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_famJoin (hF.inv d hd L hL)
  refine le_antisymm (key n hn) ?_
  have h := conjSub_mono (n := n) (key n⁻¹ ((cenZ x).inv_mem hn))
  rwa [conjSub_conjSub_inv] at h

theorem LayerFam.card_famJoin_lt (hnc : ¬ ({x} : Set G) ⊆ Subgroup.center G) :
    Nat.card (famJoin Λ) < Nat.card G :=
  card_lt_of_le_cenZ hnc hF.famJoin_le_cenZ

theorem LayerFam.cls (hL : LayerHyp Ω x) :
    ∀ L ∈ Λ, ∃ u : G, Hat2A7.IsClassical2A7 (cenZ x) L u := by
  intro L hLΛ
  obtain ⟨K, hK, rfl⟩ := hF.sub hLΛ
  obtain ⟨z, -, hzc, -⟩ := XMem.exists_data hL.gen hL.cls hL.sq hK
  exact ⟨z, XMem.isClassical2A7 hL.gen hL.sq hK hzc⟩

theorem LayerFam.system (hL : LayerHyp Ω x) :
    Hat2A7.A7SystemMod (Hat2A7.restrictTo Λ (famJoin Λ)) :=
  Hat2A7.a7SystemMod_of_lt hL.below hF.famJoin_le_cenZ (hF.card_famJoin_lt hL.nc) hF.nonempty rfl
    (fun y hy L hLΛ => hF.inv y (hF.famJoin_le_cenZ hy) L hLΛ) (hF.cls hL)

theorem LayerFam.images_eq_or_commute (hL : LayerHyp Ω x) {L M : Subgroup G} (hLΛ : L ∈ Λ)
    (hMΛ : M ∈ Λ) :
    (L.subgroupOf (famJoin Λ)).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(famJoin Λ))) =
        (M.subgroupOf (famJoin Λ)).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(famJoin Λ))) ∨
      ∀ a ∈ L, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf (famJoin Λ) :=
  Hat2A7.images_eq_or_commute_of_system (hF.system hL) rfl hLΛ hMΛ

theorem LayerFam.commutator_mem_oddCoreOf (hL : LayerHyp Ω x) {L : Subgroup G} (hLΛ : L ∈ Λ)
    {u : G} (huL : u ∈ L) (hu : ∀ a ∈ L, a * u = u * a) {y : G} (hy : y ∈ famJoin Λ) :
    u * y * u⁻¹ * y⁻¹ ∈ oddCoreOf (famJoin Λ) :=
  Hat2A7.commutator_mem_oddCoreIn_of_system (hF.system hL) rfl hLΛ huL hu hy

end Fam

end CFSG.ClassicalInvolution.Hat2A7S8.Asc77.T8
