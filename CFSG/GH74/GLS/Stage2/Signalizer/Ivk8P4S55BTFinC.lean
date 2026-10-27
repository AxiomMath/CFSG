module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinA
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinN
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTCnt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrIdx
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTO2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTLink
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrImg

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools

theorem commutator_subgroupOf_eq {A : Type*} [Group A] {C B : Subgroup A} (hCB : C ≤ B)
    (hC : ⁅C, C⁆ = C) : ⁅C.subgroupOf B, C.subgroupOf B⁆ = C.subgroupOf B := by
  apply Subgroup.map_injective B.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hCB, hC]

theorem cellV_of_finCellA (hL31 : Lemma31Narrow) (hRes : ResB)
    {F : (Y : Type) → [Group Y] → Prop}
    (hF : ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → F Y → FinCellA Y) : CellV F := by
  intro G _ _ z k S T Tstar p H P g X Y h t q I Q₁ hd J hB hFJ
  have hnc := hRes G z k S T Tstar p H P g X Y h t q I Q₁ hd J hB
  obtain ⟨Γ, _, _, V, _, _, _, ρ, K, a, P', hM, -, hL⟩ := hB
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hJ, hJg, _⟩ := hL
  have hs : IsSimpleGroup (↥J ⧸ center ↥J) := hJ.1.2.1
  have hfin := hF _ hs hFJ
  have hp : p.Prime := prime h
  have hp2 : p ≠ 2 := odd h
  have hpf : Fact p.Prime := ⟨hp⟩
  have hgH : g ∈ H := g_mem_H h
  set ν : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hν
  have h3 := no_three_comps hL31 h (z_mem_H h hd.u)
  have hIH : I ≤ H := hd.i.good.le_H
  have hIp : ⁅barIn H I, barIn H I⁆ = barIn H I := by
    have := commutator_map_barIn hIH hd.i.perf (MonoidHom.id (HBar H))
    simpa [Subgroup.map_id] using this
  have hIN : barIn H I ≤ normalizer (J : Set (HBar H)) := perfect_le_normalizer h3 hJ hIp
  have hPN : barIn H P ≤ normalizer (J : Set (HBar H)) := fun x hx => by
    obtain ⟨n, hn⟩ := (map_isPGroup ν (P_pgroup h)) ⟨x, hx⟩
    have hxn : x ^ p ^ n = 1 := congrArg Subtype.val hn
    exact mem_normalizer_of_odd h3 hJ (hp.odd_of_ne_two hp2).pow hxn
  set N : Subgroup (HBar H) := normalizer (J : Set (HBar H)) with hN
  set ψ : ↥N →* MulAut (↥J ⧸ center ↥J) := actJ J with hψ
  have hIperf : ⁅((barIn H I).subgroupOf N).map ψ, ((barIn H I).subgroupOf N).map ψ⁆ =
      ((barIn H I).subgroupOf N).map ψ := by
    rw [← Subgroup.map_commutator, commutator_subgroupOf_eq hIN hIp]
  have hIne : ((barIn H I).subgroupOf N).map ψ ≠ ⊥ := by
    intro hbot
    apply hnc
    intro x hx
    have hxN : x ∈ N := hIN hx
    have h1 : ψ ⟨x, hxN⟩ = 1 := by
      have : ψ ⟨x, hxN⟩ ∈ ((barIn H I).subgroupOf N).map ψ := ⟨⟨x, hxN⟩, hx, rfl⟩
      rw [hbot, mem_bot] at this
      exact this
    exact mem_centralizer_of_actJ_eq_one J hJ.1.1 h1
  have hXp : IsPGroup p ↥(((barIn H P).subgroupOf N).map ψ) :=
    (isPGroup_subgroupOf (map_isPGroup ν (P_pgroup h)) N).map ψ
  have hgP : ν ⟨g, hgH⟩ ∈ barIn H P := ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr (g_mem h), rfl⟩
  have hXne : ((barIn H P).subgroupOf N).map ψ ≠ ⊥ := by
    intro hbot
    apply hJg
    have hgN : ν ⟨g, hgH⟩ ∈ N := hPN hgP
    have h1 : ψ ⟨_, hgN⟩ = 1 := by
      have : ψ ⟨_, hgN⟩ ∈ ((barIn H P).subgroupOf N).map ψ := ⟨⟨_, hgN⟩, hgP, rfl⟩
      rw [hbot, mem_bot] at this
      exact this
    have hgC := mem_centralizer_of_actJ_eq_one J hJ.1.1 h1
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ zpowers g := hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx'
    have hxe : x = (⟨g, hgH⟩ : ↥H) ^ n := Subtype.ext (by rw [Subgroup.coe_zpow, ← hn])
    rw [hxe, map_zpow]
    exact Subgroup.zpow_mem _ hgC n
  have hIX : ((barIn H I).subgroupOf N).map ψ ≤
      normalizer ((((barIn H P).subgroupOf N).map ψ : Subgroup _) : Set (MulAut _)) := by
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    apply mem_normalizer_map_br ψ
    apply mem_normalizer_subgroupOf
    have hx' : x ∈ barIn H I := hx
    obtain ⟨i, hi, rfl⟩ := hx'
    exact mem_normalizer_map_br ν (mem_normalizer_subgroupOf (hd.i.norm_P hi))
  exact hfin p hp hp2 _ _ hXp hXne hIne hIperf hIX

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
