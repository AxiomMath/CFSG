module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Basic
public import CFSG.GH74.GLS.C3.Layer1.St1RigStep
public import CFSG.GH74.GLS.C3.Layer1.Th2Pump
public import CFSG.GH74.Generic.BProg.Assembly
public import CFSG.GH74.Generic.BProg.Helpers
public import CFSG.GH74.Generic.S3.PumpLift

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.GH74.GLS
open CFSG.GH74.GLS.C3.Layer1.PumpCalc
open scoped commutatorElement

theorem isCompIn_of_isILo {G : Type} [Group G] [Finite G]
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {x : G} {K : Subgroup G} (h : IsILo 2 x K) : IsCompIn (centralizer ({x} : Set G)) K := by
  have hK := h.2.2
  exact isComponentIn_of_isPComponent (hbal x h.1) hK.1 hK.2

theorem isQuasisimple_of_isILo {G : Type} [Group G] [Finite G]
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {x : G} {K : Subgroup G} (h : IsILo 2 x K) : IsQuasisimple ↥K := by
  have hc : IsCompIn (centralizer ({x} : Set G)) K := isCompIn_of_isILo hbal h
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hc.1) hc.2.1

theorem isCompIn_of_pumpUp_trivial {G : Type} [Group G] [Finite G]
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    (hrank : ∀ y : G, orderOf y = 2 → 3 ≤ CFSG.pRank 2 ↥(centralizer ({y} : Set G)))
    {x : G} {K : Subgroup G} (h : IsTwoTerminal x K) {y : G} (hy : y ∈ CxK x K)
    (hy2 : orderOf y = 2) : IsCompIn (centralizer ({y} : Set G)) K := by
  have hq : IsQuasisimple ↥K := isQuasisimple_of_isILo hbal h.1
  have hcxk : CxK x K ≤ centralizer (K : Set G) := CFSG.GH74.Generic.BProg.CxK_le_centralizer hq
  have hS : ⁅K, pPrimeCoreOf 2 (centralizer ({y} : Set G))⁆ = ⊥ := by
    have hodd : oddCore ↥(centralizer ({y} : Set G)) = ⊥ := hbal y hy2
    have hpp : pPrimeCore 2 ↥(centralizer ({y} : Set G)) = ⊥ := by
      rw [← oddCore_eq_pPrimeCore_two ↥(centralizer ({y} : Set G))]
      exact hodd
    have hmap : pPrimeCoreOf 2 (centralizer ({y} : Set G)) = ⊥ := by
      rw [pPrimeCoreOf, hpp, Subgroup.map_bot]
    rw [hmap, Subgroup.commutator_bot_right]
  have hyC : y ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.1 hy).1
  have hyK : y ∈ centralizerSection K (pPrimeCoreOf 2 K) := (Subgroup.mem_inf.1 hy).2
  have hKy : K ≤ centralizer ({y} : Set G) := by
    intro k hk
    have := Subgroup.mem_centralizer_iff.1 (hcxk hy) k hk
    exact Subgroup.mem_centralizer_singleton_iff.2 this
  obtain ⟨K', hlt⟩ := TwoThin.exists_pumpup_of_involution h.1.1 hy2 h.1.2.2 hyC hyK h.1
    (hrank y hy2)
  obtain ⟨hxN, ⟨e⟩⟩ := h.2.1 y K' hlt
  have hle : TwoThin.hatCard K' ≤ TwoThin.hatCard K :=
    (Nat.card_congr e.toEquiv).le
  obtain ⟨Λ, hΛ, hK'c, -, -, -, hcases⟩ :=
    C3.Layer1.PumpRigid.rigid_step hlt (TwoThin.mem_centralizer_symm hyC) hle
  have hKpcK : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) K := by
    have hsub : (K.subgroupOf (K ⊓ centralizer ({y} : Set G))).IsSubnormal := by
      have : K.subgroupOf (K ⊓ centralizer ({y} : Set G)) = ⊤ := by
        rw [Subgroup.subgroupOf_eq_top]
        exact inf_le_left
      rw [this]
      exact Subgroup.IsSubnormal.top
    exact CFSG.GH74.Generic.S3.isPCompIn_of_subnormal_block (le_inf le_rfl hKy) hsub hq
  have hΛK : K = Λ := hΛ.uniq K hKpcK
  rcases hcases with ⟨-, hbar⟩ | ⟨hxn, -⟩
  swap
  · exact absurd hxN hxn
  rw [← hΛK] at hbar
  have hsubn : (CFSG.GH74.Generic.S45.barSub y K).IsSubnormal := by
    have h1 := (isComponent_bar hK'c).2
    rw [← hbar] at h1
    exact h1
  have hcomm : ∀ a ∈ K, ∀ w ∈ pPrimeCoreOf 2 (centralizer ({y} : Set G)), a * w = w * a := by
    intro a ha w hw
    have h1 : ⁅a, w⁆ ∈ ⁅K, pPrimeCoreOf 2 (centralizer ({y} : Set G))⁆ :=
      Subgroup.commutator_mem_commutator ha hw
    rw [hS, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hsub := CFSG.GH74.Generic.BProg.isSubnormal_of_barSub_of_comm hsubn hcomm
  exact ⟨hKy, CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKy).symm hq,
    hsub⟩

theorem pumpUpLT_self_of_isCompIn {G : Type} [Group G] [Finite G]
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    (hrank : ∀ y : G, orderOf y = 2 → 3 ≤ CFSG.pRank 2 ↥(centralizer ({y} : Set G)))
    {x : G} {K : Subgroup G} (h : IsILo 2 x K) {y : G} (hy : y ∈ CxK x K)
    (hy2 : orderOf y = 2) (hc : IsCompIn (centralizer ({y} : Set G)) K) :
    PumpUpLT 2 x K y K := by
  have hq : IsQuasisimple ↥K := isQuasisimple_of_isILo hbal h
  have hyC : y ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.1 hy).1
  have hyK : y ∈ centralizerSection K (pPrimeCoreOf 2 K) := (Subgroup.mem_inf.1 hy).2
  have hKy : K ≤ centralizer ({y} : Set G) := hc.1
  have hKsubC : (K.subgroupOf (centralizer ({y} : Set G))).IsSubnormal := hc.2.2
  have hKpcK : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) K := by
    have hsub : (K.subgroupOf (K ⊓ centralizer ({y} : Set G))).IsSubnormal := by
      have : K.subgroupOf (K ⊓ centralizer ({y} : Set G)) = ⊤ := by
        rw [Subgroup.subgroupOf_eq_top]
        exact inf_le_left
      rw [this]
      exact Subgroup.IsSubnormal.top
    exact CFSG.GH74.Generic.S3.isPCompIn_of_subnormal_block (le_inf le_rfl hKy) hsub hq
  have hKle : K ≤ pumpUp 2 K y := by
    have h1 : K ≤ pLayerOf 2 (K ⊓ centralizer ({y} : Set G)) := le_sSup hKpcK
    intro k hk
    refine (le_iSup₂ (f := fun g (_ : g ∈ pLayerOf 2 (centralizer ({y} : Set G))) =>
      (pLayerOf 2 (K ⊓ centralizer ({y} : Set G))).map (MulAut.conj g).toMonoidHom) 1
      (one_mem _)) ?_
    exact ⟨k, h1 hk, by simp⟩
  have hsub' : (K.subgroupOf (pumpUp 2 K y)).IsSubnormal :=
    TwoThin.isSubnormal_inf_subgroupOf hKsubC (TwoThin.pumpUp_le_centralizer K y)
  refine ⟨h, ⟨hy2, by simpa [oBound] using hrank y hy2,
    CFSG.GH74.Generic.S3.isPCompIn_of_subnormal_block hKy hKsubC hq⟩, hyC, hyK,
    CFSG.GH74.Generic.S3.isPCompIn_of_subnormal_block hKle hsub' hq⟩

end CFSG.OddStandard.SmallF3.HypA2
