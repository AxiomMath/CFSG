module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrIdx
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrImg
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FrameParts
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55R3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Merge
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrLiftB
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FitCent
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem frame_of_data {G : Type} [Group G] [Finite G] {k : Kind} {p : ℕ} {H P T : Subgroup G}
    {g : G} (hp : p.Prime) (hp2 : p ≠ 2) (hgH : g ∈ H) (hgP : g ∈ P) (hPp : IsPGroup p ↥P)
    (hTP : T ≤ normalizer (P : Set G)) {Γ₀ : Type} [Group Γ₀] [Finite Γ₀] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ρ₀ : Γ₀ →* (V →ₗ[ZMod p] V)ˣ) (hρ : Function.Injective ρ₀)
    (hOp : ∀ N : Subgroup Γ₀, N.Normal → IsPGroup p ↥N → N = ⊥)
    (π : ↥H →* Γ₀) (hπ : Function.Surjective π) (T₀ : Sylow 2 Γ₀)
    (hT₀ : (T₀ : Subgroup Γ₀) = (T.subgroupOf H).map π) {K : Subgroup Γ₀} (hK : IsComponent K)
    (hKN : ∀ x ∈ (P.subgroupOf H).map π, x ∈ normalizer (K : Set Γ₀))
    (hna : π ⟨g, hgH⟩ ∉ centralizer (K : Set Γ₀))
    (hquad : (((ρ₀ (π ⟨g, hgH⟩) : (V →ₗ[ZMod p] V)ˣ) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0)
    (hgh : GHList (↥K ⧸ center ↥K)) (hr3 : InvSecGroup k (↥K ⧸ center ↥K))
    (hidx : (normalizer (K : Set Γ₀)).index ≤ 2) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hJg : ¬ barIn H (zpowers g) ≤ centralizer (J : Set (HBar H))) {Dl : Subgroup ↥H}
    (hDlperf : ⁅Dl, Dl⁆ = Dl) (hDlJ : Dl.map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) = J)
    (hDlK : Dl.map π = K)
    (hDln : ∀ h : ↥H, QuotientGroup.mk' (pPrimeCore 2 ↥H) h ∈ normalizer (J : Set (HBar H)) →
      h ∈ normalizer (Dl : Set ↥H)) :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V)
      (_ : Module (ZMod p) V) (_ : Module.Finite (ZMod p) V)
      (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ) (P' R : Subgroup Γ),
      Frame55 k p ρ K a P' R ∧ Link55 H P T g K a P' R := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hf2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pCore p Γ₀ = ⊥ := hOp _ pCore_normal pCore_isPGroup
  set N : Subgroup Γ₀ := normalizer (K : Set Γ₀) with hN
  have hNn : N.Normal := normal_of_index_le_two hidx
  have hKN' : K ≤ N := Subgroup.le_normalizer
  set P₁ : Subgroup Γ₀ := (P.subgroupOf H).map π with hP₁
  set T₁ : Subgroup Γ₀ := (T.subgroupOf H).map π with hT₁
  have hP₁N : P₁ ≤ N := fun x hx => hKN x hx
  have hgP₁ : π ⟨g, hgH⟩ ∈ P₁ := ⟨⟨g, hgH⟩, hgP, rfl⟩
  have haN : π ⟨g, hgH⟩ ∈ N := hP₁N hgP₁
  have hT₁p : IsPGroup 2 ↥T₁ := by
    rw [← hT₀]
    exact T₀.isPGroup'
  have hT₁P₁ : T₁ ≤ normalizer (P₁ : Set Γ₀) := map_le_normalizer π hTP
  have hP₁p : IsPGroup p ↥P₁ := map_isPGroup π hPp
  have hT₀top : CFSG.ABGLocalTools.IsSylowOf 2 (T₀ : Subgroup Γ₀) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, T₀.isPGroup', by rw [Subgroup.relIndex_top_right]; exact T₀.not_dvd_index⟩
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T₁ ⊓ K) K := by
    have := YCfg.isSylowOf_inf_isSubnormal_top hT₀top hK.2
    rwa [hT₀] at this
  let a' : ↥N := ⟨π ⟨g, hgH⟩, haN⟩
  have hKc : IsComponent (K.subgroupOf N) := LocalCores.component_overgroup hK hKN'
  obtain ⟨e⟩ := centralQuot_equiv hKN'
  refine ⟨↥N, inferInstance, inferInstance, V, inferInstance, inferInstance, inferInstance,
    ρ₀.comp N.subtype, K.subgroupOf N, a', P₁.subgroupOf N, T₁.subgroupOf N, ?_, ?_⟩
  · refine ⟨⟨hp, hp2, hρ.comp N.subtype_injective, ?_, hKc.1, GHList.of_mulEquiv e.symm hgh,
      hquad, ?_, isPGroup_subgroupOf hP₁p N, hgP₁, ?_⟩, isPGroup_subgroupOf hT₁p N, ?_, ?_,
      InvSecGroup.of_equiv e.symm hr3⟩
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKN').mpr le_rfl
    · intro hbot
      apply hna
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 : ⁅(⟨x, hKN' hx⟩ : ↥N), a'⁆ ∈ ⁅K.subgroupOf N, zpowers a'⁆ :=
        Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers a')
      rw [hbot, Subgroup.mem_bot] at h1
      have h3 : (⟨x, hKN' hx⟩ : ↥N) * a' = a' * ⟨x, hKN' hx⟩ :=
        commutatorElement_eq_one_iff_mul_comm.mp h1
      exact congrArg Subtype.val h3
    · intro N' hN'n hN'p
      exact eq_bot_of_normal_pgroup hO N N' hN'n hN'p
    · intro r hr
      have hr' : (r : Γ₀) ∈ T₁ := hr
      rw [mem_normalizer_iff]
      intro x
      exact mem_normalizer_iff.mp (hT₁P₁ hr') (x : Γ₀)
    · have hinf : (T₁ ⊓ K).subgroupOf N = T₁.subgroupOf N ⊓ K.subgroupOf N := by
        ext x
        simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      rw [← hinf]
      exact isSylowOf_subgroupOf (inf_le_right.trans hKN') hKN' hsyl
  · have hsub : (Dl.map H.subtype).subgroupOf H = Dl :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective Dl
    refine ⟨Γ₀, inferInstance, π, N.subtype, hgH, J, N.subtype_injective, hπ, ?_, ?_, rfl, ?_, ?_,
      hJ, hJg, Dl.map H.subtype, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.range_subtype]
      exact hNn
    · rw [Subgroup.range_subtype]
      exact hidx
    · rw [Subgroup.subgroupOf_map_subtype]
      exact inf_of_le_left hP₁N
    · rw [Subgroup.subgroupOf_map_subtype, Subgroup.range_subtype]
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · exact Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hDlperf])
    · rw [hsub]
      exact hDlJ
    · rw [hsub, hDlK, Subgroup.subgroupOf_map_subtype]
      exact (inf_of_le_left hKN').symm
    · intro h hh
      exact mem_normalizer_map_br H.subtype (hDln h hh)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
