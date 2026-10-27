module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.KGroups.Generic3
public import CFSG.GH74.KGroups.Generic9
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.NativeChecks
public import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.GH74.KGroups.Sz8
public import CFSG.GH74.KGroups.Sz8Tables
public import CFSG.GH74.Uniqueness.SU.KInputs
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.NativeChecks
public meta import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.GH74.KGroups.Sz8
public meta import CFSG.GH74.KGroups.Sz8Tables
import CFSG.Goldschmidt.Steps.GSz8Mult
import CFSG.Goldschmidt.Steps.G3MFSz8
public import Certificates.Certificate5115
public import Certificates.Certificate5128
public import Certificates.Certificate5130
public import Certificates.Certificate113
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Kernel.J4Count.KFacts
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.L5U5.ModelsBridge
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.GH74.KGroups.KI5

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.Quasithin CFSG.GH74.KGroups.Sz8

theorem szModel_eq : CFSG.Theory.Comparator.SzModel 1 = CFSG.Open.Sz 1 := by
  simp only [CFSG.Open.Sz, CFSG.Open.SzGenerators, CFSG.Theory.Comparator.SzModel,
    CFSG.Theory.Comparator.SzGenerators]

theorem equiv_open_of_szModel {G : Type} [Group G]
    (h : Nonempty (G ≃* CFSG.Theory.Comparator.SzModel 1)) : Nonempty (G ≃* CFSG.Open.Sz 1) :=
  h.map fun e => e.trans (MulEquiv.subgroupCongr szModel_eq)

theorem equiv_P_of_szModel
    {G : Type} [Group G]
    (h : Nonempty (G ≃* CFSG.Theory.Comparator.SzModel 1)) : Nonempty (G ≃* QP.originalSubgroup) := by
  obtain ⟨e⟩ := equiv_open_of_szModel h
  obtain ⟨e2⟩ := suz_equiv_matrix GF8 card_GF8
  obtain ⟨e3⟩ := equiv_suz_P
  exact ⟨e.trans ((CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv 1).trans
    (e2.symm.trans e3))⟩

theorem cent_QS_check :
    NativeChecks.centInCheck (elemsT QA) (elemsT QS) = true :=
  Certificates.certificate5115

theorem cent_QS :
    ∀ σ ∈ QA.originalSubgroup, (∀ q ∈ QS.originalSubgroup, σ * q = q * σ) →
    σ ∈ QS.originalSubgroup := by
  intro σ hσ hc
  have h1 := List.all_eq_true.1 cent_QS_check σ ((mem_elemsT QA QA_ok σ).2 hσ)
  have hCS : (elemsT QS).all (fun q => decide (σ * q = q * σ)) = true := by
    rw [List.all_eq_true]
    intro q hq
    simpa using hc q ((mem_elemsT QS QS_ok q).1 hq)
  simp only [hCS, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h1
  exact (mem_elemsT QS QS_ok σ).1 h1

theorem bender_of_equiv
    {G : Type} [Group G] (e : G ≃* QP.originalSubgroup) (T : Subgroup G)
    (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    ∀ x ∈ T, x ^ 2 = 1 → ∀ y ∈ T, y * x = x * y := by
  have : Finite G := finite_K e
  have hs := benderCheck_sound QS QS_ok bender_ok
  exact (benderTable_of_model QP.originalSubgroup e QS.originalSubgroup QS_le card_S
    (card_K' e) (by decide) hs.1 hs.2.1 hs.2.2.1 tt tt_mem hs.2.2.2.1 hs.2.2.2.2.1
    hs.2.2.2.2.2 T hT hTi).1

@[expose] def KI5d : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → IsPGroup 2 ↥(Subgroup.center K) →
    Subgroup.center K ≠ ⊥ →
      Nonempty ((K ⧸ Subgroup.center K) ≃* CFSG.Theory.Comparator.SzModel 1) →
        Nat.card (Subgroup.center K) = 2 → ∀ φ : MulAut K, ∃ g : K, φ = MulAut.conj g

theorem ki5_parts
    (K : Type) [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ2 : IsPGroup 2 ↥(Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥)
    (e : (K ⧸ Subgroup.center K) ≃* CFSG.Theory.Comparator.SzModel 1) :
    (Nat.card (Subgroup.center K) = 2 ∨ Nat.card (Subgroup.center K) = 4) ∧
      (∀ P : Sylow 2 K, Subgroup.center ↥(P : Subgroup K) =
        (Subgroup.center K).subgroupOf (P : Subgroup K)) ∧
      (∀ (P : Sylow 2 K) (φ : MulAut K), (∀ g ∈ (P : Subgroup K), φ g = g) → φ = 1) ∧
      (∀ (P : Sylow 2 K), ∀ g ∈ (P : Subgroup K), g ^ 2 ∈ Subgroup.center K → g ^ 2 = 1) ∧
      (∀ (P : Sylow 2 K), ∀ g ∈ (P : Subgroup K), ∀ h ∈ (P : Subgroup K),
        g ^ 2 ∈ Subgroup.center K → h ^ 2 ∈ Subgroup.center K → g * h = h * g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hperf0, hsimple, -⟩ := hK
  have hperf : commutator K = ⊤ := hperf0.commutator_eq_top
  have hquasi : CFSG.Open.IsQuasisimple K := ⟨hperf, hsimple⟩
  obtain ⟨eO⟩ := equiv_open_of_szModel ⟨e⟩
  obtain ⟨eP⟩ := equiv_P_of_szModel ⟨e⟩
  have hel := CFSG.Goldschmidt.GSz8Mult.isElemAbelian_center hquasi eO
  have hle4 : Nat.card (Subgroup.center K) ≤ 4 := CFSG.Goldschmidt.GSz8Mult K hquasi ⟨eO⟩
  have hMF := CFSG.Goldschmidt.GMFSz8 K hquasi hel ⟨eO⟩
  have ha : Nat.card (Subgroup.center K) = 2 ∨ Nat.card (Subgroup.center K) = 4 := by
    obtain ⟨m, hm⟩ := hZ2.exists_card_eq
    have hne : Nat.card (Subgroup.center K) ≠ 1 := fun h => hZ (Subgroup.card_eq_one.1 h)
    have hm0 : m ≠ 0 := fun h0 => hne (by rw [hm, h0]; rfl)
    have hm3 : m < 3 := by
      by_contra h3
      have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : m = 1 ∨ m = 2 := by omega
    rcases this with rfl | rfl
    · left; rw [hm]; norm_num
    · right; rw [hm]; norm_num
  have hb : ∀ P : Sylow 2 K, Subgroup.center ↥(P : Subgroup K) =
      (Subgroup.center K).subgroupOf (P : Subgroup K) := by
    intro P
    ext ⟨g, hgP⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
    constructor
    · intro hg
      by_contra hgZ
      obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
      have hcomm : ∀ x ∈ (P : Subgroup K), g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center K := by
        intro x hxP
        have h1 : x * g = g * x := congrArg Subtype.val (hg ⟨x, hxP⟩)
        have : g * x * g⁻¹ * x⁻¹ = 1 := by
          calc g * x * g⁻¹ * x⁻¹ = (x * g) * g⁻¹ * x⁻¹ := by rw [h1]
            _ = 1 := by group
        rw [this]; exact Subgroup.one_mem _
      obtain ⟨x, hxP, hx⟩ := (hMF P).2 g hgP hcomm (fun h => hgZ (Subgroup.mem_center_iff.1 h))
        z.1 z.2
      have h1 : x * g = g * x := congrArg Subtype.val (hg ⟨x, hxP⟩)
      have : x * g * x⁻¹ * g⁻¹ = 1 := by
        calc x * g * x⁻¹ * g⁻¹ = (g * x) * x⁻¹ * g⁻¹ := by rw [h1]
          _ = 1 := by group
      exact hz1 (Subtype.ext (hx.symm.trans this))
    · intro hgZ x
      exact Subtype.ext (hgZ x.1)
  have hc : ∀ (P : Sylow 2 K) (φ : MulAut K), (∀ g ∈ (P : Subgroup K), φ g = g) → φ = 1 := by
    intro P φ hφ
    obtain ⟨M, hMP, hMA⟩ := autModel eP
    have hSP : QS.originalSubgroup ≤ M.P := by rw [hMP]; exact QS_le
    refine aut_fix_sylow_trivial hperf hZ2 hb M QS.originalSubgroup hSP (v := 6) (m := 455)
      card_S (card_K' eP) (by decide) ?_ P φ hφ
    intro σ hσ hc'
    rw [hMA] at hσ
    exact cent_QS σ hσ hc'
  have hcentral : ∀ (P : Sylow 2 K) (g : K), g ∈ (P : Subgroup K) → g ^ 2 ∈ Subgroup.center K →
      ∀ x ∈ (P : Subgroup K), g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center K := by
    intro P g hgP hg2 x hxP
    set Z : Subgroup K := Subgroup.center K with hZdef
    let π : K →* K ⧸ Z := QuotientGroup.mk' Z
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
    have hT2 : IsPGroup 2 ((P : Subgroup K).map π) := P.isPGroup'.map π
    have hTi : ¬ 2 ∣ ((P : Subgroup K).map π).index := fun h =>
      P.not_dvd_index (h.trans (Subgroup.index_map_dvd (P : Subgroup K) hπ))
    have hb2 := bender_of_equiv eP _ hT2 hTi
    have hg1 : (π g) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hg2
    have h1 := hb2 (π g) (Subgroup.mem_map_of_mem π hgP) hg1 (π x)
      (Subgroup.mem_map_of_mem π hxP)
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker]
    show π (g * x * g⁻¹ * x⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc π g * π x * (π g)⁻¹ * (π x)⁻¹ = (π x * π g) * (π g)⁻¹ * (π x)⁻¹ := by rw [h1]
      _ = 1 := by group
  have he : ∀ (P : Sylow 2 K), ∀ g ∈ (P : Subgroup K), g ^ 2 ∈ Subgroup.center K → g ^ 2 = 1 := by
    intro P g hgP hg2
    exact ((hMF P).1 g hgP g hgP (hcentral P g hgP hg2) (hcentral P g hgP hg2)).2
  have hf : ∀ (P : Sylow 2 K), ∀ g ∈ (P : Subgroup K), ∀ h ∈ (P : Subgroup K),
      g ^ 2 ∈ Subgroup.center K → h ^ 2 ∈ Subgroup.center K → g * h = h * g := by
    intro P g hgP h hhP hg2 hh2
    exact ((hMF P).1 g hgP h hhP (hcentral P g hgP hg2) (hcentral P h hhP hh2)).1
  exact ⟨ha, hb, hc, he, hf⟩

theorem ki5_of_d
    (hd : KI5d) : CFSG.GH74.Uniqueness.SU.K.KI5 := by
  intro K _ _ hK hZ2 hZ ⟨e⟩
  obtain ⟨ha, hb, hc, he, hf⟩ := ki5_parts K hK hZ2 hZ e
  exact ⟨ha, hb, hc, fun h2 => hd K hK hZ2 hZ ⟨e⟩ h2, he, hf⟩

end CFSG.GH74.KGroups.KI5
