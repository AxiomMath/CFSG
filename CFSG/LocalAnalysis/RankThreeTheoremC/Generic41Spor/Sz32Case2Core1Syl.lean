module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Out
import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfig
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools

section Syl

variable {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}

theorem szh1c_syl_mem_sup {A B : Subgroup Y} (hcomm : ∀ x ∈ A, ∀ z ∈ B, x * z = z * x) {x : Y}
    (hx : x ∈ A ⊔ B) : ∃ u ∈ A, ∃ v ∈ B, x = u * v := by
  let f : A × B →* Y :=
    MonoidHom.noncommCoprod A.subtype B.subtype (fun u v => hcomm u u.2 v v.2)
  have hf : ∀ p : A × B, f p = (p.1 : Y) * (p.2 : Y) := fun p => rfl
  have hle : A ⊔ B ≤ f.range := by
    refine sup_le ?_ ?_
    · intro u hu
      exact ⟨(⟨u, hu⟩, 1), by rw [hf]; simp⟩
    · intro v hv
      exact ⟨(1, ⟨v, hv⟩), by rw [hf]; simp⟩
  obtain ⟨p, hp⟩ := hle hx
  exact ⟨p.1, p.1.2, p.2, p.2.2, by rw [← hf]; exact hp.symm⟩

theorem szh1c_syl_card_sup {A B : Subgroup Y} (hcomm : ∀ x ∈ A, ∀ z ∈ B, x * z = z * x)
    (hdisj : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  let f : A × B →* Y :=
    MonoidHom.noncommCoprod A.subtype B.subtype (fun u v => hcomm u u.2 v v.2)
  have hf : ∀ p : A × B, f p = (p.1 : Y) * (p.2 : Y) := fun p => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, v⟩ huv
    rw [hf] at huv
    have hu : (u : Y) = (v : Y)⁻¹ := eq_inv_of_mul_eq_one_left huv
    have hmem : (u : Y) ∈ A ⊓ B := ⟨u.2, by rw [hu]; exact B.inv_mem v.2⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    have hv1 : (v : Y) = 1 := by
      rw [hmem] at hu
      simpa using hu.symm
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hv1)
  have hrange : f.range = A ⊔ B := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨p, rfl⟩
      exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
    · refine sup_le ?_ ?_
      · intro u hu
        exact ⟨(⟨u, hu⟩, 1), by rw [hf]; simp⟩
      · intro v hv
        exact ⟨(1, ⟨v, hv⟩), by rw [hf]; simp⟩
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

section Two

variable {L₁ L₂ : Subgroup Y} {t : Y}

theorem szh1c_syl_commute (h : Szh1Two Pb L₁ L₂ t) : ∀ x ∈ L₁, ∀ z ∈ L₂, x * z = z * x := by
  have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne L₁ L₂ h.comp₁ h.comp₂ h.ne
  have hle : L₁ ≤ Subgroup.centralizer (L₂ : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  intro x hx z hz
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) z hz).symm

theorem szh1c_syl_inf_eq_bot (h : Szh1Two Pb L₁ L₂ t) : L₁ ⊓ L₂ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hz : (⟨x, hx.1⟩ : L₁) ∈ Subgroup.center L₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (szh1c_syl_commute h g g.2 x hx.2)
  rw [h.cen₁, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem szh1c_syl_five_dvd (hY : Sz32Case2Data Pb a c y) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hn : ∃ x z : ↥L, x * z ≠ z * x) : 5 ∣ Nat.card L := by
  by_contra hnd
  have hcore := cfsg_subnormal_primeComplementCore_eq_bot 5 L hL.2.1 hY.core
  have hcop : Nat.Coprime 5 (Nat.card (⊤ : Subgroup ↥L)) := by
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hnd
  have hle := normal_coprime_le_primeComplementCore 5 (⊤ : Subgroup ↥L) inferInstance hcop
  rw [hcore] at hle
  obtain ⟨x, z, hxz⟩ := hn
  apply hxz
  have hx : x ∈ (⊥ : Subgroup ↥L) := hle (Subgroup.mem_top x)
  have hz : z ∈ (⊥ : Subgroup ↥L) := hle (Subgroup.mem_top z)
  rw [Subgroup.mem_bot] at hx hz
  rw [hx, hz]

theorem szh1c_syl_isSylowOf_top (hY : Sz32Case2Data Pb a c y) : IsSylowOf 5 Pb ⊤ := by
  obtain ⟨S, hS⟩ := hY.sylow
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [isSylowOf_iff]
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hS]
    exact S.isPGroup'
  · rw [Subgroup.relIndex_top_right, ← hS]
    exact S.not_dvd_index

theorem szh1c_syl_pow_pElement (hY : Sz32Case2Data Pb a c y) {g : Y} (hg : g ∈ Pb) :
    ∃ k : ℕ, g ^ (5 ^ k) = 1 := by
  obtain ⟨S, hS⟩ := hY.sylow
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨g, by rw [hS]; exact hg⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem szh1c_syl_sylow_inf (hY : Sz32Case2Data Pb a c y) {L : Subgroup Y}
    (hL : ∀ g ∈ Pb, g ∈ Subgroup.normalizer (L : Set Y)) : IsSylowOf 5 (Pb ⊓ L) L := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hPL : Pb ≤ Subgroup.normalizer (L : Set Y) := fun g hg => hL g hg
  have h1 := IsSylowOf.of_le (szh1c_syl_isSylowOf_top hY) hPL le_top
  exact h1.inf_of_le_normalizer Subgroup.le_normalizer le_rfl

theorem szh1c_syl_norm_sup (h : Szh1Two Pb L₁ L₂ t) :
    ∀ g ∈ Pb, g ∈ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup Y) : Set Y) := by
  have hfwd : ∀ g ∈ Pb, ∀ x ∈ L₁ ⊔ L₂, g * x * g⁻¹ ∈ L₁ ⊔ L₂ := by
    intro g hg x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := szh1c_syl_mem_sup (szh1c_syl_commute h) hx
    have hu' : g * u * g⁻¹ ∈ L₁ := (Subgroup.mem_normalizer_iff.mp (h.norm₁ g hg) u).mp hu
    have hv' : g * v * g⁻¹ ∈ L₂ := (Subgroup.mem_normalizer_iff.mp (h.norm₂ g hg) v).mp hv
    have : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
    rw [this]
    exact (L₁ ⊔ L₂).mul_mem (Subgroup.mem_sup_left hu') (Subgroup.mem_sup_right hv')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hfwd g hg x hx, fun hx => ?_⟩
  have := hfwd g⁻¹ (Pb.inv_mem hg) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem szh1c_syl_map_conj₁ (h : Szh1Two Pb L₁ L₂ t) :
    (Pb ⊓ L₁).map (MulAut.conj t).toMonoidHom = Pb ⊓ L₂ := by
  have hPb : Pb.map (MulAut.conj t).toMonoidHom = Pb :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp h.t_norm
  rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hPb, h.t₁]

theorem szh1c_syl_card_conj (h : Szh1Two Pb L₁ L₂ t) :
    Nat.card ↥(Pb ⊓ L₂) = Nat.card ↥(Pb ⊓ L₁) := by
  rw [← szh1c_syl_map_conj₁ h]
  exact Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
    (MulAut.conj t).injective

theorem szh1c_syl_card_inf_sup (hY : Sz32Case2Data Pb a c y) (h : Szh1Two Pb L₁ L₂ t) :
    Nat.card ↥(Pb ⊓ (L₁ ⊔ L₂)) = Nat.card ↥(Pb ⊓ L₁) * Nat.card ↥(Pb ⊓ L₂) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hS : IsSylowOf 5 (Pb ⊓ (L₁ ⊔ L₂)) (L₁ ⊔ L₂) := szh1c_syl_sylow_inf hY (szh1c_syl_norm_sup h)
  have hS₁ : IsSylowOf 5 (Pb ⊓ L₁) L₁ := szh1c_syl_sylow_inf hY h.norm₁
  have hS₂ : IsSylowOf 5 (Pb ⊓ L₂) L₂ := szh1c_syl_sylow_inf hY h.norm₂
  rw [hS.card_eq, hS₁.card_eq, hS₂.card_eq,
    szh1c_syl_card_sup (szh1c_syl_commute h) (szh1c_syl_inf_eq_bot h),
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, pow_add]

theorem szh1c_syl_comm_P (h : Szh1Two Pb L₁ L₂ t) :
    ∀ x ∈ Pb ⊓ L₁, ∀ z ∈ Pb ⊓ L₂, x * z = z * x :=
  fun x hx z hz => szh1c_syl_commute h x hx.2 z hz.2

theorem szh1c_syl_disj_P (h : Szh1Two Pb L₁ L₂ t) : (Pb ⊓ L₁) ⊓ (Pb ⊓ L₂) = ⊥ :=
  le_bot_iff.mp (le_trans (inf_le_inf inf_le_right inf_le_right)
    (le_of_eq (szh1c_syl_inf_eq_bot h)))

theorem szh1c_syl_inf_sup_eq (hY : Sz32Case2Data Pb a c y) (h : Szh1Two Pb L₁ L₂ t) :
    (Pb ⊓ L₁) ⊔ (Pb ⊓ L₂) = Pb ⊓ (L₁ ⊔ L₂) := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · exact sup_le (inf_le_inf le_rfl le_sup_left) (inf_le_inf le_rfl le_sup_right)
  · rw [szh1c_syl_card_inf_sup hY h, szh1c_syl_card_sup (szh1c_syl_comm_P h) (szh1c_syl_disj_P h)]

theorem szh1c_syl_inner_of_card_five (hY : Sz32Case2Data Pb a c y) (hI713 : KFactI713Out)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hz : Subgroup.center ↥L = ⊥)
    (hnorm : ∀ g ∈ Pb, g ∈ Subgroup.normalizer (L : Set Y)) (hcard : Nat.card ↥(Pb ⊓ L) = 5) :
    ∀ g ∈ Pb, ∃ l ∈ L, ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hs, hn, hc⟩ := szh1_simple_data hY.catalog hL hz
  have hsyl := szh1c_syl_sylow_inf hY hnorm
  have hS : ∀ S : Sylow 5 ↥L, Nat.card (S : Subgroup ↥L) = 5 := by
    intro S
    rw [Sylow.card_eq_multiplicity, ← hsyl.card_eq, hcard]
  have hr : CFSG.Open.pRank 5 (⊤ : Subgroup ↥L) ≤ 1 := by
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 5 ↥L))
    exact szh1_pRank_le_one_of_cyclic_sylow S (isCyclic_of_prime_card (hS S))
  intro g hg
  obtain ⟨k, hk⟩ := szh1c_syl_pow_pElement hY hg
  exact szh1_inner_of_five_elt hI713 (H := Pb) (L := L) (fun g hg => hnorm g hg) hs hn hc hr hS hg hk

theorem szh1c_syl_mem_of_inner (h : Szh1Two Pb L₁ L₂ t) {g : Y}
    (h₁ : ∃ l ∈ L₁, ∀ x ∈ L₁, g * x * g⁻¹ = l * x * l⁻¹)
    (h₂ : ∃ l ∈ L₂, ∀ x ∈ L₂, g * x * g⁻¹ = l * x * l⁻¹) : g ∈ L₁ ⊔ L₂ := by
  obtain ⟨l₁, hl₁, e₁⟩ := h₁
  obtain ⟨l₂, hl₂, e₂⟩ := h₂
  have hcomm := szh1c_syl_commute h
  have hconj : ∀ x ∈ L₁ ⊔ L₂, g * x * g⁻¹ = (l₁ * l₂) * x * (l₁ * l₂)⁻¹ := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := szh1c_syl_mem_sup hcomm hx
    have hu' : (l₁ * l₂) * u * (l₁ * l₂)⁻¹ = l₁ * u * l₁⁻¹ := by
      have h1 : l₂ * u = u * l₂ := (hcomm u hu l₂ hl₂).symm
      calc (l₁ * l₂) * u * (l₁ * l₂)⁻¹ = l₁ * (l₂ * u) * l₂⁻¹ * l₁⁻¹ := by group
        _ = l₁ * (u * l₂) * l₂⁻¹ * l₁⁻¹ := by rw [h1]
        _ = l₁ * u * l₁⁻¹ := by group
    have hv' : (l₁ * l₂) * v * (l₁ * l₂)⁻¹ = l₂ * v * l₂⁻¹ := by
      have h1 : l₁ * (l₂ * v * l₂⁻¹) = (l₂ * v * l₂⁻¹) * l₁ :=
        hcomm l₁ hl₁ _ (L₂.mul_mem (L₂.mul_mem hl₂ hv) (L₂.inv_mem hl₂))
      calc (l₁ * l₂) * v * (l₁ * l₂)⁻¹ = l₁ * (l₂ * v * l₂⁻¹) * l₁⁻¹ := by group
        _ = (l₂ * v * l₂⁻¹) * l₁ * l₁⁻¹ := by rw [h1]
        _ = l₂ * v * l₂⁻¹ := by group
    calc g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
      _ = (l₁ * u * l₁⁻¹) * (l₂ * v * l₂⁻¹) := by rw [e₁ u hu, e₂ v hv]
      _ = ((l₁ * l₂) * u * (l₁ * l₂)⁻¹) * ((l₁ * l₂) * v * (l₁ * l₂)⁻¹) := by rw [hu', hv']
      _ = (l₁ * l₂) * (u * v) * (l₁ * l₂)⁻¹ := by group
  have hw : (l₁ * l₂)⁻¹ * g ∈ Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hconj x hx
    have h2 : g * x = (l₁ * l₂) * x * (l₁ * l₂)⁻¹ * g := by
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = (l₁ * l₂) * x * (l₁ * l₂)⁻¹ * g := by rw [h1]
    calc x * ((l₁ * l₂)⁻¹ * g) = (l₁ * l₂)⁻¹ * ((l₁ * l₂) * x * (l₁ * l₂)⁻¹ * g) := by group
      _ = (l₁ * l₂)⁻¹ * (g * x) := by rw [← h2]
      _ = (l₁ * l₂)⁻¹ * g * x := by group
  rw [h.cent, Subgroup.mem_bot] at hw
  have hg : g = l₁ * l₂ := (inv_mul_eq_one.mp hw).symm
  rw [hg]
  exact (L₁ ⊔ L₂).mul_mem (Subgroup.mem_sup_left hl₁) (Subgroup.mem_sup_right hl₂)

theorem szh1c_syl_comm_sup {A B : Subgroup Y} (hcomm : ∀ x ∈ A, ∀ z ∈ B, x * z = z * x)
    (hA : ∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x) (hB : ∀ z ∈ B, ∀ z' ∈ B, z * z' = z' * z) :
    IsMulCommutative ↥(A ⊔ B) := by
  refine ⟨⟨fun p q => ?_⟩⟩
  obtain ⟨u, hu, v, hv, hp⟩ := szh1c_syl_mem_sup hcomm p.2
  obtain ⟨u', hu', v', hv', hq⟩ := szh1c_syl_mem_sup hcomm q.2
  apply Subtype.ext
  show (p : Y) * q = q * p
  rw [hp, hq]
  have hvu' : v * u' = u' * v := (hcomm u' hu' v hv).symm
  have huu' : u * u' = u' * u := hA u hu u' hu'
  have hvv' : v * v' = v' * v := hB v hv v' hv'
  have huv' : u * v' = v' * u := hcomm u hu v' hv'
  calc u * v * (u' * v') = u * (v * u') * v' := by group
    _ = u * (u' * v) * v' := by rw [hvu']
    _ = (u * u') * (v * v') := by group
    _ = (u' * u) * (v' * v) := by rw [huu', hvv']
    _ = u' * (u * v') * v := by group
    _ = u' * (v' * u) * v := by rw [huv']
    _ = u' * v' * (u * v) := by group

theorem szh1c_syl_zpowers_comm (g : Y) :
    ∀ x ∈ Subgroup.zpowers g, ∀ x' ∈ Subgroup.zpowers g, x * x' = x' * x := by
  intro x hx x' hx'
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨m', rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
  exact (Commute.zpow_zpow_self g m m').eq

theorem szh1c_syl_cyclic_of_card_25 {P : Subgroup Y} (hP : Nat.card ↥P = 25) {g : Y} (hg : g ∈ P)
    (hg5 : g ^ 5 ≠ 1) : orderOf g = 25 ∧ P = Subgroup.zpowers g := by
  have h25 : g ^ 25 = 1 := by
    have := pow_card_eq_one' (G := ↥P) (x := (⟨g, hg⟩ : ↥P))
    rw [hP] at this
    exact congrArg Subtype.val this
  have hdvd : orderOf g ∣ 25 := orderOf_dvd_of_pow_eq_one h25
  obtain ⟨i, hi, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 (show orderOf g ∣ 5 ^ 2 by simpa using hdvd)
  have hord : orderOf g = 25 := by
    interval_cases i
    · exfalso
      apply hg5
      have : orderOf g = 1 := by simpa using hoi
      simp [orderOf_eq_one_iff.mp this]
    · exfalso
      apply hg5
      have : orderOf g = 5 := by simpa using hoi
      rw [← this]
      exact pow_orderOf_eq_one g
    · simpa using hoi
  refine ⟨hord, ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg) ?_).symm
  rw [Nat.card_zpowers, hord, hP]

end Two

theorem szh1_two_sylow (hY : Sz32Case2Data Pb a c y) (hI713 : KFactI713Out)
    {L₁ L₂ : Subgroup Y} {t : Y} (h : Szh1Two Pb L₁ L₂ t) : Szh1Cyc Pb a c y L₁ L₂ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨-, hn₁, -⟩ := szh1_simple_data hY.catalog h.comp₁ h.cen₁
  have hS₁ : IsSylowOf 5 (Pb ⊓ L₁) L₁ := szh1c_syl_sylow_inf hY h.norm₁
  have hc₁ : Nat.card ↥(Pb ⊓ L₁) = 5 ^ (Nat.card L₁).factorization 5 := hS₁.card_eq
  generalize hk : (Nat.card L₁).factorization 5 = k at hc₁
  have hc₂ : Nat.card ↥(Pb ⊓ L₂) = 5 ^ k := (szh1c_syl_card_conj h).trans hc₁
  have hcard := szh1c_syl_card_inf_sup hY h
  rw [hc₁, hc₂] at hcard
  have hk1 : 1 ≤ k := by
    rw [← hk]
    exact Nat.Prime.factorization_pos_of_dvd Nat.prime_five Nat.card_pos.ne'
      (szh1c_syl_five_dvd hY h.comp₁ hn₁)
  have hPb5 : Nat.card ↥Pb = 5 ^ 5 := hY.facts.card
  have hk2 : k ≤ 2 := by
    have hle : Nat.card ↥(Pb ⊓ (L₁ ⊔ L₂)) ≤ Nat.card ↥Pb := Subgroup.card_le_of_le inf_le_left
    rw [hcard, hPb5, ← pow_add] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1 hle
    omega
  have hk_ne : k ≠ 1 := by
    intro hk1'
    subst hk1'
    have hc₁' : Nat.card ↥(Pb ⊓ L₁) = 5 := by rw [hc₁]; norm_num
    have hc₂' : Nat.card ↥(Pb ⊓ L₂) = 5 := by rw [hc₂]; norm_num
    have hin₁ := szh1c_syl_inner_of_card_five hY hI713 h.comp₁ h.cen₁ h.norm₁ hc₁'
    have hin₂ := szh1c_syl_inner_of_card_five hY hI713 h.comp₂ h.cen₂ h.norm₂ hc₂'
    have hle : Pb ≤ L₁ ⊔ L₂ := fun g hg => szh1c_syl_mem_of_inner h (hin₁ g hg) (hin₂ g hg)
    rw [inf_eq_left.mpr hle, hPb5] at hcard
    norm_num at hcard
  have hk_eq : k = 2 := by omega
  subst hk_eq
  have hc₁' : Nat.card ↥(Pb ⊓ L₁) = 25 := by rw [hc₁]; norm_num
  have hc₂' : Nat.card ↥(Pb ⊓ L₂) = 25 := by rw [hc₂]; norm_num
  have hex : ∃ g ∈ Pb ⊓ L₁, g ^ 5 ≠ 1 := by
    by_contra hno
    push Not at hno
    have hP₁ : Pb ⊓ L₁ ≤ sz32Om a c y := fun g hg => hY.facts.Om_all g hg.1 (hno g hg)
    have hP₂ : Pb ⊓ L₂ ≤ sz32Om a c y := by
      intro u hu
      have hu' : u ∈ (Pb ⊓ L₁).map (MulAut.conj t).toMonoidHom := by
        rw [szh1c_syl_map_conj₁ h]
        exact hu
      obtain ⟨g, hg, hgu⟩ := Subgroup.mem_map.mp hu'
      refine hY.facts.Om_all u hu.1 ?_
      rw [← hgu, ← map_pow, hno g hg, map_one]
    have h1 := Subgroup.card_le_of_le (sup_le hP₁ hP₂)
    rw [hY.facts.Om_card, szh1c_syl_card_sup (szh1c_syl_comm_P h) (szh1c_syl_disj_P h), hc₁', hc₂'] at h1
    norm_num at h1
  obtain ⟨g₁, hg₁, hg₁5⟩ := hex
  obtain ⟨ho₁, hP₁⟩ := szh1c_syl_cyclic_of_card_25 hc₁' hg₁ hg₁5
  have hg₂ : (MulAut.conj t).toMonoidHom g₁ ∈ Pb ⊓ L₂ := by
    rw [← szh1c_syl_map_conj₁ h]
    exact Subgroup.mem_map_of_mem _ hg₁
  have hg₂5 : ((MulAut.conj t).toMonoidHom g₁) ^ 5 ≠ 1 := by
    rw [← map_pow]
    intro h1
    exact hg₁5 ((map_eq_one_iff (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).mp h1)
  obtain ⟨ho₂, hP₂⟩ := szh1c_syl_cyclic_of_card_25 hc₂' hg₂ hg₂5
  have hQ0 : (Pb ⊓ L₁) ⊔ (Pb ⊓ L₂) = sz32Q0 a c := by
    refine hY.facts.Q0_unique _ (sup_le inf_le_left inf_le_left) ?_ ?_
    · refine szh1c_syl_comm_sup (szh1c_syl_comm_P h) ?_ ?_
      · rw [hP₁]
        exact szh1c_syl_zpowers_comm g₁
      · rw [hP₂]
        exact szh1c_syl_zpowers_comm _
    · rw [szh1c_syl_card_sup (szh1c_syl_comm_P h) (szh1c_syl_disj_P h), hc₁', hc₂']
      norm_num
  refine ⟨⟨g₁, ho₁, hP₁⟩, ⟨_, ho₂, hP₂⟩, hQ0.symm, ?_⟩
  intro hy
  have hmem : y ∈ (Pb ⊓ L₁) ⊔ (Pb ⊓ L₂) := by
    rw [szh1c_syl_inf_sup_eq hY h]
    exact ⟨hY.pres.y_mem, hy⟩
  rw [hQ0] at hmem
  exact hY.pres.y_not hmem

end Syl

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
