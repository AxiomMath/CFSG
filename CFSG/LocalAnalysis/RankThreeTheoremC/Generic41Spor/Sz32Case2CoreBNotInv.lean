module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Fin
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Out
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2CoreBN1
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2CoreBSyl
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43BComp
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43BCP
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

open CFSG.Open Subgroup

variable {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y} {L₁ L₂ : Subgroup Y} {t : Y}

@[expose] def sz32bW (L₁ L₂ : Subgroup Y) : Subgroup Y :=
  Subgroup.closure {g : Y | g ∈ Subgroup.normalizer (L₁ : Set Y) ∧ Nat.Coprime (orderOf g) 5} ⊔
    (L₁ ⊔ L₂)

theorem sz32b_closure_normal (N : Subgroup Y) [hN : N.Normal] :
    (Subgroup.closure {g : Y | g ∈ N ∧ Nat.Coprime (orderOf g) 5}).Normal := by
  refine ⟨fun x hx g => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    refine ⟨hN.conj_mem x hx.1 g, ?_⟩
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    simpa using this.symm ▸ hx.2
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem sz32bW_normal (h : Szh1Two Pb L₁ L₂ t) : (sz32bW L₁ L₂).Normal := by
  haveI := sz32b_N1_normal h
  haveI := sz32b_sup_normal h
  haveI := sz32b_closure_normal (Subgroup.normalizer (L₁ : Set Y))
  exact inferInstanceAs
    ((Subgroup.closure {g : Y | g ∈ Subgroup.normalizer (L₁ : Set Y) ∧ Nat.Coprime (orderOf g) 5} ⊔
      (L₁ ⊔ L₂)).Normal)

theorem sz32bW_le (h : Szh1Two Pb L₁ L₂ t) : sz32bW L₁ L₂ ≤ Subgroup.normalizer (L₁ : Set Y) :=
  sup_le ((Subgroup.closure_le _).2 (fun _ hg => hg.1)) (sz32b_sup_le_N1 h)

theorem sz32bW_five {g : Y} (hg : g ∈ Subgroup.normalizer (L₁ : Set Y))
    (hc : Nat.Coprime (orderOf g) 5) : g ∈ sz32bW L₁ L₂ :=
  Subgroup.mem_sup_left (Subgroup.subset_closure ⟨hg, hc⟩)

theorem sz32b_Q0_le_W (hs : Szh1Cyc Pb a c y L₁ L₂) : sz32Q0 a c ≤ sz32bW L₁ L₂ := by
  rw [hs.Q0]
  exact (sup_le_sup inf_le_right inf_le_right).trans le_sup_right

theorem sz32b_y_not_mem_W (hY : Sz32Case2Data Pb a c y) (hI713 : KFactI713Out)
    (h : Szh1Two Pb L₁ L₂ t) (hs : Szh1Cyc Pb a c y L₁ L₂) : y ∉ sz32bW L₁ L₂ := by
  intro hyW
  have hsd₁ := szh1_simple_data hY.catalog h.comp₁ h.cen₁
  have hsd₂ := szh1_simple_data hY.catalog h.comp₂ h.cen₂
  obtain ⟨hr₁, hr₂⟩ := sz32b_pRank_le_one hY h hs
  have hyN : y ∈ Subgroup.normalizer (L₁ : Set Y) := sz32b_Pb_le_N1 h hY.pres.y_mem
  have hA₁ : ∀ g ∈ L₁ ⊔ L₂, ∃ l ∈ L₁, ∀ x ∈ L₁, g * x * g⁻¹ = l * x * l⁻¹ := by
    intro g hg
    obtain ⟨u, hu, v, hv, rfl⟩ := (A10B123.mem_sup_iff_of_comm (sz32b_comm h)).1 hg
    refine ⟨u, hu, fun x hx => ?_⟩
    have hxv : x * v = v * x := sz32b_comm h x hx v hv
    have e : v * x * v⁻¹ = x := by rw [← hxv]; group
    calc u * v * x * (u * v)⁻¹ = u * (v * x * v⁻¹) * u⁻¹ := by group
      _ = u * x * u⁻¹ := by rw [e]
  have hA₂ : ∀ g ∈ L₁ ⊔ L₂, ∃ l ∈ L₂, ∀ x ∈ L₂, g * x * g⁻¹ = l * x * l⁻¹ := by
    intro g hg
    obtain ⟨u, hu, v, hv, rfl⟩ := (A10B123.mem_sup_iff_of_comm (sz32b_comm h)).1 hg
    refine ⟨v, hv, fun x hx => ?_⟩
    have hw : v * x * v⁻¹ ∈ L₂ := L₂.mul_mem (L₂.mul_mem hv hx) (L₂.inv_mem hv)
    have huw : u * (v * x * v⁻¹) = (v * x * v⁻¹) * u := sz32b_comm h u hu _ hw
    calc u * v * x * (u * v)⁻¹ = u * (v * x * v⁻¹) * u⁻¹ := by group
      _ = v * x * v⁻¹ := by rw [huw]; group
  obtain ⟨l₁, hl₁, hl₁'⟩ := szh1_inner_of_mem_O5 hI713 (H := Subgroup.normalizer (L₁ : Set Y))
    (L := L₁) (A := L₁ ⊔ L₂) le_rfl (sz32b_sup_le_N1 h) hA₁ hsd₁.1 hsd₁.2.1 hsd₁.2.2 hr₁ hyN
    hY.pres.y5 hyW
  obtain ⟨l₂, hl₂, hl₂'⟩ := szh1_inner_of_mem_O5 hI713 (H := Subgroup.normalizer (L₁ : Set Y))
    (L := L₂) (A := L₁ ⊔ L₂) (fun g hg => sz32b_N1_mem_N2 h hg) (sz32b_sup_le_N1 h) hA₂ hsd₂.1
    hsd₂.2.1 hsd₂.2.2 hr₂ hyN hY.pres.y5 hyW
  have hz1 : ∀ x ∈ L₁, ((l₁ * l₂)⁻¹ * y) * x = x * ((l₁ * l₂)⁻¹ * y) := by
    intro x hx
    have hc : x * l₂ = l₂ * x := sz32b_comm h x hx l₂ hl₂
    have e1 : (l₁ * l₂)⁻¹ * (y * x * y⁻¹) * (l₁ * l₂) = x := by
      rw [hl₁' x hx]
      calc (l₁ * l₂)⁻¹ * (l₁ * x * l₁⁻¹) * (l₁ * l₂) = l₂⁻¹ * (x * l₂) := by group
        _ = l₂⁻¹ * (l₂ * x) := by rw [hc]
        _ = x := by group
    have e3 : ((l₁ * l₂)⁻¹ * y) * x * ((l₁ * l₂)⁻¹ * y)⁻¹ = x := by
      have e2 : ((l₁ * l₂)⁻¹ * y) * x * ((l₁ * l₂)⁻¹ * y)⁻¹ =
          (l₁ * l₂)⁻¹ * (y * x * y⁻¹) * (l₁ * l₂) := by group
      rw [e2, e1]
    exact mul_inv_eq_iff_eq_mul.1 e3
  have hz2 : ∀ x ∈ L₂, ((l₁ * l₂)⁻¹ * y) * x = x * ((l₁ * l₂)⁻¹ * y) := by
    intro x hx
    have hc : l₁ * x = x * l₁ := sz32b_comm h l₁ hl₁ x hx
    have hc12 : l₁ * l₂ = l₂ * l₁ := sz32b_comm h l₁ hl₁ l₂ hl₂
    have e1 : (l₁ * l₂)⁻¹ * (y * x * y⁻¹) * (l₁ * l₂) = x := by
      rw [hl₂' x hx, hc12]
      calc (l₂ * l₁)⁻¹ * (l₂ * x * l₂⁻¹) * (l₂ * l₁) = l₁⁻¹ * (x * l₁) := by group
        _ = l₁⁻¹ * (l₁ * x) := by rw [← hc]
        _ = x := by group
    have e3 : ((l₁ * l₂)⁻¹ * y) * x * ((l₁ * l₂)⁻¹ * y)⁻¹ = x := by
      have e2 : ((l₁ * l₂)⁻¹ * y) * x * ((l₁ * l₂)⁻¹ * y)⁻¹ =
          (l₁ * l₂)⁻¹ * (y * x * y⁻¹) * (l₁ * l₂) := by group
      rw [e2, e1]
    exact mul_inv_eq_iff_eq_mul.1 e3
  have hLz : L₁ ⊔ L₂ ≤ Subgroup.centralizer ({(l₁ * l₂)⁻¹ * y} : Set Y) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hz1 x hx
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hz2 x hx
  have hz : (l₁ * l₂)⁻¹ * y ∈ Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_centralizer_iff.1 (hLz hg) _ (Set.mem_singleton _)
    exact this.symm
  rw [h.cent, Subgroup.mem_bot, inv_mul_eq_one] at hz
  apply hs.y_not
  rw [← hz]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl₁) (Subgroup.mem_sup_right hl₂)

theorem sz32b_N1_eq_sup (hY : Sz32Case2Data Pb a c y) (h : Szh1Two Pb L₁ L₂ t)
    (hs : Szh1Cyc Pb a c y L₁ L₂) :
    Subgroup.normalizer (L₁ : Set Y) = sz32bW L₁ L₂ ⊔ Subgroup.zpowers y := by
  obtain ⟨S, hS⟩ := hY.sylow
  haveI := sz32bW_normal h
  have hSN : (S : Subgroup Y) ≤ Subgroup.normalizer (L₁ : Set Y) := hS ▸ sz32b_Pb_le_N1 h
  have h1 := szh1_H_eq_sup (sz32bW_le h) (fun g hg hc => sz32bW_five hg hc) S hSN
  rw [hS] at h1
  apply le_antisymm
  · rw [h1]
    refine sup_le ?_ le_sup_left
    rw [hY.pres.gen]
    exact sup_le_sup_right (sz32b_Q0_le_W hs) _
  · exact sup_le (sz32bW_le h) (Subgroup.zpowers_le.2 (sz32b_Pb_le_N1 h hY.pres.y_mem))

theorem szh1_two_not_inverting' (hY : Sz32Case2Data Pb a c y) (hI713 : KFactI713Out)
    {L₁ L₂ : Subgroup Y} {t : Y} (h : Szh1Two Pb L₁ L₂ t) (hs : Szh1Cyc Pb a c y L₁ L₂) :
    t * y * t⁻¹ * y⁻¹ ∉ sz32Q0 a c := by
  intro hmem
  haveI := sz32b_N1_normal h
  haveI := sz32bW_normal h
  exact szh1_final_contra hY.perf (sz32bW_le h) (fun g hg hc => sz32bW_five hg hc)
    (sz32b_N1_tt h) (sz32b_N1_split h) (sz32b_Pb_le_N1 h hY.pres.y_mem) hY.pres.y5
    (sz32b_y_not_mem_W hY hI713 h hs) (sz32b_N1_eq_sup hY h hs) (sz32b_Q0_le_W hs hmem)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
