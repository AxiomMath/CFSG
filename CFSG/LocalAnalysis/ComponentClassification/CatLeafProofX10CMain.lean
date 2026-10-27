module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CComp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CNilpE
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10C
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Sec
public import CFSG.RankThree.SubgroupLists.CentralizerPerfect
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAFixedLayerPComponent
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S9c
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def GS81Step10CDiagInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H) (H₁ : h.L81Hyp) (d : H₁.Data) (v : H),
    d.Stage7 v → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
      Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f) →
      Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 p f → 3 < p ^ f →
      layerIn (centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H)) = ⊥ →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f → ∀ J₁ J₂ : Subgroup H, J₁ ≠ J₂ →
        X10.AzComp K d J₁ → X10.AzComp K d J₂ →
        (∀ L₀ : Subgroup (↥(centralizer ({h.a * d.z} : Set H)) ⧸
            pPrimeCore 2 ↥(centralizer ({h.a * d.z} : Set H))), IsComponent L₀ →
          QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({h.a * d.z} : Set H)))
            ⟨h.a * d.z, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ L₀ → 3 ∣ Nat.card L₀ →
          Blueprint.LieModel (↥L₀ ⧸ center ↥L₀) .PSL 3 2 2) →
        ∃ (z₀ : H) (J₀ : Subgroup H), orderOf z₀ = 2 ∧ z₀ ∈ J₀ ∧
          Open.IsSubnormal J₀ (centralizer ({z₀} : Set H)) ∧
          (∃ S : Sylow 2 J₀, ∃ r : ℕ, 3 ≤ r ∧
            Nonempty ((S : Subgroup J₀) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
          Open.classicalInvolutionWitness J₀

namespace X10CM

variable {G : Type} [Group G] [Finite G]

noncomputable def centralizerInfEquiv {F : Subgroup G} {a : G} (ha : a ∈ F) :
    ↥(centralizer ({(⟨a, ha⟩ : F)} : Set F)) ≃* ↥(centralizer ({a} : Set G) ⊓ F) := by
  have h1 : centralizer ({(⟨a, ha⟩ : F)} : Set F) = (centralizer ({a} : Set G)).subgroupOf F := by
    ext x
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    exact ⟨fun h2 => congrArg Subtype.val h2, fun h2 => Subtype.ext h2⟩
  exact (MulEquiv.subgroupCongr h1).trans
    ((((centralizer ({a} : Set G)).subgroupOf F).equivMapOfInjective F.subtype
      F.subtype_injective).trans (MulEquiv.subgroupCongr (subgroupOf_map_subtype _ _)))

theorem pLayer_eq_bot_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] [Finite Y] [Finite Y']
    (e : Y ≃* Y') (h : pLayer Y' 2 = ⊥) : pLayer Y 2 = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 e
  rw [h] at h1
  exact (map_eq_bot_iff_of_injective _ e.injective).mp h1

end X10CM

open CatLeafProof

theorem gs81Step10CInput_of_diag (hN : CFTwoNilpSL2) (hD : GS81Step10CDiagInput) :
    GS81Step10CInput := by
  intro H _ _ h H₁ d v hst p f hp hp2 hf hJ hK hq h9 K _ _ hKc J₁ J₂ hne hJ₁ hJ₂ _ _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := centralizer ({h.a * d.z} : Set H) with hF
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥F) with hπ
  have hazF : h.a * d.z ∈ F := mem_centralizer_singleton_iff.mpr rfl
  set z' : ↥F := ⟨h.a * d.z, hazF⟩ with hz'
  by_cases hcase : ∃ L₀ : Subgroup (↥F ⧸ pPrimeCore 2 ↥F), IsComponent L₀ ∧ π z' ∈ L₀ ∧
      3 ∣ Nat.card L₀ ∧ ¬ Blueprint.LieModel (↥L₀ ⧸ center ↥L₀) .PSL 3 2 2
  swap
  · push Not at hcase
    exact hD H h H₁ d v hst p f hp hp2 hf hJ hK hq h9 K hKc J₁ J₂ hne hJ₁ hJ₂
      fun L₀ hL₀ hzL h3 => hcase L₀ hL₀ hzL h3
  obtain ⟨L₀, hL₀, hzL, h3, h34⟩ := hcase
  have haa := Six.a_mul_a_self h.toHyp52
  have hza := d.z_comm_a
  have haF : h.a ∈ F := mem_centralizer_singleton_iff.mpr (by
    calc h.a * (h.a * d.z) = h.a * (d.z * h.a) := by rw [hza]
      _ = h.a * d.z * h.a := by group)
  have haz2 : h.a * d.z * (h.a * d.z) = 1 := by
    calc h.a * d.z * (h.a * d.z) = h.a * (d.z * h.a) * d.z := by group
      _ = h.a * (h.a * d.z) * d.z := by rw [hza]
      _ = 1 := by rw [← mul_assoc, haa, one_mul, d.z_mul_self]
  have haz1 : h.a * d.z ≠ 1 := by
    intro h1
    apply d.z_ne_a
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right haa]
  set a' : ↥F := ⟨h.a, haF⟩ with ha'
  have ha'2 : orderOf a' = 2 := by rw [ha', Subgroup.orderOf_mk]; exact h.orderOf_a
  have hz'2 : orderOf z' = 2 := by
    rw [hz', Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact haz2) haz1
  have hz'Z : z' ∈ center ↥F := by
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.2)
  have hFK : SectionRank.IsKGroupCat ↥F := by
    rcases H₁.kOrSimple with hKG | hs
    · exact hKG.subgroup F
    · refine isKGroupCat_of_ne_top' h.toHyp52.kProper fun htop => ?_
      obtain ⟨u, w, huw⟩ := h.exists_ne_commute_generalizedFitting
      have hZ : (h.a * d.z) ∈ center H := by
        rw [mem_center_iff]
        intro g
        have hg : g ∈ F := by rw [htop]; exact mem_top g
        exact mem_centralizer_singleton_iff.mp hg
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center H) with hb | ht
      · rw [hb, mem_bot] at hZ
        exact haz1 hZ
      · apply huw
        have := mem_center_iff.mp (ht ▸ mem_top (u : H)) (w : H)
        exact Subtype.ext this.symm
  set e := X10CM.centralizerInfEquiv haF with he
  have hL : pLayer ↥(centralizer ({a'} : Set ↥F)) 2 = ⊥ := by
    refine X10CM.pLayer_eq_bot_of_mulEquiv e ?_
    have h1 : (pLayer ↥(centralizer ({h.a} : Set H) ⊓ F) 2).map
        (centralizer ({h.a} : Set H) ⊓ F).subtype = ⊥ := h9
    exact (map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  have hC : HasNormalPComplement 2 ↥(centralizer ({a'} : Set ↥F)) :=
    QuasiDihedralFusion.hasNormalPComplement_of_mulEquiv e.symm
      (d.hasNormalPComplement_centralizer_a_az hst)
  have hW0 :=
    CatLeafProof.X10C.sl2_or_twoA7_of_component hN hFK ha'2 hL hC hz'Z hz'2 hL₀ hzL h34 h3
  exact X10.gs81Step10S8 L₀ hL₀.2 hzL hW0

end CFSG.ComponentClassification.GSThmB
