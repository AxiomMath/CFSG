module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs96
public import CFSG.LargeExtraspecial.Transport
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Subgroup CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def SylowStr (S : Type) [Group S] : Prop :=
  IsPGroup 2 S ∧ Nat.card S = 2 ^ 9 ∧ Nat.card (Subgroup.center S) = 2 ^ 3 ∧
    (∀ z ∈ Subgroup.center S, z ^ 2 = 1) ∧
    ∀ V : Subgroup S, V ≤ Subgroup.center S → Nat.card V = 4 →
      ∃ (E : Type) (_ : Group E) (π : S →* E), Function.Surjective π ∧ π.ker = V ∧
        CFSG.IsExtraspecialPGroup 2 E ∧ Nat.card E = 2 ^ (2 * 3 + 1)

theorem SylowStr.of_mulEquiv {S R : Type} [Group S] [Group R] (e : S ≃* R) (h : SylowStr S) :
    SylowStr R := by
  obtain ⟨hp, hc, hz, hsq, hV⟩ := h
  have hcen : (Subgroup.center S).map e.toMonoidHom = Subgroup.center R :=
    CFSG.LargeExtraspecial.map_center_of_mulEquiv e
  have hcen' : (Subgroup.center R).map e.symm.toMonoidHom = Subgroup.center S :=
    CFSG.LargeExtraspecial.map_center_of_mulEquiv e.symm
  refine ⟨hp.of_equiv e, (Nat.card_congr e.toEquiv).symm.trans hc, ?_, ?_, ?_⟩
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hz]
  · intro z hz'
    have hz'' : e.symm z ∈ Subgroup.center S := by
      rw [← hcen'] at *
      exact ⟨z, hz', rfl⟩
    have h3 := congrArg e (hsq _ hz'')
    simpa [map_pow] using h3
  · intro V hV4 hVc
    have hV'c : V.map e.symm.toMonoidHom ≤ Subgroup.center S :=
      (Subgroup.map_mono hV4).trans (le_of_eq hcen')
    have hV'card : Nat.card (V.map e.symm.toMonoidHom) = 4 := by
      rw [Subgroup.card_map_of_injective e.symm.injective]; exact hVc
    obtain ⟨E, _, π, hπ, hker, hE, hEc⟩ := hV _ hV'c hV'card
    refine ⟨E, inferInstance, π.comp e.symm.toMonoidHom, hπ.comp e.symm.surjective, ?_, hE, hEc⟩
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker]
    simp


theorem map_subtype_center {M : Type*} [Group M] (T : Subgroup M) :
    (Subgroup.center ↥T).map T.subtype = T ⊓ Subgroup.centralizer (T : Set M) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff, Subgroup.coe_subtype, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨r.2, fun h hh => ?_⟩
    exact congrArg Subtype.val (hr ⟨h, hh⟩)
  · rintro ⟨hyT, hy⟩
    exact ⟨⟨y, hyT⟩, fun g => Subtype.ext (hy g g.2), rfl⟩

@[expose] def SylowAmb {M : Type} [Group M] (T : Subgroup M) : Prop :=
  IsPGroup 2 T ∧ Nat.card T = 2 ^ 9 ∧
    Nat.card ↥(T ⊓ Subgroup.centralizer (T : Set M)) = 2 ^ 3 ∧
    (∀ z ∈ T ⊓ Subgroup.centralizer (T : Set M), z ^ 2 = 1) ∧
    ∀ V : Subgroup M, V ≤ T ⊓ Subgroup.centralizer (T : Set M) → Nat.card V = 4 →
      IsExtraspecialMod V T 3

theorem sylowStr_of_amb {M : Type} [Group M] {T : Subgroup M} (h : SylowAmb T) :
    SylowStr ↥T := by
  obtain ⟨hp, hc, hz, hsq, hV⟩ := h
  have hmap := map_subtype_center T
  refine ⟨hp, hc, ?_, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective T.subtype_injective, hmap]; exact hz
  · intro z hz'
    have : (z : M) ∈ T ⊓ Subgroup.centralizer (T : Set M) := hmap ▸ Subgroup.mem_map_of_mem _ hz'
    exact Subtype.ext (by simpa using hsq _ this)
  · intro V hVc hV4
    have hVle : V.map T.subtype ≤ T ⊓ Subgroup.centralizer (T : Set M) :=
      hmap ▸ Subgroup.map_mono hVc
    have hVcard : Nat.card (V.map T.subtype) = 4 := by
      rw [Subgroup.card_map_of_injective T.subtype_injective]; exact hV4
    obtain ⟨E, _, π, hπ, hker, hE, hEc⟩ := hV _ hVle hVcard
    refine ⟨E, inferInstance, π, hπ, ?_, hE, hEc⟩
    rw [hker, ← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective T.subtype_injective]

theorem sylowAmb_of_str {M : Type} [Group M] {T : Subgroup M} (h : SylowStr ↥T) :
    SylowAmb T := by
  obtain ⟨hp, hc, hz, hsq, hV⟩ := h
  have hmap := map_subtype_center T
  refine ⟨hp, hc, ?_, ?_, ?_⟩
  · rw [← hmap, Subgroup.card_map_of_injective T.subtype_injective]; exact hz
  · intro z hz'
    rw [← hmap] at hz'
    obtain ⟨a, ha, rfl⟩ := hz'
    have := congrArg Subtype.val (hsq a ha)
    simpa using this
  · intro V hVle hV4
    have hVT : V ≤ T := hVle.trans inf_le_left
    have hVc : V.subgroupOf T ≤ Subgroup.center ↥T := by
      intro v hv
      have : (v : M) ∈ T ⊓ Subgroup.centralizer (T : Set M) := hVle hv
      rw [← hmap] at this
      obtain ⟨a, ha, haV⟩ := this
      have : a = v := Subtype.ext haV
      exact this ▸ ha
    have hVcard : Nat.card (V.subgroupOf T) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVT).toEquiv]; exact hV4
    exact hV _ hVc hVcard


abbrev U38Model : Type := StatedProj (StatedSU 3 (2 ^ 3) (GaloisField 2 6))

end CFSG.LocalAnalysis.GLTheoremA.CatB
