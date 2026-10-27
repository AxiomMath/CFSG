module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.Partition
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

theorem twoSubgroupsFourGenerated_of_conj_le {A P : Subgroup G}
    (hP : ∀ Q : Subgroup G, Q ≤ P →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = Q)
    (hAP : ∀ X : Subgroup G, IsPGroup 2 X → X ≤ A → ∃ g : G, X ≤ conjSub g P) :
    TwoSubgroupsFourGenerated ↥A := by
  classical
  intro Q hQ
  set X : Subgroup G := Q.map A.subtype with hXdef
  have hX2 : IsPGroup 2 X := hQ.map A.subtype
  have hXA : X ≤ A := Subgroup.map_subtype_le Q
  obtain ⟨g, hg⟩ := hAP X hX2 hXA
  have hX0 : conjSub g⁻¹ X ≤ P := by
    intro y hy
    have h1 := hg (mem_conjSub_iff.mp hy)
    rw [mem_conjSub_iff] at h1
    simpa [mul_assoc] using h1
  obtain ⟨s, hs4, hscl⟩ := hP _ hX0
  set s' : Finset G := s.image (fun x => g * x * g⁻¹) with hs'
  have hX : Subgroup.closure (s' : Set G) = X := by
    have hcoe : (s' : Set G) = (MulAut.conj g).toMonoidHom '' (s : Set G) := by
      rw [hs', Finset.coe_image]
      rfl
    rw [hcoe, ← MonoidHom.map_closure, hscl]
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_conjSub_iff,
      inv_inv]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [e]
      exact hx
  have hmem : ∀ x ∈ s', x ∈ A := fun x hx =>
    hXA (hX ▸ Subgroup.subset_closure hx)
  refine ⟨s'.attach.image (fun x => (⟨x.1, hmem x.1 x.2⟩ : ↥A)),
    (Finset.card_image_le).trans ((Finset.card_attach).le.trans
      (Finset.card_image_le.trans hs4)), ?_⟩
  apply Subgroup.map_injective A.subtype_injective
  rw [MonoidHom.map_closure]
  have himg : A.subtype '' ((s'.attach.image (fun x => (⟨x.1, hmem x.1 x.2⟩ : ↥A)) :
      Finset ↥A) : Set ↥A) = (s' : Set G) := by
    ext y
    simp only [Set.mem_image, Finset.coe_image, Finset.mem_coe, Finset.mem_attach, true_and,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact x.2
    · intro hy
      exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  rw [himg, hX]

theorem twoSubgroupsFourGenerated_of_sylow_le [Finite G] (T : Sylow 2 G) {A : Subgroup G}
    (hT : ∀ Q : Subgroup G, Q ≤ (T : Subgroup G) →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = Q) :
    TwoSubgroupsFourGenerated ↥A := by
  refine twoSubgroupsFourGenerated_of_conj_le hT fun X hX2 _ => ?_
  obtain ⟨T', hXT'⟩ := hX2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T T'
  refine ⟨g, fun x hx => ?_⟩
  have hT' : (T' : Subgroup G) = conjSub g (T : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  exact hT' ▸ hXT' hx

end CFSG.ClassicalInvolution.Q3
