module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Glue
public import CFSG.GH74.GLS.Stage1.Thm6.Adapters
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Prop41

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

theorem lemma_4_2 (hII : II4_4_4_center) (h31 : IVK_3_1a_lifted) : Lemma4_2 := by
  unfold Lemma4_2
  intro G _ _ z S K₁ K₂ h hex
  have hM := m42_of_std hII h31 h
  obtain ⟨t, htR, ht2, htz, htne⟩ := hex
  rw [Rz_eq h] at htR
  have key := hM.lemma42 ⟨t, htR, ht2, htz, htne⟩
  rw [Pz_eq h, Qz_eq h]
  exact key

theorem zStar_instance {G : Type} [Group G] [Finite G] (hs : IsKProperSimple G) :
    ∀ P : Subgroup G, M.Syl2In P ⊤ → ∀ x ∈ P, x * x = 1 → x ≠ 1 →
      (∀ s ∈ P, x * s = s * x) → ∃ g : G, g⁻¹ * x * g ∈ P ∧ g⁻¹ * x * g ≠ x :=
  fun P hP x hxP hx2 hx1 hxc =>
    Stage1.Thm6.Sec12.ig_15_3 G hs.1 hs.2.1 P hP x hxP hx2 hx1 hxc

theorem lemma_4_4 (hII : II4_4_4_center) (hrec : Bg.B_reciprocity) (h19 : IVK_1_9_lifted)
    (h12 : IVK_1_2f_lifted) (hsd : SD_involution_fusion) : Lemma4_4 := by
  unfold Lemma4_4
  intro G _ _ z S K₁ K₂ h hA
  have hM := m44_of_std hII hrec h19 h12 hsd h
  obtain ⟨t, htS, htz, htne, hI⟩ := hM.lemma44 ((hyp4A_iff h).1 hA) (zStar_instance h.simple)
  exact ⟨t, htS, htz, htne, (interchanges_iff t).2 hI⟩

theorem lemma_4_5 (hII : II4_4_4_center) (h31 : IVK_3_1a_lifted) (hrec : Bg.B_reciprocity)
    (hbal : L45_balance_step) : Lemma4_5 := by
  unfold Lemma4_5
  intro G _ _ z S K₁ K₂ h hA t htS htz htne hI
  have hM := m45_of_std hII h31 hrec hbal h
  obtain ⟨hQ, hfus, hnc⟩ :=
    hM.lemma45 ((hyp4A_iff h).1 hA) htS htz htne ((interchanges_iff t).1 hI)
  rw [Pz_eq h, Qz_eq h]
  exact ⟨hQ, hfus, hnc⟩

theorem prop_4_1 (hII : II4_4_4_center) (h31 : IVK_3_1a_lifted) (hrec : Bg.B_reciprocity)
    (h19 : IVK_1_9_lifted) (h12 : IVK_1_2f_lifted) (hsd : SD_involution_fusion)
    (hbal : L45_balance_step) : Prop4_1 := by
  unfold Prop4_1
  intro G _ _ z S K₁ K₂ h
  have h44 := m44_of_std hII hrec h19 h12 hsd h
  have h45 := m45_of_std hII h31 hrec hbal h
  obtain ⟨hQ, hb, hc⟩ := M.prop41 h44 h45 (zStar_instance h.simple)
  rw [Qz_eq h, Pz_eq h]
  refine ⟨hQ, ?_, ?_⟩
  · rcases hb with hb | ⟨t, htS, htz, htne, hI, hfus, hnc⟩
    · exact Or.inl hb
    · exact Or.inr ⟨t, htS, htz, htne, (interchanges_iff t).2 hI, hfus, hnc⟩
  · intro t htC htz hI g hg
    have hI' := hc t htC htz ((interchanges_iff t).1 hI) g hg
    unfold Interchanges
    simp only [← cj_eq_conjugate]
    have e1 : M.cj (M.cj K₁ g) z = M.cj (M.cj K₁ (g * z * g⁻¹)) g := M.cj_cj_of_conj K₁ g z
    have e2 : M.cj (M.cj K₂ g) z = M.cj (M.cj K₂ (g * z * g⁻¹)) g := M.cj_cj_of_conj K₂ g z
    rw [e1, e2, hI'.1, hI'.2]
    exact ⟨rfl, rfl⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec4
