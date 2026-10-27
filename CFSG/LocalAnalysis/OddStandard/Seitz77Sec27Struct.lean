module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructTwo
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructLe

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG CFSG.Blueprint CFSG.LocalCores CFSG.ComponentClassification

theorem fourGenerated_subtype {G : Type} [Group G] (H : Subgroup G)
    (h : ∀ P : Subgroup G, IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P) :
    ∀ P : Subgroup ↥H, IsPGroup 2 P →
      ∃ s : Finset ↥H, s.card ≤ 4 ∧ Subgroup.closure (s : Set ↥H) = P := by
  classical
  intro P hP
  obtain ⟨s, hs4, hsP⟩ := h (P.map H.subtype) (hP.map H.subtype)
  have hsH : ∀ x ∈ s, x ∈ H := fun x hx => by
    have : x ∈ Subgroup.closure (s : Set G) := Subgroup.subset_closure hx
    rw [hsP] at this
    obtain ⟨y, -, rfl⟩ := this
    exact y.2
  refine ⟨s.subtype (· ∈ H),
    ((Finset.card_subtype _ _).trans_le (Finset.card_filter_le _ _)).trans hs4, ?_⟩
  apply Subgroup.map_injective H.subtype_injective
  rw [MonoidHom.map_closure, ← hsP]
  congr 1
  ext x
  simp only [Set.mem_image, Finset.mem_coe, Finset.mem_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hsH x hx⟩, hx, rfl⟩

section Main


theorem classify27_of_families (hHar : ComponentClassification.HSFLit.HaradaInput)
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N} (c : Local27 N X t)
    (m : Mod27 N X)
    (fam : NotL2Odd ∧ NotL28 ∧ NotU33 ∧ NotAlt ∧ NotU42 ∧ NotJ2 ∧ NotL34 ∧ CaseAL216) :
    Out27A N X t ∨ Out27B N X t := by
  obtain ⟨fL2, fL28, fU33, fAlt, fU42, fJ2, fL34, fA⟩ := fam
  have hcent := centralizer_layer_eq_bot27 c
  have hchar : (layer N).Characteristic := layer_characteristic
  have ht1 : t ≠ 1 := by
    intro h1
    have := c.t_order
    rw [h1, orderOf_one] at this
    omega
  by_cases hex : ∃ K₁ K₂ : Subgroup N, IsComponent K₁ ∧ IsComponent K₂ ∧ K₁ ≠ K₂
  ·
    obtain ⟨K₁, K₂, h₁, h₂, h12⟩ := hex
    have hall : ∀ K : Subgroup N, IsComponent K → K = K₁ ∨ K = K₂ := by
      intro K hK
      by_contra hne
      push Not at hne
      exact not_three_components hHar c h₁ h₂ hK h12 (Ne.symm hne.1) (Ne.symm hne.2)
    have hsup : K₁ ⊔ K₂ = layer N := by
      refine le_antisymm (sup_le (component_le_layer h₁) (component_le_layer h₂)) ?_
      refine sSup_le fun K hK => ?_
      rcases hall K hK with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    obtain ⟨s₁, a₁, b₁, hab₁⟩ := component_simple27 c h₁
    obtain ⟨s₂, a₂, b₂, hab₂⟩ := component_simple27 c h₂
    have hcomm := component_commute27 h₁ h₂ h12
    refine Or.inr (twoComp27 c K₁ K₂ s₁ s₂ hsup ?_ hcomm ⟨a₁, b₁, hab₁⟩ ⟨a₂, b₂, hab₂⟩ hcent)
    rw [disjoint_iff]
    have hC : K₂ ≤ centralizer (K₁ : Set N) := fun b hb =>
      mem_centralizer_iff.2 fun a ha => hcomm a ha b hb
    exact (inf_comm K₁ K₂).trans (inf_component_eq_bot27 c h₁ hC)
  · push Not at hex
    by_cases hone : ∃ K : Subgroup N, IsComponent K
    · obtain ⟨K, hK⟩ := hone
      have hall : ∀ L : Subgroup N, IsComponent L → L = K := fun L hL => hex L K hL hK
      have hlay : layer N = K := by
        refine le_antisymm (sSup_le fun L hL => (hall L hL).le) (component_le_layer hK)
      let eK : ↥(layer N) ≃* ↥K := MulEquiv.subgroupCongr hlay
      obtain ⟨hs, a, b, hab⟩ := component_simple27 c hK
      have hsimple : IsSimpleGroup ↥(layer N) := eK.isSimpleGroup
      have hnonab : ∃ a b : ↥(layer N), a * b ≠ b * a :=
        ⟨eK.symm a, eK.symm b, fun h => hab (by simpa using congrArg eK h)⟩
      have hgen := fourGenerated_subtype (layer N) (harada27 hHar c)
      have hdvd : Nat.card ↥(layer N) ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 :=
        (Subgroup.card_subgroup_dvd_card (layer N)).trans m.card_dvd
      have hS := survivors27 hGH hnonab hgen hdvd
      have hXle := X_le_layer27 c hcent hdvd hS
      have o : OneComp27 N X t := ⟨c, hsimple, hnonab, hcent, hXle⟩
      rcases hS with ⟨n, hn7, hn10, ⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, h⟩ | h | h | h | h | h | h
      · exact (fAlt N X t o n hn7 hn10 ⟨e⟩).elim
      · exact (fL2 N X t o m p f hp hp2 hf h).elim
      · exact (fL28 N X t o h).elim
      · exact Or.inl (fA N X t o h)
      · exact (fL34 N X t o m h).elim
      · exact (fU33 N X t o h).elim
      · exact (fU42 N X t o h).elim
      · exact (fJ2 N X t o h).elim
    · exfalso
      push Not at hone
      have hlay : layer N = ⊥ := layer_eq_bot_of_forall hone
      apply ht1
      have : t ∈ centralizer ((layer N : Subgroup N) : Set N) := by
        rw [mem_centralizer_iff]
        intro y hy
        have hy' : y ∈ layer N := hy
        rw [hlay, mem_bot] at hy'
        rw [hy', one_mul, mul_one]
      rw [hcent, mem_bot] at this
      exact this

end Main

end CFSG.OddStandard.Seitz77
