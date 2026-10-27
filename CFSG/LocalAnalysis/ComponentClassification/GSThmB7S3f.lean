module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Inst

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

section Sylow

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem isSylowOf_of_isSylowIn {S Y : Subgroup H} (h : IsSylowIn S Y) :
    ABGLocalTools.IsSylowOf 2 S Y := by
  obtain ⟨hSY, R, hR⟩ := h
  exact ⟨R, by rw [hR, map_subgroupOf_eq_of_le hSY]⟩

omit [Finite H] in
theorem isSylowIn_of_isSylowOf {S Y : Subgroup H} (h : ABGLocalTools.IsSylowOf 2 S Y) :
    IsSylowIn S Y :=
  ⟨h.le, h.exists_sylow_eq_subgroupOf⟩

theorem isSylowIn_P_inf_normal (h : Hyp52 H) (F : Subgroup H) [F.Normal] :
    IsSylowIn (h.P ⊓ F) (F ⊓ centralizer ({h.a} : Set H) ⊓ coreActionKernel h.J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := h.S_sylow
  have hS : ABGLocalTools.IsSylowOf 2 h.S
      (centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)) :=
    isSylowOf_of_isSylowIn ⟨h.S_le, R, hR⟩
  set K₁ := centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H) ⊓ coreActionKernel h.J
    with hK₁
  have h1 := hS.inf_of_le_normalizer (N := K₁) inf_le_left fun g hg =>
    mem_normalizer_inf (le_normalizer hg)
      (normalizer_le_normalizer_coreActionKernel h.J (mem_inf.mp hg).2)
  set K₂ := K₁ ⊓ F with hK₂
  have hFn : normalizer (F : Set H) = ⊤ := normalizer_eq_top_iff.mpr inferInstance
  have h2 := h1.inf_of_le_normalizer (N := K₂) inf_le_left fun g hg =>
    mem_normalizer_inf (le_normalizer hg) (hFn ▸ mem_top g)
  have hSa : ∀ g ∈ h.S, g ∈ centralizer ({h.a} : Set H) := fun g hg => (mem_inf.mp (h.S_le hg)).1
  have hSN : ∀ g ∈ h.S, g ∈ normalizer (h.J : Set H) := fun g hg => (mem_inf.mp (h.S_le hg)).2
  have hKN : ∀ g ∈ coreActionKernel h.J, g ∈ normalizer (h.J : Set H) := fun g hg =>
    (mem_coreActionKernel.mp hg).1
  have e1 : h.S ⊓ K₁ ⊓ K₂ = h.P ⊓ F := by
    ext g
    simp only [hK₁, hK₂, mem_inf]
    have := hSa g
    have := hSN g
    tauto
  have e2 : K₂ = F ⊓ centralizer ({h.a} : Set H) ⊓ coreActionKernel h.J := by
    ext g
    simp only [hK₁, hK₂, mem_inf]
    have := hKN g
    tauto
  rw [e1, e2] at h2
  exact isSylowIn_of_isSylowOf h2

end Sylow

variable {X : Type} [Group X] [Finite X]

theorem localB_of_isKGroupCat
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    {H : Type} [Group H] [Finite H] (hKG : SectionRank.IsKGroupCat H)
    (hO : pPrimeCore 2 H = ⊥) : Assembly.ComponentType.LocalBProperty H :=
  ((ProperSectionB.kGroupBConclusion_of_inputs hS hU hheld hKG).2.1
    (by rw [B5a.assembly_oddCore_eq]; exact hO)).2

variable {h : Hyp52 X} {y : X}

end Seven

end CFSG.ComponentClassification.GSThmB
