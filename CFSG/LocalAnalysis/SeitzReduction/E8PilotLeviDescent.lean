module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.SeitzReduction.EPilot

section BaseChange


variable {K M : Type} [Field K] [Field M]

theorem baseChangeGL_mem_rootSpan_perpRoots (ι : K →+* M) (g : e7Levi K) :
    baseChangeGL ι ((g : adjointGroup .E8 K) : ModGL .E8 K) ∈ rootSpan .E8 M (perpRoots .E8) :=
  F4Pilot.map_rootSpan_baseChangeGL_le ι _ ⟨_, mem_e7Levi_iff.1 g.2, rfl⟩

@[expose] noncomputable def e7LeviBaseChange (ι : K →+* M) : ↥(e7Levi K) →* ↥(e7Levi M) :=
  (((baseChangeGL ι).comp ((adjointGroup .E8 K).subtype.comp (e7Levi K).subtype)).codRestrict
      (adjointGroup .E8 M) fun g => rootSpan_le_adjointGroup_E8 _
        (baseChangeGL_mem_rootSpan_perpRoots ι g)).codRestrict
    (e7Levi M) fun g => mem_e7Levi_iff.2 (baseChangeGL_mem_rootSpan_perpRoots ι g)

theorem coe_e7LeviBaseChange (ι : K →+* M) (g : e7Levi K) :
    (((e7LeviBaseChange ι g : e7Levi M) : adjointGroup .E8 M) : ModGL .E8 M) =
      baseChangeGL ι ((g : adjointGroup .E8 K) : ModGL .E8 K) :=
  rfl

theorem e7LeviBaseChange_injective (ι : K →+* M) : Function.Injective (e7LeviBaseChange ι) :=
  fun _ _ hgh => Subtype.ext (Subtype.ext (baseChangeGL_injective ι
    (congrArg (fun x : e7Levi M => ((x : adjointGroup .E8 M) : ModGL .E8 M)) hgh)))

theorem e7LeviBaseChange_e7LeviPar (ι : K →+* M) {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : IsRoot .E7 γ) (c : K) :
    e7LeviBaseChange ι ⟨e7LeviPar K γ c, e7LeviPar_mem_e7Levi hγ c⟩ =
      ⟨e7LeviPar M γ (ι c), e7LeviPar_mem_e7Levi hγ (ι c)⟩ :=
  Subtype.ext (Subtype.ext (baseChangeGL_pinnedX ι _ c))

@[expose] noncomputable def adjointBaseChangeE7 (ι : K →+* M) :
    ↥(adjointGroup .E7 K) →* ↥(adjointGroup .E7 M) :=
  ((baseChangeGL ι).comp (adjointGroup .E7 K).subtype).codRestrict (adjointGroup .E7 M)
    fun g => baseChangeGL_mem_adjointGroup ι g.2

theorem coe_adjointBaseChangeE7 (ι : K →+* M) (g : adjointGroup .E7 K) :
    ((adjointBaseChangeE7 ι g : adjointGroup .E7 M) : ModGL .E7 M) =
      baseChangeGL ι (g : ModGL .E7 K) :=
  rfl

theorem adjointBaseChangeE7_pinnedX (ι : K →+* M) (γ : Fin (Tag.rank .E7) → ℤ) (c : K) :
    adjointBaseChangeE7 ι ⟨pinnedX .E7 K γ c, pinnedX_mem_adjointGroup γ c⟩ =
      ⟨pinnedX .E7 M γ (ι c), pinnedX_mem_adjointGroup γ (ι c)⟩ :=
  Subtype.ext (baseChangeGL_pinnedX ι γ c)

end BaseChange

section Naturality


variable {K M : Type} [Field K] [Finite K] [CharP K 2] [Field M] [Finite M] [CharP M 2]

theorem e7LeviEquiv_baseChange (ι : K →+* M) (g : e7Levi K) :
    e7LeviEquiv M (e7LeviBaseChange ι g) = adjointBaseChangeE7 ι (e7LeviEquiv K g) := by
  have hhom : ((e7LeviEquiv M).toMonoidHom.comp (e7LeviBaseChange ι)).comp
      (e7MinEquivLevi K).toMonoidHom =
      ((adjointBaseChangeE7 ι).comp (e7LeviEquiv K).toMonoidHom).comp
        (e7MinEquivLevi K).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense closure_xm_eq_top ?_
    rintro _ ⟨γ, hγ, c, rfl⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [e7MinEquivLevi_xm hγ c, e7LeviBaseChange_e7LeviPar ι hγ c, e7LeviEquiv_e7LeviPar hγ,
      e7LeviEquiv_e7LeviPar hγ, adjointBaseChangeE7_pinnedX]
  obtain ⟨x, rfl⟩ := (e7MinEquivLevi K).surjective g
  exact DFunLike.congr_fun hhom x

end Naturality

section Descent


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_baseChangeGL_eq_of_frob_fixed_E7 {g : ModGL .E7 (FiniteField.Extension K 2 2)}
    (hg : g ∈ adjointGroup .E7 (FiniteField.Extension K 2 2))
    (hσg : baseChangeGL (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom g = g) :
    ∃ g₀ ∈ adjointGroup .E7 K,
      baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) g₀ = g := by
  set φ : FiniteField.Extension K 2 2 ≃+* FiniteField.Extension K 2 2 :=
    (FiniteField.Extension.frob K 2 2).toRingEquiv with hφ
  have h1 : g ∈ entrywiseFixedGroup .E7 φ :=
    mem_entrywiseFixedGroup.2 ⟨hg, by
      rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self]; exact hσg⟩
  rw [entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (Or.inr (Or.inr (Or.inr
    (Or.inl rfl)))) (ringChar.eq _ 2) φ, fixedFieldImage,
    map_adjointGroup_baseChangeGL_eq_of_range_eq (fixSubfield φ).subtype
      (algebraMap K (FiniteField.Extension K 2 2)) ?_] at h1
  · obtain ⟨g₀, hg₀, rfl⟩ := h1
    exact ⟨g₀, hg₀, rfl⟩
  · ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (F4Pilot.frob_eq_self_iff (w : FiniteField.Extension K 2 2)).1 w.2
    · intro hz
      exact ⟨⟨z, (F4Pilot.frob_eq_self_iff z).2 hz⟩, rfl⟩


theorem perpLeviFrobDescent_E8 : E6Pilot.PerpLeviFrobDescent .E8 K := by
  intro d hd hσd
  set σ := (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom with hσ
  set ι := algebraMap K (FiniteField.Extension K 2 2) with hι
  set dl : e7Levi (FiniteField.Extension K 2 2) :=
    ⟨⟨d, rootSpan_le_adjointGroup_E8 _ hd⟩, mem_e7Levi_iff.2 hd⟩ with hdl
  have hfix : e7LeviBaseChange σ dl = dl := Subtype.ext (Subtype.ext hσd)
  have hfix' : adjointBaseChangeE7 σ (e7LeviEquiv _ dl) = e7LeviEquiv _ dl := by
    rw [← e7LeviEquiv_baseChange, hfix]
  obtain ⟨g₀, hg₀, hg₀d⟩ := exists_baseChangeGL_eq_of_frob_fixed_E7
    (e7LeviEquiv _ dl).2 (congrArg Subtype.val hfix')
  set d₀ : e7Levi K := (e7LeviEquiv K).symm ⟨g₀, hg₀⟩ with hd₀
  have hd₀d : e7LeviBaseChange ι d₀ = dl := by
    apply (e7LeviEquiv _).injective
    rw [e7LeviEquiv_baseChange, hd₀, MulEquiv.apply_symm_apply]
    exact Subtype.ext hg₀d
  refine ⟨((d₀ : adjointGroup .E8 K) : ModGL .E8 K), mem_e7Levi_iff.1 d₀.2, ?_⟩
  rw [← coe_e7LeviBaseChange, hd₀d]

end Descent

end CFSG.SeitzReduction.E8Pilot
