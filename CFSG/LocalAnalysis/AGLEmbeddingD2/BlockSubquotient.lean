module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockInnerStep
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LeviSection
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.AGLEmbeddingD2.InnerStep

open CFSG.Open CFSG.AGLEmbedding

section Quot

variable {Y : Type*} [Group Y]

@[expose] noncomputable def conjQuot (Lb : Subgroup Y) :
    ↥Lb ⧸ Subgroup.center ↥Lb →* MulAut ↥Lb :=
  QuotientGroup.lift (Subgroup.center ↥Lb) (MulAut.conj : ↥Lb →* MulAut ↥Lb) fun z hz => by
    rw [MonoidHom.mem_ker]
    ext w
    simp [MulAut.conj_apply, (Subgroup.mem_center_iff.mp hz w).symm]

theorem conjQuot_mk (Lb : Subgroup Y) (l : ↥Lb) :
    conjQuot Lb (QuotientGroup.mk' (Subgroup.center ↥Lb) l) = MulAut.conj l := rfl

theorem hasSubquotient_of_inner_quotient {Lb J : Subgroup Y} (hJL : J ≤ Lb)
    {W : Type*} [Group W] (β : W →* Y) (hβN : ∀ w, β w ∈ Subgroup.normalizer (Lb : Set Y))
    (hβJ : ∀ w, ∃ l ∈ J, β w * l⁻¹ ∈ Subgroup.centralizer (Lb : Set Y))
    {Q : Type*} [Group Q] (φ : W →* Q) (hφ : Function.Surjective φ)
    (hker : ∀ w, β w ∈ Subgroup.centralizer (Lb : Set Y) → φ w = 1) :
    LeviSection.HasSubquotient ((J.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)))
      Q := by
  set Nn := Subgroup.normalizer (Lb : Set Y) with hNn
  set ρ : Nn →* MulAut Lb := Lb.normalizerMonoidHom with hρ
  have hρker : ∀ g : Nn, ρ g = 1 ↔ (g : Y) ∈ Subgroup.centralizer (Lb : Set Y) := by
    intro g
    constructor
    · intro h1
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h2 := congrArg (fun f : MulAut Lb => ((f ⟨w, hw⟩ : Lb) : Y)) h1
      simp only [hρ, MulAut.one_apply] at h2
      change (g : Y) * w * (g : Y)⁻¹ = w at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · intro hg
      ext ⟨w, hw⟩
      change (g : Y) * w * (g : Y)⁻¹ = w
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.mp hg w hw).symm
  set β' : W →* Nn := β.codRestrict Nn hβN with hβ'
  set f : W →* MulAut Lb := ρ.comp β' with hf
  have hsurj : Function.Surjective (φ.comp (⊤ : Subgroup W).subtype) := fun q => by
    obtain ⟨w, rfl⟩ := hφ q
    exact ⟨⟨w, Subgroup.mem_top w⟩, rfl⟩
  have h1 : LeviSection.HasSubquotient ((⊤ : Subgroup W).map f) Q :=
    LeviSection.HasSubquotient.map f le_rfl _ hsurj fun x hx => hker x ((hρker (β' x)).mp hx)
  refine LeviSection.HasSubquotient.of_map (conjQuot Lb) (h1.mono ?_)
  rintro _ ⟨w, -, rfl⟩
  obtain ⟨l, hl, hxl⟩ := hβJ w
  have hlN : l ∈ Nn := Subgroup.le_normalizer (hJL hl)
  have h2 : ρ (β' w * (⟨l, hlN⟩ : Nn)⁻¹) = 1 := (hρker _).mpr hxl
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  refine ⟨QuotientGroup.mk' (Subgroup.center ↥Lb) ⟨l, hJL hl⟩,
    ⟨⟨l, hJL hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩, ?_⟩
  rw [conjQuot_mk]
  change MulAut.conj (⟨l, hJL hl⟩ : ↥Lb) = ρ (β' w)
  rw [h2]
  ext ⟨v, hv⟩
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rfl

end Quot

section Block

variable {G : Type} [Group G]

theorem hasSubquotient_parabImage {M S L U : Subgroup G}
    (hSL : barM M S ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hB : BlockInnerNormalizerAt M S L) (hUM : U ≤ M)
    (hUN : U ≤ Subgroup.normalizer (S : Set G))
    (hUL : barM M U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {Q : Type*} [Group Q] (φ : U →* Q) (hφ : Function.Surjective φ)
    (hker : ∀ u ∈ centralizerBar M hUM (barM M L), φ u = 1) :
    LeviSection.HasSubquotient (((blockPL M S L).subgroupOf (barM M L)).map
      (QuotientGroup.mk' (Subgroup.center ↥(barM M L)))) Q := by
  set Lb := barM M L with hLb
  have hPL : blockPL M S L ≤ Lb := barM_mono inf_le_right
  have hUK : ∀ u : U, barElt M hUM u ∈ barM M (Subgroup.normalizer (S : Set G)) := fun u =>
    barM_mono hUN (barElt_mem_barM hUM u)
  refine hasSubquotient_of_inner_quotient hPL (barElt M hUM)
    (fun u => (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _))
      (hUL (barElt_mem_barM hUM u))) (fun u => ?_) φ hφ hker
  exact exists_mem_of_inner hSL hB (mem_normalizer_barM_of_mem_barM_normalizer (hUK u))
    (hUL (barElt_mem_barM hUM u))

end Block

end CFSG.AGLEmbeddingD2.InnerStep
