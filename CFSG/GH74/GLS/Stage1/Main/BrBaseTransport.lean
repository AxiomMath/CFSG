module

public import CFSG.GH74.GLS.Stage1.Main.BrPairStd4

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Abstract

variable {Γ : Type*} [Group Γ]

theorem mem_sup_iff_of_comps {W : Subgroup Γ}
    (hWc : ∀ H : Subgroup ↥W, IsComponent H → IsComponent (H.map W.subtype)) {A₁ A₂ : Subgroup Γ}
    (hcomps : {K : Subgroup Γ | IsComponent K} = {A₁, A₂}) {Y : Type*} [Group Y]
    (Ψ : ↥W ≃* Y) {E₁ E₂ : Subgroup Y} (hE₁ : IsComponent E₁) (hE₂ : IsComponent E₂)
    (hne : E₁ ≠ E₂) (γ : ↥W) : (γ : Γ) ∈ A₁ ⊔ A₂ ↔ Ψ γ ∈ E₁ ⊔ E₂ := by
  set F₁ : Subgroup Γ := (E₁.map Ψ.symm.toMonoidHom).map W.subtype with hF₁
  set F₂ : Subgroup Γ := (E₂.map Ψ.symm.toMonoidHom).map W.subtype with hF₂
  have hc₁ : IsComponent F₁ := hWc _ (isComponent_map_of_isComponent Ψ.symm hE₁)
  have hc₂ : IsComponent F₂ := hWc _ (isComponent_map_of_isComponent Ψ.symm hE₂)
  have hF₁m : F₁ ∈ ({A₁, A₂} : Set (Subgroup Γ)) := by rw [← hcomps]; exact hc₁
  have hF₂m : F₂ ∈ ({A₁, A₂} : Set (Subgroup Γ)) := by rw [← hcomps]; exact hc₂
  have hFne : F₁ ≠ F₂ := by
    intro h
    apply hne
    have h1 : E₁.map Ψ.symm.toMonoidHom = E₂.map Ψ.symm.toMonoidHom :=
      Subgroup.map_injective W.subtype_injective h
    exact Subgroup.map_injective Ψ.symm.injective h1
  have hsup : F₁ ⊔ F₂ = A₁ ⊔ A₂ := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF₁m hF₂m
    rcases hF₁m with h1 | h1 <;> rcases hF₂m with h2 | h2
    · exact absurd (h1.trans h2.symm) hFne
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
    · exact absurd (h1.trans h2.symm) hFne
  have hmem : ∀ H : Subgroup Y, (γ : Γ) ∈ (H.map Ψ.symm.toMonoidHom).map W.subtype ↔ Ψ γ ∈ H := by
    intro H
    constructor
    · rintro ⟨y', ⟨h, hh, rfl⟩, hy'⟩
      have : Ψ.symm h = γ := Subtype.ext hy'
      rw [← this, MulEquiv.apply_symm_apply]
      exact hh
    · intro h
      exact ⟨Ψ.symm (Ψ γ), ⟨Ψ γ, h, rfl⟩, by simp⟩
  rw [← hsup, hF₁, hF₂, ← Subgroup.map_sup, ← Subgroup.map_sup]
  exact hmem _

end Abstract

section Transport

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem LBar_eq_imgBar (hII : II4_4_4_center) (h41 : Prop4_1) (hs : Std4 G z S K₁ K₂) :
    LBar z = imgBar z K₁ ⊔ imgBar z K₂ :=
  LBar_eq_pair_of_std4 hII h41 hs

theorem exists_sigma_of_compat (hXC : K₁ ⊔ K₂ ⊔ S ≤ centralizer ({z} : Set G))
    (hWc : ∀ H : Subgroup ↥(barOf z (K₁ ⊔ K₂ ⊔ S)), IsComponent H →
      IsComponent (H.map (barOf z (K₁ ⊔ K₂ ⊔ S)).subtype))
    (hcomps : {K : Subgroup (CentralizerBar z) | IsComponent K} = {imgBar z K₁, imgBar z K₂})
    (hLB : LBar z = imgBar z K₁ ⊔ imgBar z K₂) (hSp : IsPGroup 2 ↥S)
    (hS : ∀ s ∈ S, s ∈ Oz z → s = 1) {Gs : Type} [Group Gs] {E S' E₁ E₂ : Subgroup Gs}
    (hE : E = E₁ ⊔ E₂) (hcompat : Compat7 z (K₁ ⊔ K₂ ⊔ S) S E S')
    (hc₁ : IsComponent (E₁.subgroupOf (E ⊔ S'))) (hc₂ : IsComponent (E₂.subgroupOf (E ⊔ S')))
    (hne : E₁.subgroupOf (E ⊔ S') ≠ E₂.subgroupOf (E ⊔ S')) :
    ∃ σ : ↥S ≃* ↥S', ∀ s : ↥S, ((s : G) ∈ LC z ↔ ((σ s : ↥S') : Gs) ∈ E) := by
  obtain ⟨hN, ψ, hψS, hψS', -⟩ := hcompat
  set X : Subgroup G := K₁ ⊔ K₂ ⊔ S with hX
  have hSX : S ≤ X := le_sup_right
  let φ : ↥X →* CentralizerBar z := (toBar z).comp (Subgroup.inclusion hXC)
  have hker : φ.ker = (Oz z).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hatMk_eq_one_iff (Cz z) ⟨(x : G), hXC x.2⟩
  have hrange : φ.range = barOf z X := by
    show ((toBar z).comp (Subgroup.inclusion hXC)).range = (X.subgroupOf (Cen z)).map (toBar z)
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hWn : ∀ H : Subgroup ↥φ.range, IsComponent H → IsComponent (H.map φ.range.subtype) := by
    rw [hrange]; exact hWc
  let e : (↥X ⧸ (Oz z).subgroupOf X) ≃* ↥φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  let Ψ : ↥φ.range ≃* ↥(E ⊔ S') := e.symm.trans ψ
  let g : ↥S →* ↥(E ⊔ S') :=
    ψ.toMonoidHom.comp ((QuotientGroup.mk' ((Oz z).subgroupOf X)).comp (Subgroup.inclusion hSX))
  have hgS : ∀ s : ↥S, (g s : Gs) ∈ S' := fun s => hψS ⟨(s : G), hSX s.2⟩ s.2
  let f : ↥S →* ↥S' :=
    { toFun := fun s => ⟨(g s : Gs), hgS s⟩
      map_one' := Subtype.ext (by
        show ((g 1 : ↥(E ⊔ S')) : Gs) = 1
        rw [map_one]
        rfl)
      map_mul' := fun x y => Subtype.ext (by
        show ((g (x * y) : ↥(E ⊔ S')) : Gs) = (g x : Gs) * (g y : Gs)
        rw [map_mul]
        rfl) }
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : g x = g y := Subtype.ext
      (show ((g x : ↥(E ⊔ S')) : Gs) = (g y : Gs) from congrArg (fun u : ↥S' => (u : Gs)) hxy)
    have h2 : (QuotientGroup.mk (Subgroup.inclusion hSX x) : ↥X ⧸ (Oz z).subgroupOf X) =
        QuotientGroup.mk (Subgroup.inclusion hSX y) := ψ.injective h1
    rw [QuotientGroup.eq] at h2
    have h3 : (x : G)⁻¹ * y ∈ Oz z := h2
    have h4 : (x : G)⁻¹ * y = 1 := hS _ (S.mul_mem (S.inv_mem x.2) y.2) h3
    exact Subtype.ext (inv_mul_eq_one.1 h4)
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : Gs) ∈ E ⊔ S' := Subgroup.mem_sup_right y.2
    obtain ⟨s, hsS, hs⟩ := hψS' (ψ.symm ⟨y, hy⟩) (by simp)
    refine ⟨⟨(s : G), hsS⟩, ?_⟩
    apply Subtype.ext
    show ((g ⟨(s : G), hsS⟩ : ↥(E ⊔ S')) : Gs) = y
    have : g ⟨(s : G), hsS⟩ = ⟨y, hy⟩ := by
      show ψ (QuotientGroup.mk (Subgroup.inclusion hSX ⟨(s : G), hsS⟩)) = _
      have e' : Subgroup.inclusion hSX ⟨(s : G), hsS⟩ = s := Subtype.ext rfl
      rw [e', hs]
      exact ψ.apply_symm_apply _
    rw [this]
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥S ≃* ↥S', ∀ s : ↥S, ((σ s : ↥S') : Gs) = (g s : Gs) :=
    ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun s => rfl⟩
  refine ⟨σ, fun s => ?_⟩
  have hsX : (s : G) ∈ X := hSX s.2
  have hsC : (s : G) ∈ centralizer ({z} : Set G) := hXC hsX
  set γ : ↥φ.range := e (QuotientGroup.mk ⟨(s : G), hsX⟩) with hγ
  have hγ' : (γ : CentralizerBar z) = toBar z ⟨(s : G), hsC⟩ := rfl
  have hΨγ : ((Ψ γ : ↥(E ⊔ S')) : Gs) = ((σ s : ↥S') : Gs) := by
    rw [hσ]
    show ((e.symm.trans ψ) (e (QuotientGroup.mk ⟨(s : G), hsX⟩)) : Gs) = (g s : Gs)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨k, hk⟩ := hSp ⟨(s : G), s.2⟩
  have hk' : (⟨(s : G), hsC⟩ : ↥(Cen z)) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hLC : (s : G) ∈ LC z ↔ toBar z ⟨(s : G), hsC⟩ ∈ LBar z :=
    mem_LC_iff_of_pElt (z := z) ⟨(s : G), hsC⟩ hk'
  rw [hLC, hLB, ← hγ', mem_sup_iff_of_comps hWn hcomps Ψ hc₁ hc₂ hne γ]
  have h1 : E₁ ≤ E ⊔ S' := by
    rw [hE]
    exact le_sup_left.trans le_sup_left
  have h2 : E₂ ≤ E ⊔ S' := by
    rw [hE]
    exact le_sup_right.trans le_sup_left
  rw [← Subgroup.subgroupOf_sup h1 h2, ← hE, Subgroup.mem_subgroupOf, hΨγ]

end Transport

end CFSG.GH74.GLS.Stage1.Main
