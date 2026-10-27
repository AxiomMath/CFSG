module

public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx65

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

section SwapAbstract

variable {Γ : Type*} [Group Γ]

theorem isComponent_map_subtype_of_normal {W : Subgroup Γ} (hW : W.Normal) {H : Subgroup ↥W}
    (hH : IsComponent H) : IsComponent (H.map W.subtype) := by
  refine ⟨?_, ?_⟩
  · exact (isQuasisimple_congr (H.equivMapOfInjective W.subtype W.subtype_injective)).1 hH.1
  · have hle : H.map W.subtype ≤ W := Subgroup.map_subtype_le H
    refine Subgroup.IsSubnormal.trans hle ?_ hW.isSubnormal
    have : (H.map W.subtype).subgroupOf W = H :=
      Subgroup.comap_map_eq_self_of_injective W.subtype_injective H
    rw [this]
    exact hH.2

theorem map_conj_equiv {Y : Type*} [Group Y] (Ψ : Γ ≃* Y) (H : Subgroup Γ) (g : Γ) :
    (H.map (MulAut.conj g).toMonoidHom).map Ψ.toMonoidHom =
      (H.map Ψ.toMonoidHom).map (MulAut.conj (Ψ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  ext x
  simp [MulAut.conj_apply]

theorem swap_of_comps {W : Subgroup Γ}
    (hWc : ∀ H : Subgroup ↥W, IsComponent H → IsComponent (H.map W.subtype)) {A₁ A₂ : Subgroup Γ}
    (hcomps : {K : Subgroup Γ | IsComponent K} = {A₁, A₂})
    {Y : Type*} [Group Y] (Ψ : ↥W ≃* Y) {E₁ E₂ : Subgroup Y} (hE₁ : IsComponent E₁)
    (hE₂ : IsComponent E₂) (hne : E₁ ≠ E₂) (u : Y)
    (hu₁ : E₁.map (MulAut.conj u).toMonoidHom = E₂) (hu₂ : E₂.map (MulAut.conj u).toMonoidHom = E₁) :
    A₁.map (MulAut.conj ((Ψ.symm u : ↥W) : Γ)).toMonoidHom = A₂ ∧
      A₂.map (MulAut.conj ((Ψ.symm u : ↥W) : Γ)).toMonoidHom = A₁ := by
  set w : ↥W := Ψ.symm u with hw
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
  have hconj : ∀ (H : Subgroup Y),
      ((H.map (MulAut.conj u).toMonoidHom).map Ψ.symm.toMonoidHom).map W.subtype =
        ((H.map Ψ.symm.toMonoidHom).map W.subtype).map (MulAut.conj (w : Γ)).toMonoidHom := by
    intro H
    rw [map_conj_equiv Ψ.symm H u, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    ext x
    simp [MulAut.conj_apply, hw]
  have hF₁₂ : F₁.map (MulAut.conj (w : Γ)).toMonoidHom = F₂ := by
    rw [hF₁, hF₂, ← hconj, hu₁]
  have hF₂₁ : F₂.map (MulAut.conj (w : Γ)).toMonoidHom = F₁ := by
    rw [hF₁, hF₂, ← hconj, hu₂]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF₁m hF₂m
  rcases hF₁m with h1 | h1 <;> rcases hF₂m with h2 | h2
  · exact absurd (h1.trans h2.symm) hFne
  · rw [h1, h2] at hF₁₂ hF₂₁; exact ⟨hF₁₂, hF₂₁⟩
  · rw [h1, h2] at hF₁₂ hF₂₁; exact ⟨hF₂₁, hF₁₂⟩
  · exact absurd (h1.trans h2.symm) hFne

end SwapAbstract

section SwapCompat

theorem map_conj_inv_eq_of_map_conj {Γ : Type*} [Group Γ] {A B : Subgroup Γ} {g : Γ}
    (h : A.map (MulAut.conj g).toMonoidHom = B) : B.map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [← h, Subgroup.map_map]
  have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id Γ := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
    group
  rw [this, Subgroup.map_id]

variable {G : Type} [Group G]

theorem exists_swap_of_compat {z : G} {S K₁ K₂ : Subgroup G}
    (hXC : K₁ ⊔ K₂ ⊔ S ≤ centralizer ({z} : Set G))
    (hWc : ∀ H : Subgroup ↥(barOf z (K₁ ⊔ K₂ ⊔ S)), IsComponent H →
      IsComponent (H.map (barOf z (K₁ ⊔ K₂ ⊔ S)).subtype))
    (hcomps : {K : Subgroup (CentralizerBar z) | IsComponent K} = {imgBar z K₁, imgBar z K₂})
    {Gs : Type} [Group Gs] {E S' : Subgroup Gs} (hcompat : Compat7 z (K₁ ⊔ K₂ ⊔ S) S E S')
    {E₁ E₂ : Subgroup ↥(E ⊔ S')} (hE₁ : IsComponent E₁) (hE₂ : IsComponent E₂) (hne : E₁ ≠ E₂)
    (u : ↥(E ⊔ S')) (huS : (u : Gs) ∈ S')
    (hu₁ : E₁.map (MulAut.conj u).toMonoidHom = E₂)
    (hu₂ : E₂.map (MulAut.conj u).toMonoidHom = E₁) :
    ∃ s ∈ S, Swaps z s (imgBar z K₁) (imgBar z K₂) := by
  obtain ⟨hN, ψ, -, hψS', -⟩ := hcompat
  set X : Subgroup G := K₁ ⊔ K₂ ⊔ S with hX
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
  obtain ⟨s, hsS, hs⟩ := hψS' (ψ.symm u) (by simpa using huS)
  have hΨ : ((Ψ.symm u : ↥φ.range) : CentralizerBar z) = φ s := by
    have h1 : Ψ.symm u = e (ψ.symm u) := rfl
    rw [h1, ← hs]
    rfl
  obtain ⟨h₁, h₂⟩ := swap_of_comps hWn hcomps Ψ hE₁ hE₂ hne u hu₁ hu₂
  rw [hΨ] at h₁ h₂
  refine ⟨(s : G), hsS, hXC s.2, ?_, ?_⟩
  · exact map_conj_inv_eq_of_map_conj h₂
  · exact map_conj_inv_eq_of_map_conj h₁

end SwapCompat

end CFSG.GH74.GLS.Stage1.Main
