module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Parts

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage2.Local.P34
open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound (bar_mem_barOf_iff bar_mem_conjugate_iff)
open CFSG.GH74.GLS.Stage2.Final.Thm6.L2012 (F20_conj_mem F20_le_OddCore)

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

@[expose] def CentCoreProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H J F₁ : Subgroup G), (∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) → J ≤ H →
    ⁅J, J⁆ = J → F₁ ≤ H → (∀ f ∈ F₁, ∀ j ∈ J, f * j * f⁻¹ * j⁻¹ ∈ pPrimeCoreOf 2 J) →
    Nat.Coprime (Nat.card ↥F₁) (Nat.card ↥⁅pPrimeCoreOf 2 J, J⁆) →
    ∀ S₀ : Subgroup G, S₀ ≤ J → (∀ s ∈ S₀, ∀ f ∈ F₁, s * f * s⁻¹ ∈ F₁) →
      (∀ s ∈ S₀, ∀ f ∈ F₁, s * f = f * s) ∧
      ∀ j ∈ J, ∃ d ∈ J, (∀ f ∈ F₁, d * f = f * d) ∧ j * d⁻¹ ∈ pPrimeCoreOf 2 J

section Basic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem perfect_of_pCompIn {H K : Subgroup G} (hKH : K ≤ H) (h : IsPComponent 2 (K.subgroupOf H)) :
    ⁅K, K⁆ = K := by
  have hp : Group.IsPerfect (K.subgroupOf H) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect h
  have hp' : Group.IsPerfect K := by
    have e := Subgroup.subgroupOfEquivOfLe hKH
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Subgroup.isPerfect_iff.mp hp'

end Basic

section CentS

variable {G : Type} [Group G] [Finite G]

theorem centS20_of (h20b : Coprime20b) (hcore : CentCoreProp) : CentS20 := by
  intro G _ _ z k S hC g hg hJ hSJ
  have hctx : Stage2Ctx G z k S := hC.1.ctx.ctx17.ctx
  set H := H0 z g with hH
  set J := J0 z g with hJdef
  set F₁ : Subgroup G := F20 z ⊓ pPrimeCoreOf 2 H with hF₁
  have hJH : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J := fun h hh j hj => J0_conj_mem z g hh hj
  have hJle : J ≤ H := J0_le_H0 z g
  have hperf : ⁅J, J⁆ = J := perfect_of_pCompIn hJle hJ.comp
  have hF₁H : F₁ ≤ H := inf_le_right.trans (CFSG.RankThree.PartTwo.Sec14.pPrimeCoreOf_le 2 H)
  have hF₁N : ∀ f ∈ F₁, ∀ j ∈ J, f * j * f⁻¹ * j⁻¹ ∈ pPrimeCoreOf 2 J := by
    intro f hf j hj
    have hfH : f ∈ H := hF₁H hf
    have hjH : j ∈ H := hJle hj
    refine inf_pPrimeCoreOf_le hJle hJH ⟨?_, ?_⟩
    · exact J.mul_mem (hJH f hfH j hj) (J.inv_mem hj)
    · have h1 : j * f⁻¹ * j⁻¹ ∈ pPrimeCoreOf 2 H :=
        pPrimeCoreOf_conj_mem hjH ((pPrimeCoreOf 2 H).inv_mem hf.2)
      have e : f * j * f⁻¹ * j⁻¹ = f * (j * f⁻¹ * j⁻¹) := by group
      rw [e]
      exact (pPrimeCoreOf 2 H).mul_mem hf.2 h1
  have hcop : Nat.Coprime (Nat.card ↥F₁) (Nat.card ↥⁅pPrimeCoreOf 2 J, J⁆) := by
    refine Nat.coprime_of_dvd fun r hr h1 h2 => ?_
    have h3 : r ∣ Nat.card ↥(F20 z) := h1.trans (Subgroup.card_dvd_of_le inf_le_left)
    exact h20b G z k S hC g hg hJ r hr h3 h2
  have hSF : ∀ s ∈ S, ∀ f ∈ F₁, s * f * s⁻¹ ∈ F₁ := by
    intro s hs f hf
    exact ⟨F20_conj_mem z (hctx.S_le_Cen hs) hf.1, pPrimeCoreOf_conj_mem (hJle (hSJ hs)) hf.2⟩
  exact hcore G H J F₁ hJH hJle hperf hF₁H hF₁N hcop S hSJ hSF

end CentS

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
