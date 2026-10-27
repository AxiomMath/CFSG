module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47Transport
public import CFSG.LocalAnalysis.ComponentClassification.Foote5ActG
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {𝕊 : Type} [Group 𝕊]

theorem exists_actG_eq_of_footeFixed {a b : G} {K Kb : Subgroup G} (hKbe : footeFixed K b = Kb)
    (hK : IsTwoComponentAt a K) (hb : orderOf b = 2) (hbK : b ∈ coreActionKernel K)
    (hKb : IsTwoComponentAt b Kb) (ε : K ⧸ pPrimeCore 2 K ≃* 𝕊) :
    ∃ εb : Kb ⧸ pPrimeCore 2 Kb ≃* 𝕊, ∀ d : G, d ∈ normalizer (K : Set G) →
      d ∈ normalizer (Kb : Set G) → d ∈ centralizer ({b} : Set G) →
        actG Kb εb d = actG K ε d := by
  subst hKbe
  obtain ⟨φ, hφ⟩ := Foote47.exists_congr_oddBarConj_eq hK hb hbK hKb
  refine ⟨φ.symm.trans ε, fun d hdN hdNb hdb => ?_⟩
  rw [actG_of_mem _ hdNb, actG_of_mem _ hdN, act, act, MonoidHom.comp_apply,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
    ← hφ d hdN hdNb hdb]
  ext s
  simp [MulAut.congr_apply]

omit [Finite G] in
theorem mem_innAut_of_mem_commutator {Lin : Subgroup (MulAut 𝕊)} [Finite 𝕊]
    (hD : Foote5AutData 𝕊 Lin) {A P : Subgroup G} (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊)
    (hPN : P ≤ normalizer (A : Set G)) {c : G} (hc : c ∈ ⁅P, P⁆) :
    actG A ε c ∈ innAut5 𝕊 := by
  set K : Subgroup G :=
    ((innAut5 𝕊).comap (act A ε)).map (normalizer (A : Set G)).subtype with hK
  have hmemK : ∀ g ∈ normalizer (A : Set G), actG A ε g ∈ innAut5 𝕊 → g ∈ K := by
    intro g hg hgI
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    show act A ε ⟨g, hg⟩ ∈ innAut5 𝕊
    rw [← actG_of_mem ε hg]
    exact hgI
  have hle : ⁅P, P⁆ ≤ K := by
    rw [commutator_le]
    intro x hx y hy
    have hxN := hPN hx
    have hyN := hPN hy
    have h1 : x * y * x⁻¹ ∈ normalizer (A : Set G) := mul_mem (mul_mem hxN hyN) (inv_mem hxN)
    have h2 : ⁅x, y⁆ ∈ normalizer (A : Set G) := by
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem hyN)
    refine hmemK ⁅x, y⁆ h2 ?_
    rw [commutatorElement_def, actG_mul ε h1 (inv_mem hyN), actG_mul ε (mul_mem hxN hyN)
      (inv_mem hxN), actG_mul ε hxN hyN, actG_inv ε hxN, actG_inv ε hyN]
    exact hD.commutator_mem _ _
  obtain ⟨g, hg, rfl⟩ := hle hc
  have hg' : act A ε g ∈ innAut5 𝕊 := hg
  rw [subtype_apply, actG_of_mem ε g.2]
  exact hg'

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem exists_actG_footeF_eq (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊) {b : G} (hbQ : b ∈ Q)
    (hb2 : orderOf b = 2) :
    ∃ εb : footeF L₀ b ⧸ pPrimeCore 2 (footeF L₀ b) ≃* 𝕊, ∀ d ∈ normalizer (L : Set G),
      d ∈ centralizer ({b} : Set G) → actG (footeF L₀ b) εb d = actG L ε d := by
  have h4 := h.sec4
  have hbC : b ∈ coreActionKernel L := h.Q_le hbQ
  obtain ⟨hfix, hLb, hLbF⟩ := footeFixed_eq_footeF h4.hLB h4.hGA h4.hGC h4.hSA
    h4.footeFamilyType h4.huniq h4.hrank2 h.pmax h.memF hb2 hbC
  obtain ⟨εb, hεb⟩ := exists_actG_eq_of_footeFixed hfix h.zL hb2 hbC hLb ε
  exact ⟨εb, fun d hdN hdb =>
    hεb d hdN (le_normalizer_of_mem_footeFamilyOf h4.huniq hLb hLbF hdb) hdb⟩

end Sec5

end CFSG.ComponentClassification.Foote5
