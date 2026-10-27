module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWACent
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Act

variable {G : Type} [Group G] {L : Subgroup G}

theorem mem_sup_zpowers_of_inner {t : G}
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {g : G}
    (hgC : g ∈ centralizer ({t} : Set G)) {l : G} (hl : l ∈ L)
    (h : ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹) : g ∈ L ⊔ zpowers t := by
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hlt : l ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) l hl)
  have hlg : l⁻¹ * g ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun x hx => ?_, mul_mem (inv_mem hlt) hgC⟩
    have h1 := h x hx
    calc x * (l⁻¹ * g) = l⁻¹ * (l * x * l⁻¹) * g := by group
      _ = l⁻¹ * (g * x * g⁻¹) * g := by rw [← h1]
      _ = l⁻¹ * g * x := by group
  rw [hKt] at hlg
  have h2 : g = l * (l⁻¹ * g) := by group
  rw [h2]
  exact mul_mem (mem_sup_left hl) (mem_sup_right hlg)

theorem outer_of_not_mem_sup {t : G}
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {g : G}
    (hgC : g ∈ centralizer ({t} : Set G)) (hg : g ∉ L ⊔ zpowers t) :
    ∀ l ∈ L, ∃ x ∈ L, g * x * g⁻¹ ≠ l * x * l⁻¹ := by
  intro l hl
  by_contra h
  push Not at h
  exact hg (mem_sup_zpowers_of_inner hKt hgC hl h)

variable [Finite G]

theorem exists_mul_self_mem_zpowers (hset : SeitzSetting G L) {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {g : G}
    (hgC : g ∈ centralizer ({t} : Set G)) (hg : g ∉ L ⊔ zpowers t) :
    ∃ l ∈ L, (l⁻¹ * g) * (l⁻¹ * g) ∈ zpowers t := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
  have hgL : g ∈ normalizer (L : Set G) := hCN hgC
  set α : MulAut (projectiveSL 5 K) := e.symm.trans ((conjAutOfMemNormalizer hgL).trans e)
    with hα
  have hαapp : ∀ x : projectiveSL 5 K, ((e.symm (α x) : L) : G) = g * (e.symm x : G) * g⁻¹ := by
    intro x
    rw [hα, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      coe_conjAutOfMemNormalizer_apply]
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := K) (n := 5) (by norm_num)).2 α
  rw [SeitzQ2.fieldAut_eq_one_of_card_eq_two hK σ, mul_one] at hαeq
  obtain ⟨p, hp⟩ := SeitzQ2.conjAut_mem_inner_of_card_eq_two hK A
  set l : L := e.symm p with hl
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    exfalso
    rw [pow_zero, mul_one, ← hp] at hαeq
    refine hg (mem_sup_zpowers_of_inner hKt hgC l.2 fun x hx => ?_)
    have h1 := hαapp (e ⟨x, hx⟩)
    rw [hαeq, MulAut.conj_apply, MulEquiv.symm_apply_apply] at h1
    rw [← h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, ← hl]
    rfl
  ·
    rw [pow_one, ← hp] at hαeq
    refine ⟨l, l.2, ?_⟩
    set y := (l : G)⁻¹ * g with hy
    have hδ : ∀ x : L, y * (x : G) * y⁻¹ = (e.symm (dualAut 5 K (e x)) : G) := by
      intro x
      have h1 := hαapp (e x)
      rw [hαeq, MulAut.mul_apply, MulAut.conj_apply, MulEquiv.symm_apply_apply, map_mul,
        map_mul, map_inv] at h1
      have h2 : y * (x : G) * y⁻¹ = (l : G)⁻¹ * (g * (x : G) * g⁻¹) * l := by rw [hy]; group
      rw [h2, ← h1]
      change (l : G)⁻¹ * ((l : G) * _ * (l : G)⁻¹) * l = _
      group
    have hδδ : dualAut 5 K * dualAut 5 K = 1 :=
      (standard_automorphism_transport (K := K) (n := 5)).2.2.2.1
    have hlt : (l : G) ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) l l.2)
    have hyC : y ∈ centralizer ({t} : Set G) := mul_mem (inv_mem hlt) hgC
    have hyy : y * y ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
      refine mem_inf.2 ⟨mem_centralizer_iff.2 fun x hx => ?_, mul_mem hyC hyC⟩
      have h1 := hδ ⟨x, hx⟩
      have h2 := hδ (e.symm (dualAut 5 K (e ⟨x, hx⟩)))
      rw [MulEquiv.apply_symm_apply, ← MulAut.mul_apply, hδδ, MulAut.one_apply,
        MulEquiv.symm_apply_apply, ← h1] at h2
      calc x * (y * y) = (y * y) * (y⁻¹ * (y⁻¹ * x * y) * y) := by group
        _ = (y * y) * x := by
          have h3 : y⁻¹ * (y⁻¹ * x * y) * y = x := by
            calc y⁻¹ * (y⁻¹ * x * y) * y = y⁻¹ * (y⁻¹ * (y * (y * x * y⁻¹) * y⁻¹) * y) * y := by
                  rw [h2]
              _ = x := by group
          rw [h3]
    rw [hKt] at hyy
    exact hyy

end Act

end CFSG.SeitzReduction.LinearPilot
