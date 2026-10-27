module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Main
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Cocycle

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped commutatorElement

theorem nTwo_eq_sup_KA {G : Type*} [Group G] {D₂ K₂ D₁ A₂ : Subgroup G} (hA : A₂ ≤ D₂) :
    nTwo D₂ K₂ D₁ = D₂ ⊔ (K₂ ⊔ A₂) ⊔ D₁ := by
  refine le_antisymm (sup_le_sup_right (sup_le_sup_left le_sup_left _) _) ?_
  refine sup_le_sup_right (sup_le le_sup_left (sup_le le_sup_right (hA.trans le_sup_left))) _

theorem nTwo_normalizer' {G : Type*} [Group G] {D₂ K₂ D₁ A₂ : Subgroup G} (hA : A₂ ≤ D₂) {g : G}
    (h₂ : g ∈ normalizer (D₂ : Set G)) (hK : g ∈ normalizer ((K₂ ⊔ A₂ : Subgroup G) : Set G))
    (h₁ : g ∈ normalizer (D₁ : Set G)) :
    g ∈ normalizer ((nTwo D₂ K₂ D₁ : Subgroup G) : Set G) := by
  rw [nTwo_eq_sup_KA hA]
  exact mem_normalizer_sup' (mem_normalizer_sup' h₂ hK) h₁

theorem normalizer_nTwo_of_global {G : Type*} [Group G] {t : G} {D₂ K₂ D₁ A₂ S : Subgroup G}
    (hA : A₂ ≤ D₂)
    (hG1 : ∀ x ∈ normalizer (D₂ : Set G), x⁻¹ * (t * x * t⁻¹) ∈ D₂ →
      ∃ y ∈ normalizer (A₂ : Set G) ⊓ centralizer ({t} : Set G), y⁻¹ * x ∈ D₂)
    (hG2 : normalizer (A₂ : Set G) ⊓ centralizer ({t} : Set G) ≤
      K₂ ⊔ (normalizer (S : Set G) ⊓ centralizer ({t} : Set G)))
    (hNS : normalizer (S : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (D₂ : Set G) ⊓ normalizer ((K₂ ⊔ A₂ : Subgroup G) : Set G) ⊓
        normalizer (D₁ : Set G)) :
    ∀ x ∈ normalizer (D₂ : Set G), x⁻¹ * (t * x * t⁻¹) ∈ D₂ →
      x ∈ normalizer ((nTwo D₂ K₂ D₁ : Subgroup G) : Set G) := by
  have hN : K₂ ⊔ (normalizer (S : Set G) ⊓ centralizer ({t} : Set G)) ≤
      normalizer ((nTwo D₂ K₂ D₁ : Subgroup G) : Set G) := by
    refine sup_le ((le_sup_right.trans le_sup_left : K₂ ≤ nTwo D₂ K₂ D₁).trans le_normalizer)
      fun g hg => ?_
    obtain ⟨⟨h₂, hK⟩, h₁⟩ := hNS hg
    exact nTwo_normalizer' hA h₂ hK h₁
  intro x hx hxt
  obtain ⟨y, hy, hyx⟩ := hG1 x hx hxt
  have : x = y * (y⁻¹ * x) := by group
  rw [this]
  exact mul_mem (hN (hG2 hy))
    (le_normalizer ((le_sup_left.trans le_sup_left : D₂ ≤ nTwo D₂ K₂ D₁) hyx))

section Coboundary

variable {G : Type} [Group G] {t : G} {D₁ V₁ D₂ A₂ K₂ : Subgroup G} {θ₂ : SL3 →* G}
  {ιG : (Fin 9 → ZMod 2) → G}

theorem Y14Hyp.exists_coboundary_G [Finite G] (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) {s : G}
    (hs : s ∈ nTwo D₂ K₂ D₁) (hst : s * (t * s * t⁻¹) = 1) :
    ∃ g ∈ nTwo D₂ K₂ D₁, s⁻¹ * (g * (t * g * t⁻¹)⁻¹) ∈ D₂ := by
  have : Fact (ElemSec D₂ (⊥ : Subgroup G)) := ⟨h.elemSec⟩
  have hN := h.normal_nTwo
  obtain ⟨-, X, h1, h2, h3, -⟩ := h.r3bHyp.main
  have hτ : mk2 D₂ K₂ D₁ ⟨s, hs⟩ * tauG2 h (mk2 D₂ K₂ D₁ ⟨s, hs⟩) = 1 := by
    rw [tauG2_mk, ← map_mul]
    have e : (⟨s, hs⟩ : nTwo D₂ K₂ D₁) * conjD t h.t_mem_normalizer ⟨s, hs⟩ = 1 :=
      Subtype.ext hst
    rw [e, map_one]
  obtain ⟨γ, hγ⟩ := exists_coboundary h.pi_ττ h1 h2 h3 hτ
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective γ
  refine ⟨n, n.2, ?_⟩
  have e2 : (QuotientGroup.mk n : ↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)) =
      mk2 D₂ K₂ D₁ n := rfl
  rw [e2, tauG2_mk, ← map_inv, ← map_mul, Y14Hyp.mk2_eq_iff] at hγ
  simpa [conjD] using hγ

theorem Y14Hyp.mem_normalizer_of_comm [Finite G] (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG)
    (hG : ∀ x ∈ normalizer (D₂ : Set G), x⁻¹ * (t * x * t⁻¹) ∈ D₂ →
      x ∈ normalizer ((nTwo D₂ K₂ D₁ : Subgroup G) : Set G))
    {p : G} (hp : p ∈ normalizer (D₂ : Set G)) (hpt : p * t * p⁻¹ * t⁻¹ ∈ nTwo D₂ K₂ D₁) :
    p ∈ normalizer ((nTwo D₂ K₂ D₁ : Subgroup G) : Set G) := by
  have hst : (p * t * p⁻¹ * t⁻¹) * (t * (p * t * p⁻¹ * t⁻¹) * t⁻¹) = 1 := by
    have e : (p * t * p⁻¹ * t⁻¹) * (t * (p * t * p⁻¹ * t⁻¹) * t⁻¹) =
        p * (t * t) * p⁻¹ * (t * t)⁻¹ := by group
    rw [e, h.t_sq]; group
  obtain ⟨g, hg, hgD⟩ := h.exists_coboundary_G hpt hst
  have hgN : g ∈ normalizer (D₂ : Set G) := h.nTwo_le_normalizer hg
  have hc : g⁻¹ * p ∈ normalizer (D₂ : Set G) := mul_mem (inv_mem hgN) hp
  have ha : t * p⁻¹ * t⁻¹ ∈ normalizer (D₂ : Set G) :=
    mul_mem (mul_mem h.t_D₂ (inv_mem hp)) (inv_mem h.t_D₂)
  have hct : (g⁻¹ * p)⁻¹ * (t * (g⁻¹ * p) * t⁻¹) ∈ D₂ := by
    have := (mem_normalizer_iff.mp ha _).mp hgD
    convert this using 1
    group
  have hcN := hG _ hc hct
  have : p = g * (g⁻¹ * p) := by group
  rw [this]
  exact mul_mem (le_normalizer hg) hcN

theorem Y14Hyp.le_nTwo [Finite G] (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG)
    (hG : ∀ x ∈ normalizer (D₂ : Set G), x⁻¹ * (t * x * t⁻¹) ∈ D₂ →
      x ∈ normalizer ((nTwo D₂ K₂ D₁ : Subgroup G) : Set G))
    {P : Subgroup G} (hPD : P ≤ normalizer (D₂ : Set G))
    (hPt : ∀ p ∈ P, p * t * p⁻¹ * t⁻¹ ∈ nTwo D₂ K₂ D₁) {j : G} (hj : j ∈ nTwo D₂ K₂ D₁)
    (hJ : ∀ x ∈ P, x⁻¹ * ⁅j, x⁆ * ⁅j ^ 2, x⁆ ∈ D₁ ⊔ D₂) : P ≤ nTwo D₂ K₂ D₁ := by
  intro x hx
  have hxN := h.mem_normalizer_of_comm hG (hPD hx) (hPt x hx)
  have hc : ∀ k ∈ nTwo D₂ K₂ D₁, ⁅k, x⁆ ∈ nTwo D₂ K₂ D₁ := fun k hk => by
    have e : ⁅k, x⁆ = k * (x * k⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem hk ((mem_normalizer_iff.mp hxN _).mp (inv_mem hk))
  have hD : D₁ ⊔ D₂ ≤ nTwo D₂ K₂ D₁ := sup_le D₁_le_nTwo D₂_le_nTwo
  have h1 := hD (hJ x hx)
  have e : x = ⁅j, x⁆ * ⁅j ^ 2, x⁆ * (x⁻¹ * ⁅j, x⁆ * ⁅j ^ 2, x⁆)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (hc j hj) (hc _ (pow_mem hj 2))) (inv_mem h1)

end Coboundary

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
