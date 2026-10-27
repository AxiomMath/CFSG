module

public import CFSG.Goldschmidt75.Comp26

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped commutatorElement

variable {L : Type*} [Group L] [Finite L]

omit [Finite L] in
theorem le_normalizer_commutator {N H K : Subgroup L} (hH : N ≤ normalizer (H : Set L))
    (hK : N ≤ normalizer (K : Set L)) : N ≤ normalizer ((⁅H, K⁆ : Subgroup L) : Set L) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator, mem_normalizer_iff_map_conj_eq.mp (hH hg),
    mem_normalizer_iff_map_conj_eq.mp (hK hg)]

omit [Finite L] in
theorem commutatorElement_mul_central {x a b : L} (ha : a ∈ center L) :
    ⁅x, a * b⁆ = ⁅x, b⁆ := by
  have hca : ∀ y : L, a * y = y * a := fun y => (mem_center_iff.mp ha y).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc x * (a * b) * x⁻¹ * (b⁻¹ * a⁻¹) = a * (x * b * x⁻¹ * b⁻¹) * a⁻¹ := by
        rw [show x * (a * b) = a * (x * b) by rw [← mul_assoc, ← hca x, mul_assoc]]; group
    _ = x * b * x⁻¹ * b⁻¹ := by rw [hca, mul_assoc, mul_inv_cancel, mul_one]

theorem eq_bot_of_coreSep_32 (hO : goldschmidtOddCore L = ⊥) {V₁ V₂ X : Subgroup L}
    {t u₁ u₂ v₁ : L}
    (hsep : ∀ K : Subgroup L, CFSG.IsComponent K →
      V₁ ≤ centralizer (K : Set L) ∨ V₂ ≤ centralizer (K : Set L))
    (ht : orderOf t = 2) (hX : X ≤ oddCoreOf (centralizer ({t} : Set L))) (hXV : ⁅X, V₁⁆ = X)
    (hv₁c : v₁ ∈ center L) (hu₂ : u₂ ∈ V₂) (htu : t = u₁ * u₂)
    (hc : u₁ * u₂ = u₂ * u₁) (hu₂2 : u₂ * u₂ = 1)
    (hV₁ : u₁ ∈ zpowers v₁ ∨ V₁ ≤ zpowers v₁ ⊔ zpowers u₁) : X = ⊥ := by
  by_contra hX1
  obtain ⟨K, hK, -, hXK, htC, hXC⟩ := exists_component_of_oddCore hO ht hX1 hX
  apply hXC
  have hXCt : X ≤ centralizer ({t} : Set L) := hX.trans (Subgroup.map_subtype_le _)
  rcases hsep K hK with h1 | h2
  · rw [← hXV]
    exact commutator_le_centralizer_of_centralizes h1 hXK
  have hu₂K : u₂ ∈ centralizer (K : Set L) := h2 hu₂
  have hcen : zpowers v₁ ≤ center L := zpowers_le.mpr hv₁c
  have hu₁v : u₁ ∉ zpowers v₁ := by
    intro hmem
    apply htC
    rw [htu]
    exact (centralizer _).mul_mem (Subgroup.center_le_centralizer _ (hcen hmem)) hu₂K
  have hV₁le : V₁ ≤ zpowers v₁ ⊔ zpowers u₁ := hV₁.resolve_left hu₁v
  have hNv : (zpowers v₁).Normal := normal_of_le_center hcen
  have htu₂ : t * u₂ = u₂ * t := by
    rw [htu]
    conv_lhs => rw [hc]
    rw [mul_assoc]
  have hu₁eq : u₁ = t * u₂ := by rw [htu, mul_assoc, hu₂2, mul_one]
  have htN : t ∈ normalizer (((⁅X, zpowers u₂⁆ : Subgroup L)) : Set L) := by
    refine le_normalizer_commutator (N := zpowers t) ?_ ?_ (mem_zpowers t)
    · rw [zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
        fun x hx => mem_centralizer_singleton_iff.mp (hXCt hx))
    · rw [zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
        fun w hw => by
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
          exact ((Commute.zpow_left htu₂.symm k).eq))
  have hstep : ⁅X, V₁⁆ ≤ ⁅X, zpowers u₂⁆ := by
    rw [commutator_le]
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_left.mp (hV₁le hy)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    rw [commutatorElement_mul_central (hcen ha)]
    have hxt : Commute x t := (mem_centralizer_singleton_iff.mp (hXCt hx))
    have hpow : u₁ ^ k = t ^ k * u₂ ^ k := by rw [hu₁eq]; exact htu₂ ▸ (Commute.mul_zpow htu₂ k)
    have e2 : ⁅x, t ^ k * u₂ ^ k⁆ = t ^ k * ⁅x, u₂ ^ k⁆ * (t ^ k)⁻¹ := by
      have hc' : x * t ^ k = t ^ k * x := (hxt.zpow_right k).eq
      rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
      calc x * (t ^ k * u₂ ^ k) * x⁻¹ * ((u₂ ^ k)⁻¹ * (t ^ k)⁻¹)
          = (x * t ^ k) * u₂ ^ k * x⁻¹ * (u₂ ^ k)⁻¹ * (t ^ k)⁻¹ := by group
        _ = (t ^ k * x) * u₂ ^ k * x⁻¹ * (u₂ ^ k)⁻¹ * (t ^ k)⁻¹ := by rw [hc']
        _ = t ^ k * (x * u₂ ^ k * x⁻¹ * (u₂ ^ k)⁻¹) * (t ^ k)⁻¹ := by group
    rw [hpow, e2]
    have hcm : ⁅x, u₂ ^ k⁆ ∈ ⁅X, zpowers u₂⁆ :=
      commutator_mem_commutator hx (zpow_mem (mem_zpowers u₂) k)
    exact (mem_normalizer_iff.mp (zpow_mem htN k) _).mp hcm
  rw [← hXV]
  exact hstep.trans (commutator_le_centralizer_of_centralizes (zpowers_le.mpr hu₂K) hXK)

end CFSG.Goldschmidt75
