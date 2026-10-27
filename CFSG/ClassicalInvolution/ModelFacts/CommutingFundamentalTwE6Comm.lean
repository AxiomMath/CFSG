module

public import CFSG.LieType.Steinberg.TwistedE6.Local

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

section Roots

theorem twistedE6_rho_add_of_fixed {a b : Fin (Tag.rank .E6) → ℤ} (hb : rho b = b) :
    rho (a + b) = rho a + b := by
  change rho a + rho b = _
  rw [hb]

theorem twistedE6_rho_add_ne_of_fixed {a b : Fin (Tag.rank .E6) → ℤ} (hb : rho b = b)
    (ha : rho a ≠ a) : rho (a + b) ≠ a + b := fun h =>
  ha (add_right_cancel (by rwa [twistedE6_rho_add_of_fixed hb] at h))

theorem twistedE6_rho_add_rho_add_of_fixed {a b : Fin (Tag.rank .E6) → ℤ} (hb : rho b = b) :
    rho (a + rho a + b) = a + rho a + b := by
  change rho a + rho (rho a) + rho b = _
  rw [hb, rho_rho, add_comm (rho a) a]

end Roots

section Extraction

private theorem commutatorElement_mul_expand {G : Type*} [Group G] (A B X : G) :
    ⁅A * B, X⁆ = ⁅A, ⁅B, X⁆⁆ * ⁅B, X⁆ * ⁅A, X⁆ := by
  simp only [commutatorElement_def]
  group

variable {k : Type*} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

theorem commutator_xPair_xFixed {a b : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a)
    (hb : IsRoot .E6 b) (hρb : rho b = b) (hρa : rho a ≠ a) (hab : IsRoot .E6 (a + b))
    (hγ : IsRoot .E6 (a + rho a + b)) :
    ∃ σ₁ σ₂ : k, IsSign σ₁ ∧ IsSign σ₂ ∧ ∀ t : k, ∃ g₀ : k, θ g₀ = g₀ ∧
      ((⁅xPair θ hθ ha hρa t, xFixed θ hb hρb 1 (map_one θ)⁆ : fixedGroup k θ) :
          e6Data_valid.minGroup k) =
        e6Data_valid.xm k (a + rho a + b) g₀ *
          (e6Data_valid.xm k (rho a + b) (σ₂ * ((twistSign a : k) * θ t) * 1) *
            e6Data_valid.xm k (a + b) (σ₁ * t * 1)) := by
  have hρab : IsRoot .E6 (rho a + b) := by
    have := isRoot_rho hab
    rwa [twistedE6_rho_add_of_fixed hρb] at this
  have hγ' : IsRoot .E6 (a + (rho a + b)) := by rwa [← add_assoc]
  have hρa' : IsRoot .E6 (rho a) := isRoot_rho ha
  obtain ⟨σ₁, hσ₁, h₁⟩ := (e6Data_valid.commutator_xm k ha hb hab.ne_zero).1 hab
  obtain ⟨σ₂, hσ₂, h₂⟩ := (e6Data_valid.commutator_xm k hρa' hb hρab.ne_zero).1 hρab
  obtain ⟨σ₃, hσ₃, h₃⟩ := (e6Data_valid.commutator_xm k ha hρab hγ'.ne_zero).1 hγ'
  refine ⟨σ₁, σ₂, hσ₁, hσ₂, fun t => ⟨σ₃ * t * (σ₂ * ((twistSign a : k) * θ t) * 1), ?_, ?_⟩⟩
  · have hσθ : ∀ σ : k, IsSign σ → θ σ = σ := by
      rintro σ (rfl | rfl) <;> simp
    have hεθ : θ ((twistSign a : ℤ) : k) = ((twistSign a : ℤ) : k) := map_intCast θ _
    simp only [map_mul, hσθ _ hσ₃, hσθ _ hσ₂, hεθ, hθ, map_one]
    ring
  · have e1 := commutatorElement_mul_expand (e6Data_valid.xm k a t)
      (e6Data_valid.xm k (rho a) ((twistSign a : k) * θ t)) (e6Data_valid.xm k b 1)
    have e2 := h₂ ((twistSign a : k) * θ t) 1
    have e3 := h₁ t 1
    have e4 := h₃ t (σ₂ * ((twistSign a : k) * θ t) * 1)
    rw [e2, e4] at e1
    rw [e3] at e1
    rw [← add_assoc] at e1
    exact e1

theorem xPair_mem_of_commutator {a b : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a)
    (hb : IsRoot .E6 b) (hρb : rho b = b) (hρa : rho a ≠ a) (hab : IsRoot .E6 (a + b))
    (hγ : IsRoot .E6 (a + rho a + b)) {N : Subgroup (fixedGroup k θ)}
    (hX : xFixed θ hb hρb 1 (map_one θ) ∈ N)
    (hγN : ∀ (g : k) (hg : θ g = g), xFixed θ hγ (twistedE6_rho_add_rho_add_of_fixed hρb) g hg ∈ N)
    (hconj : ∀ t : k, xPair θ hθ ha hρa t * xFixed θ hb hρb 1 (map_one θ) *
      (xPair θ hθ ha hρa t)⁻¹ ∈ N) (w : k) :
    xPair θ hθ hab (twistedE6_rho_add_ne_of_fixed hρb hρa) w ∈ N := by
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hcomm⟩ := commutator_xPair_xFixed θ hθ ha hb hρb hρa hab hγ
  have hρc : rho (a + b) ≠ a + b := twistedE6_rho_add_ne_of_fixed hρb hρa
  obtain ⟨g₀, hg₀, hZ⟩ := hcomm (σ₁ * w)
  set y := xPair θ hθ ha hρa (σ₁ * w) with hy
  set x := xFixed θ hb hρb 1 (map_one θ) with hx
  have hZN : ⁅y, x⁆ ∈ N := by
    have := N.mul_mem (hconj (σ₁ * w)) (N.inv_mem hX)
    rwa [← commutatorElement_def] at this
  set X₂ : fixedGroup k θ := xFixed θ hγ (twistedE6_rho_add_rho_add_of_fixed hρb) g₀ hg₀ with hX₂
  set y₀ : fixedGroup k θ := X₂⁻¹ * ⁅y, x⁆ with hy₀
  have hy₀N : y₀ ∈ N := N.mul_mem (N.inv_mem (hγN g₀ hg₀)) hZN
  set z₂ : k := σ₂ * ((twistSign a : k) * θ (σ₁ * w)) * 1 with hz₂
  have hy₀val : (y₀ : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (rho (a + b)) z₂ * e6Data_valid.xm k (a + b) (σ₁ * (σ₁ * w) * 1) := by
    rw [twistedE6_rho_add_of_fixed hρb]
    show (e6Data_valid.xm k (a + rho a + b) g₀)⁻¹ *
      ((⁅y, x⁆ : fixedGroup k θ) : e6Data_valid.minGroup k) = _
    rw [hZ]
    group
  have hz₁ : σ₁ * (σ₁ * w) * 1 = w := by
    rw [mul_one, ← mul_assoc, hσ₁.mul_self, one_mul]
  rw [hz₁] at hy₀val
  have hmem : y₀ ∈ twistedRootGroup k θ (proj (a + b)) := by
    refine (mem_twistedRootGroup_iff θ hab rfl y₀).2 ?_
    rw [hy₀val]
    exact mul_mem (Subgroup.mem_sup_right (e6Data_valid.xm_mem_rootGroup k _ _))
      (Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup k _ _))
  obtain ⟨w₁, hw₁⟩ := (mem_twistedRootGroup_iff_of_pair θ hab rfl hρc y₀).1 hmem
  have hc := (commute_xm_rho hab hρc w z₂).eq
  rw [hy₀val, ← hc] at hw₁
  obtain ⟨hww₁, hz₂w⟩ := xm_mul_xm_rho_inj hab hρc hw₁
  have : y₀ = xPair θ hθ hab hρc w := by
    apply Subtype.ext
    rw [hy₀val, ← hc, xPair_val, hww₁, hz₂w]
  rw [← this]
  exact hy₀N

end Extraction

end CFSG.ClassicalInvolution.ModelFacts
