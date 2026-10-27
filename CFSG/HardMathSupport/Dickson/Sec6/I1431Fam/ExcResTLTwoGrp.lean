module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLPsl

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Open.StatedAPI
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem excTL_card_scalars_le {F : Type} [Field F] :
    Nat.card ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) ≤ 2 := by
  by_contra h
  push Not at h
  have : Finite ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) :=
    Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
  obtain ⟨a, b, c, hab, hac, hbc⟩ : ∃ a b c : ((StatedScalars (Fin 2) F).subgroupOf
      (StatedSL 2 F)), a ≠ b ∧ a ≠ c ∧ b ≠ c :=
    Fintype.two_lt_card_iff.1 (by rw [← Nat.card_eq_fintype_card]; exact h)
  rcases excTL_scalar_three a.2 b.2 c.2 with h | h | h
  · exact hab (Subtype.ext h)
  · exact hac (Subtype.ext h)
  · exact hbc (Subtype.ext h)

theorem excTL_card_psl2_ge {F : Type} [Field F] [Finite F] (hq : 10 ≤ Nat.card F) :
    495 ≤ Nat.card (StatedProj (StatedSL 2 F)) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
  have h2 := card_statedSL_two F
  have h3 := excTL_card_scalars_le (F := F)
  change Nat.card (StatedSL 2 F) = Nat.card (StatedProj (StatedSL 2 F)) * _ at h1
  have h4 : 990 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := by
    have : 100 ≤ Nat.card F ^ 2 := by nlinarith
    have : 99 ≤ Nat.card F ^ 2 - 1 := by omega
    nlinarith
  have h5 : Nat.card (StatedProj (StatedSL 2 F)) * 2 ≥ 990 := by
    calc 990 ≤ Nat.card (StatedSL 2 F) := by rw [h2]; exact h4
      _ = Nat.card (StatedProj (StatedSL 2 F)) *
            Nat.card ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) := h1
      _ ≤ Nat.card (StatedProj (StatedSL 2 F)) * 2 := Nat.mul_le_mul_left _ h3
  omega

theorem excTL_false_of_card {G : Type*} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    (φ : (G ⧸ Subgroup.center G) ≃* StatedProj (StatedSL 2 F)) (hq : 10 ≤ Nat.card F)
    (hG : Nat.card G ≤ 168) : False := by
  have h1 := excTL_card_psl2_ge hq
  have h2 : Nat.card (G ⧸ Subgroup.center G) ≤ Nat.card G :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.center G))
  rw [Nat.card_congr φ.toEquiv] at h2
  omega

theorem excTL_comm_mul_commute {G : Type*} [Group G] {x y w : G} (h : Commute y w) :
    ⁅x * y, w⁆ = ⁅x, w⁆ := by
  have h' : y * w * y⁻¹ = w := by
    rw [mul_inv_eq_iff_eq_mul]
    exact h.eq
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * y * w * (y⁻¹ * x⁻¹) * w⁻¹ = x * (y * w * y⁻¹) * x⁻¹ * w⁻¹ := by group
    _ = x * w * x⁻¹ * w⁻¹ := by rw [h']

theorem excTL_false_of_A3 {G : Type*} [Group G] {F : Type} [Field F]
    (φ : (G ⧸ Subgroup.center G) ≃* StatedProj (StatedSL 2 F)) {u₁ u₂ u₃ z : G}
    (hz : z ∉ Subgroup.center G) (h₁ : Commute u₁ z) (h₂ : Commute u₂ z) (h₃ : Commute u₃ z)
    (h₁₂ : Commute ⁅u₁, u₂⁆ z) (h₂₃ : Commute ⁅u₂, u₃⁆ z)
    (r₁ : ⁅u₁, ⁅u₂, u₃⁆⁆ = z) (r₂ : ⁅⁅u₁, u₂⁆, u₃⁆ = z) (h₃' : Commute u₃ ⁅u₂, u₃⁆) : False := by
  set Hc : Subgroup G := Subgroup.centralizer {z} with hHc
  have memH : ∀ x : G, Commute x z → x ∈ Hc := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      exact hx.eq.symm
  set π := QuotientGroup.mk' (Subgroup.center G) with hπ
  set f : Hc →* StatedProj (StatedSL 2 F) :=
    (φ : (G ⧸ Subgroup.center G) →* StatedProj (StatedSL 2 F)).comp (π.comp Hc.subtype) with hf
  have hg : φ (π z) ≠ 1 := fun h => hz
    ((QuotientGroup.eq_one_iff z).1 (φ.injective (h.trans (map_one φ).symm)))
  have hfz : ∀ a : Hc, Commute (f a) (φ (π z)) := fun a => by
    have : Commute (a : G) z := (Subgroup.mem_centralizer_iff.1 a.2 z rfl).symm
    exact (this.map π).map φ.toMonoidHom
  obtain ⟨K, -, hK1, hK2, hK3⟩ := excTL_psl2_abelian_index_two hg f hfz
  have toCenter : ∀ a b : Hc, Commute (f a) (f b) → ⁅(a : G), (b : G)⁆ ∈ Subgroup.center G := by
    intro a b h
    refine (QuotientGroup.eq_one_iff _).1 (φ.injective ?_)
    rw [map_one]
    have e : φ (QuotientGroup.mk ⁅(a : G), (b : G)⁆) = ⁅f a, f b⁆ := by
      change φ (π ⁅(a : G), (b : G)⁆) = _
      rw [map_commutatorElement, map_commutatorElement]
      rfl
    rw [e]
    exact commutatorElement_eq_one_iff_mul_comm.2 h.eq
  set v₁ : Hc := ⟨u₁, memH _ h₁⟩ with hv₁
  set v₂ : Hc := ⟨u₂, memH _ h₂⟩ with hv₂
  set v₃ : Hc := ⟨u₃, memH _ h₃⟩ with hv₃
  have e12 : ((⁅v₁, v₂⁆ : Hc) : G) = ⁅u₁, u₂⁆ := by simp [commutatorElement_def, hv₁, hv₂]
  have e23 : ((⁅v₂, v₃⁆ : Hc) : G) = ⁅u₂, u₃⁆ := by simp [commutatorElement_def, hv₂, hv₃]
  rcases hK2 v₁ v₃ with h | h | h
  · have := toCenter v₁ ⁅v₂, v₃⁆ (hK3 v₁ h _ (hK1 v₂ v₃))
    rw [e23] at this
    exact hz (r₁ ▸ this)
  · have := toCenter ⁅v₁, v₂⁆ v₃ (hK3 _ (hK1 v₁ v₂) v₃ h)
    rw [e12] at this
    exact hz (r₂ ▸ this)
  · have := toCenter (v₁ * v₃) ⁅v₂, v₃⁆ (hK3 _ h _ (hK1 v₂ v₃))
    rw [e23] at this
    have e13 : ((v₁ * v₃ : Hc) : G) = u₁ * u₃ := rfl
    rw [e13, excTL_comm_mul_commute h₃', r₁] at this
    exact hz this

end CFSG.HardMathSupport.Dickson.Sec6.I1431
