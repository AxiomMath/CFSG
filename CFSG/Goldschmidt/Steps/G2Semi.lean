module

public import CFSG.Goldschmidt.Steps.G2Lin

public section

namespace CFSG.Goldschmidt.G2

open Module CFSG.QuasithinUnique
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {X : Subgroup (V ≃ₗ[ZMod 2] V)} {η : V ≃ₗ[ZMod 2] V}

namespace LinHyp

variable (h : LinHyp X η)
include h

theorem orbitMap_injective {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ X)
    (hfree : ∀ k : ℕ, (η ^ k) • (x • fixSp η) = x • fixSp η → η ^ k = 1) :
    Function.Injective (fun p : Subgroup.zpowers η × {s : V // s ∈ x • fixSp η ∧ s ≠ 0} =>
      (p.1 : V ≃ₗ[ZMod 2] V) p.2.1) := by
  rintro ⟨g, s⟩ ⟨g', s'⟩ heq
  simp only at heq
  have hmem1 : (g : V ≃ₗ[ZMod 2] V) s.1 ∈ ((g : V ≃ₗ[ZMod 2] V) * x) • fixSp η := by
    rw [mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ s.2.1
  have hmem2 : (g : V ≃ₗ[ZMod 2] V) s.1 ∈ ((g' : V ≃ₗ[ZMod 2] V) * x) • fixSp η := by
    rw [mul_smul, heq]
    exact Submodule.smul_mem_pointwise_smul _ _ _ s'.2.1
  have hne0 : (g : V ≃ₗ[ZMod 2] V) s.1 ≠ 0 := fun h0 => s.2.2 (by
    simpa using congrArg (g : V ≃ₗ[ZMod 2] V).symm h0)
  have heqS : ((g : V ≃ₗ[ZMod 2] V) * x) • fixSp η = ((g' : V ≃ₗ[ZMod 2] V) * x) • fixSp η := by
    refine h.smul_eq_of_inf_ne_bot (X.mul_mem (h.zpowers_le g.2) hx)
      (X.mul_mem (h.zpowers_le g'.2) hx) fun hbot => hne0 ?_
    have := Submodule.mem_inf.mpr ⟨hmem1, hmem2⟩
    rwa [hbot, Submodule.mem_bot] at this
  have hstab : ((g' : V ≃ₗ[ZMod 2] V)⁻¹ * g) • (x • fixSp η) = x • fixSp η := by
    rw [mul_smul, ← mul_smul (g : V ≃ₗ[ZMod 2] V) x, heqS, mul_smul, inv_smul_smul]
  obtain ⟨k, hk⟩ :=
    exists_pow_eq_of_mem_zpowers (Subgroup.mul_mem _ (Subgroup.inv_mem _ g'.2) g.2)
  have h1 := hfree k (by rw [hk]; exact hstab)
  rw [hk, inv_mul_eq_one] at h1
  have hs : s = s' := Subtype.ext ((g : V ≃ₗ[ZMod 2] V).injective (by rw [heq, h1]))
  exact Prod.ext (Subtype.ext h1.symm) hs

theorem finrank_fixSp_eq_one
    (hirr : ∀ S : Submodule (ZMod 2) V, (∀ x ∈ X, ∀ v ∈ S, x v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hsemi : ∀ x ∈ X, x • fixSp η ≠ fixSp η → ∀ k : ℕ,
      (η ^ k) • (x • fixSp η) = x • fixSp η → η ^ k = 1) :
    finrank (ZMod 2) (fixSp η) = 1 := by
  by_contra hk1
  have hk : 2 ≤ finrank (ZMod 2) (fixSp η) := by
    have := Submodule.one_le_finrank_iff.mpr h.fixSp_ne_bot
    omega
  have hm := h.two_le_finrank_comSp
  obtain ⟨x₀, hx₀, hx₀W⟩ : ∃ x ∈ X, x • fixSp η ≠ fixSp η := by
    by_contra hcon
    push Not at hcon
    rcases hirr (fixSp η) (fun x hx v hv => by
      rw [← hcon x hx]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hv) with h0 | h0
    · exact h.fixSp_ne_bot h0
    · apply h.comSp_ne_bot
      have := h.isCompl.inf_eq_bot
      rwa [h0, inf_top_eq] at this
  have ha := card_nonzero_add_one (comSp η)
  have hb := card_nonzero_add_one (fixSp η)
  rw [ONan.natCard_submodule] at ha hb
  have hzp : Nat.card (Subgroup.zpowers η) = Nat.card {d : V // d ∈ comSp η ∧ d ≠ 0} := by
    have := h.card_zpowers_add_one
    rw [ONan.natCard_submodule] at this
    omega
  have hcardDom : ∀ x : V ≃ₗ[ZMod 2] V,
      Nat.card (Subgroup.zpowers η × {s : V // s ∈ x • fixSp η ∧ s ≠ 0}) =
        Nat.card {d : V // d ∈ comSp η ∧ d ≠ 0} * Nat.card {w : V // w ∈ fixSp η ∧ w ≠ 0} := by
    intro x
    rw [Nat.card_prod, hzp, card_nonzero_smul]
  have step1 : ∀ x ∈ X, x • fixSp η ≠ fixSp η → x • fixSp η ⊓ comSp η = ⊥ := by
    intro x hx hxW
    by_contra hne
    have hinj : Function.Injective
        (fun p : Subgroup.zpowers η × {s : V // s ∈ x • fixSp η ∧ s ≠ 0} =>
          (⟨(p.1 : V ≃ₗ[ZMod 2] V) p.2.1, by
            have hd := h.sub_mem_comSp p.1.2 p.2.1
            have : (p.1 : V ≃ₗ[ZMod 2] V) p.2.1 = p.2.1 + ((p.1 : V ≃ₗ[ZMod 2] V) p.2.1 - p.2.1) :=
              by abel
            rw [this]
            exact Submodule.add_mem_sup p.2.2.1 hd, fun h0 => p.2.2.2 (by
              simpa using congrArg (p.1 : V ≃ₗ[ZMod 2] V).symm h0)⟩ :
            {v : V // v ∈ x • fixSp η ⊔ comSp η ∧ v ≠ 0})) := by
      intro p q hpq
      exact h.orbitMap_injective hx (hsemi x hx hxW) (congrArg Subtype.val hpq)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hcardDom] at hle
    have hsup := card_nonzero_add_one (x • fixSp η ⊔ comSp η)
    rw [ONan.natCard_submodule] at hsup
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq (x • fixSp η) (comSp η)
    have hfr1 : 1 ≤ finrank (ZMod 2) (x • fixSp η ⊓ comSp η : Submodule (ZMod 2) V) :=
      Submodule.one_le_finrank_iff.mpr hne
    rw [ONan.finrank_smul] at hfr
    set k := finrank (ZMod 2) (fixSp η)
    set m := finrank (ZMod 2) (comSp η)
    set r := finrank (ZMod 2) (x • fixSp η ⊔ comSp η : Submodule (ZMod 2) V)
    have hr : r + 1 ≤ k + m := by omega
    have h2r : 2 ^ r * 2 ≤ 2 ^ k * 2 ^ m := by
      rw [← pow_succ, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) hr
    have hkk : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h4m : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h2k : 2 ≤ 2 ^ (k - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hkk] at h2r
    set A := 2 ^ m
    set B := 2 ^ (k - 1)
    set a := Nat.card {d : V // d ∈ comSp η ∧ d ≠ 0}
    set b := Nat.card {w : V // w ∈ fixSp η ∧ w ≠ 0}
    have hsup' : Nat.card {v : V // v ∈ x • fixSp η ⊔ comSp η ∧ v ≠ 0} + 1 = 2 ^ r := hsup
    rw [hkk] at hb
    nlinarith
  have step2 : ∀ v : V, v ∉ fixSp η → v ∉ comSp η →
      ∃ g ∈ Subgroup.zpowers η, v ∈ g • (x₀ • fixSp η) := by
    have hS₀ := step1 x₀ hx₀ hx₀W
    let ι : Subgroup.zpowers η × {s : V // s ∈ x₀ • fixSp η ∧ s ≠ 0} →
        {v : V // v ∉ fixSp η ∧ v ∉ comSp η} := fun p =>
      ⟨(p.1 : V ≃ₗ[ZMod 2] V) p.2.1, by
        have hgS : ((p.1 : V ≃ₗ[ZMod 2] V) * x₀) • fixSp η ≠ fixSp η := by
          rw [mul_smul]
          intro heq
          apply hx₀W
          calc x₀ • fixSp η = (p.1 : V ≃ₗ[ZMod 2] V)⁻¹ • ((p.1 : V ≃ₗ[ZMod 2] V) • x₀ • fixSp η) :=
                (inv_smul_smul _ _).symm
            _ = (p.1 : V ≃ₗ[ZMod 2] V)⁻¹ • fixSp η := by rw [heq]
            _ = fixSp η := smul_fixSp_of_mem_zpowers (Subgroup.inv_mem _ p.1.2)
        have hmem : (p.1 : V ≃ₗ[ZMod 2] V) p.2.1 ∈ ((p.1 : V ≃ₗ[ZMod 2] V) * x₀) • fixSp η := by
          rw [mul_smul]
          exact Submodule.smul_mem_pointwise_smul _ _ _ p.2.2.1
        have hne0 : (p.1 : V ≃ₗ[ZMod 2] V) p.2.1 ≠ 0 := fun h0 => p.2.2.2 (by
          simpa using congrArg (p.1 : V ≃ₗ[ZMod 2] V).symm h0)
        have hgX : (p.1 : V ≃ₗ[ZMod 2] V) * x₀ ∈ X := X.mul_mem (h.zpowers_le p.1.2) hx₀
        refine ⟨fun hW => hne0 ?_, fun hD => hne0 ?_⟩
        · have := Submodule.mem_inf.mpr ⟨hmem, hW⟩
          rwa [h.ti _ hgX hgS, Submodule.mem_bot] at this
        · have := Submodule.mem_inf.mpr ⟨hmem, hD⟩
          rwa [step1 _ hgX hgS, Submodule.mem_bot] at this⟩
    have hinj : Function.Injective ι := by
      intro p q hpq
      exact h.orbitMap_injective hx₀ (hsemi x₀ hx₀ hx₀W) (congrArg Subtype.val hpq)
    have hbij := hinj.bijective_of_nat_card_le (by rw [h.card_compl, hcardDom])
    intro v hvW hvD
    obtain ⟨⟨g, s⟩, hgs⟩ := hbij.2 ⟨v, hvW, hvD⟩
    refine ⟨g, g.2, ?_⟩
    have : (g : V ≃ₗ[ZMod 2] V) s.1 = v := congrArg Subtype.val hgs
    rw [← this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ s.2.1
  have step3 : ∀ x ∈ X, ∀ d ∈ comSp η, x d ∈ comSp η := by
    intro x hx d hd
    by_contra hxd
    have hd0 : d ≠ 0 := fun h0 => hxd (by rw [h0, map_zero]; exact (comSp η).zero_mem)
    obtain ⟨y, hy, hdy⟩ : ∃ y ∈ X, d ∈ y • fixSp η := by
      by_cases hxW : x d ∈ fixSp η
      · refine ⟨x⁻¹, X.inv_mem hx, ?_⟩
        rw [ONan.mem_smul_iff, inv_inv]
        exact hxW
      · obtain ⟨g, hg, hgv⟩ := step2 (x d) hxW hxd
        refine ⟨x⁻¹ * (g * x₀), X.mul_mem (X.inv_mem hx) (X.mul_mem (h.zpowers_le hg) hx₀), ?_⟩
        rw [mul_smul, mul_smul, ONan.mem_smul_iff, inv_inv]
        exact hgv
    have hyW : y • fixSp η ≠ fixSp η := by
      intro heq
      rw [heq] at hdy
      have := Submodule.mem_inf.mpr ⟨hd, hdy⟩
      rw [h.isCompl.inf_eq_bot, Submodule.mem_bot] at this
      exact hd0 this
    have := Submodule.mem_inf.mpr ⟨hdy, hd⟩
    rw [step1 y hy hyW, Submodule.mem_bot] at this
    exact hd0 this
  rcases hirr (comSp η) step3 with h0 | h0
  · exact h.comSp_ne_bot h0
  · apply h.fixSp_ne_bot
    have := h.isCompl.inf_eq_bot
    rwa [h0, top_inf_eq] at this

end LinHyp

end CFSG.Goldschmidt.G2
