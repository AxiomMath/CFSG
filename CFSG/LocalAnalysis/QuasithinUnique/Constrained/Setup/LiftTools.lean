module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBasic

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer Module
open scoped commutatorElement Pointwise

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {X : Type*} [Group X]

theorem fixSub_sup (ρ : X →* (V ≃ₗ[k] V)) (A D : Subgroup X) :
    fixSub ρ (A ⊔ D) = fixSub ρ A ⊓ fixSub ρ D := by
  refine le_antisymm (le_inf (fixSub_anti ρ le_sup_left) (fixSub_anti ρ le_sup_right)) ?_
  intro v hv
  have hv' : v ∈ fixSub ρ A ∧ v ∈ fixSub ρ D := hv
  have hle : A ⊔ D ≤ (MulAction.stabilizer (V ≃ₗ[k] V) v).comap ρ :=
    sup_le (fun a ha => hv'.1 a ha) (fun d hd => hv'.2 d hd)
  exact fun b hb => hle hb

theorem natCard_sup_of_commute_of_disjoint {A D : Subgroup X}
    (h : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a) (hd : Disjoint A D) :
    Nat.card ↥(A ⊔ D) = Nat.card A * Nat.card D := by
  have hA : A ≤ Subgroup.normalizer (D : Set X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · intro hdD
      rw [show a * d * a⁻¹ = d from by rw [h a ha d hdD]; group]
      exact hdD
    · intro hdD
      have hc := h a ha _ hdD
      have h2 : a⁻¹ * (a * d * a⁻¹) * a = a * d * a⁻¹ := by
        rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
      have hb2 : d = a * d * a⁻¹ := by
        calc d = a⁻¹ * (a * d * a⁻¹) * a := by group
          _ = a * d * a⁻¹ := h2
      rw [hb2]
      exact hdD
  have hset : ((A ⊔ D : Subgroup X) : Set X) = (A : Set X) * (D : Set X) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hA
  have hinj := Subgroup.mul_injective_of_disjoint hd
  let f : A × D → (A ⊔ D : Subgroup X) := fun g => ⟨g.1 * g.2, by
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left g.1.2) (Subgroup.mem_sup_right g.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply hinj
      exact congrArg Subtype.val hxy
    · intro y
      have hy : (y : X) ∈ ((A ⊔ D : Subgroup X) : Set X) := y.2
      rw [hset] at hy
      obtain ⟨a, ha, d, hd', hy'⟩ := hy
      exact ⟨(⟨a, ha⟩, ⟨d, hd'⟩), Subtype.ext hy'⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem fixed_codimensions_add [Finite V] (ρ : X →* (V ≃ₗ[k] V)) (A D : Subgroup X)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a) (W : Submodule k V) (hDW : W ≤ fixSub ρ D)
    (hV : W ⊔ fixSub ρ A = ⊤) :
    fixSub ρ D = W ⊔ fixSub ρ (A ⊔ D) ∧
    finrank k (V ⧸ fixSub ρ (A ⊔ D)) = finrank k (V ⧸ fixSub ρ A) + finrank k (V ⧸ fixSub ρ D) ∧
    (Disjoint A D → weight ρ (A ⊔ D) * Nat.card V = weight ρ A * weight ρ D ∧
      (weight ρ A = Nat.card V → weight ρ (A ⊔ D) = Nat.card V → weight ρ D = Nat.card V)) := by
  have hfin : Module.Finite k V := Module.Finite.of_finite
  have hF : fixSub ρ (A ⊔ D) = fixSub ρ A ⊓ fixSub ρ D := fixSub_sup ρ A D
  have h1 : fixSub ρ D = W ⊔ fixSub ρ (A ⊔ D) := by
    apply le_antisymm
    · intro v hv
      have hv' : v ∈ W ⊔ fixSub ρ A := by rw [hV]; trivial
      obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.1 hv'
      have hcD : c ∈ fixSub ρ D := by
        have : c = (w + c) - w := by abel
        rw [this]
        exact (fixSub ρ D).sub_mem hv (hDW hw)
      exact Submodule.add_mem_sup hw (by rw [hF]; exact ⟨hc, hcD⟩)
    · exact sup_le hDW (fixSub_anti ρ le_sup_right)
  refine ⟨h1, ?_, fun hdisj => ?_⟩
  ·
    have hWF : W ⊓ fixSub ρ (A ⊔ D) = W ⊓ fixSub ρ A := by
      rw [hF]
      apply le_antisymm
      · exact inf_le_inf_left _ (inf_le_left)
      · exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hDW))
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq W (fixSub ρ (A ⊔ D))
    have e2 := Submodule.finrank_sup_add_finrank_inf_eq W (fixSub ρ A)
    rw [← h1, hWF] at e1
    rw [hV] at e2
    have e3 := Submodule.finrank_quotient_add_finrank (fixSub ρ (A ⊔ D))
    have e4 := Submodule.finrank_quotient_add_finrank (fixSub ρ A)
    have e5 := Submodule.finrank_quotient_add_finrank (fixSub ρ D)
    have e6 : finrank k (⊤ : Submodule k V) = finrank k V := finrank_top k V
    omega
  ·
    have hdim : finrank k (V ⧸ fixSub ρ (A ⊔ D)) =
        finrank k (V ⧸ fixSub ρ A) + finrank k (V ⧸ fixSub ρ D) := by
      have hWF : W ⊓ fixSub ρ (A ⊔ D) = W ⊓ fixSub ρ A := by
        rw [hF]
        apply le_antisymm
        · exact inf_le_inf_left _ (inf_le_left)
        · exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hDW))
      have e1 := Submodule.finrank_sup_add_finrank_inf_eq W (fixSub ρ (A ⊔ D))
      have e2 := Submodule.finrank_sup_add_finrank_inf_eq W (fixSub ρ A)
      rw [← h1, hWF] at e1
      rw [hV] at e2
      have e3 := Submodule.finrank_quotient_add_finrank (fixSub ρ (A ⊔ D))
      have e4 := Submodule.finrank_quotient_add_finrank (fixSub ρ A)
      have e5 := Submodule.finrank_quotient_add_finrank (fixSub ρ D)
      have e6 : finrank k (⊤ : Submodule k V) = finrank k V := finrank_top k V
      omega
    have hcard : ∀ U : Submodule k V, Nat.card ↥U = Nat.card k ^ finrank k ↥U := fun U =>
      natCard_eq_pow_finrank
    have hcardV : Nat.card V = Nat.card k ^ finrank k V := natCard_eq_pow_finrank
    have q3 := Submodule.finrank_quotient_add_finrank (fixSub ρ (A ⊔ D))
    have q4 := Submodule.finrank_quotient_add_finrank (fixSub ρ A)
    have q5 := Submodule.finrank_quotient_add_finrank (fixSub ρ D)
    have hfix : Nat.card ↥(fixSub ρ (A ⊔ D)) * Nat.card V =
        Nat.card ↥(fixSub ρ A) * Nat.card ↥(fixSub ρ D) := by
      rw [hcard, hcard, hcard, hcardV, ← pow_add, ← pow_add]
      congr 1
      omega
    have hAD : Nat.card ↥(A ⊔ D) = Nat.card A * Nat.card D :=
      natCard_sup_of_commute_of_disjoint hcomm hdisj
    have hmain : weight ρ (A ⊔ D) * Nat.card V = weight ρ A * weight ρ D := by
      unfold weight
      calc Nat.card ↥(A ⊔ D) * Nat.card ↥(fixSub ρ (A ⊔ D)) * Nat.card V
          = Nat.card ↥(A ⊔ D) * (Nat.card ↥(fixSub ρ (A ⊔ D)) * Nat.card V) := by ring
        _ = Nat.card A * Nat.card D * (Nat.card ↥(fixSub ρ A) * Nat.card ↥(fixSub ρ D)) := by
            rw [hfix, hAD]
        _ = _ := by ring
    refine ⟨hmain, fun hA hAD' => ?_⟩
    have hVpos : 0 < Nat.card V := Nat.card_pos
    rw [hA, hAD'] at hmain
    exact Nat.eq_of_mul_eq_mul_left hVpos hmain.symm

end CFSG.QuasithinUnique.Setup.Lift
