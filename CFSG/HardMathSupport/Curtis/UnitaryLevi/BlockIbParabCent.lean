module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSmallGeneric
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbParabSelfNorm
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbOuterThree

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {Y : Type} [Group Y]

omit [Group Y] in
theorem inv_mul_mem_centralizer_of_act {Y : Type} [Group Y] {Lb : Subgroup Y} {u ℓ : Y}
    (h : Lift.Act Lb u ℓ) : ℓ⁻¹ * u ∈ Subgroup.centralizer (Lb : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h1 := h g hg
  calc g * (ℓ⁻¹ * u) = ℓ⁻¹ * (ℓ * g * ℓ⁻¹) * u := by group
    _ = ℓ⁻¹ * (u * g * u⁻¹) * u := by rw [h1]
    _ = (ℓ⁻¹ * u) * g := by group

section Decomp

variable [Finite Y]

theorem exists_mul_of_normalizer_of_outer {Lb Pb : Subgroup Y} (hpar : IsParabolicTwo Lb Pb)
    (hOut : Nat.card (Outer ↥Lb) ∣ 2) {u : Y} (hu : u ∈ Subgroup.normalizer (Lb : Set Y))
    (huP : u ∈ Subgroup.normalizer (Pb : Set Y)) {k : ℕ} (huk : u ^ 3 ^ k = 1) :
    ∃ p ∈ Pb, ∃ c ∈ Subgroup.centralizer (Lb : Set Y), u = p * c := by
  obtain ⟨ℓ, hℓ, hact⟩ := exists_act_of_outer_dvd_two hOut hu huk
  have hPL : Pb ≤ Lb := hpar.1
  have hℓP : ℓ ∈ Subgroup.normalizer (Pb : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      rw [← hact q (hPL hq)]
      exact (Subgroup.mem_normalizer_iff.1 huP q).1 hq
    · intro hq
      have hq' : ℓ * q * ℓ⁻¹ ∈ Pb := hq
      have hactinv := Lift.act_inv hℓ hact
      have hp : ℓ * q * ℓ⁻¹ ∈ Lb := hPL hq'
      have h2 := hactinv _ hp
      have h3 : u⁻¹ * (ℓ * q * ℓ⁻¹) * u⁻¹⁻¹ = ℓ⁻¹ * (ℓ * q * ℓ⁻¹) * ℓ⁻¹⁻¹ := h2
      have h4 : ℓ⁻¹ * (ℓ * q * ℓ⁻¹) * ℓ⁻¹⁻¹ = q := by group
      rw [h4] at h3
      rw [← h3]
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ huP) (ℓ * q * ℓ⁻¹)).1 hq'
      exact this
  have hℓPb : ℓ ∈ Pb := mem_of_mem_normalizer_of_isParabolicTwo hpar hℓ hℓP
  refine ⟨ℓ, hℓPb, ℓ⁻¹ * u, inv_mul_mem_centralizer_of_act hact, by group⟩

end Decomp

section Quotient

theorem exists_mul_of_mem_sup_commute_aux {A B : Subgroup Y}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Y} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup Y :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact hle hx

theorem exists_quotient_hom [Finite Y] {Lb Pb U : Subgroup Y} (hPL : Pb ≤ Lb)
    (hU : U ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y)) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (θ : ↥U →* Q),
      (∀ a : ↥U, θ a = 1 ↔ (a : Y) ∈ Subgroup.centralizer (Lb : Set Y)) ∧
        Nat.card Q ∣ Nat.card Pb := by
  set C : Subgroup Y := Subgroup.centralizer (Lb : Set Y) with hC
  set W : Subgroup Y := Pb ⊔ C with hW
  have hCW : C ≤ W := le_sup_right
  have hPW : Pb ≤ W := le_sup_left
  have hnorm : W ≤ Subgroup.normalizer (C : Set Y) :=
    sup_le (hPL.trans (le_normalizer_centralizer_aux Lb)) Subgroup.le_normalizer
  have : (C.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCW).mpr hnorm
  let π : ↥W →* ↥W ⧸ C.subgroupOf W := QuotientGroup.mk' (C.subgroupOf W)
  refine ⟨↥W ⧸ C.subgroupOf W, inferInstance, inferInstance,
    π.comp (Subgroup.inclusion hU), ?_, ?_⟩
  · intro a
    show π (Subgroup.inclusion hU a) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  · have hcomm : ∀ a ∈ Pb, ∀ b ∈ C, a * b = b * a :=
      fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a (hPL ha)
    have hsurj : Function.Surjective (π.comp (Subgroup.inclusion hPW)) := by
      intro q
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf W) q
      obtain ⟨p, hp, c, hc, hpc⟩ := exists_mul_of_mem_sup_commute_aux hcomm w.2
      refine ⟨⟨p, hp⟩, ?_⟩
      show π ⟨p, hPW hp⟩ = π w
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      show (⟨p, hPW hp⟩ : ↥W)⁻¹ * w ∈ C.subgroupOf W
      rw [Subgroup.mem_subgroupOf]
      have : ((⟨p, hPW hp⟩ : ↥W)⁻¹ * w : ↥W) = ⟨c, hCW hc⟩ := by
        apply Subtype.ext
        show p⁻¹ * (w : Y) = c
        rw [hpc]; group
      rw [this]
      exact hc
    exact Subgroup.card_dvd_of_surjective hsurj

end Quotient

end CFSG.HardMathSupport.Curtis.UnitaryLevi
