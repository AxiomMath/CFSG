module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem u42_mem_fixedSubgroup {G : Type} [Group G] {σ : MulAut G} {x : G} :
    x ∈ fixedSubgroup σ ↔ σ x = x := Iff.rfl

theorem u42_count_fixed {S : Type} [Group S] [Finite S] (Z : Subgroup S) [Z.Normal]
    (hZ : Z ≤ Subgroup.center S) (ψ : MulAut S) (σ : MulAut (S ⧸ Z))
    (hσ : ∀ g : S, σ (QuotientGroup.mk g) = QuotientGroup.mk (ψ g)) :
    ∃ R : Subgroup S, R ≤ Z ∧ (∀ r ∈ R, ∃ g : S, ψ g = r * g) ∧
      Nat.card ↥(fixedSubgroup σ) * Nat.card ↥Z = Nat.card ↥R * Nat.card ↥(fixedSubgroup ψ) := by
  classical
  set π : S →* S ⧸ Z := QuotientGroup.mk' Z with hπ
  set H : Subgroup S := (fixedSubgroup σ).comap π with hH
  have hmemH : ∀ g : S, g ∈ H ↔ ψ g * g⁻¹ ∈ Z := by
    intro g
    rw [hH, Subgroup.mem_comap, u42_mem_fixedSubgroup]
    change σ (QuotientGroup.mk g) = QuotientGroup.mk g ↔ _
    rw [hσ, QuotientGroup.eq]
    constructor
    · intro h1
      have h2 := Z.inv_mem h1
      rw [mul_inv_rev, inv_inv] at h2
      have h3 := (inferInstance : Z.Normal).conj_mem _ h2 g
      have h4 : g * (g⁻¹ * ψ g) * g⁻¹ = ψ g * g⁻¹ := by group
      rwa [h4] at h3
    · intro h1
      have h3 := (inferInstance : Z.Normal).conj_mem _ (Z.inv_mem h1) g⁻¹
      have h4 : g⁻¹ * (ψ g * g⁻¹)⁻¹ * g⁻¹⁻¹ = (ψ g)⁻¹ * g := by group
      rwa [h4] at h3
  have hcen : ∀ z ∈ Z, ∀ x : S, x * z = z * x := fun z hz x => Subgroup.mem_center_iff.mp (hZ hz) x
  let θ : H →* S :=
    { toFun := fun g => ψ (g : S) * (g : S)⁻¹
      map_one' := by simp
      map_mul' := fun g h => by
        have hh : ψ (h : S) * (h : S)⁻¹ ∈ Z := (hmemH h).1 h.2
        have hc := hcen _ hh (ψ (g : S))
        have hc' := hcen _ hh (g : S)⁻¹
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc ψ (g : S) * ψ (h : S) * ((h : S)⁻¹ * (g : S)⁻¹)
            = ψ (g : S) * (ψ (h : S) * (h : S)⁻¹) * (g : S)⁻¹ := by group
          _ = ψ (g : S) * ((g : S)⁻¹ * (ψ (h : S) * (h : S)⁻¹)) := by rw [mul_assoc, hc']
          _ = ψ (g : S) * (g : S)⁻¹ * (ψ (h : S) * (h : S)⁻¹) := by rw [← mul_assoc] }
  have hθ : ∀ g : H, θ g = ψ (g : S) * (g : S)⁻¹ := fun g => rfl
  refine ⟨θ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    rw [hθ]
    exact (hmemH g).1 g.2
  · rintro _ ⟨g, rfl⟩
    exact ⟨g, by rw [hθ]; group⟩
  ·
    have hker : Nat.card ↥θ.ker = Nat.card ↥(fixedSubgroup ψ) := by
      refine Nat.card_congr
        { toFun := fun x => ⟨(x.1 : S), ?_⟩
          invFun := fun y => ⟨⟨(y : S), ?_⟩, ?_⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
      · have := x.2
        rw [MonoidHom.mem_ker, hθ, mul_inv_eq_one] at this
        exact this
      · rw [hmemH]
        have := y.2
        rw [u42_mem_fixedSubgroup] at this
        rw [this, mul_inv_cancel]
        exact Z.one_mem
      · rw [MonoidHom.mem_ker, hθ, mul_inv_eq_one]
        exact y.2
    have hH1 : Nat.card H = Nat.card ↥θ.range * Nat.card ↥θ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv]
    have hidx : H.index = (fixedSubgroup σ).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective Z)
    have hpos : 0 < (fixedSubgroup σ).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h1 := Subgroup.card_mul_index H
    have h2 := Subgroup.card_mul_index (fixedSubgroup σ)
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [hidx] at h1
    have h4 : Nat.card H * (fixedSubgroup σ).index =
        (Nat.card ↥(fixedSubgroup σ) * Nat.card ↥Z) * (fixedSubgroup σ).index := by
      rw [h1, h3, ← h2]
      ring
    have h5 := Nat.eq_of_mul_eq_mul_right hpos h4
    rw [← hker, ← hH1, h5]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
