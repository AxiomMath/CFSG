module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10Sp4In

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4

namespace X10Sp4

variable {K : Type} [Field K]

theorem field_card [Finite K] (hodd : Odd (Nat.card K)) (A : gsp 2 K) (σ : K ≃+* K)
    (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) (d : Kˣ)
    (hd : (A : GL (Fin 2 ⊕ Fin 2) K) *
        CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) σ (A : GL (Fin 2 ⊕ Fin 2) K) =
      GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d)
    {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hMX : M ≤ fixOf (conjAut 2 K A * fieldAut 2 K σ))
    (hM : IsPComponent 2 (M.subgroupOf (fixOf (conjAut 2 K A * fieldAut 2 K σ)))) :
    IsSimpleGroup M ∧ Nat.card M * 2 =
      Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ^ 4 *
        ((Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ^ 2 - 1) *
          (Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ^ 4 - 1)) := by
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨hQ, hcard⟩ := fixOf_conjSp_fieldSp hodd A σ hσ2 hσ1 d hd
  have hθα : ∀ g, (conjAut 2 K A * fieldAut 2 K σ) (proj 2 K g) =
      proj 2 K ((conjSp 2 K A * fieldSp 2 K σ) g) := fun g => by
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, MulAut.mul_apply]
  have hZ : ∀ z ∈ spScalars 2 K, (conjSp 2 K A * fieldSp 2 K σ) z = z := fun z hz =>
    conjSp_fieldSp_scalar A σ hz
  rw [eq_map_fixOf_of_isPComponent _ hθα hQ hMX hM]
  exact ⟨isSimpleGroup_map_fixOf h2 _ hZ hQ (card_center_fixOf_field hodd A σ hσ2 hσ1 d hd),
    by rw [card_map_fixOf_mul_two h2 _ hZ, hcard]⟩

theorem allTraces_of_card [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα2 : α * α = 1) (hα1 : α ≠ 1) {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hMX : M ≤ fixOf α) (hM : IsPComponent 2 (M.subgroupOf (fixOf α))) {o : ℕ} (ho : Odd o)
    (hMc : Nat.card M = o * (p ^ f * ((p ^ f) ^ 2 - 1) / 2)) :
    AllTraces M ∧ IsSimpleGroup M := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have hqodd : Odd (p ^ f) := hK ▸ hodd
  have hq3 : 3 ≤ p ^ f := by omega
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, -, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      (GH74.Generic.ringChar_ne_two_of_card_eq hp hp2 hK) le_rfl).2.2 α hα2 hα1
  rw [hα] at hMX hM hα1
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, mul_one] at hMX hM hα1
    rcases inner_cases hp hp2 hf hK h5 A d (mul_self_of_rep A d hd) hα1 hMX hM with
      ⟨e⟩ | h1 | h1
    · obtain ⟨e⟩ := e
      have h1 := Nat.card_congr e.toEquiv
      rw [card_SL2, hK, hMc] at h1
      exact absurd h1 (card_ne_SL2 hqodd hq3 ho)
    · exact ⟨h1.1, h1.2.1⟩
    · have h1 := h1.2
      rw [hMc] at h1
      exact absurd h1 (card_ne_L2sq hqodd hq3 ho)
  · exfalso
    have hc := (field_card hodd A σ hσ2 hσ d hd hMX hM).2
    obtain ⟨hKk, -⟩ := hfield hσ
    have hk : Nat.card {c : K // σ c = c} =
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (CatalogueBLinearTwoDescent.mem_fixedSubfield K σ c).symm)
    rw [hk, hK] at hKk
    set k := Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ)
    have hkodd : Odd k := by
      have : Odd (k ^ 2) := hKk ▸ hqodd
      exact (Nat.odd_mul.mp (by rwa [sq] at this)).1
    have hk3 : 3 ≤ k := by
      by_contra hlt
      have : k ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    rw [hMc, hKk] at hc
    exact card_ne_PSp4sqrt hkodd hk3 ho hc

theorem card_of_fix_allTraces [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {β : MulAut (StatedProj (StatedSp 2 K))}
    (hβ2 : β * β = 1) (hβ1 : β ≠ 1) {L : Subgroup (StatedProj (StatedSp 2 K))}
    (hL : AllTraces L) (hβL : ∀ x ∈ L, β x = x) {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hMX : M ≤ fixOf β) (hM : IsPComponent 2 (M.subgroupOf (fixOf β))) :
    Nat.card M ≤ p ^ f * ((p ^ f) ^ 2 - 1) ∨
      Nat.card M * 2 = (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  obtain ⟨A, σ, hβ, -, ⟨d, hd⟩, -, -⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      (GH74.Generic.ringChar_ne_two_of_card_eq hp hp2 hK) le_rfl).2.2 β hβ2 hβ1
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, mul_one] at hβ
    rw [hβ] at hMX hM hβ1
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = p ^ f * ((p ^ f) ^ 2 - 1) := by
      rw [card_SL2, hK]
    rcases inner_cases hp hp2 hf hK h5 A d (mul_self_of_rep A d hd) hβ1 hMX hM with
      ⟨e⟩ | h1 | h1
    · obtain ⟨e⟩ := e
      exact Or.inl ((Nat.card_congr e.toEquiv).trans hSL).le
    · exact Or.inl ((Nat.le_mul_of_pos_right _ two_pos).trans (h1.2.2.trans hSL).le)
    · exact Or.inr h1.2
  · exact (false_of_allTraces (two_ne_zero_of_odd_card hodd) hL A hσ fun x hx =>
      hβ ▸ hβL x hx).elim

end X10Sp4

end CFSG.ComponentClassification.GSThmB
