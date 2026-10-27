module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Goldschmidt

open CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.GorensteinWalter CFSG.QuasithinUnique.RankOneRecog
open scoped MatrixGroups

@[expose] def GoldschmidtTypeAutomorphismsReeJ1 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X P E : Subgroup Y),
    IsSimpleGroup X →
    ((∃ m : ℕ, 1 ≤ m ∧ Nat.card (X ⧸ Subgroup.center X) = ordRee (3 ^ (2 * m + 1))) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* goldschmidtJ1)) →
    IsSylowOf 2 P X → IsElemAbelian 2 E →
    E ≤ Subgroup.normalizer (X : Set Y) → E ≤ Subgroup.normalizer (P : Set Y) →
    (∀ e ∈ E, ∀ x ∈ omegaOne P, e * x = x * e) →
    (∀ e ∈ E, ∀ p ∈ P, e⁻¹ * p⁻¹ * e * p ∈ omegaOne P) →
    Nat.card E ≤ Nat.card (omegaOne P) *
      Nat.card (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y)

@[expose] def GoldschmidtTypeGenerationReeJ1 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X P : Subgroup Y),
    IsSimpleGroup X →
    ((∃ m : ℕ, 1 ≤ m ∧ Nat.card (X ⧸ Subgroup.center X) = ordRee (3 ^ (2 * m + 1))) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* goldschmidtJ1)) →
    IsSylowOf 2 P X →
    (∃ n : ℕ, IsBenderType X n) ∨
    X ≤ ⨆ z : {z : Y // z ∈ P ∧ z ^ 2 = 1 ∧ z ≠ 1}, X ⊓ Subgroup.centralizer {(z : Y)}

section Reduction

variable {Y : Type} [Group Y] [Finite Y] {X P E : Subgroup Y}

omit [Finite Y] in
theorem card_le_of_bound (hP : IsSylowOf 2 P X) (hE : IsElemAbelian 2 E)
    (hEX : E ≤ Subgroup.normalizer (X : Set Y)) (hEP : E ≤ Subgroup.normalizer (P : Set Y))
    (hEcent : ∀ e ∈ E, ∀ x ∈ omegaOne P, e * x = x * e)
    (hEcomm : ∀ e ∈ E, ∀ p ∈ P, e⁻¹ * p⁻¹ * e * p ∈ omegaOne P)
    (hbound : ∀ (Q : Sylow 2 X) (A : Subgroup (MulAut X)), (∀ α ∈ A, α * α = 1) →
      (∀ α ∈ A, ∀ q ∈ (Q : Subgroup X), α q ∈ (Q : Subgroup X)) →
      (∀ α ∈ A, ∀ q ∈ (Q : Subgroup X), q ^ 2 = 1 → α q = q) →
      (∀ α ∈ A, ∀ q ∈ (Q : Subgroup X), q⁻¹ * α q ∈ omegaOne (Q : Subgroup X)) →
      Nat.card A ≤ Nat.card (omegaOne (Q : Subgroup X))) :
    Nat.card E ≤ Nat.card (omegaOne P) *
      Nat.card (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y) := by
  obtain ⟨Q, hQ⟩ := hP
  have hprop := conjAct_range_properties hQ hE hEX hEP hEcent hEcomm
  have hA := hbound Q (conjAct hEX).range (fun α hα => (hprop α hα).1)
    (fun α hα => (hprop α hα).2.1) (fun α hα => (hprop α hα).2.2.1)
    (fun α hα => (hprop α hα).2.2.2)
  calc Nat.card E = Nat.card (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y) *
        Nat.card (conjAct hEX).range := card_eq_mul_card_range hEX
    _ ≤ Nat.card (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y) *
        Nat.card (omegaOne (Q : Subgroup X)) := Nat.mul_le_mul_left _ hA
    _ = Nat.card (omegaOne P) *
        Nat.card (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y) := by
      rw [card_omegaOne hQ, mul_comm]

theorem center_eq_bot_of_bender (hX : IsSimpleGroup X)
    (hL : fusionIsBenderGroup (X ⧸ Subgroup.center X)) : Subgroup.center X = ⊥ := by
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := isSimpleGroup_of_fusionIsBenderGroup hL
  exact center_eq_bot_of_nontrivial inferInstance

theorem aut_bound_of_bender (hX : IsSimpleGroup X)
    (hL : fusionIsBenderGroup (X ⧸ Subgroup.center X)) (hP : IsSylowOf 2 P X)
    (hE : IsElemAbelian 2 E) (hEX : E ≤ Subgroup.normalizer (X : Set Y))
    (hEP : E ≤ Subgroup.normalizer (P : Set Y))
    (hEcent : ∀ e ∈ E, ∀ x ∈ omegaOne P, e * x = x * e)
    (hEcomm : ∀ e ∈ E, ∀ p ∈ P, e⁻¹ * p⁻¹ * e * p ∈ omegaOne P) :
    Nat.card E ≤ Nat.card (omegaOne P) *
      Nat.card (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y) := by
  have hG := fusionIsBenderGroup_of_center_eq_bot (center_eq_bot_of_bender hX hL) hL
  exact card_le_of_bound hP hE hEX hEP hEcent hEcomm fun Q A h1 h2 h3 h4 =>
    card_le_omegaOne_of_bender hG Q A h1 h2 h3 h4

theorem aut_bound_of_psl2_odd (hX : IsSimpleGroup X) {p f : ℕ} [hp : Fact p.Prime]
    (hpodd : Odd p) (hf : 0 < f) (h5 : 5 ≤ p ^ f) (hmod : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    (e₀ : X ⧸ Subgroup.center X ≃* PSL(2, GaloisField p f)) (hP : IsSylowOf 2 P X)
    (hE : IsElemAbelian 2 E) (hEX : E ≤ Subgroup.normalizer (X : Set Y))
    (hEP : E ≤ Subgroup.normalizer (P : Set Y))
    (hEcent : ∀ e ∈ E, ∀ x ∈ omegaOne P, e * x = x * e)
    (hEcomm : ∀ e ∈ E, ∀ p ∈ P, e⁻¹ * p⁻¹ * e * p ∈ omegaOne P) :
    Nat.card E ≤ Nat.card (omegaOne P) *
      Nat.card (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y) := by
  have hKcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hK : IsOddPrimePower (Nat.card (GaloisField p f)) := ⟨p, f, hp.out, hpodd, hf, hKcard⟩
  have : Nontrivial (PSL2 (GaloisField p f)) := nontrivial_psl2 hK
  have hcenter := center_eq_bot_of_nontrivial (G := X) e₀.toEquiv.nontrivial
  let e : X ≃* PSL2 (GaloisField p f) := mulEquivOfCenterEqBot hcenter e₀
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  have hfodd := odd_of_pow_mod_eight hpodd hmod
  have h3 : 3 < Nat.card (GaloisField p f) := by rw [hKcard]; omega
  apply card_le_of_bound hP hE hEX hEP hEcent hEcomm
  intro Q A h1 _ _ _
  have hA' := card_le_four_of_sq_eq_one hKcard hp2 hfodd h3
    (A.map (MulAut.congr e).toMonoidHom) (by
      rintro _ ⟨α, hα, rfl⟩
      rw [← map_mul, h1 α hα, map_one])
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective] at hA'
  exact hA'.trans (four_le_card_omegaOne hK e Q)

end Reduction

theorem goldschmidtTypeAutomorphisms_of_reeJ1 (h : GoldschmidtTypeAutomorphismsReeJ1) :
    GoldschmidtTypeAutomorphisms := by
  intro Y _ _ X P E hX hType hP hE hEX hEP hEcent hEcomm
  rcases hType with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ |
    ⟨p, f, hp, hpodd, hf, h5, hmod, ⟨e⟩⟩ | hRee | hJ1
  · exact aut_bound_of_bender hX (Or.inl ⟨f, by omega, ⟨e⟩⟩) hP hE hEX hEP hEcent hEcomm
  · exact aut_bound_of_bender hX (Or.inr (Or.inr ⟨n, hn, ⟨e⟩⟩)) hP hE hEX hEP hEcent hEcomm
  · exact aut_bound_of_bender hX (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩)) hP hE hEX hEP hEcent hEcomm
  · exact aut_bound_of_psl2_odd hX hpodd hf h5 hmod e hP hE hEX hEP hEcent hEcomm
  · exact h Y X P E hX (Or.inl hRee) hP hE hEX hEP hEcent hEcomm
  · exact h Y X P E hX (Or.inr hJ1) hP hE hEX hEP hEcent hEcomm

theorem goldschmidtTypeGeneration_of_reeJ1 (h : GoldschmidtTypeGenerationReeJ1) :
    GoldschmidtTypeGeneration := by
  intro Y _ _ X P hX hType hP
  rcases hType with ⟨f, hf, ⟨e₀⟩⟩ | ⟨n, hn, ⟨e₀⟩⟩ | ⟨f, hf, ⟨e₀⟩⟩ |
    ⟨p, f, hp, hpodd, hf, h5, hmod, ⟨e₀⟩⟩ | hRee | hJ1
  · left
    have hc := center_eq_bot_of_bender hX (Or.inl ⟨f, by omega, ⟨e₀⟩⟩)
    exact ⟨f, Or.inl ⟨by omega, ⟨mulEquivOfCenterEqBot hc e₀⟩⟩⟩
  · left
    have hc := center_eq_bot_of_bender hX (Or.inr (Or.inr ⟨n, hn, ⟨e₀⟩⟩))
    exact ⟨2 * n + 1, Or.inr (Or.inl ⟨n, hn, rfl, ⟨mulEquivOfCenterEqBot hc e₀⟩⟩)⟩
  · left
    have hc := center_eq_bot_of_bender hX (Or.inr (Or.inl ⟨f, hf, ⟨e₀⟩⟩))
    exact ⟨f, Or.inr (Or.inr ⟨hf, ⟨mulEquivOfCenterEqBot hc e₀⟩⟩)⟩
  · have hKcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
    have hK : IsOddPrimePower (Nat.card (GaloisField p f)) :=
      ⟨p, f, hp.out, hpodd, hf, hKcard⟩
    have : Nontrivial (PSL2 (GaloisField p f)) := nontrivial_psl2 hK
    have : IsSimpleGroup X := hX
    have hcenter := center_eq_bot_of_nontrivial (G := X) e₀.toEquiv.nontrivial
    let e : X ≃* PSL2 (GaloisField p f) := mulEquivOfCenterEqBot hcenter e₀
    by_cases h5' : p ^ f = 5
    · left
      obtain ⟨e4⟩ := nonempty_mulEquiv_psl2_four (K := GaloisField p f) (by rw [hKcard, h5'])
      exact ⟨2, Or.inl ⟨le_rfl, ⟨e.trans e4⟩⟩⟩
    · right
      exact le_iSup_centralizer_of_psl2 hKcard hK (by rw [hKcard]; omega) e hP
  · exact h Y X P hX (Or.inl hRee) hP
  · exact h Y X P hX (Or.inr hJ1) hP

theorem theorem3KnownGroupFacts_of_reeJ1 (h₁ : GoldschmidtTypeAutomorphismsReeJ1)
    (h₂ : GoldschmidtTypeGenerationReeJ1) : Theorem3KnownGroupFacts :=
  ⟨goldschmidtTypeAutomorphisms_of_reeJ1 h₁, goldschmidtTypeGeneration_of_reeJ1 h₂⟩

end Goldschmidt

end CFSG.ComponentClassification.AschbacherToolkit
