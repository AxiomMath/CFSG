module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ProdCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup
open scoped commutatorElement

theorem isShapeCentralizerFiveC_of_data {G : Type} [Group G] [Finite G] (X L Y : Subgroup G)
    (ψ : ↥Y →* Equiv.Perm (Fin 5)) {a u v : G} (hLX : L ≤ X) (hYX : Y ≤ X)
    (hX : Nat.card ↥X = Nat.card ↥L * Nat.card ↥Y) (hL : Nat.card ↥L = 5)
    (hLcen : ∀ l ∈ L, ∀ x ∈ X, x * l = l * x) (hLY : ∀ l ∈ L, l ∈ Y → l = 1)
    (hY : Nat.card ↥Y = 240) (hψ : Nat.card ↥ψ.range = 120) (haY : a ∈ Y) (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hacen : ∀ y ∈ Y, y * a = a * y) (haψ : ψ ⟨a, haY⟩ = 1) (hu : u ∈ Y)
    (hv : v ∈ Y) (hcomm : u * v * u⁻¹ * v⁻¹ = a) : IsShapeCentralizerFiveC ↥X := by
  haveI : Finite ↥Y := Nat.finite_of_card_ne_zero (by rw [hY]; norm_num)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eX⟩ := nonempty_mulEquiv_prod_of_central X L Y hLX hYX hLcen hLY hX
  have hZ5card : Nat.card (Multiplicative (ZMod 5)) = 5 := by simp
  have hLiso : Nonempty (↥L ≃* Multiplicative (ZMod 5)) :=
    ⟨mulEquivOfPrimeCardEq hL hZ5card⟩
  let a' : ↥Y := ⟨a, haY⟩
  let u' : ↥Y := ⟨u, hu⟩
  let v' : ↥Y := ⟨v, hv⟩
  let Z : Subgroup ↥Y := Subgroup.zpowers a'
  have ha'2 : a' ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    simpa [a'] using ha2
  have ha'1 : a' ≠ 1 := by
    intro h
    exact ha1 (Subtype.ext_iff.mp h)
  have ha'ord : orderOf a' = 2 := orderOf_eq_prime ha'2 ha'1
  have hZcard : Nat.card Z = 2 := by
    change Nat.card (Subgroup.zpowers a') = 2
    rw [Nat.card_zpowers a', ha'ord]
  have ha'cen : a' ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (hacen x.1 x.2)
  have hZcen : Z ≤ Subgroup.center ↥Y := by
    change Subgroup.zpowers a' ≤ Subgroup.center ↥Y
    rw [Subgroup.zpowers_le]
    exact ha'cen
  haveI : Z.Normal := Subgroup.normal_of_le_center hZcen
  have hker_card : Nat.card ψ.ker = 2 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hY, hψ] at h
    omega
  have hZker : Z = ψ.ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · change Subgroup.zpowers a' ≤ ψ.ker
      rw [Subgroup.zpowers_le]
      exact haψ
    · rw [hZcard, hker_card]
  have hperm_card : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  have hrange_top : ψ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hψ, hperm_card]
  have hψsurj : Function.Surjective ψ := MonoidHom.range_eq_top.mp hrange_top
  have hisoQ : Nonempty (↥Y ⧸ Z ≃* Equiv.Perm (Fin 5)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hZker).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)⟩
  have hZcomm : Z ≤ commutator ↥Y := by
    change Subgroup.zpowers a' ≤ commutator ↥Y
    rw [Subgroup.zpowers_le]
    have hcomm' : ⁅u', v'⁆ = a' := by
      apply Subtype.ext
      change u * v * u⁻¹ * v⁻¹ = a
      exact hcomm
    rw [← hcomm', _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) trivial trivial
  refine ⟨↥Y, inferInstance, ⟨Z, inferInstance, hZcard, hisoQ, hZcomm⟩, ?_⟩
  exact ⟨eX.trans (MulEquiv.prodCongr hLiso.some (MulEquiv.refl ↥Y))⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
