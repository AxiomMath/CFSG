module

public import CFSG.LargeExtraspecial.AS35VBlock

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.RankThree.OrthogonalInvolutions
open Setting (mem_normalizer_of_conj_le)

namespace AS35V

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem standing_conj (hS : S.SixHyp) (hRI : RootInvolutionComponentsInput.{0})
    (hsup : PbarSupply S) :
    ∀ a ∈ S.DbarAsc, ∀ b ∈ S.DbarAsc, ∃ g ∈ closure S.DbarAsc, g * a * g⁻¹ = b := by
  intro a ha b hb
  have hab := mem_comp12_of_mem_DbarAsc hS hRI hsup ha hb
  obtain ⟨x, hx, rfl⟩ := hRI S.Qt S.q S.q_nondegenerate S.Mbar S.s12_noNormalTwo_Mbar S.Dbar12
    rfl a (mem_Dbar12_of_mem_DbarAsc hS ha) b hab
  exact ⟨x, closure_mono (comp12_subset_DbarAsc hS hRI ha) hx, rfl⟩

theorem standing_fstar_card (hS : S.SixHyp) (hsup : PbarSupply S) :
    Nat.card (CFSG.generalizedFitting (S.Mbar ⊓ centralizer S.DbarAsc : Subgroup S.O)) ≤ 3 := by
  obtain ⟨σ, hσ⟩ := DbarAsc_nonempty hS
  obtain ⟨P, hP, h58⟩ := hsup σ hσ
  set H : Subgroup S.O := S.Mbar ⊓ centralizer S.DbarAsc with hH
  have hconj : ∀ m ∈ S.Mbar, ∀ x ∈ H, m * x * m⁻¹ ∈ H := by
    intro m hm x hx
    refine mem_inf.mpr ⟨S.Mbar.mul_mem (S.Mbar.mul_mem hm hx.1) (S.Mbar.inv_mem hm), ?_⟩
    rw [mem_centralizer_iff]
    intro d hd
    have hd' : m⁻¹ * d * m⁻¹⁻¹ ∈ S.DbarAsc := conj_mem_DbarAsc (S.Mbar.inv_mem hm) hd
    have e := mem_centralizer_iff.mp hx.2 _ hd'
    calc d * (m * x * m⁻¹) = m * ((m⁻¹ * d * m⁻¹⁻¹) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * d * m⁻¹⁻¹)) * m⁻¹ := by rw [e]
      _ = m * x * m⁻¹ * d := by group
  have hN2 : S12NoNormalTwo H := S.s12_noNormalTwo_Mbar.of_normal inf_le_left fun m hm =>
    mem_normalizer_of_conj_le (hconj m hm) (hconj m⁻¹ (S.Mbar.inv_mem hm))
  have hHσ : ∀ y ∈ H, y * σ = σ * y := fun y hy => (mem_centralizer_iff.mp hy.2 σ hσ).symm
  obtain ⟨-, -, hF3, hFs⟩ := fitting_of_fiveEight h58 inf_le_left hHσ
    (fun p hp => hconj p (hP.le_Mbar hp)) hN2
  rw [hFs]
  exact hF3

theorem le_center_of_commute {N : Subgroup (closure S.DbarAsc)}
    (hN : ∀ d ∈ S.DbarAsc, ∀ x ∈ N.map (closure S.DbarAsc).subtype, d * x = x * d) :
    N ≤ center (closure S.DbarAsc) := by
  intro n hn
  rw [mem_center_iff]
  intro g
  have : closure S.DbarAsc ≤ centralizer ({(n : S.O)} : Set S.O) := by
    rw [closure_le]
    intro d hd
    exact mem_centralizer_singleton_iff.mpr (hN d hd n ⟨n, hn, rfl⟩)
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (this g.2))

theorem fitting_le_center_or (hS : S.SixHyp) (hsup : PbarSupply S) :
    CFSG.fittingSubgroup (closure S.DbarAsc) ≤ center (closure S.DbarAsc) ∨
      (S.width = 3 ∧ ∃ X : Subgroup S.O, X ≤ S.Mbar ∧ (∀ m ∈ S.Mbar, ∀ x ∈ X, m * x * m⁻¹ ∈ X) ∧
        IsPGroup 3 X ∧ ∃ t ∈ S.DSet, ∃ ht : t ∈ S.M, ∃ x ∈ X,
          S.ρ ⟨t, ht⟩ * x ≠ x * S.ρ ⟨t, ht⟩) := by
  by_cases hF : CFSG.fittingSubgroup (closure S.DbarAsc) ≤ center (closure S.DbarAsc)
  · exact Or.inl hF
  right
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨X, hX⟩ : ∃ X : Subgroup S.O,
      X = (CFSG.pCore 3 (closure S.DbarAsc)).map (closure S.DbarAsc).subtype := ⟨_, rfl⟩
  have hXM : X ≤ S.Mbar := hX ▸ (map_subtype_le _).trans closure_DbarAsc_le_Mbar
  have hX3 : IsPGroup 3 X := hX ▸ CFSG.pCore_isPGroup.map _
  have hMX : ∀ m ∈ S.Mbar, ∀ x ∈ X, m * x * m⁻¹ ∈ X := fun m hm x hx => by
    rw [hX] at hx ⊢
    exact conj_mem_map_of_characteristic _ (Mbar_le_normalizer_closure_DbarAsc hm) hx
  obtain ⟨d, hd, x, hx, hdx⟩ : ∃ d ∈ S.DbarAsc, ∃ x ∈ X, d * x ≠ x * d := by
    by_contra hcon
    push Not at hcon
    apply hF
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    have hp : (p.1.1).Prime := Nat.prime_of_mem_primeFactors p.1.2
    have : Fact p.1.1.Prime := ⟨hp⟩
    by_cases h2 : p.1.1 = 2
    · rw [h2, pCore_two_eq_bot noNormalTwo_closure_DbarAsc]
      exact bot_le
    by_cases h3 : p.1.1 = 3
    · rw [h3]
      exact le_center_of_commute (hX ▸ hcon)
    · refine le_center_of_commute fun d hd x hx => ?_
      set O := (CFSG.pCore p.1.1 (closure S.DbarAsc)).map (closure S.DbarAsc).subtype with hO
      have hle : O.map S.O.subtype ≤ TauCeti.QuadraticMap.orthogonalGroup S.q := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      have hcop : Nat.Coprime (Nat.card (O.map S.O.subtype)) 6 := by
        rw [card_map_of_injective (subtype_injective _), hO,
          card_map_of_injective (subtype_injective _)]
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p.1.1)
          (G := closure S.DbarAsc)).exists_card_eq
        rw [hk]
        refine Nat.Coprime.pow_left k ?_
        rw [show (6 : ℕ) = 2 * 3 by norm_num]
        exact Nat.Coprime.mul_right ((Nat.coprime_primes hp Nat.prime_two).mpr h2)
          ((Nat.coprime_primes hp Nat.prime_three).mpr h3)
      have hdL : d ∈ closure S.DbarAsc := subset_closure hd
      have hnorm : ∀ y ∈ O.map S.O.subtype, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) * y *
          (d : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ ∈ O.map S.O.subtype := by
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨d * y * d⁻¹, ?_, by simp⟩
        rw [hO] at hy ⊢
        exact conj_mem_map_of_characteristic _ (le_normalizer hdL) hy
      have h := commute_of_normalizes_of_coprime S.q_nondegenerate
        (isTypeA_of_mem_DbarAsc hS hd) hle hcop hnorm (x := (x : S.Qt ≃ₗ[ZMod 2] S.Qt))
        ⟨x, hx, rfl⟩
      exact Subtype.ext (by simpa using h)
  obtain ⟨t, htD, ht, rfl⟩ := hd
  obtain ⟨P, hP, h58⟩ := hsup _ ⟨t, htD, ht, rfl⟩
  have hw := (hP.fiveEleven h58 hXM hX3 (fun p hp => hMX p (hP.le_Mbar hp)) ⟨x, hx, hdx⟩).1
  exact ⟨le_antisymm hw hS.three_le_width, X, hXM, hMX, hX3, t, htD, ht, x, hx, hdx⟩

end AS35V

end CFSG.LargeExtraspecial
