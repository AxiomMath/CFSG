module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Norm
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section FL2

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}

theorem fl2_model {Y : Type} [Group Y] (hY : FL2 Y) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), IVK.L2Field F ∧ Nonempty (Y ≃* IVK.L2 F) := by
  obtain ⟨p₀, f, hp₀, hf, hp₀2, hLie⟩ := hY
  obtain ⟨-, -, -, hpf3, F, _, _, hFcard, ⟨e0⟩⟩ :=
    ComponentClassification.AutL2Facts.lieModel_psl2_data hLie
  have hoddF : Odd (Nat.card F) := by
    rw [hFcard]
    exact (hp₀.odd_of_ne_two hp₀2).pow
  have hF3 : 3 < Nat.card F := by
    have h1 : p₀ ≤ p₀ ^ f := Nat.le_self_pow (by omega) p₀
    have h2 : 3 ≤ p₀ := by have := hp₀.two_le; omega
    have h3 : Nat.card F ≠ 3 := by rw [hFcard]; exact hpf3
    have : 3 ≤ Nat.card F := by rw [hFcard]; exact h2.trans h1
    omega
  exact ⟨F, inferInstance, inferInstance, ⟨hoddF, hF3⟩, ⟨e0.trans (IVK.L2.equivPSL F).symm⟩⟩

theorem fl2_of_normalizes (hfr : AFrame A zb Sb Vb) {J : Subgroup A} (hJ : IsComponent J)
    (hY : FL2 (↥J ⧸ center ↥J)) (hsw : Sb ≤ normalizer (J : Set A)) : False := by
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_aut_of_normalizes hfr hJ hsw
  obtain ⟨F, _, _, hFL, ⟨e⟩⟩ := fl2_model hY
  have := IVK.card_le_eight_of_elemAbelian e hFL E hE
  omega

theorem exists_four_le_of_FL2 {J : Subgroup A} (hZ : center ↥J = ⊥)
    (hY : FL2 (↥J ⧸ center ↥J)) : ∃ U : Subgroup A, U ≤ J ∧ IVK.IsFourSubgroup U := by
  obtain ⟨F, _, _, hFL, ⟨e⟩⟩ := fl2_model hY
  let eJ : ↥J ≃* GorensteinWalter.PSL2 F :=
    ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
      e).trans (IVK.L2.equivPSL F)
  have : Finite (GorensteinWalter.PSL2 F) := Finite.of_equiv _ eJ.toEquiv
  have hdihP : GorensteinWalter.HasDihedralSylowTwo (GorensteinWalter.PSL2 F) :=
    GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
      (IVK.isOddPrimePower_of_odd_card hFL.1)
  have hdih : GorensteinWalter.HasDihedralSylowTwo ↥J :=
    IVK.hasDihedralSylowTwo_of_equiv eJ.symm hdihP
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥J) := Sylow.nonempty
  obtain ⟨m, hm, ⟨d⟩⟩ := hdih S
  obtain ⟨V, -, hV⟩ := GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (S : Subgroup ↥J) hm d
  have hV4 := IVK.isFourSubgroup_of_isKleinFour hV
  obtain ⟨hcV, hsV⟩ := IVK.isFourSubgroup_props hV4
  refine ⟨V.map J.subtype, Subgroup.map_subtype_le _, IVK.isFourSubgroup_of ?_ ?_ ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hcV a ha b hb)
  · rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hsV a ha)
  · rw [Subgroup.card_map_of_injective J.subtype_injective]
    exact hV4.2

theorem card_of_model {Y : Type} [Group Y] {F : Type} [Field F] [Finite F] (hF : IVK.L2Field F)
    (e : Y ≃* IVK.L2 F) : Nat.card Y = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
  have h1 : Nat.card Y = Nat.card (IVK.L2 F) := Nat.card_congr e.toEquiv
  have h2 : Nat.card (IVK.L2 F) = Nat.card (GorensteinWalter.PSL2 F) :=
    Nat.card_congr (IVK.L2.equivPSL F).toEquiv
  rw [h1, h2]
  exact GorensteinWalter.psl2_card_formula F (IVK.isOddPrimePower_of_odd_card hF.1)

end FL2

theorem q_cases (q : ℕ) (hodd : Odd q) (h3 : 3 < q)
    (hd : (q * (q ^ 2 - 1) / 2) ^ 2 ∣ Nat.factorial 11) : q = 5 ∨ q = 9 := by
  have hle := Nat.le_of_dvd (Nat.factorial_pos 11) hd
  have hq : q ≤ 23 := by
    by_contra h
    push Not at h
    have h1 : 24 ≤ q := h
    have h2 : 24 * (24 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h1 2) 1)
    have h3' : 6900 ≤ q * (q ^ 2 - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      omega
    have h4 : 6900 ^ 2 ≤ (q * (q ^ 2 - 1) / 2) ^ 2 := Nat.pow_le_pow_left h3' 2
    have h5 : Nat.factorial 11 = 39916800 := by decide
    omega
  have hodd' : q % 2 = 1 := Nat.odd_iff.mp hodd
  interval_cases q <;> first
    | omega
    | (exfalso; revert hd; norm_num [Nat.factorial])

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
