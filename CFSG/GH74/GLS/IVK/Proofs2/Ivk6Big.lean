module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6NI
public import CFSG.GH74.GLS.C3.Layer1.BkIvk6Split
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Four

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section Big

theorem exists_l2Field_of_hasL2Model_gt {K : Type} [Group K]
    (h : HasL2Model K (fun r => Odd r ∧ 9 < r)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : K ≃* L2 F), L2Field F ∧ 11 ≤ Nat.card F := by
  obtain ⟨p, f, hp, hf, ⟨hodd, hbig⟩, hL⟩ := h
  rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hq11 : 11 ≤ p ^ f := by
      have h2 : (p ^ f) % 2 = 1 := Nat.odd_iff.1 hodd
      omega
    exact ⟨F, hF, hFin, e, ⟨by rw [hcard]; exact hodd, by rw [hcard]; omega⟩, by rw [hcard]; exact hq11⟩
  all_goals exact absurd h0 (by norm_num)

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem fixedSubgroup_le_gammaAut {W : Subgroup (MulAut K)} {w : MulAut K} (hw : w ∈ W)
    (hord : orderOf w = 2) : fixedSubgroup K w ≤ CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K W :=
  le_iSup_of_le w (le_iSup_of_le hw (le_iSup_of_le hord le_rfl))

theorem b_ivk_6_big :
    CFSG.GH74.GLS.C3.Layer1.Bk.B_ivk_6_big := by
  intro K _ _ hL B hBel hB4
  obtain ⟨F, _, _, e0, hF, hq⟩ := exists_l2Field_of_hasL2Model_gt hL
  obtain ⟨e, N, -⟩ :=
    ivk_1_2a_exists F hF K e0 (inferInstance : Nonempty (Sylow 2 (MulAut K))).some
  have hinj := conj_injective_of_L2 e
  have hBsq : ∀ b ∈ B, b ^ 2 = 1 := fun b hb => by
    have := hBel
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian b hb
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBel.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥B) ⟨b, hb⟩)
  have hordc : ∀ u : K, orderOf (MulAut.conj u) = orderOf u := fun u => orderOf_injective _ hinj u
  have hinnerB : ∀ w ∈ B, w ≠ 1 → w ∈ innAut K → ∃ u : K, orderOf u = 2 ∧ MulAut.conj u ∈ B := by
    rintro w hwB hw1 ⟨u, rfl⟩
    have hu1 : u ≠ 1 := fun h => hw1 (by rw [h, map_one])
    have hu2 : u ^ 2 = 1 := hinj (by rw [map_pow, hBsq _ hwB, map_one])
    exact ⟨u, orderOf_eq_prime hu2 hu1, hwB⟩
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := CFSG.QuasithinUnique.Unc25Small.exists_two_nonid hB4
  have hex : ∃ w₁ ∈ B, ∃ w₂ ∈ B, w₁ ≠ 1 ∧ w₂ ≠ 1 ∧ w₁ ≠ w₂ ∧ w₁ ∈ innDiagSub e ∧
      IsCoatom (fixedSubgroup K w₁) := by
    by_cases hinn : ∃ u : K, orderOf u = 2 ∧ MulAut.conj u ∈ B
    · obtain ⟨u, hu, huB⟩ := hinn
      have hw₁1 : MulAut.conj u ≠ 1 := fun h => by
        have : u = 1 := hinj (by rw [h, map_one])
        rw [this, orderOf_one] at hu
        omega
      have hcoat : IsCoatom (fixedSubgroup K (MulAut.conj u)) := by
        rw [Lemma118.fixedSubgroup_conj]
        exact isCoatom_centralizer_of_inner hF hq e hu
      by_cases hau : a = MulAut.conj u
      · exact ⟨MulAut.conj u, huB, b, hb, hw₁1, hb1, fun h => hab (hau.trans h), 
          innAut_le_innDiagSub e ⟨u, rfl⟩, hcoat⟩
      · exact ⟨MulAut.conj u, huB, a, ha, hw₁1, ha1, fun h => hau h.symm,
          innAut_le_innDiagSub e ⟨u, rfl⟩, hcoat⟩
    · obtain ⟨w₁, hw₁B, hw₁1, hw₁D⟩ := exists_inndiag_involution_of_klein hF e hB4 hBsq
      have hw₁I : w₁ ∉ innAut K := fun h => hinn (hinnerB w₁ hw₁B hw₁1 h)
      obtain ⟨w₂, hw₂B, hw₂1, hw₁₂⟩ : ∃ w₂ ∈ B, w₂ ≠ 1 ∧ w₁ ≠ w₂ := by
        by_cases hab1 : a = w₁
        · exact ⟨b, hb, hb1, fun h => hab (hab1.trans h)⟩
        · exact ⟨a, ha, ha1, fun h => hab1 h.symm⟩
      have hw₂D : w₂ ∉ innDiagSub e := by
        intro hD
        have hw₂I : w₂ ∉ innAut K := fun h => hinn (hinnerB w₂ hw₂B hw₂1 h)
        have hmem := mul_mem_innAut_of_not_mem hF e hw₁D hD hw₁I hw₂I
        have hprod1 : w₁ * w₂ ≠ 1 := by
          intro h
          have h1 : w₁ * w₁ = 1 := by rw [← pow_two]; exact hBsq w₁ hw₁B
          exact hw₁₂ (mul_left_cancel (h.trans h1.symm)).symm
        exact hinn (hinnerB (w₁ * w₂) (B.mul_mem hw₁B hw₂B) hprod1 hmem)
      obtain ⟨q₀, hq₀, -⟩ := card_fixedSubgroup_outer hF e N (hBsq w₂ hw₂B) hw₂D
      have hq16 : 11 < Nat.card F := by
        rw [← hq₀]
        have h4 : 4 ≤ q₀ := by
          by_contra h
          have h3 : q₀ ≤ 3 := by omega
          have : q₀ ^ 2 ≤ 9 := by nlinarith
          omega
        nlinarith
      have hcoat := (ivk_1_3e F hF K e w₁ hw₁D (orderOf_eq_prime (hBsq w₁ hw₁B) hw₁1)).1 hq16
      exact ⟨w₁, hw₁B, w₂, hw₂B, hw₁1, hw₂1, hw₁₂, hw₁D, hcoat⟩
  obtain ⟨w₁, hw₁B, w₂, hw₂B, hw₁1, hw₂1, hw₁₂, hw₁D, hcoat⟩ := hex
  have hcomm : w₁ * w₂ = w₂ * w₁ := hBcomm w₁ hw₁B w₂ hw₂B
  have hnle := not_fixed_le hF hq e N (hBsq w₁ hw₁B) (hBsq w₂ hw₂B) hw₁₂ hw₁1 hw₂1 hcomm hw₁D
  have hsup : fixedSubgroup K w₁ ⊔ fixedSubgroup K w₂ = ⊤ :=
    hcoat.2 _ (lt_of_le_of_ne le_sup_left fun h => hnle (le_sup_right.trans (le_of_eq h.symm)))
  apply eq_top_iff.2
  rw [← hsup]
  exact sup_le (fixedSubgroup_le_gammaAut hw₁B (orderOf_eq_prime (hBsq w₁ hw₁B) hw₁1))
    (fixedSubgroup_le_gammaAut hw₂B (orderOf_eq_prime (hBsq w₂ hw₂B) hw₂1))

end Big

end CFSG.GH74.GLS.IVK.Proofs2
