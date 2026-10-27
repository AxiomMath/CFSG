module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionE

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open CFSG.GH74.QTGen4.Recog.G23.P7.B27A

variable {G : Type} [Group G]

section SStruct

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ Pb W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

theorem e2_ne_one [Finite G] (hlet : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e) :
    e 2 ≠ 1 := by
  intro h2
  have hle : Psub e ≤ Subgroup.zpowers (e 0) := by
    unfold Psub
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_zpowers _
    · rw [h2]
      exact Subgroup.one_mem _
  have hc := Subgroup.card_le_of_le hle
  rw [hF.card_P, Nat.card_zpowers] at hc
  have h3 : e 0 ^ 3 = 1 := (hlet_cube hlet).1
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)
  omega

theorem Mf_le_normalizer_M₁ (hst : B27State e M₁ Pb W₁ Mf t') :
    Mf ≤ Subgroup.normalizer (M₁ : Set G) := fun x hx =>
  mem_normalizer_of_conj (hst.M₁_normal x hx) (hst.M₁_normal x⁻¹ (Mf.inv_mem hx))

theorem Mf_le_normalizer_Mbar [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hst : B27State e M₁ Pb W₁ Mf t') (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hstab : ∀ g ∈ (rhoGL b).range, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 1 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2 = 0) :
    Mf ≤ Subgroup.normalizer (Mbar b : Set G) := fun x hx =>
  mem_normalizer_of_conj_le (fun y hy => Mbar_conj_mem b hstab x
    (Mf_le_normalizer_M₁ hst hx) y hy)

theorem Mf_not_le_Mbar [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) (hst : B27State e M₁ Pb W₁ Mf t')
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁)) :
    ¬ Mf ≤ Mbar b := by
  intro hle
  have hs2M : e 2 ∈ Mbar b := hle hst.s₂_mem
  have hc2 : Commute (e 2) (e 0) := ((hlet_comm hlet).1).symm
  have hs2N : e 2 ∈ Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G) := by
    apply mem_normalizer_of_conj_le
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [(hc2.zpow_right j).eq, mul_inv_cancel_right]
    exact hx
  have hM := Mbar_inf_norm hone hlet hv hst b hb0 (e 2) hs2M hs2N
  have hH2 : e 2 ∈ H₂ := (hlet_mem hlet).2.2.1
  have hHe : e 2 ∈ M₁ ⊓ H := ⟨hM, hone.le_two hH2⟩
  rw [hv.inf_H] at hHe
  have hz : e 2 ∈ Subgroup.zpowers (e 0) ⊓ H₂ := ⟨hHe, hH2⟩
  rw [hF.disj₁, Subgroup.mem_bot] at hz
  exact e2_ne_one hlet hF hz

theorem card_Mf_inf_Mbar_le [Finite G] (N M : Subgroup G) (hnot : ¬ N ≤ M)
    (hN : Nat.card N = 243) : Nat.card ↥(N ⊓ M) ≤ 81 := by
  have hdvd : Nat.card ↥(N ⊓ M) ∣ 243 := by
    rw [← hN]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card ↥(N ⊓ M) ≠ 243 := by
    intro h
    apply hnot
    have hEq : N ⊓ M = N := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hN, h])
    rw [← hEq]
    exact inf_le_right
  have hmem : Nat.card ↥(N ⊓ M) ∈ Nat.divisors 243 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdiv : Nat.divisors 243 = {1, 3, 9, 27, 81, 243} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem card_S_bounds [Finite G] (N M : Subgroup G) (hnot : ¬ N ≤ M)
    (hNnorm : N ≤ Subgroup.normalizer (M : Set G))
    (hN : Nat.card N = 243) (hM : Nat.card M = 243) :
    729 ≤ Nat.card ↥(N ⊔ M) ∧ Nat.card ↥(N ⊔ M) ∣ 3 ^ 10 := by
  have hprod := card_sup_mul_card_inf N M hNnorm
  rw [hN, hM] at hprod
  have hI := card_Mf_inf_Mbar_le N M hnot hN
  have hpos : 0 < Nat.card ↥(N ⊓ M) := Nat.card_pos
  constructor
  · nlinarith
  · exact ⟨Nat.card ↥(N ⊓ M), by rw [show (3 : ℕ) ^ 10 = 243 * 243 by norm_num]; exact hprod.symm⟩

end SStruct

end CFSG.GH74.QTGen4.Recog.G23.P7
