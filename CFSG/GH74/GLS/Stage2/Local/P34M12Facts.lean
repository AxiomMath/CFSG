module

public import CFSG.GH74.GLS.Stage2.Local.P34M12Bar
public import CFSG.GH74.GLS.Stage2.Local.Lemma23eRes
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34M12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem stage1M12_of_ctx {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (h : Stage2Ctx G z Kind.m12 S) : Stage1M12 G z S := by
  have hd := h.data
  cases hd with
  | m12 hM => exact hM

theorem card_Q8' : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem perm_inv_key : ∀ τ ρ : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 → ρ * ρ * ρ = 1 → ρ ≠ 1 →
    τ * ρ * τ⁻¹ * ρ = 1 := by
  decide

section Facts

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem exists_barFacts (hz : orderOf z = 2) (h : Stage1M12 G z S) :
    ∃ a : CentralizerBar z, BarFacts (WBar z) (toBar z ⟨z, mem_Cen_self z⟩) a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, B, hprod, hAq, hBq, -⟩ := h.W_shape
  obtain ⟨A', ⟨eA'⟩, -, -, hFst, -, hfixA'⟩ := h.L_shape
  obtain ⟨hWn0, ⟨eq⟩⟩ := h.quot
  obtain ⟨ζ, -, -, hζ1, hζsq, -, hcomm, hcen, hext⟩ := q8_central_product hprod hAq hBq
  obtain ⟨zb, hzb⟩ : ∃ zb, zb = toBar z ⟨z, mem_Cen_self z⟩ := ⟨_, rfl⟩
  have hzbc : zb ∈ center (CentralizerBar z) := hzb ▸ toBar_z_mem_center z
  have hzbW : zb ∈ WBar z := by
    have := centralizer_generalizedFitting_le (CentralizerBar z)
      (Subgroup.mem_centralizer_iff.mpr fun y _ => Subgroup.mem_center_iff.mp hzbc y)
    rw [hFst] at this
    exact hzb ▸ this
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  have hzb1 : zb ≠ 1 := by
    intro h1
    have hsq : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) ^ 2 = 1 := Subtype.ext hz2
    have := eq_one_of_toBar_eq_one z hsq (hzb ▸ h1)
    have hz1 : z = 1 := congrArg Subtype.val this
    rw [hz1, orderOf_one] at hz
    omega
  have hzbζ : zb = ζ := by
    have := hcen zb hzbW (fun g _ => Subgroup.mem_center_iff.mp hzbc g)
    rcases mem_zpowers_involution hζsq this with h1 | h1
    · exact absurd h1 hzb1
    · exact h1
  have hζc : ∀ y, y * ζ = ζ * y := fun y => hzbζ ▸ Subgroup.mem_center_iff.mp hzbc y
  have hcardA' : Nat.card ↥A' = 3 := by
    rw [Nat.card_congr eA'.toEquiv, Nat.card_eq_fintype_card]
    simp
  obtain ⟨a, haA', hAgen, ha3⟩ := CFSG.GH74.GLS.Stage1.Thm6.Prod.exists_gen_card_three hcardA'
  have hfix : ∀ w ∈ WBar z, a * w = w * a → w ∈ zpowers ζ := by
    intro w hw hcw
    have hall : ∀ a' ∈ A', a' * w = w * a' := by
      intro a' ha'
      rw [hAgen] at ha'
      obtain ⟨n, rfl⟩ := ha'
      exact (((show Commute a w from hcw).zpow_left n)).eq
    have := hfixA' w hw hall
    rw [barOf_zpowers_self, ← hzb, hzbζ] at this
    exact this
  have hWn : (WBar z).Normal := by
    rw [← hFst]
    exact CFSG.LocalCores.generalized_fitting_characteristic.2
  have hAcard : Nat.card ↥A = 8 := by rw [Nat.card_congr hAq.some.toEquiv]; exact card_Q8'
  have hBcard : Nat.card ↥B = 8 := by rw [Nat.card_congr hBq.some.toEquiv]; exact card_Q8'
  have hWcard : Nat.card ↥(WBar z) = 32 := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hprod.2.1).1
    rw [hprod.1, hprod.2.2, hAcard, hBcard] at this
    omega
  have hWpg : IsPGroup 2 ↥(WBar z) := IsPGroup.of_card (n := 5) (by rw [hWcard]; norm_num)
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot] at hAgen
    have : Nat.card ↥A' = 1 := by rw [hAgen]; exact Subgroup.card_bot
    omega
  have ha3' : a * a * a = 1 := by simpa [pow_succ, mul_assoc] using ha3
  have haW : a ∉ WBar z := by
    intro haW
    have h1 : orderOf a ∣ Nat.card ↥(WBar z) := by
      have := Subgroup.orderOf_dvd_natCard (WBar z) haW
      simpa using this
    have h2 : orderOf a = 3 := orderOf_eq_prime ha3 ha1
    rw [h2, hWcard] at h1
    omega
  refine ⟨a, ?_⟩
  rw [← hzb, hzbζ]
  refine ⟨hWn, hWcard, hzbζ ▸ hzbW, hζ1, by simpa [pow_two] using hζsq, hζc, hcomm, hext, ha3', hfix, ?_, ?_⟩
  ·
    intro y hy2 hyW
    let q : CentralizerBar z →* Equiv.Perm (Fin 3) :=
      (eq : (CentralizerBar z ⧸ WBar z) ≃* Equiv.Perm (Fin 3)).toMonoidHom.comp
        (QuotientGroup.mk' (WBar z))
    have hqW : ∀ x : CentralizerBar z, q x = 1 → x ∈ WBar z := by
      intro x hx
      have h1 : QuotientGroup.mk' (WBar z) x = 1 := by
        apply eq.injective
        rw [map_one]
        exact hx
      exact (QuotientGroup.eq_one_iff x).1 h1
    have hqy : q y ≠ 1 := fun h1 => hyW (hqW y h1)
    have hqa : q a ≠ 1 := fun h1 => haW (hqW a h1)
    have hqy2 : q y * q y = 1 := by rw [← map_mul, hy2, map_one]
    have hqa3 : q a * q a * q a = 1 := by rw [← map_mul, ← map_mul, ha3', map_one]
    have key := perm_inv_key (q y) (q a) hqy2 hqy hqa3 hqa
    apply hqW
    rw [map_mul, map_mul, map_mul, map_inv]
    exact key
  ·
    intro M hMn hM2
    have hMp : IsPGroup 2 ↥M := fun g => ⟨1, by
      apply Subtype.ext
      simpa [pow_two] using hM2 g g.2⟩
    have h1 : M ≤ pCore 2 (CentralizerBar z) := le_sSup ⟨hMn, hMp⟩
    calc M ≤ pCore 2 (CentralizerBar z) := h1
      _ ≤ fittingSubgroup (CentralizerBar z) := pCore_le_fitting _ 2
      _ ≤ generalizedFitting (CentralizerBar z) := le_sup_left
      _ = WBar z := hFst

end Facts

end CFSG.GH74.GLS.Stage2.Local.P34M12
