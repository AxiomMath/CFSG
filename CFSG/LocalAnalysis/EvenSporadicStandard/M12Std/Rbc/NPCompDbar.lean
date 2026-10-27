module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPCompDbarB
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPCompDbarC

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Equiv Subgroup

variable {K : Type*} [Group K] {A : Subgroup K} [A.Normal]

theorem sup_centralizer_eq_top (e : ↥A ≃* alternatingGroup (Fin 5))
    (hsign : ∀ k : K, Perm.sign (conjPerm5 e k) = 1) : A ⊔ centralizer (A : Set K) = ⊤ := by
  rw [eq_top_iff]
  intro k _
  set a : ↥A := e.symm ⟨conjPerm5 e k, Perm.mem_alternatingGroup.2 (hsign k)⟩ with ha
  have hΘa : conjPerm5 e (a : K) = conjPerm5 e k := by
    rw [conjPerm5_of_mem]
    simp [ha]
  have hmem : (a : K)⁻¹ * k ∈ centralizer (A : Set K) := by
    rw [← conjPerm5_eq_one_iff e, map_mul, map_inv, hΘa, inv_mul_cancel]
  have hk : k = (a : K) * ((a : K)⁻¹ * k) := by group
  rw [hk]
  exact mul_mem (mem_sup_left a.2) (mem_sup_right hmem)

theorem exists_mul_of_sup_centralizer_eq_top [Finite K]
    (hsup : A ⊔ centralizer (A : Set K) = ⊤) (y : K) :
    ∃ a ∈ A, ∃ t ∈ centralizer (A : Set K), y = a * t := by
  have hc : ∀ x ∈ A, ∀ t ∈ centralizer (A : Set K), x * t = t * x := fun x hx t ht =>
    mem_centralizer_iff.1 ht x hx
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A (centralizer (A : Set K))
    hc).2
  have hy : y ∈ ((A ⊔ centralizer (A : Set K) : Subgroup K) : Set K) := by
    rw [hsup]
    exact mem_top y
  rw [h] at hy
  obtain ⟨a, ha, t, ht, rfl⟩ := Set.mem_mul.1 hy
  exact ⟨a, ha, t, ht, rfl⟩

theorem exists_involution_of_normal_alt5 [Finite K] (hO : CFSG.oddCore K = ⊥)
    (e : ↥A ≃* alternatingGroup (Fin 5)) {w c : K} (hw : w * w = 1) (hcA : c ∈ A)
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hwc : ∀ a ∈ A, w * a * w⁻¹ = c * a * c⁻¹)
    (hab : ∀ a ∈ centralizer ({w} : Set K), ∀ b ∈ centralizer ({w} : Set K), a * b = b * a)
    (hcard : Nat.card ↥(centralizer ({w} : Set K)) = 8) :
    ∃ h : K, orderOf h = 2 ∧ centralizer (A : Set K) = zpowers h ∧ center K = zpowers h ∧
      A ⊔ zpowers h = ⊤ ∧ A ⊓ zpowers h = ⊥ ∧
      centralizer ({w} : Set K) = (A ⊓ centralizer ({w} : Set K)) ⊔ zpowers h ∧
      Nat.card ↥(A ⊓ centralizer ({w} : Set K)) = 4 ∧
      ∀ y ∈ centralizer ({w} : Set K), y * y = 1 := by
  have hS : Alt5Pair A w c := ⟨hw, hcA, hc2, hc1, hwc⟩
  have hcard8 : Nat.card ↥(centralizer ({w} : Set K)) ≤ 8 := hcard.le
  have hHcen : centralizer (A : Set K) ≤ center K := centralizer_le_center hO e hS hcard8
  have hsign := sign_conjPerm5_eq_one e hS hab hHcen
  have hsup := sup_centralizer_eq_top e hsign
  have hdec := exists_mul_of_sup_centralizer_eq_top hsup
  have hAH : A ⊓ centralizer (A : Set K) = ⊥ := inf_centralizer_eq_bot_of_alt5 e
  have hAc := card_inf_centralizer_single_of_alt5 e hcA hc2 hc1
  have hSeq := inf_centralizer_single_eq hS
  have hcomm : ∀ x ∈ A ⊓ centralizer ({w} : Set K), ∀ t ∈ centralizer (A : Set K),
      x * t = t * x := fun x hx t ht => mem_centralizer_iff.1 ht x hx.1
  have hC : centralizer ({w} : Set K) =
      (A ⊓ centralizer ({w} : Set K)) ⊔ centralizer (A : Set K) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨a, ha, t, ht, rfl⟩ := hdec y
      have htC : t ∈ centralizer ({w} : Set K) := center_le_centralizer _ (hHcen ht)
      have haC : a ∈ centralizer ({w} : Set K) := by
        have := mul_mem hy (inv_mem htC)
        simpa using this
      exact mul_mem (mem_sup_left ⟨ha, haC⟩) (mem_sup_right ht)
    · exact sup_le inf_le_right (hHcen.trans (center_le_centralizer _))
  have hinf : (A ⊓ centralizer ({w} : Set K)) ⊓ centralizer (A : Set K) = ⊥ := by
    rw [eq_bot_iff, ← hAH]
    exact inf_le_inf inf_le_left le_rfl
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (A ⊓ centralizer ({w} : Set K)) (centralizer (A : Set K)) hcomm).1
  rw [hinf, ← hC, Subgroup.card_bot, hcard, hSeq, hAc.1] at hprod
  have hH2 : Nat.card ↥(centralizer (A : Set K)) = 2 := by omega
  obtain ⟨h, hhH, hh1⟩ : ∃ h ∈ centralizer (A : Set K), h ≠ 1 := by
    by_contra hcon
    have hbot : centralizer (A : Set K) = ⊥ := eq_bot_iff.2 fun x hx => by
      rw [Subgroup.mem_bot]
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩
    rw [hbot, Subgroup.card_bot] at hH2
    omega
  have hzp : zpowers h = centralizer (A : Set K) := by
    apply eq_of_le_of_card_ge (zpowers_le.2 hhH)
    rw [hH2, Nat.card_zpowers]
    have h1 : orderOf h ≠ 1 := fun h1 => hh1 (orderOf_eq_one_iff.1 h1)
    have h2 : 0 < orderOf h := orderOf_pos h
    omega
  have hord : orderOf h = 2 := by
    rw [← Nat.card_zpowers, hzp, hH2]
  have hsq : ∀ t ∈ centralizer (A : Set K), t * t = 1 := by
    intro t ht
    rw [← hzp] at ht
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two]
    have : h * h = 1 := by
      rw [← sq, ← hord]
      exact pow_orderOf_eq_one h
    rw [this, one_zpow]
  refine ⟨h, hord, hzp.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hzp]
    refine le_antisymm ?_ hHcen
    intro z hz
    exact mem_centralizer_iff.2 fun a ha => mem_center_iff.1 hz a
  · rw [hzp]
    exact hsup
  · rw [hzp]
    exact hAH
  · rw [hzp]
    exact hC
  · rw [hSeq]
    exact hAc.1
  · intro y hy
    obtain ⟨a, ha, t, ht, rfl⟩ := hdec y
    have htC : t ∈ centralizer ({w} : Set K) := center_le_centralizer _ (hHcen ht)
    have haC : a ∈ centralizer ({w} : Set K) := by
      have := mul_mem hy (inv_mem htC)
      simpa using this
    have haS : a ∈ A ⊓ centralizer ({c} : Set K) := by
      rw [← hSeq]
      exact ⟨ha, haC⟩
    have hat : a * t = t * a := mem_centralizer_iff.1 ht a ha
    calc a * t * (a * t) = a * (t * a) * t := by group
      _ = a * (a * t) * t := by rw [← hat]
      _ = (a * a) * (t * t) := by group
      _ = 1 := by rw [hAc.2 a haS, hsq t ht, one_mul]

end CFSG.EvenSporadicStandard.M12Std.Rbc
