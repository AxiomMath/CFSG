module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.OmegaFour
public import CFSG.GF2Type.Smith1979.W4AsOmega
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

theorem eq_one_or_eq_of_mem_zpowers {X : Type} [Group X] {t u : X} (ht2 : t * t = 1)
    (hu : u ∈ zpowers t) : u = 1 ∨ u = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem eq_one_of_mem_zpowers_of_mem_card_nine (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    {P : Subgroup S.O} (hP9 : Nat.card P = 9) {w : S.O} (hwt : w ∈ zpowers t) (hwP : w ∈ P) :
    w = 1 := by
  have ht2 : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hwt
  have hw2 : (t ^ k) ^ 2 = 1 := by
    rw [pow_two, ← zpow_add, ← two_mul, zpow_mul, zpow_two, ht2, one_zpow]
  have hw9 : (t ^ k) ^ 9 = 1 := by
    have h := pow_card_eq_one' (G := P) (x := ⟨t ^ k, hwP⟩)
    rw [hP9] at h
    exact congrArg Subtype.val h
  have h1 : orderOf (t ^ k) ∣ Nat.gcd 2 9 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw2) (orderOf_dvd_of_pow_eq_one hw9)
  norm_num at h1
  exact h1

theorem eq_one_or_eq_of_commute_card_nine (hCE : CentralExtInput.{0}) (hw : S.width = 4)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9) {u : S.O} (hu : u ∈ S.Lbar g)
    (huP : ∀ x ∈ P, u * x = x * u) : u = 1 ∨ u = t := by
  obtain ⟨Q, hQ, -, hR, -, hsing⟩ := hΩ.exists_form
  have hplusQ : CFSG.GroupTheory.WeirSylow.IsPlusType Q := by
    obtain ⟨P₀, hP₀2, hP₀⟩ := hplus
    refine ⟨P₀, by rw [hP₀2, h4], fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
    · exact (hsing v hv0).mpr (hP₀ v hv hv0)
  have hN : Nbar S g t = zpowers t := W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4
  have huR : u ∈ Rbar S g t := Lbar_le_Rbar ht hu
  have hKP : ∀ x : P.subgroupOf (Rbar S g t), ((x : Rbar S g t) : S.O) ∈ P :=
    fun x => mem_subgroupOf.mp x.2
  obtain ⟨f, hfdef⟩ :
      ∃ f : P.subgroupOf (Rbar S g t) →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t),
      f = (resV H.conj_mem t).comp (P.subgroupOf (Rbar S g t)).subtype := ⟨_, rfl⟩
  have hfx : ∀ x : P.subgroupOf (Rbar S g t), f x = resV H.conj_mem t (x : Rbar S g t) :=
    fun x => by rw [hfdef]; rfl
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : f (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : (((a⁻¹ * b : P.subgroupOf (Rbar S g t)) : Rbar S g t) : S.O) ∈ Nbar S g t := by
      rw [hfx] at h1
      exact (resV_eq_one_iff H.conj_mem _).mp h1
    rw [hN] at h2
    have h3 := eq_one_of_mem_zpowers_of_mem_card_nine H ht hP9 h2 (hKP (a⁻¹ * b))
    have h4' : a⁻¹ * b = 1 := Subtype.ext (Subtype.ext h3)
    rw [inv_mul_eq_one] at h4'
    exact h4'
  have hKcard : Nat.card (P.subgroupOf (Rbar S g t)) = 9 := by
    rw [← hP9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv
  have hP'9 : Nat.card f.range = 9 := by
    rw [← hKcard]
    exact Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm
  have hP'Ω : f.range ≤ omegaGroup Q hQ := by
    rw [← hR]
    rintro _ ⟨x, rfl⟩
    rw [hfx]
    exact ⟨((x : Rbar S g t) : S.O), (x : Rbar S g t).2,
      fun v => coe_resV_apply H.conj_mem (x : Rbar S g t) v⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = resV H.conj_mem t ⟨u, huR⟩ := ⟨_, rfl⟩
  have hσΩ : σ ∈ omegaGroup Q hQ := by
    rw [← hR, hσdef]
    exact ⟨u, huR, fun v => coe_resV_apply H.conj_mem _ v⟩
  have hσ2 : σ ^ 2 = 1 := by
    rw [hσdef, ← map_pow]
    have hu2 : (⟨u, huR⟩ : Rbar S g t) ^ 2 = 1 :=
      Subtype.ext (by rw [pow_two]; exact mul_self_of_mem_Lbar S H.conj_mem hu)
    rw [hu2, map_one]
  have hσP : ∀ y ∈ f.range, σ * y = y * σ := by
    rintro _ ⟨x, rfl⟩
    have hcomm : (⟨u, huR⟩ : Rbar S g t) * (x : Rbar S g t) = (x : Rbar S g t) * ⟨u, huR⟩ :=
      Subtype.ext (huP _ (hKP x))
    rw [hfx, hσdef]
    calc resV H.conj_mem t ⟨u, huR⟩ * resV H.conj_mem t (x : Rbar S g t)
        = resV H.conj_mem t (⟨u, huR⟩ * (x : Rbar S g t)) := (map_mul _ _ _).symm
      _ = resV H.conj_mem t ((x : Rbar S g t) * ⟨u, huR⟩) := congrArg _ hcomm
      _ = resV H.conj_mem t (x : Rbar S g t) * resV H.conj_mem t ⟨u, huR⟩ := map_mul _ _ _
  have hσ1 := eq_one_of_commute_card_nine_omega hQ h4 hplusQ hP'Ω hP'9 hσΩ hσ2 hσP
  rw [hσdef] at hσ1
  have huN : u ∈ Nbar S g t := (resV_eq_one_iff H.conj_mem ⟨u, huR⟩).mp hσ1
  rw [hN] at huN
  exact eq_one_or_eq_of_mem_zpowers (mul_self_of_mem_Lbar S H.conj_mem ht) huN

end CFSG.GF2Type.Smith1979.OmegaPlus
