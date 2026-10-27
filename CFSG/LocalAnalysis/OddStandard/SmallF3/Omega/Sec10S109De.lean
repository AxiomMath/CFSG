module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZStar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Dd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec10D_zStar_abs {X : Type} [Group X] [Finite X] {c τ : X} (hc1 : c ≠ 1)
    (hc2 : c * c = 1) (hcc : ∀ x : X, x * c = c * x) (hτ2 : τ * τ = 1) (hτ1 : τ ∉ zpowers c)
    (hiso : ∀ x : X, (x * τ * x⁻¹) * τ * (x * τ * x⁻¹)⁻¹ * τ⁻¹ ∈ zpowers c →
      x * τ * x⁻¹ = τ ∨ x * τ * x⁻¹ = τ * c) :
    ∀ x : X, ∃ y ∈ CFSG.oddCore X, ∃ k : X,
      (k * τ * k⁻¹ = τ ∨ k * τ * k⁻¹ = τ * c) ∧ x = y * k := by
  have hzp : ∀ w ∈ zpowers c, w = 1 ∨ w = c := by
    intro w hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' i
    · left
      rw [hk, zpow_mul, zpow_two, hc2, one_zpow]
    · right
      rw [hk, zpow_add, zpow_mul, zpow_two, hc2, one_zpow, one_mul, zpow_one]
  have hcen2 : ∀ w ∈ zpowers c, ∀ a : X, a * w = w * a := by
    intro w hw a
    rcases hzp w hw with rfl | rfl
    · simp
    · exact hcc a
  have hcen : ∀ w ∈ zpowers c, ∀ a : X, w * a * w⁻¹ = a := by
    intro w hw a
    rw [← hcen2 w hw a]
    group
  haveI hnorm : (zpowers c).Normal := ⟨fun n hn g => by
    rw [hcen2 n hn g, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  have hτh1 : (τ : X ⧸ zpowers c) ≠ 1 := fun h => hτ1 ((QuotientGroup.eq_one_iff τ).mp h)
  have hτh2 : (τ : X ⧸ zpowers c) * (τ : X ⧸ zpowers c) = 1 := by
    rw [← QuotientGroup.mk_mul, hτ2]
    rfl
  have hcQ : ((c : X) : X ⧸ zpowers c) = 1 :=
    (QuotientGroup.eq_one_iff c).mpr (Subgroup.mem_zpowers c)
  have hisoQ : ∀ ĥ ∈ (⊤ : Subgroup (X ⧸ zpowers c)),
      (ĥ * (τ : X ⧸ zpowers c) * ĥ⁻¹) * (τ : X ⧸ zpowers c) =
        (τ : X ⧸ zpowers c) * (ĥ * (τ : X ⧸ zpowers c) * ĥ⁻¹) →
      ĥ * (τ : X ⧸ zpowers c) * ĥ⁻¹ = (τ : X ⧸ zpowers c) := by
    intro ĥ _ hcomm
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective ĥ
    have h1 : (((x * τ * x⁻¹) * τ : X) : X ⧸ zpowers c) =
        ((τ * (x * τ * x⁻¹) : X) : X ⧸ zpowers c) := by
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hcomm
    have h2 : (x * τ * x⁻¹) * τ * (x * τ * x⁻¹)⁻¹ * τ⁻¹ ∈ zpowers c := by
      have h := QuotientGroup.eq_iff_div_mem.mp h1
      have e : (x * τ * x⁻¹) * τ / (τ * (x * τ * x⁻¹)) =
          (x * τ * x⁻¹) * τ * (x * τ * x⁻¹)⁻¹ * τ⁻¹ := by
        rw [div_eq_mul_inv]
        group
      rwa [e] at h
    rcases hiso x h2 with h | h
    · have h3 : ((x * τ * x⁻¹ : X) : X ⧸ zpowers c) = (τ : X ⧸ zpowers c) := by rw [h]
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h3
    · have h3 : ((x * τ * x⁻¹ : X) : X ⧸ zpowers c) = ((τ * c : X) : X ⧸ zpowers c) := by rw [h]
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcQ, mul_one] using h3
  have hZ := sec10_zStar (G := X ⧸ zpowers c) (H := (⊤ : Subgroup (X ⧸ zpowers c)))
    (t := (τ : X ⧸ zpowers c)) (Subgroup.mem_top _) hτh1 hτh2 hisoQ
  have hdec := sec10_zStar_decomp (G := X ⧸ zpowers c) (H := (⊤ : Subgroup (X ⧸ zpowers c)))
    (t := (τ : X ⧸ zpowers c)) (Subgroup.mem_top _) hτh2 hZ
  haveI hNn : (oddCoreIn (⊤ : Subgroup (X ⧸ zpowers c))).Normal :=
    ⟨fun n hn g => CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (X := ⊤)
      (Subgroup.mem_top g) hn⟩
  have hNodd : Odd (Nat.card (oddCoreIn (⊤ : Subgroup (X ⧸ zpowers c)))) :=
    CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn ⊤
  obtain ⟨Y, hYn, hYodd, hlift⟩ := sec10D_odd_lift hc1 hc2 hcc hNodd
  have hYO : Y ≤ CFSG.oddCore X :=
    le_sSup (s := {N : Subgroup X | N.Normal ∧ Odd (Nat.card N)}) ⟨hYn, hYodd⟩
  have hconj : ∀ w' ∈ zpowers c, ∀ w ∈ zpowers c, ∀ k : X,
      (w' * k * w) * τ * (w' * k * w)⁻¹ = k * τ * k⁻¹ := by
    intro w' hw' w hw k
    have h1 : w * τ * w⁻¹ = τ := hcen w hw τ
    have h2 : w' * (k * τ * k⁻¹) * w'⁻¹ = k * τ * k⁻¹ := hcen w' hw' _
    calc (w' * k * w) * τ * (w' * k * w)⁻¹ = w' * (k * (w * τ * w⁻¹) * k⁻¹) * w'⁻¹ := by group
      _ = w' * (k * τ * k⁻¹) * w'⁻¹ := by rw [h1]
      _ = k * τ * k⁻¹ := h2
  intro x
  obtain ⟨o, ho, κ, hκ, hxo⟩ := hdec (x : X ⧸ zpowers c) (Subgroup.mem_top _)
  obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective o
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective κ
  obtain ⟨y, hy, hx₁⟩ := hlift x₁ ho
  have hkτ : k * τ * k⁻¹ = τ ∨ k * τ * k⁻¹ = τ * c := by
    have hc : (k : X ⧸ zpowers c) * (τ : X ⧸ zpowers c) = (τ : X ⧸ zpowers c) * k :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hκ).2
    have h1 : (τ : X ⧸ zpowers c) = ((k * τ * k⁻¹ : X) : X ⧸ zpowers c) := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hc]
      group
    have h2 : τ⁻¹ * (k * τ * k⁻¹) ∈ zpowers c := QuotientGroup.eq.mp h1
    rcases hzp _ h2 with h | h
    · left
      calc k * τ * k⁻¹ = τ * (τ⁻¹ * (k * τ * k⁻¹)) := by group
        _ = τ := by rw [h, mul_one]
    · right
      calc k * τ * k⁻¹ = τ * (τ⁻¹ * (k * τ * k⁻¹)) := by group
        _ = τ * c := by rw [h]
  have hw : (x₁ * k)⁻¹ * x ∈ zpowers c := by
    have h : (((x₁ * k : X)) : X ⧸ zpowers c) = (x : X ⧸ zpowers c) := by
      rw [QuotientGroup.mk_mul]
      exact hxo.symm
    exact QuotientGroup.eq.mp h
  have hxw : x = x₁ * k * ((x₁ * k)⁻¹ * x) := by group
  rcases hx₁ with hx₁ | hx₁
  · refine ⟨y, hYO hy, 1 * k * ((x₁ * k)⁻¹ * x), ?_, ?_⟩
    · rw [hconj 1 (Subgroup.one_mem _) _ hw k]
      exact hkτ
    · rw [← hx₁]
      calc x = x₁ * k * ((x₁ * k)⁻¹ * x) := hxw
        _ = x₁ * (1 * k * ((x₁ * k)⁻¹ * x)) := by group
  · refine ⟨y, hYO hy, c * k * ((x₁ * k)⁻¹ * x), ?_, ?_⟩
    · rw [hconj c (Subgroup.mem_zpowers c) _ hw k]
      exact hkτ
    · calc x = x₁ * k * ((x₁ * k)⁻¹ * x) := hxw
        _ = c * y * k * ((x₁ * k)⁻¹ * x) := by rw [hx₁]
        _ = y * c * k * ((x₁ * k)⁻¹ * x) := by rw [hcc y]
        _ = y * (c * k * ((x₁ * k)⁻¹ * x)) := by group

end CFSG.OddStandard.SmallF3.Omega
