module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R56Zstar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section E8Norm

variable {n : ℕ}

abbrev p23B {Y : Type} [Group Y] (t u e : Y) : Subgroup Y := Subgroup.closure ({u * e, u, t} : Set Y)

@[expose] def p23Gam {Y : Type} [Group Y] (B H : Subgroup Y) : Subgroup Y :=
  ⨆ A ∈ {A : Subgroup Y | A ≤ B ∧ (IsElemAbelian2 A 2 ∨ A = B)},
    H ⊓ Subgroup.normalizer (A : Set Y)

@[expose] def P23E8YGam (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      rLayer (Om R) u ≤ p23Gam (p23B t u e) (rLayer (Om R) u)

theorem normalizer_le_normalizer_alphaOf {Y : Type} [Group Y] (A : Subgroup Y) :
    Subgroup.normalizer (A : Set Y) ≤ Subgroup.normalizer (alphaOf A : Set Y) := by
  intro x hx
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  have h1 : conjSub x A = A := mem_normalizer_iff_conjSub_eq.mp hx
  have h2 := alphaOf_conjSub x A
  rw [h1] at h2
  exact h2.symm

theorem p23Gam_le_normalizer {Y : Type} [Group Y] {B α₀ A₀ : Subgroup Y}
    (h : ∀ A : Subgroup Y, A ≤ B → IsElemAbelian2 A 2 → alphaOf A = α₀) (hA₀ : A₀ ≤ B)
    (hA₀2 : IsElemAbelian2 A₀ 2) (H : Subgroup Y) :
    p23Gam B H ≤ Subgroup.normalizer (α₀ : Set Y) := by
  refine iSup₂_le fun A hA => inf_le_right.trans ?_
  obtain ⟨hAB, h2 | rfl⟩ := hA
  · rw [← h A hAB h2]
    exact normalizer_le_normalizer_alphaOf A
  · intro x hx
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    have hxB : conjSub x A = A := mem_normalizer_iff_conjSub_eq.mp hx
    have hle : conjSub x A₀ ≤ A := hxB ▸ conjSub_mono hA₀
    have h2' : IsElemAbelian2 (conjSub x A₀) 2 := by
      refine ⟨?_, fun y hy => ?_⟩
      · rw [← hA₀2.1]
        exact Subgroup.card_map_of_injective (MulAut.conj x).injective
      · have hy' := hA₀2.2 _ (mem_conjSub_iff.mp hy)
        have e1 : y * y = x * ((x⁻¹ * y * x) * (x⁻¹ * y * x)) * x⁻¹ := by group
        rw [e1, hy']; group
    have e2 := h _ hle h2'
    rwa [alphaOf_conjSub, h A₀ hA₀ hA₀2] at e2

theorem p23_cu_frattini (hT : Thm4RTwinBelow 3 n) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g) {x : Y}
    (hx : x ∈ Subgroup.centralizer ({u} : Set Y)) :
    ∃ y ∈ rLayer (Om R) u, y ∈ Subgroup.centralizer ({u} : Set Y) ∧
      u * e * (y⁻¹ * x) * (u * e)⁻¹ * (y⁻¹ * x)⁻¹ ∈
        oddCoreOf (Subgroup.centralizer ({u} : Set Y)) := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hτ₁, hτ₂, hdich⟩ := R56.u_trans_or_pair hT hc
  obtain ⟨htC, htH, hzz₁⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₁ hτ₁
  obtain ⟨htC₂, htH₂, hzz₂⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₂ hτ₂
  set C := Subgroup.centralizer ({u} : Set Y) with hCdef
  set H := coreHull (Om R) u with hH
  set tb : ↥H ⧸ classicalInvolutionOddCore ↥H := QuotientGroup.mk (⟨⟨u * e, htC⟩, htH⟩ : ↥H)
    with htb
  set gx : ↥C := ⟨x, hx⟩ with hgx
  have hA := secImg_mem_secFam hJ₁
  have hmap := TwinExitPf10.secAut_map_secFam hΩ hc2 gx hA
  have h1 := TwinPerpV3.isUniqueInvolution_map_mulEquiv
    (TwinExitPf6.secAut (Om R) u hΩ hc2 gx) hzz₁
  have key : ∃ y₀ : ↥H, TwinExitPf6.secAut (Om R) u hΩ hc2 gx tb =
      QuotientGroup.mk y₀ * tb * (QuotientGroup.mk y₀)⁻¹ := by
    rcases hdich with htr | hpair
    · obtain ⟨y, hy⟩ := htr _ hA _ hmap
      obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
      have h2' := hzz₁.conj (QuotientGroup.mk y₀ : ↥H ⧸ classicalInvolutionOddCore ↥H)
      rw [hy] at h2'
      exact ⟨y₀, h1.eq h2'⟩
    · refine ⟨1, ?_⟩
      have e1 : TwinExitPf6.secAut (Om R) u hΩ hc2 gx tb = tb := by
        rcases hpair _ hmap with h | h
        · rw [h] at h1; exact h1.eq hzz₁
        · rw [h] at h1; exact h1.eq hzz₂
      rw [e1, QuotientGroup.mk_one]; group
  obtain ⟨y₀, hy₀⟩ := key
  have h5 := TwinExitPf6.secMap_secAut hΩ hc2 gx tb
  rw [hy₀, map_mul, map_mul, map_inv] at h5
  change Balance.oddQuotMk u (y₀ : ↥C) * Balance.oddQuotMk u ⟨u * e, htC⟩ * (Balance.oddQuotMk u (y₀ : ↥C))⁻¹ =
    Balance.oddQuotMk u gx * Balance.oddQuotMk u ⟨u * e, htC⟩ * (Balance.oddQuotMk u gx)⁻¹ at h5
  set m : ↥C := (y₀ : ↥C)⁻¹ * gx with hm
  have hcomm : Balance.oddQuotMk u (⟨u * e, htC⟩ * m * (⟨u * e, htC⟩ : ↥C)⁻¹ * m⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hm, map_mul, map_inv, mul_inv_rev, inv_inv]
    calc Balance.oddQuotMk u ⟨u * e, htC⟩ * ((Balance.oddQuotMk u ↑y₀)⁻¹ * Balance.oddQuotMk u gx) *
          (Balance.oddQuotMk u ⟨u * e, htC⟩)⁻¹ * ((Balance.oddQuotMk u gx)⁻¹ * Balance.oddQuotMk u ↑y₀)
        = Balance.oddQuotMk u ⟨u * e, htC⟩ * (Balance.oddQuotMk u ↑y₀)⁻¹ *
            (Balance.oddQuotMk u gx * Balance.oddQuotMk u ⟨u * e, htC⟩ * (Balance.oddQuotMk u gx)⁻¹)⁻¹ *
            Balance.oddQuotMk u ↑y₀ := by group
      _ = 1 := by rw [← h5]; group
  have hmem := (QuotientGroup.eq_one_iff _).mp hcomm
  refine ⟨((y₀ : ↥C) : Y), TwinDisc.coreHull_map_le_rLayer hΩ hc2 ⟨(y₀ : ↥C), y₀.2, rfl⟩,
    (y₀ : ↥C).2, ?_⟩
  refine mem_oddCoreOf_iff.mpr ⟨(⟨u * e, htC⟩ * m * (⟨u * e, htC⟩ : ↥C)⁻¹ * m⁻¹ : ↥C).2, ?_⟩
  exact hmem

end E8Norm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
