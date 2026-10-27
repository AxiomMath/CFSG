module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Thm6

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem index_dvd_six_of_hom {Y O : Type} [Group Y] [Finite Y] [Group O] [Finite O]
    {N : Subgroup Y} (Ω : Y →* O) (hker : Ω.ker = N) (Dbar : Subgroup O) (hD3 : Nat.card Dbar ∣ 3)
    (hcomm : ∀ a b : O, a * b * a⁻¹ * b⁻¹ ∈ Dbar) {S₀ : Subgroup Y}
    (hgen : ∀ M : Subgroup Y, (∀ y : Y, conjSub y S₀ ≤ M) → M = ⊤)
    (hS : ∀ s₁ ∈ S₀, ∀ s₂ ∈ S₀, Ω s₁ ∉ Dbar → Ω s₂ ∉ Dbar → Ω (s₁⁻¹ * s₂) ∈ Dbar)
    (hS2 : ∀ s ∈ S₀, Ω (s ^ 2) ∈ Dbar) : N.index ∣ 6 := by
  have : Dbar.Normal := ⟨fun d hd g => by simpa using Dbar.mul_mem (hcomm g d) hd⟩
  have hQc : ∀ x y : O ⧸ Dbar, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h := hcomm b⁻¹ a⁻¹
    rwa [inv_inv, inv_inv, ← mul_inv_rev, mul_assoc] at h
  set ψ : Y →* O ⧸ Dbar := (QuotientGroup.mk' Dbar).comp Ω with hψ
  have hψ1 : ∀ y, ψ y = 1 ↔ Ω y ∈ Dbar := fun y => by
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set Y₁ : Subgroup Y := Dbar.comap Ω with hY₁
  have hkerψ : ψ.ker = Y₁ := by
    ext y
    rw [MonoidHom.mem_ker, hψ1]
    rfl
  have hNY : N ≤ Y₁ := fun n hn => by
    show Ω n ∈ Dbar
    rw [← hker, MonoidHom.mem_ker] at hn
    rw [hn]
    exact Dbar.one_mem
  have hrange : ψ.range ≤ S₀.map ψ := by
    have hH : (S₀.map ψ).comap ψ = ⊤ := hgen _ fun y x hx => by
      rw [mem_conjSub_iff] at hx
      show ψ x ∈ S₀.map ψ
      have h1 : ψ x = ψ (y⁻¹ * x * y) := by
        rw [map_mul, map_mul, map_inv, hQc (ψ y)⁻¹ (ψ x), mul_assoc, inv_mul_cancel, mul_one]
      rw [h1]
      exact Subgroup.mem_map_of_mem ψ hx
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ (S₀.map ψ).comap ψ := hH ▸ Subgroup.mem_top y
    exact hy
  have hmap : Nat.card (S₀.map ψ) ≤ 2 := by
    by_cases hall : ∀ s ∈ S₀, Ω s ∈ Dbar
    · have hbot : S₀.map ψ = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨s, hs, rfl⟩
        exact Subgroup.mem_bot.mpr ((hψ1 s).mpr (hall s hs))
      rw [hbot, Subgroup.card_bot]
      norm_num
    obtain ⟨u, huS, hu⟩ : ∃ u ∈ S₀, Ω u ∉ Dbar := by
      by_contra h
      exact hall fun s hs => by_contra fun hn => h ⟨s, hs, hn⟩
    have hle : S₀.map ψ ≤ Subgroup.zpowers (ψ u) := by
      rintro _ ⟨s, hs, rfl⟩
      by_cases hsD : Ω s ∈ Dbar
      · rw [(hψ1 s).mpr hsD]
        exact Subgroup.one_mem _
      have h1 := (hψ1 _).mpr (hS u huS s hs hu hsD)
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      rw [← h1]
      exact Subgroup.mem_zpowers _
    have hu2 : ψ u ^ 2 = 1 := by
      rw [← map_pow]
      exact (hψ1 _).mpr (hS2 u huS)
    calc Nat.card (S₀.map ψ) ≤ Nat.card (Subgroup.zpowers (ψ u)) := Subgroup.card_le_of_le hle
      _ = orderOf (ψ u) := Nat.card_zpowers _
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hu2
  have hidx1 : Y₁.index ∣ 2 := by
    have h := (Subgroup.card_le_of_le hrange).trans hmap
    rw [← Subgroup.index_ker, hkerψ] at h
    have h0 : Y₁.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (by omega : Y₁.index = 1 ∨ Y₁.index = 2) with h1 | h1 <;> simp [h1]
  have hrel : N.relIndex Y₁ ∣ 3 := by
    have hker' : (Ω.comp Y₁.subtype).ker = N.subgroupOf Y₁ := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
      rfl
    have hle : (Ω.comp Y₁.subtype).range ≤ Dbar := by
      rintro _ ⟨y, rfl⟩
      exact y.2
    rw [Subgroup.relIndex, ← hker', Subgroup.index_ker]
    exact (Subgroup.card_dvd_of_le hle).trans hD3
  rw [← Subgroup.relIndex_mul_index hNY]
  exact Nat.mul_dvd_mul hrel hidx1

@[expose] noncomputable def transConj {Y P : Type} [Group Y] [Group P] (N : Subgroup Y) [N.Normal]
    (θ : N ≃* P) : Y →* MulAut P :=
  (MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal

theorem transConj_apply {Y P : Type} [Group Y] [Group P] (N : Subgroup Y) [N.Normal] (θ : N ≃* P)
    (y : Y) (p : P) : transConj N θ y p = θ (MulAut.conjNormal y (θ.symm p)) := rfl

theorem transConj_mem_inner_iff {Y P : Type} [Group Y] [Group P] {N : Subgroup Y} [N.Normal]
    (θ : N ≃* P) (hC : Subgroup.centralizer (N : Set Y) = ⊥) (y : Y) :
    transConj N θ y ∈ inner P ↔ y ∈ N := by
  constructor
  · rintro ⟨m, hm⟩
    have key : ∀ x : N, (θ.symm m : N) * x * (θ.symm m)⁻¹ = MulAut.conjNormal y x := by
      intro x
      apply θ.injective
      have h1 := DFunLike.congr_fun hm (θ x)
      rw [transConj_apply, MulEquiv.symm_apply_apply] at h1
      rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]
    have hcen : ((θ.symm m : N) : Y)⁻¹ * y ∈ Subgroup.centralizer (N : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h2 := congrArg Subtype.val (key ⟨x, hx⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] at h2
      calc x * (((θ.symm m : N) : Y)⁻¹ * y) =
          ((θ.symm m : N) : Y)⁻¹ * (((θ.symm m : N) : Y) * x * ((θ.symm m : N) : Y)⁻¹) * y := by
            group
        _ = ((θ.symm m : N) : Y)⁻¹ * (y * x * y⁻¹) * y := by rw [h2]
        _ = ((θ.symm m : N) : Y)⁻¹ * y * x := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcen
    rw [← hcen]
    exact (θ.symm m).2
  · intro hy
    refine ⟨θ ⟨y, hy⟩, ?_⟩
    ext p
    have h : MulAut.conjNormal y (θ.symm p) = ⟨y, hy⟩ * θ.symm p * (⟨y, hy⟩ : N)⁻¹ :=
      Subtype.ext (by simp [MulAut.conjNormal_apply])
    rw [MulAut.conj_apply, transConj_apply, h, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]

end CFSG.ClassicalInvolution.Q3.TL4.Thm6
