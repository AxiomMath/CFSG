module

public import CFSG.GH74.Generic.S1.KL5Lift
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape

public section

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
  CFSG.GH74.GLS.IVK.GHInv CFSG.ClassicalInvolution
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

theorem kl5_mem_center_of_mul_self_eq_one_of_equiv_sl2 {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {P : Type} [Group P] (e : P ≃* SL(2, F)) {u : P} (hu : u * u = 1) :
    u ∈ Subgroup.center P := by
  by_cases hu1 : u = 1
  · rw [hu1]; exact Subgroup.one_mem _
  · have h2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu) hu1
    rw [mem_center_iff_of_equiv_sl2 e u]
    have : u = e.symm (-1) := (orderOf_eq_two_iff_of_equiv_sl2 hodd e u).1 h2
    rw [this, MulEquiv.apply_symm_apply]
    exact (mem_center_sl2_iff _).2 (Or.inr rfl)

theorem kl5_commute_of_mul_self_eq_one_shape {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Finite F₁] [Finite F₂] (hF₁ : Odd (Nat.card F₁)) (hF₂ : Odd (Nat.card F₂))
    (S : Shape Y F₁ F₂) {h : ↥S.I₁ × ↥S.I₂} (hh : h * h = 1) (g : ↥S.I₁ × ↥S.I₂) :
    h * g = g * h := by
  obtain ⟨u, v⟩ := h
  obtain ⟨c, d⟩ := g
  have hu : u * u = 1 := (Prod.mk.inj hh).1
  have hv : v * v = 1 := (Prod.mk.inj hh).2
  have h1 := Subgroup.mem_center_iff.1 (kl5_mem_center_of_mul_self_eq_one_of_equiv_sl2 hF₁ S.e₁ hu) c
  have h2 := Subgroup.mem_center_iff.1 (kl5_mem_center_of_mul_self_eq_one_of_equiv_sl2 hF₂ S.e₂ hv) d
  exact Prod.ext h1.symm h2.symm

theorem kl5_false_of_shape (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {Y : Type} [Group Y] [Finite Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (hF₁ : Odd (Nat.card F₁)) (hF₂ : Odd (Nat.card F₂)) (S : Shape Y F₁ F₂) {Q : Type} [Group Q]
    (α : Q →* Y) (hα : Function.Injective α) (hQ : CFSG.IsQuasisimple Q) {p f : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 3 p f ∨
      StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 3 p f) : False := by
  classical
  have hQperf : Group.IsPerfect Q := hQ.1
  have hAperf : ⁅α.range, α.range⁆ = α.range :=
    Subgroup.isPerfect_iff.1 (Group.IsPerfect.ofSurjective α.rangeRestrict_surjective)
  have hn₁ := normal_I₁ S
  have hn₂ := normal_I₂ S
  have hle : α.range ≤ S.I₁ ⊔ S.I₂ :=
    le_of_perfect_of_sup_zpowers (J := S.I₁ ⊔ S.I₂) (t := S.t) S.gen hAperf
  have hcomm : ∀ (m : ↥S.I₁) (n : ↥S.I₂), Commute (S.I₁.subtype m) (S.I₂.subtype n) :=
    fun m n => S.comm m m.2 n n.2
  let π₀ : (↥S.I₁ × ↥S.I₂) →* Y := (S.I₁.subtype).noncommCoprod (S.I₂.subtype) hcomm
  have hπ₀ : ∀ x : ↥S.I₁ × ↥S.I₂, π₀ x = (x.1 : Y) * (x.2 : Y) := fun x => by
    simp [π₀, MonoidHom.noncommCoprod_apply]
  have hmem : ∀ x : ↥S.I₁ × ↥S.I₂, π₀ x ∈ S.I₁ ⊔ S.I₂ := fun x => by
    rw [hπ₀]
    exact Subgroup.mul_mem_sup x.1.2 x.2.2
  let π : (↥S.I₁ × ↥S.I₂) →* ↥(S.I₁ ⊔ S.I₂) := π₀.codRestrict _ hmem
  have hπs : Function.Surjective π := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute S.comm hy
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (by simp [π, hπ₀])⟩
  have hzI₁ : ∀ x ∈ S.I₁, ∀ c ∈ Subgroup.zpowers S.z, x * c = c * x := by
    intro x hx c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact ((show Commute x S.z from S.comm x hx S.z S.z_mem₂).zpow_right k).eq
  have hzI₂ : ∀ y ∈ S.I₂, ∀ c ∈ Subgroup.zpowers S.z, y * c = c * y := by
    intro y hy c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact ((show Commute y S.z from (S.comm S.z S.z_mem₁ y hy).symm).zpow_right k).eq
  have hker : π.ker ≤ Subgroup.center (↥S.I₁ × ↥S.I₂) := by
    rintro ⟨a, b⟩ hab
    have h1 : (a : Y) * (b : Y) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hab)
      simpa [π, hπ₀] using this
    have hbinv : (b : Y) = (a : Y)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have haI₂ : (a : Y) ∈ S.I₂ := by
      have : (a : Y) = (b : Y)⁻¹ := by rw [hbinv, inv_inv]
      rw [this]; exact S.I₂.inv_mem b.2
    have haz : (a : Y) ∈ Subgroup.zpowers S.z := by
      rw [← S.inter]; exact ⟨a.2, haI₂⟩
    have hbz : (b : Y) ∈ Subgroup.zpowers S.z := by
      rw [hbinv]; exact (Subgroup.zpowers S.z).inv_mem haz
    rw [Subgroup.mem_center_iff]
    rintro ⟨c, d⟩
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact hzI₁ c c.2 a haz
    · exact hzI₂ d d.2 b hbz
  have hαJ : ∀ q : Q, α q ∈ S.I₁ ⊔ S.I₂ := fun q => hle ⟨q, rfl⟩
  let α' : Q →* ↥(S.I₁ ⊔ S.I₂) := α.codRestrict _ hαJ
  have hα' : Function.Injective α' := fun x y h => hα (congrArg Subtype.val h)
  obtain ⟨Ã, -, -, h₁, -, h₂, -, h11, h22, -, -, ⟨a₁, -, ha₁⟩, -, -⟩ :=
    kl5_liftA hGA π hπs hker α' hα' hQ hp2 hmodel
  exact ha₁ (kl5_commute_of_mul_self_eq_one_shape hF₁ hF₂ S h11 a₁)

section Exceptional

theorem kl5_false_G2 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {S : Type} [Group S] [Finite S] {p' f' : ℕ} (hp' : p'.Prime) (hp2' : p' ≠ 2)
    (hM : LieModel S .G2 0 p' f') {A : Subgroup S} {b : S} (hb2 : orderOf b = 2)
    (hAb : ∀ a ∈ A, a * b = b * a) (hAq : CFSG.IsQuasisimple ↥A) {p f : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel (↥A ⧸ Subgroup.center ↥A) .PSL 3 p f ∨
      StatedClassicalModel (↥A ⧸ Subgroup.center ↥A) .PSU 3 p f) : False := by
  obtain ⟨F, hF, hFin, Sh, hcard, -⟩ := exists_shape_G2 hp' hp2' hM b hb2
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact (hp'.odd_of_ne_two hp2').pow
  have hle : A ≤ Subgroup.centralizer ({b} : Set S) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (hAb a ha)
  exact kl5_false_of_shape hGA hodd hodd Sh (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle) hAq hp2 hmodel

theorem kl5_false_D4 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {S : Type} [Group S] [Finite S] {p' f' : ℕ} (hp' : p'.Prime) (hp2' : p' ≠ 2)
    (hM : LieModel S .trialityD4 0 p' f') {A : Subgroup S} {b : S} (hb2 : orderOf b = 2)
    (hAb : ∀ a ∈ A, a * b = b * a) (hAq : CFSG.IsQuasisimple ↥A) {p f : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel (↥A ⧸ Subgroup.center ↥A) .PSL 3 p f ∨
      StatedClassicalModel (↥A ⧸ Subgroup.center ↥A) .PSU 3 p f) : False := by
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, Sh, hc₁, hc₂, -⟩ := exists_shape_D4 hp' hp2' hM b hb2
  have hodd : Odd (p' ^ f') := (hp'.odd_of_ne_two hp2').pow
  have hodd₂ : Odd (Nat.card F₂) := by rw [hc₂]; exact hodd
  have hodd₁ : Odd (Nat.card F₁) := by rw [hc₁]; exact hodd.pow
  have hle : A ≤ Subgroup.centralizer ({b} : Set S) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (hAb a ha)
  exact kl5_false_of_shape hGA hodd₁ hodd₂ Sh (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle) hAq hp2 hmodel

end Exceptional

end CFSG.GH74.Generic.S1
