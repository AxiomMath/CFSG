module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.CharacterTheory.Burnside
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Subgroup CFSG CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups commutatorElement

theorem isQuasisimple_of_isPerfect_of_isSimpleGroup {Q : Type*} [Group Q] (hp : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) : CFSG.IsQuasisimple Q := by
  refine ⟨hp, hs, ?_⟩
  by_contra h
  push Not at h
  have : IsMulCommutative (Q ⧸ Subgroup.center Q) := ⟨⟨h⟩⟩
  have : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isMulCommutative _ ‹_›

theorem isQuasisimple_sl2 {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple SL(2, K) :=
  isQuasisimple_of_isPerfect_of_isSimpleGroup (CFSG.ClassicalInvolution.sl2_isPerfect h4)
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4)

theorem isSolvable_sl2_of_card_three {K : Type} [Field K] [Finite K] (h3 : Nat.card K = 3) :
    Group.IsSolvable SL(2, K) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype SL(2, K) := Fintype.ofFinite _
  have hc := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K
  rw [h3] at hc
  refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (p := 2) (q := 3) (a := 3) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
  rw [← Nat.card_eq_fintype_card, hc]
  norm_num


section ShapeComponents

variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem mem_normalizer_of_conj {H : Subgroup Y} {g : Y} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨h1 h, fun hh => ?_⟩
  have := h2 _ hh
  simpa [mul_assoc] using this

theorem inv_eq_self_of_mul_self {t : Y} (ht : t * t = 1) : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht

theorem normal_of_gen {I I' : Subgroup Y} {t : Y} (hgen : I ⊔ I' ⊔ Subgroup.zpowers t = ⊤)
    (hcomm : ∀ a ∈ I, ∀ b ∈ I', a * b = b * a) (ht : t * t = 1)
    (htI : ∀ x ∈ I, t * x * t⁻¹ ∈ I) : I.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen]
  refine sup_le (sup_le Subgroup.le_normalizer ?_) ?_
  · intro b hb
    refine mem_normalizer_of_conj (fun x hx => ?_) (fun x hx => ?_)
    · rw [← hcomm x hx b hb]; simpa using hx
    · have : b⁻¹ * x * b = x := by
        have h := hcomm x hx b hb
        calc b⁻¹ * x * b = b⁻¹ * (x * b) := by group
          _ = b⁻¹ * (b * x) := by rw [h]
          _ = x := by group
      rw [this]; exact hx
  · rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj (fun x hx => htI x hx) (fun x hx => ?_)
    have h := htI x hx
    rw [inv_eq_self_of_mul_self ht] at h ⊢
    exact h

theorem normal_I₁ (S : Shape Y F₁ F₂) : S.I₁.Normal :=
  normal_of_gen S.gen S.comm S.t_sq (fun _ hx => S.act₁.conj_mem hx)

theorem normal_I₂ (S : Shape Y F₁ F₂) : S.I₂.Normal := by
  refine normal_of_gen (I := S.I₂) (I' := S.I₁) ?_ (fun a ha b hb => (S.comm b hb a ha).symm) S.t_sq
    (fun _ hx => S.act₂.conj_mem hx)
  rw [sup_comm S.I₂ S.I₁]; exact S.gen


theorem commutator_mem_of_sup_zpowers {J : Subgroup Y} [J.Normal] {t : Y}
    (hgen : J ⊔ Subgroup.zpowers t = ⊤) (y₁ y₂ : Y) : ⁅y₁, y₂⁆ ∈ J := by
  have key : ∀ y : Y, ∃ k : ℤ, QuotientGroup.mk' J y = (QuotientGroup.mk' J t) ^ k := by
    intro y
    have h1 : y ∈ J ⊔ Subgroup.zpowers t := by rw [hgen]; trivial
    rw [Subgroup.mem_sup_of_normal_left] at h1
    obtain ⟨j, hj, a, ha, rfl⟩ := h1
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    refine ⟨m, ?_⟩
    rw [map_mul, map_zpow]
    have : QuotientGroup.mk' J j = 1 := (QuotientGroup.eq_one_iff j).2 hj
    rw [this, one_mul]
  obtain ⟨k, hk⟩ := key y₁
  obtain ⟨l, hl⟩ := key y₂
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement, hk, hl]
  exact commutatorElement_eq_one_iff_mul_comm.2 ((Commute.zpow_zpow_self _ k l).eq)

theorem le_of_perfect_of_sup_zpowers {J B : Subgroup Y} [J.Normal] {t : Y}
    (hgen : J ⊔ Subgroup.zpowers t = ⊤) (hB : ⁅B, B⁆ = B) : B ≤ J := by
  rw [← hB]
  exact Subgroup.commutator_le.2 fun b₁ _ b₂ _ => commutator_mem_of_sup_zpowers hgen b₁ b₂


variable [Finite Y]

theorem mem_z_of_isComponent (S : Shape Y F₁ F₂)
    (h₁ : CFSG.IsQuasisimple ↥S.I₁ ∨ Group.IsSolvable ↥S.I₁)
    (h₂ : CFSG.IsQuasisimple ↥S.I₂ ∨ Group.IsSolvable ↥S.I₂)
    {B : Subgroup Y} (hB : CFSG.IsComponent B) : S.z ∈ B := by
  have hperf : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hB.1.1
  have hnt : ∃ x ∈ B, x ≠ 1 := by
    have := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥B)
    exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
  have hnab : ¬ ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    intro hab
    have h0 : ⁅B, B⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro b hb b' hb'
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hab b hb b' hb')
    rw [hperf] at h0
    obtain ⟨x, hx, hx1⟩ := hnt
    rw [h0] at hx
    exact hx1 (Subgroup.mem_bot.1 hx)
  have aux : ∀ I : Subgroup Y, I.Normal → (CFSG.IsQuasisimple ↥I ∨ Group.IsSolvable ↥I) →
      B ≤ I → I ≤ B := by
    intro I hI hq hBI
    rcases hq with hq | hs
    · have hIc : CFSG.IsComponent I := ⟨hq, hI.isSubnormal⟩
      rcases CFSG.LocalCores.component_subnormal_subgroup hIc hB.2 with h | h
      · exact h
      · exfalso
        apply hnab
        intro b hb b' hb'
        have h3 : ⁅b', b⁆ ∈ ⁅I, B⁆ := Subgroup.commutator_mem_commutator (hBI hb') hb
        rw [h, Subgroup.mem_bot] at h3
        exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
    · exfalso
      have hsB : Group.IsSolvable ↥B :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBI)
      have hp : Group.IsPerfect ↥B := hB.1.1
      have hn : Nontrivial ↥B := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
      exact Group.IsPerfect.not_isSolvable ↥B hsB
  have := normal_I₁ S
  have := normal_I₂ S
  rcases CFSG.LocalCores.component_normal_subgroup hB (normal_I₁ S) with h1 | h1
  · exact aux _ (normal_I₁ S) h₁ h1 S.z_mem₁
  rcases CFSG.LocalCores.component_normal_subgroup hB (normal_I₂ S) with h2 | h2
  · exact aux _ (normal_I₂ S) h₂ h2 S.z_mem₂
  exfalso
  have hBJ : B ≤ S.I₁ ⊔ S.I₂ := by
    have hJ : (S.I₁ ⊔ S.I₂).Normal := inferInstance
    refine le_of_perfect_of_sup_zpowers (J := S.I₁ ⊔ S.I₂) (t := S.t) ?_ hperf
    exact S.gen
  apply hnab
  intro b hb b' hb'
  have hB1 : B ≤ Subgroup.centralizer (S.I₁ : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hB2 : B ≤ Subgroup.centralizer (S.I₂ : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
  have hc : S.I₁ ⊔ S.I₂ ≤ Subgroup.centralizer ({b} : Set Y) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 (hB1 hb) a ha
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 (hB2 hb) a ha
  have := Subgroup.mem_centralizer_singleton_iff.1 (hc (hBJ hb'))
  exact this.symm

theorem isQuasisimple_or_isSolvable_of_equiv_sl2 {K : Type} [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    {G : Type*} [Group G] (e : G ≃* SL(2, K)) : CFSG.IsQuasisimple G ∨ Group.IsSolvable G := by
  rcases Nat.lt_or_ge (Nat.card K) 4 with hlt | h4
  · right
    have h : Nat.card K = 3 := by omega
    have := isSolvable_sl2_of_card_three h
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · left
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl2 h4)

theorem mem_z_of_isComponent_of_card (S : Shape Y F₁ F₂) [Finite F₁] [Finite F₂]
    (h₁ : 3 ≤ Nat.card F₁) (h₂ : 3 ≤ Nat.card F₂) {B : Subgroup Y} (hB : CFSG.IsComponent B) :
    S.z ∈ B :=
  mem_z_of_isComponent S (isQuasisimple_or_isSolvable_of_equiv_sl2 h₁ S.e₁)
    (isQuasisimple_or_isSolvable_of_equiv_sl2 h₂ S.e₂) hB

end ShapeComponents

end CFSG.GH74.GLS.IVK.GHInv
