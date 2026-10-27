module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplit
import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.ClassicalInvolution.ModelFacts.RootLength
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

theorem le_of_perfect_of_solvable_commuting {X : Type*} [Group X] {A B L : Subgroup X}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hA : Group.IsSolvable ↥A) (hL : L ≤ A ⊔ B)
    (hperf : Group.IsPerfect ↥L) : L ≤ B := by
  have hAM : A ≤ A ⊔ B := le_sup_left
  have hconj : ∀ a ∈ A, ∀ y ∈ B, a * y * a⁻¹ = y := fun a ha y hy => by
    rw [hcomm a ha y hy, mul_inv_cancel_right]
  have hnormA : A ≤ Subgroup.normalizer (B : Set X) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hconj a ha b hb]
      exact hb
    · intro hb
      have h := hconj a⁻¹ (A.inv_mem ha) (a * b * a⁻¹) hb
      rw [inv_inv] at h
      have : b = a⁻¹ * (a * b * a⁻¹) * a := by group
      rw [this, h]
      exact hb
  have hdec : ∀ m : ↥(A ⊔ B), ∃ a ∈ A, ∃ b ∈ B, a * b = (m : X) := fun m => by
    have hm : (m : X) ∈ (↑(A ⊔ B) : Set X) := m.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hnormA] at hm
    exact hm
  have hBn : (B.subgroupOf (A ⊔ B)).Normal := by
    refine ⟨fun n hn m => ?_⟩
    obtain ⟨a, ha, b₀, hb₀, hm⟩ := hdec m
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hy : b₀ * (n : X) * b₀⁻¹ ∈ B := B.mul_mem (B.mul_mem hb₀ hn) (B.inv_mem hb₀)
    have : ((m * n * m⁻¹ : ↥(A ⊔ B)) : X) = a * (b₀ * (n : X) * b₀⁻¹) * a⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hm]
      group
    rw [this, hconj a ha _ hy]
    exact hy
  let g : ↥A →* ↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hAM)
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, hm⟩ := hdec m
    refine ⟨⟨a, ha⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion hAM ⟨a, ha⟩) = QuotientGroup.mk m
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : (((Subgroup.inclusion hAM ⟨a, ha⟩)⁻¹ * m : ↥(A ⊔ B)) : X) = b := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hm]
      simp [Subgroup.inclusion]
    rw [this]
    exact hb
  have : Group.IsSolvable (↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_surjective hg
  let f : ↥L →* ↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hL)
  have : Group.IsPerfect ↥L := hperf
  have : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have : Group.IsSolvable ↥f.range := inferInstance
  have hsub : Subsingleton ↥f.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable (G := ↥f.range) inferInstance
  intro x hx
  have h1 : f ⟨x, hx⟩ = 1 := by
    have := hsub.elim ⟨f ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩ (1 : ↥f.range)
    exact congrArg Subtype.val this
  have h2 : QuotientGroup.mk (Subgroup.inclusion hL ⟨x, hx⟩) =
      (1 : ↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B)) := h1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  exact h2

section Member

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem quasisimple_and_eq_of_isClassicalMember (hq4 : 4 ≤ p ^ f) {L A B : Subgroup G} {z : G}
    (h : IsClassicalMember p f L z) (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hLAB : L ≤ A ⊔ B) (hzB : z ∉ B) (hAC : A ≤ Subgroup.centralizer ({z} : Set G))
    (hA : CFSG.Open.IsQuasisimple ↥A ∨ Group.IsSolvable ↥A)
    (hB : CFSG.Open.IsQuasisimple ↥B ∨ Group.IsSolvable ↥B) :
    CFSG.Open.IsQuasisimple ↥A ∧ L = A := by
  have hcomm' : ∀ x ∈ B, ∀ y ∈ A, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hAq : CFSG.Open.IsQuasisimple ↥A := by
    rcases hA with hA | hA
    · exact hA
    · exfalso
      exact hzB (le_of_perfect_of_solvable_commuting hcomm hA hLAB h.perfect h.mem)
  refine ⟨hAq, ?_⟩
  rcases hB with hBq | hBs
  · exact eq_of_le_sup_of_isClassicalMember hq4 h hcomm hLAB hzB hAC hAq (Or.inr hBq)
  · have hLA : L ≤ A := by
      refine le_of_perfect_of_solvable_commuting hcomm' hBs ?_ h.perfect
      rwa [sup_comm] at hLAB
    have hzbot : z ∉ (⊥ : Subgroup G) := fun hz => h.ne_one (Subgroup.mem_bot.mp hz)
    refine eq_of_le_sup_of_isClassicalMember hq4 h (B := ⊥) (fun x hx y hy => ?_) ?_ hzbot hAC hAq
      (Or.inl rfl)
    · rw [Subgroup.mem_bot.mp hy, mul_one, one_mul]
    · rw [sup_bot_eq]
      exact hLA

end Member

section SL2

theorem eq_of_mul_sq_sub_one_eq {q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (h : q * (q ^ 2 - 1) = q' * (q' ^ 2 - 1)) : q = q' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : q * (q ^ 2 - 1) < q' * (q' ^ 2 - 1) := by
      have : q ^ 2 - 1 < q' ^ 2 - 1 := by
        have : q ^ 2 < q' ^ 2 := by nlinarith
        have : 1 ≤ q ^ 2 := by nlinarith
        omega
      calc q * (q ^ 2 - 1) ≤ q * (q' ^ 2 - 1) := Nat.mul_le_mul_left _ this.le
        _ < q' * (q' ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hlt (by omega)
    omega
  · have h1 : q' * (q' ^ 2 - 1) < q * (q ^ 2 - 1) := by
      have : q' ^ 2 - 1 < q ^ 2 - 1 := by
        have : q' ^ 2 < q ^ 2 := by nlinarith
        have : 1 ≤ q' ^ 2 := by nlinarith
        omega
      calc q' * (q' ^ 2 - 1) ≤ q' * (q ^ 2 - 1) := Nat.mul_le_mul_left _ this.le
        _ < q * (q ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hlt (by omega)
    omega

theorem card_eq_of_isClassicalMember_equiv_sl2 {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y]
    {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z) (hq : 5 ≤ p ^ f) {F : Type}
    [Field F] [Finite F] (hF4 : 4 ≤ Nat.card F) (e : SL(2, F) ≃* ↥L) : Nat.card F = p ^ f := by
  obtain ⟨e2⟩ := h.nonempty_equiv
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hqs : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (native_isQuasisimple (isQuasisimple_specialLinearGroup_two hF4))
  have : Finite ↥L := Finite.of_equiv _ e.toEquiv
  set O := classicalInvolutionOddCore ↥L with hO
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card ↥L
  have hcenter : Nat.card (Subgroup.center ↥L) ≤ 2 := by
    have h1 : Nat.card (Subgroup.center ↥L) = Nat.card (Subgroup.center SL(2, F)) :=
      (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
    rw [h1, Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2)
      (R := F)).toEquiv]
    have : NeZero (max (Fintype.card (Fin 2)) 1) := ⟨by simp⟩
    have := card_rootsOfUnity (k := max (Fintype.card (Fin 2)) 1) (R := F)
    simpa using this
  have hOle : Nat.card O ≤ 2 := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hqs O with hle | htop
    · exact (Subgroup.card_le_of_le hle).trans hcenter
    · exfalso
      have h1 : Nat.card (↥L ⧸ O) = 1 := by
        have : O.index = 1 := by rw [htop, Subgroup.index_top]
        exact this
      rw [Nat.card_congr e2.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
        GaloisField.card p f hf] at h1
      have h5 : 5 ≤ p ^ f := hq
      have h6 : 24 ≤ (p ^ f) ^ 2 - 1 := by
        have : 25 ≤ (p ^ f) ^ 2 := by nlinarith
        omega
      have : 5 * 24 ≤ p ^ f * ((p ^ f) ^ 2 - 1) := Nat.mul_le_mul h5 h6
      omega
  have hO1 : Nat.card O = 1 := by
    obtain ⟨k, hk⟩ := hOodd
    have : 0 < Nat.card O := Nat.card_pos
    omega
  have hcardL : Nat.card ↥L = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hmul := Subgroup.card_mul_index O
  rw [hO1, one_mul] at hmul
  have hidx : O.index = Nat.card (↥L ⧸ O) := rfl
  rw [hidx, Nat.card_congr e2.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    GaloisField.card p f hf, hcardL] at hmul
  exact eq_of_mul_sq_sub_one_eq (by omega) (by omega) hmul.symm

theorem isSolvable_sl_two_of_card_lt {F : Type} [Field F] [Finite F] (hF : Nat.card F < 4) :
    Group.IsSolvable SL(2, F) := by
  refine CFSG.GroupTheory.groups_order_below_sixty_solvable ?_
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  interval_cases (Nat.card F) <;> norm_num

theorem card_eq_of_isClassicalMember_equiv_sl2' {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y]
    {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z) (hq : 5 ≤ p ^ f) {F : Type}
    [Field F] [Finite F] (e : SL(2, F) ≃* ↥L) : Nat.card F = p ^ f := by
  by_cases hF4 : 4 ≤ Nat.card F
  · exact card_eq_of_isClassicalMember_equiv_sl2 h hq hF4 e
  · exfalso
    have := isSolvable_sl_two_of_card_lt (F := F) (by omega)
    have hsolv : Group.IsSolvable ↥L :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    have hperf : Group.IsPerfect ↥L := h.perfect
    have hnt : Nontrivial ↥L := ⟨⟨z, h.mem⟩, 1, fun hz => h.ne_one (congrArg Subtype.val hz)⟩
    exact Group.IsPerfect.not_isSolvable (G := ↥L) hsolv

end SL2

end CFSG.ClassicalInvolution.Upgrade
