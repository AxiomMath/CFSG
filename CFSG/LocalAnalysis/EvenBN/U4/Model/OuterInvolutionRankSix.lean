module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolutionRankFive
public import CFSG.LocalAnalysis.EvenBN.U4.RootE

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement

theorem sup_le_range_diagonalHom_sup_zpowers {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {t : G} (hperf : ⁅A, A⁆ = A)
    (hn : ∀ M : Subgroup G, M ≤ A → A ≤ normalizer (M : Set G) →
      M ≤ centralizer (A : Set G) ∨ M = A)
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) {z : G} (hz : z ∈ A)
    (hzc : z ∉ centralizer (A : Set G)) :
    A ⊔ A.map (MulAut.conj t⁻¹).toMonoidHom ≤
      (Common.diagonalHom A t hcomm).range ⊔ zpowers z := by
  set δ := Common.diagonalHom A t hcomm with hδdef
  set H : Subgroup G := δ.range ⊔ zpowers z with hH
  have hδH : ∀ a : A, δ a ∈ H := fun a => mem_sup_left ⟨a, rfl⟩
  have hzH : z ∈ H := mem_sup_right (mem_zpowers z)
  have hconj : ∀ a : A, ∀ b ∈ A, δ a * b * (δ a)⁻¹ = a * b * (a : G)⁻¹ := by
    intro a b hb
    have h1 := Common.commute_conj_of_commutator_eq_bot hcomm a.2 hb
    rw [Common.diagonalHom_apply]
    calc (a : G) * (t⁻¹ * a * t) * b * ((a : G) * (t⁻¹ * a * t))⁻¹ =
        a * ((t⁻¹ * a * t) * b) * (t⁻¹ * a * t)⁻¹ * (a : G)⁻¹ := by group
      _ = a * (b * (t⁻¹ * a * t)) * (t⁻¹ * a * t)⁻¹ * (a : G)⁻¹ := by rw [← h1]
      _ = a * b * (a : G)⁻¹ := by group
  set N : Subgroup G := H ⊓ A with hN
  have hAN : A ≤ normalizer (N : Set G) := by
    intro a ha
    refine mem_normalizer_fintype fun n hn => ?_
    have hn' := mem_inf.1 hn
    refine mem_inf.2 ⟨?_, mul_mem (mul_mem ha hn'.2) (inv_mem ha)⟩
    rw [← hconj ⟨a, ha⟩ n hn'.2]
    exact mul_mem (mul_mem (hδH ⟨a, ha⟩) hn'.1) (inv_mem (hδH ⟨a, ha⟩))
  rcases hn N inf_le_right hAN with hc | he
  ·
    exfalso
    apply hzc
    have h1 : quotientCenterConjHom A ⟨z, le_normalizer hz⟩ = 1 := by
      refine MulEquiv.ext fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H a =>
        rw [quotientCenterConjHom_mk, MulAut.one_apply, QuotientGroup.eq]
        have hmem : z * a * z⁻¹ * (a : G)⁻¹ ∈ N := by
          refine mem_inf.2 ⟨?_, mul_mem (mul_mem (mul_mem hz a.2) (inv_mem hz)) (inv_mem a.2)⟩
          have e : z * a * z⁻¹ * (a : G)⁻¹ = z * (δ a * z⁻¹ * (δ a)⁻¹) := by
            rw [hconj a z⁻¹ (inv_mem hz)]
            group
          rw [e]
          exact mul_mem hzH (mul_mem (mul_mem (hδH a) (inv_mem hzH)) (inv_mem (hδH a)))
        have hcz := hc hmem
        have hci : (z * a * z⁻¹ * (a : G)⁻¹)⁻¹ ∈ centralizer (A : Set G) := inv_mem hcz
        have hca : (a : G) * (z * a * z⁻¹ * (a : G)⁻¹)⁻¹ = (z * a * z⁻¹ * (a : G)⁻¹)⁻¹ * a :=
          mem_centralizer_iff.1 hci a a.2
        have hw : (z * a * z⁻¹)⁻¹ * (a : G) = (z * a * z⁻¹ * (a : G)⁻¹)⁻¹ := by
          calc (z * a * z⁻¹)⁻¹ * (a : G) =
              (a : G)⁻¹ * ((z * a * z⁻¹ * (a : G)⁻¹)⁻¹ * a) := by group
            _ = (a : G)⁻¹ * ((a : G) * (z * a * z⁻¹ * (a : G)⁻¹)⁻¹) := by rw [hca]
            _ = (z * a * z⁻¹ * (a : G)⁻¹)⁻¹ := by group
        rw [mem_center_iff]
        intro b
        apply Subtype.ext
        change (b : G) * ((z * a * z⁻¹)⁻¹ * a) = ((z * a * z⁻¹)⁻¹ * a) * b
        rw [hw]
        exact mem_centralizer_iff.1 hci b b.2
    exact mem_centralizer_of_quotientCenterConjHom_eq_one hperf h1
  ·
    have hAH : A ≤ H := fun a ha => (mem_inf.1 (he.symm ▸ ha : a ∈ N)).1
    refine sup_le hAH ?_
    rintro _ ⟨a, ha, rfl⟩
    have e : (MulAut.conj t⁻¹).toMonoidHom a = (a : G)⁻¹ * δ ⟨a, ha⟩ := by
      rw [Common.diagonalHom_apply]
      simp
    rw [e]
    exact mul_mem (inv_mem (hAH ha)) (hδH _)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem normalizer_Q_le_normalizer_L_sup_E (hS : Setting h L η t Q T) :
    normalizer (Q : Set G) ≤
      normalizer ((L ⊔ miyamotoEG h L η Q : Subgroup G) : Set G) := by
  obtain ⟨-, -, -, hNQ, -⟩ := hS.sec3_2
  have hB₂ : miyamotoB2 h L η t ≤
      normalizer ((L ⊔ miyamotoEG h L η Q : Subgroup G) : Set G) := fun b hb =>
    Common.mem_normalizer_sup (hS.centralizer_le_normalizer (hS.B2_le_C hb))
      (hS.H_le_normalizer_E (hS.M_le_H (hS.B2_le_M hb)))
  have hM : miyamotoM0 Q ≤ normalizer ((L ⊔ miyamotoEG h L η Q : Subgroup G) : Set G) := by
    rw [← hS.E_sup_B2]
    exact sup_le (le_sup_right.trans le_normalizer) hB₂
  intro g hg
  obtain ⟨c, hc, d, hd, rfl⟩ := hNQ g hg
  refine mul_mem (Common.mem_normalizer_sup (hS.centralizer_le_normalizer (mem_inf.1 hc).2)
    (hS.H_le_normalizer_E (normalizer_le_normalizer_centerIn Q (mem_inf.1 hc).1))) (hM hd)

theorem sup_eq_L_sup_E (hS : Setting h L η t Q T) {A : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hδ : (Common.diagonalHom A t hcomm).range = L)
    (hE : miyamotoEG h L η Q ≤ A ⊔ A.map (MulAut.conj t⁻¹).toMonoidHom) {z : G} (hzA : z ∈ A)
    (hzc : z ∉ centralizer (A : Set G)) (hzE : z ∈ miyamotoEG h L η Q) :
    A ⊔ A.map (MulAut.conj t⁻¹).toMonoidHom = L ⊔ miyamotoEG h L η Q := by
  obtain ⟨-, -, hn⟩ := SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple
    (hS.isQuasisimple_of_diagonal hA hcomm hδ)
  refine le_antisymm ((sup_le_range_diagonalHom_sup_zpowers hA hn hcomm hzA hzc).trans ?_)
    (sup_le ?_ hE)
  · rw [hδ]
    exact sup_le_sup_left ((zpowers_le).2 hzE) _
  · rw [← hδ]
    rintro _ ⟨a, rfl⟩
    rw [Common.diagonalHom_apply]
    exact mul_mem (mem_sup_left a.2) (mem_sup_right (Common.conj_mem_map_conj_inv t a.2))

theorem exists_mul_ne_L (hS : Setting h L η t Q T) : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hle : L ≤ centralizer (L : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => hcon y hy x hx
  have hbot : L = ⊥ := by
    rw [← hS.commutator_L, commutator_eq_bot_iff_le_centralizer.2 hle]
  have hP : Nat.card (miyamotoPG h L η) ≤ Nat.card L := card_le_of_le (miyamotoPull_le h L η _)
  rw [card_miyamotoPG] at hP
  have hL1 : Nat.card L = 1 := by
    rw [Subgroup.card_eq_one]
    exact hbot
  have h4 : 4 ^ 6 ≤ (2 ^ f) ^ 6 := Nat.pow_le_pow_left hS.four_le 6
  norm_num at h4
  omega

theorem odd_card_ker_diagonalHom (hS : Setting h L η t Q T) {A : Subgroup G}
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hδ : (Common.diagonalHom A t hcomm).range = L) :
    Odd (Nat.card (Common.diagonalHom A t hcomm).ker) := by
  refine Common.odd_card_ker_diagonalHom_of_centralizer_le hcomm hS.t_mul_t ?_ ?_
  · rw [hδ]
    exact hS.kernel_eq_zpowers'.le
  · rw [hδ]
    exact hS.exists_mul_ne_L

theorem false_of_diagonal_swap_of_E (hS : Setting h L η t Q T) {A : Subgroup G}
    (hA : ⁅A, A⁆ = A) (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hδ : (Common.diagonalHom A t hcomm).range = L)
    (hE : miyamotoEG h L η Q ≤ A ⊔ A.map (MulAut.conj t⁻¹).toMonoidHom) {z : G} (hzA : z ∈ A)
    (hzc : z ∉ centralizer (A : Set G)) (hzE : z ∈ miyamotoEG h L η Q) : False := by
  refine hS.false_of_diagonal_swap hA hcomm hδ (hS.odd_card_ker_diagonalHom hcomm hδ) ?_
  rw [hS.sup_eq_L_sup_E hA hcomm hδ hE hzA hzc hzE]
  exact hS.normalizer_Q_le_normalizer_L_sup_E

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
