module

public import CFSG.CGT.PushingUpLit.SolKR2.Engine

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78 CFSG.Timmesfeld
open CFSG.RankThree.PartTwo (omegaOneSub)
open scoped commutatorElement

variable {G : Type} [Group G]

structure R2Facts {M B : Subgroup G} (h : R2 M B) : Prop where
  comm_B0 : ∀ A ∈ Lam M B, ∀ a ∈ A, ∀ b ∈ omegaOneSub B, a * b = b * a
  isConj_B0 : ∀ x ∈ omegaOneSub B, ∀ y ∈ omegaOneSub B, x ≠ 1 → y ≠ 1 → IsConj x y
  conjCent_mem_lam : ∀ t ∈ omegaOneSub B, t ≠ 1 → ∀ τ : G, τ * t = t * τ → IsConj t τ →
    ∃ A ∈ Lam M B, τ ∈ A
  exists_noncomm : ∃ (S : Sylow 2 M) (A D : Subgroup G), A ∈ Lam M B ∧ D ∈ Lam M B ∧
    A ≤ (S : Subgroup M).map M.subtype ∧ D ≤ (S : Subgroup M).map M.subtype ∧
    ¬ ∀ a ∈ A, ∀ d ∈ D, a * d = d * a
  fusion_lam : ∀ F ∈ Lam M B, F ≠ omegaOneSub B → ∀ t ∈ omegaOneSub B, t ≠ 1 →
    ∀ τ ∈ F, τ ≠ 1 → IsConj t (t * τ)
  rootGroup_eq : ∀ t ∈ omegaOneSub B, t ≠ 1 → rootGroup (CorB.cls t) t = omegaOneSub B
  isPGroup : IsPGroup 2 ↥(⨆ A ∈ Lam M B, A)
  derived_le : ⁅⨆ A ∈ Lam M B, A, ⨆ A ∈ Lam M B, A⁆ ≤ omegaOneSub B

namespace R2Facts

variable {M B : Subgroup G} {h : R2 M B}

theorem mul_self_of_mem_lam (h : R2 M B) {A : Subgroup G} (hA : A ∈ Lam M B) {a : G}
    (ha : a ∈ A) : a * a = 1 := by
  obtain ⟨g, hg, -⟩ := hA
  rw [hg, mem_conjSubgroup] at ha
  have h1 : g⁻¹ * a * g * (g⁻¹ * a * g) = 1 := ((mem_omegaOneSub_iff h.H.comm).1 ha).2
  calc a * a = g * (g⁻¹ * a * g * (g⁻¹ * a * g)) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem isConj_of_mem_lam (hf : R2Facts h) {A : Subgroup G} (hA : A ∈ Lam M B) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) {t : G} (ht : t ∈ omegaOneSub B) (ht1 : t ≠ 1) : IsConj t a := by
  obtain ⟨g, hg, -⟩ := hA
  rw [hg, mem_conjSubgroup] at ha
  have hb1 : g⁻¹ * a * g ≠ 1 := by
    intro h1
    apply ha1
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  exact (hf.isConj_B0 t ht _ ha ht1 hb1).trans (isConj_iff.2 ⟨g, by group⟩)

theorem weakClosure_eq (hf : R2Facts h) {t : G} (ht : t ∈ omegaOneSub B) (ht1 : t ≠ 1) :
    CorB.weakClosure t = ⨆ A ∈ Lam M B, A := by
  apply le_antisymm
  · rw [CorB.weakClosure, Subgroup.closure_le]
    rintro τ ⟨hcomm, hconj⟩
    obtain ⟨A, hA, hτ⟩ := hf.conjCent_mem_lam t ht ht1 τ hcomm hconj
    exact le_iSup₂ (f := fun (A : Subgroup G) (_ : A ∈ Lam M B) => A) A hA hτ
  · refine iSup₂_le fun A hA a ha => ?_
    by_cases ha1 : a = 1
    · rw [ha1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure
        ⟨hf.comm_B0 A hA a ha t ht, hf.isConj_of_mem_lam hA ha ha1 ht ht1⟩

theorem commutator_commutator_eq_bot (hf : R2Facts h) :
    ⁅⁅⨆ A ∈ Lam M B, A, ⨆ A ∈ Lam M B, A⁆, ⨆ A ∈ Lam M B, A⁆ = ⊥ := by
  have hWc : (⨆ A ∈ Lam M B, A) ≤ Subgroup.centralizer (omegaOneSub B : Set G) := by
    refine iSup₂_le fun A hA a ha => ?_
    exact Subgroup.mem_centralizer_iff.2 fun b hb => (hf.comm_B0 A hA a ha b hb).symm
  have h1 : ⁅⨆ A ∈ Lam M B, A, omegaOneSub B⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 hWc
  refine le_antisymm ?_ bot_le
  calc ⁅⁅⨆ A ∈ Lam M B, A, ⨆ A ∈ Lam M B, A⁆, ⨆ A ∈ Lam M B, A⁆
      ≤ ⁅omegaOneSub B, ⨆ A ∈ Lam M B, A⁆ := Subgroup.commutator_mono hf.derived_le le_rfl
    _ = ⊥ := by rw [Subgroup.commutator_comm, h1]

theorem setup (hf : R2Facts h) {t : G} (ht : t ∈ omegaOneSub B) (ht1 : t ≠ 1) :
    CorB.Setup t where
  orderOf_eq := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ht1
    rw [sq]
    exact ((mem_omegaOneSub_iff h.H.comm).1 ht).2
  isPGroup := by
    rw [hf.weakClosure_eq ht ht1]
    exact hf.isPGroup
  class_two := by
    rw [hf.weakClosure_eq ht ht1]
    exact hf.commutator_commutator_eq_bot
  fusion := by
    intro τ hcomm hconj hne
    have hτ1 : τ ≠ 1 := by
      intro h1
      rw [h1] at hconj
      exact ht1 (isConj_one_right.1 hconj.symm)
    obtain ⟨A, hA, hτA⟩ := hf.conjCent_mem_lam t ht ht1 τ hcomm hconj
    by_cases hAB : A = omegaOneSub B
    · rw [hAB] at hτA
      have htt : t * t = 1 := ((mem_omegaOneSub_iff h.H.comm).1 ht).2
      refine hf.isConj_B0 t ht (t * τ) ((omegaOneSub B).mul_mem ht hτA) ht1 ?_
      intro h1
      apply hne
      calc τ = t * (t * τ) := by rw [← mul_assoc, htt, one_mul]
        _ = t := by rw [h1, mul_one]
    · exact hf.fusion_lam A hA hAB t ht ht1 τ hτA hτ1

theorem exists_orderOf_eq_four [Finite G] (hF : R2First) (hf : R2Facts h) {t : G}
    (ht : t ∈ omegaOneSub B) (ht1 : t ≠ 1) :
    ∃ d e : G, IsConj t d ∧ IsConj t e ∧ orderOf (d * e) = 4 := by
  obtain ⟨S, A, D, hA, hD, hAS, hDS, hnc⟩ := hf.exists_noncomm
  obtain ⟨hAD, -⟩ := hF G M B h S A D hA hD hAS hDS hnc
  push Not at hnc
  obtain ⟨a, ha, x, hx, hax⟩ := hnc
  have ha1 : a ≠ 1 := fun h1 => hax (by rw [h1]; simp)
  have hx1 : x ≠ 1 := fun h1 => hax (by rw [h1]; simp)
  have haa : a * a = 1 := mul_self_of_mem_lam h hA ha
  have hxx : x * x = 1 := mul_self_of_mem_lam h hD hx
  refine ⟨a, x, hf.isConj_of_mem_lam hA ha ha1 ht ht1, hf.isConj_of_mem_lam hD hx hx1 ht ht1, ?_⟩
  have hcomm : ⁅a, x⁆ = (a * x) ^ 2 := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hxx,
      sq]
    simp [mul_assoc]
  have hcB : ⁅a, x⁆ ∈ omegaOneSub B := by
    rw [← hAD]
    exact Subgroup.commutator_mem_commutator ha hx
  have hc2 : ⁅a, x⁆ * ⁅a, x⁆ = 1 := ((mem_omegaOneSub_iff h.H.comm).1 hcB).2
  have hne2 : ¬ (a * x) ^ 2 ^ 1 = 1 := by
    intro h1
    rw [pow_one, ← hcomm, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hax h1
  have hfin4 : (a * x) ^ 2 ^ (1 + 1) = 1 := by
    have : (a * x) ^ 2 ^ (1 + 1) = ((a * x) ^ 2) ^ 2 := by
      rw [← pow_mul]
      norm_num
    rw [this, ← hcomm, sq]
    exact hc2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := orderOf_eq_prime_pow hne2 hfin4
  simpa using h4

end R2Facts

section Main


variable {G : Type} [Group G] [Finite G] {M B : Subgroup G}

theorem R2.false_of_facts [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hF : R2First)
    (h : R2 M B) (hf : R2Facts h) : False := by
  obtain ⟨⟨t, ht⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (show omegaOneSub B ≠ ⊥ by
    intro hbot
    have h4 := h.card4
    rw [hbot, Subgroup.card_bot] at h4
    omega)
  have ht1 : t ≠ 1 := fun h1 => ht1' (Subtype.ext h1)
  exact h.false_of_setup hnab (hf.setup ht ht1) (hf.rootGroup_eq t ht ht1)
    (hf.exists_orderOf_eq_four hF ht ht1)

end Main

end CFSG.CGT.PushingUpLit.SolKR2
