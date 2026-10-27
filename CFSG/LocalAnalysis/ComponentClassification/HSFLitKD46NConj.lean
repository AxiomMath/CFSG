module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NTri
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NConj
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NC

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

namespace Inst

variable {I : Inst S} {H : Hyp S R}

theorem controls (I : Inst S) (H : Hyp S R) : ∀ e ∈ S.E I.yi, ConjTo t e →
    ∃ n ∈ normalizer (S.E I.yi : Set X), n * t * n⁻¹ = e := by
  intro e he hc
  obtain ⟨w, rfl⟩ := I.eq_wV he
  rw [I.conjTo_wV_iff H.fus] at hc
  obtain ⟨p, q, c', r⟩ := w
  simp only at hc
  subst hc
  obtain ⟨ε, -, v₀, hv₀, w₀, hw₀, w₀', hw₀', hv₀c, hw₀c, hw₀'c⟩ := I.exists_vww H
  obtain ⟨a, b, c, habc⟩ := exists_gC ε p q r
  have hgM : I.Mat (v₀ ^ (c : ℕ) * (w₀ ^ (a : ℕ) * w₀' ^ (b : ℕ))) (gC ε a b c) :=
    (Mat.pw ⟨_, hv₀c⟩ c).mul ((Mat.pw ⟨_, hw₀c⟩ a).mul (Mat.pw ⟨_, hw₀'c⟩ b))
  refine ⟨_, hgM.mem, ?_⟩
  rw [hgM.conj_t, gC_col_two, habc]

theorem card_conj (I : Inst S) (H : Hyp S R) :
    Nat.card {e : S.E I.yi // ConjTo t e} = 8 := by
  let f : Fin 2 × Fin 2 × Fin 2 → {e : S.E I.yi // ConjTo t e} := fun p =>
    ⟨⟨I.wV (p.1, p.2.1, 1, p.2.2), I.wV_mem _⟩, (I.conjTo_wV_iff H.fus _).mpr rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => ?_, fun x => ?_⟩
    · have := I.wV_injective (congrArg (fun y : {e : S.E I.yi // ConjTo t e} => (y : X)) h)
      simp only [Prod.mk.injEq] at this
      exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2.2)
    · obtain ⟨⟨e, he⟩, hc⟩ := x
      obtain ⟨w, rfl⟩ := I.eq_wV he
      have hw := (I.conjTo_wV_iff H.fus w).mp hc
      obtain ⟨p, q, c, r⟩ := w
      simp only at hw
      subst hw
      exact ⟨(p, q, r), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

namespace Data6

variable (D : I.Data6 H)

variable (Rl : D.Rel)

include Rl in
theorem no_conj_one (hε : D.ε = 0) (hs4 : Rl.s4 = 0) :
    ∀ q ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ D.C₁, ¬ ConjTo t q := by
  have hγ : Rl.γ = (0, 0, 0, 0) := by rw [Rl.h0, hs4]
  have hQ := Rl.rel.comm_one hε hγ
  have hkc : I.ki * D.c₁ = D.c₁ * I.ki := by
    have h := D.c₁_mat.conj_ki
    rw [show I.wV (vC 3) = I.ki by simp [vC, wV]] at h
    calc I.ki * D.c₁ = D.c₁ * (D.c₁⁻¹ * I.ki * D.c₁) := by group
      _ = D.c₁ * I.ki := by
          congr 1
          calc D.c₁⁻¹ * I.ki * D.c₁ = D.c₁⁻¹ * (D.c₁ * I.ki * D.c₁⁻¹) * D.c₁ := by rw [h]
            _ = I.ki := by group
  have hC₁ : ∀ x ∈ D.C₁, ∀ y ∈ D.C₁, x * y = y * x := by
    intro x hx y hy
    refine comm_of_mem_closure (fun a ha b hb => ?_) hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hkc
    · exact hkc.symm
    · rfl
  have hcl : S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ D.C₁ =
      closure ((S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) ∪ D.C₁) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hcomm : ∀ a ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ D.C₁, ∀ b ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ D.C₁,
      a * b = b * a := by
    intro a ha b hb
    rw [hcl] at ha hb
    refine comm_of_mem_closure (fun x hx y hy => ?_) ha hb
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hQ x hx y hy
    · exact (D.C₁_comm Rl y hy x hx).symm
    · exact D.C₁_comm Rl x hx y hy
    · exact hC₁ x hx y hy
  have hc₁C : D.c₁ ∈ D.C₁ := subset_closure (by simp)
  have hsup : S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ D.C₁ = S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ zpowers D.c₁ := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [C₁, closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact mem_sup_left (I.E0_le_Q0 _ _ (subset_closure (by simp)))
      · exact mem_sup_right (mem_zpowers _)
    · exact sup_le le_sup_left (zpowers_le.mpr (mem_sup_right hc₁C))
  have hN : D.c₁ ∈ normalizer (S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) :=
    mem_normalizer_of_conj_mem fun q hq => by
      rw [D.C₁_comm Rl _ hc₁C q hq, mul_inv_cancel_right]; exact hq
  have hc2 : D.c₁ ^ 2 ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ :=
    (zpowers_le.mpr (I.E0_le_Q0 _ _ (subset_closure (by simp)))) D.c₁_sq_mem
  have hcQ : D.c₁ ∉ S.Q0 I.yi I.ki D.w₁ D.w₂ := by
    intro h
    obtain ⟨a, b, e, he, he'⟩ := Rl.rel.mem_Q0_iff.mp h
    have hM : I.Mat D.c₁ (comp (pw (M2C D.ε) b) (pw (M1C D.ε) a)) := by
      rw [he']
      exact ((Rl.rel.m2.pw b).mul (Rl.rel.m1.pw a)).mul_central (I.E0_le_centralizer he)
    exact vC_ne_Q0 D.ε a b (D.c₁_mat.unique hM)
  have hcard : Nat.card (S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ D.C₁ : Subgroup X) = 64 := by
    rw [hsup, card_sup_zpowers hN hc2 hcQ, Rl.rel.card_Q0]
  intro q hq
  exact not_conjTo_of_comm S hcomm hcard hq

end Data6

end Inst

end CFSG.ComponentClassification.HSFLit.KD46
