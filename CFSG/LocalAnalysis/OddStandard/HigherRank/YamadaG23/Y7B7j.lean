module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7f

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7b_BM_le_NM3_aux (c : Ctx7 G L) (hb : B5Std c) :
    y7bBM c.s ≤ normalizer (M3 c.s : Set G) :=
  fun _ hx => y7b_W_le_NM3 c hb (y7b_BM_le_W c hb hx)

theorem y7b_comm_conj_of_mem_H (c : Ctx7 G L) {n : G} (hn : n ∈ c.s.H) (y : G) :
    ⁅n * y * n⁻¹, c.s.t⁆ = n * ⁅y, c.s.t⁆ * n⁻¹ := by
  have hnt : n * c.s.t = c.s.t * n := Subgroup.mem_centralizer_singleton_iff.mp hn
  have hconj : n * c.s.t * n⁻¹ = c.s.t := by rw [hnt]; group
  have h := conjugate_commutatorElement (g₁ := y) (g₂ := c.s.t) (g₃ := n)
  rw [hconj] at h
  exact h.symm

theorem y7b_exists_theta (c : Ctx7 G L) (hb : B5Std c)
    [hN : ((M3 c.s).subgroupOf (y7bBM c.s)).Normal] :
    ∃ θ : ↥(X7 c.s) →* ↥(y7bBM c.s) ⧸ (M3 c.s).subgroupOf (y7bBM c.s),
      (∀ (y : ↥(X7 c.s)) (u : ↥(y7bBM c.s)),
        θ y = QuotientGroup.mk u ↔ (u : G)⁻¹ * ⁅(y : G), c.s.t⁆ ∈ M3 c.s) ∧
      (∀ n ∈ normIn c.s.H c.s.fr.B, ∀ y y' : ↥(X7 c.s), (y' : G) = n * y * n⁻¹ →
        ∀ u u' : ↥(y7bBM c.s), (u' : G) = n * u * n⁻¹ →
          θ y = QuotientGroup.mk u → θ y' = QuotientGroup.mk u') := by
  let F : ↥(X7 c.s) → (↥(y7bBM c.s) ⧸ (M3 c.s).subgroupOf (y7bBM c.s)) := fun y =>
    QuotientGroup.mk ⟨⁅(y : G), c.s.t⁆,
      y7b_comm_t_mem_BM c hb (y : G) (y7b_X7_le_X c y.2)⟩
  have hsq : ∀ q : (↥(y7bBM c.s) ⧸ (M3 c.s).subgroupOf (y7bBM c.s)), q * q = 1 := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro u
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul, pow_two] using y7b_BM_sq_mem_M3 c hb u u.2
  have hcomm : ∀ a b : (↥(y7bBM c.s) ⧸ (M3 c.s).subgroupOf (y7bBM c.s)), a * b = b * a := by
    intro a b
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq (a * b))).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
            rw [inv_eq_of_mul_eq_one_right (hsq b), inv_eq_of_mul_eq_one_right (hsq a)]
  have hF : ∀ a b : ↥(X7 c.s), F (a * b) = F a * F b := by
    intro a b
    have ha7 : (a : G) ∈ X7 c.s := a.2
    have hb7 : (b : G) ∈ X7 c.s := b.2
    have haX : (a : G) ∈ y7bX c.s := y7b_X7_le_X c ha7
    have hbX : (b : G) ∈ y7bX c.s := y7b_X7_le_X c hb7
    set u : G := ⁅(a : G), c.s.t⁆ with hu
    set v : G := ⁅(b : G), c.s.t⁆ with hv
    have huBM : u ∈ y7bBM c.s := by rw [hu]; exact y7b_comm_t_mem_BM c hb (a : G) haX
    have hvBM : v ∈ y7bBM c.s := by rw [hv]; exact y7b_comm_t_mem_BM c hb (b : G) hbX
    have hmain : F (a * b) = QuotientGroup.mk (⟨v, hvBM⟩ : ↥(y7bBM c.s)) *
        QuotientGroup.mk (⟨u, huBM⟩ : ↥(y7bBM c.s)) := by
      change QuotientGroup.mk (⟨⁅(a : G) * (b : G), c.s.t⁆, _⟩ : ↥(y7bBM c.s)) =
        QuotientGroup.mk (⟨v, hvBM⟩ : ↥(y7bBM c.s)) *
          QuotientGroup.mk (⟨u, huBM⟩ : ↥(y7bBM c.s))
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_inv, Subgroup.coe_mul]
      have heq : ⁅(a : G) * (b : G), c.s.t⁆⁻¹ * (v * u) =
          u⁻¹ * ⁅(a : G), v⁻¹⁆ * u := by
        rw [commutatorElement_mul_left_eq_conj_mul, ← hv, ← hu, commutatorElement_def]
        group
      rw [heq]
      have hm : ⁅(a : G), v⁻¹⁆ ∈ M3 c.s :=
        ((y7b_mem_X7 c hb).mp ha7).2 v⁻¹ ((y7bBM c.s).inv_mem hvBM)
      exact (Subgroup.mem_normalizer_iff''.mp (y7b_BM_le_NM3_aux c hb huBM) _).mp hm
    calc F (a * b) = QuotientGroup.mk (⟨v, hvBM⟩ : ↥(y7bBM c.s)) *
            QuotientGroup.mk (⟨u, huBM⟩ : ↥(y7bBM c.s)) := hmain
      _ = F b * F a := rfl
      _ = F a * F b := (hcomm (F a) (F b)).symm
  let θ : ↥(X7 c.s) →* (↥(y7bBM c.s) ⧸ (M3 c.s).subgroupOf (y7bBM c.s)) := MonoidHom.mk' F hF
  have hchar : ∀ (y : ↥(X7 c.s)) (u : ↥(y7bBM c.s)),
      θ y = QuotientGroup.mk u ↔ (u : G)⁻¹ * ⁅(y : G), c.s.t⁆ ∈ M3 c.s := by
    intro y u
    change QuotientGroup.mk (⟨⁅(y : G), c.s.t⁆, _⟩ : ↥(y7bBM c.s)) = QuotientGroup.mk u ↔
      (u : G)⁻¹ * ⁅(y : G), c.s.t⁆ ∈ M3 c.s
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_inv, Subgroup.coe_mul]
    constructor
    · intro h
      simpa only [mul_inv_rev, inv_inv] using (M3 c.s).inv_mem h
    · intro h
      simpa only [mul_inv_rev, inv_inv] using (M3 c.s).inv_mem h
  refine ⟨θ, hchar, ?_⟩
  intro n hn y y' hy' u u' hu' h
  have hnH : n ∈ c.s.H := (Subgroup.mem_inf.mp hn).1
  have hm : (u : G)⁻¹ * ⁅(y : G), c.s.t⁆ ∈ M3 c.s := (hchar y u).mp h
  rw [hchar y' u', hu', hy', y7b_comm_conj_of_mem_H c hnH (y : G)]
  have heq : (n * (u : G) * n⁻¹)⁻¹ * (n * ⁅(y : G), c.s.t⁆ * n⁻¹) =
      n * ((u : G)⁻¹ * ⁅(y : G), c.s.t⁆) * n⁻¹ := by group
  rw [heq]
  exact (Subgroup.mem_normalizer_iff.mp (y7b_N_le_NM3 c hb hn) _).mp hm

theorem y7b_X0_iff (c : Ctx7 G L) (hb : B5Std c) {y : G} (hy : y ∈ X7 c.s) :
    y ∈ y7bX0 c.s ↔ ⁅y, c.s.t⁆ ∈ M3 c.s := by
  constructor
  · intro hy0
    have ht : c.s.t ∈ y7bW c.s := y7b_t_mem_W c hb
    have h := hy0.2.2 c.s.t ht
    simpa only [commutatorElement_inv] using (M3 c.s).inv_mem h
  · intro h
    have hyX : y ∈ y7bX c.s := y7b_X7_le_X c hy
    refine ⟨(Subgroup.mem_inf.mp hyX).1, (Subgroup.mem_inf.mp hyX).2, fun k hk => ?_⟩
    obtain ⟨w, hw, hkw | hkw⟩ := (y7b_mem_W c hb).mp hk
    · rw [hkw]
      simpa only [commutatorElement_inv] using
        (M3 c.s).inv_mem (((y7b_mem_X7 c hb).mp hy).2 w hw)
    · rw [hkw, commutatorElement_mul_left_eq_conj_mul]
      have hwy : ⁅w, y⁆ ∈ M3 c.s := by
        simpa only [commutatorElement_inv] using
          (M3 c.s).inv_mem (((y7b_mem_X7 c hb).mp hy).2 w hw)
      have hty : ⁅c.s.t, y⁆ ∈ M3 c.s := by
        simpa only [commutatorElement_inv] using (M3 c.s).inv_mem h
      exact (M3 c.s).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (y7b_BM_le_NM3_aux c hb hw) ⁅c.s.t, y⁆).mp hty) hwy

theorem y7b_X7_sq_mem_X0 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ y ∈ X7 c.s, y ^ 2 ∈ y7bX0 c.s := by
  intro y hy
  have hy2 : y ^ 2 ∈ X7 c.s := (X7 c.s).pow_mem hy 2
  rw [y7b_X0_iff c hb hy2]
  have hu : ⁅y, c.s.t⁆ ∈ y7bBM c.s := y7b_comm_t_mem_BM c hb y (y7b_X7_le_X c hy)
  have hcomm : ⁅y, ⁅y, c.s.t⁆⁆ ∈ M3 c.s := ((y7b_mem_X7 c hb).mp hy).2 ⁅y, c.s.t⁆ hu
  have hyu_eq : y * ⁅y, c.s.t⁆ * y⁻¹ = ⁅y, ⁅y, c.s.t⁆⁆ * ⁅y, c.s.t⁆ := by
    rw [commutatorElement_def]; group
  rw [show y ^ 2 = y * y by rw [pow_two], commutatorElement_mul_left_eq_conj_mul, hyu_eq,
    mul_assoc, ← pow_two]
  exact (M3 c.s).mul_mem hcomm (y7b_BM_sq_mem_M3 c hb ⁅y, c.s.t⁆ hu)

end CFSG.OddStandard.HigherRank.YamadaG23
