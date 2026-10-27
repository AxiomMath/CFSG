module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e2b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e3c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e4a0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e3b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise
open scoped commutatorElement
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private abbrev q13eQP (t tau x₁ x₂ rho om : G) : Type :=
  ↥(q13P t tau x₁ x₂ rho om) ⧸
    ((ctxN tau x₁ x₂).subgroupOf (q13P t tau x₁ x₂ rho om))

private lemma q13e_isMulCommutative_P (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    IsMulCommutative ↥(q13P t tau x₁ x₂ rho om) :=
  IsMulCommutative.of_comm fun a b =>
    Subtype.ext (q13d_P_comm h hD.A_cent a a.2 b b.2)

private lemma q13e_quot_eq_of_mul_inv_mem (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {x y : G}
    (hx : x ∈ q13P t tau x₁ x₂ rho om) (hy : y ∈ q13P t tau x₁ x₂ rho om)
    (hxy : x * y⁻¹ ∈ ctxN tau x₁ x₂) :
    ((⟨x, hx⟩ : ↥(q13P t tau x₁ x₂ rho om)) : q13eQP t tau x₁ x₂ rho om) =
      (⟨y, hy⟩ : ↥(q13P t tau x₁ x₂ rho om)) := by
  haveI : IsMulCommutative ↥(q13P t tau x₁ x₂ rho om) := q13e_isMulCommutative_P h hD
  exact QuotientGroup.eq_iff_div_mem.mpr (by
    simpa [Subgroup.mem_subgroupOf, div_eq_mul_inv] using hxy)

private lemma q13e_mul_inv_mem_of_quot_eq (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {x y : G}
    (hx : x ∈ q13P t tau x₁ x₂ rho om) (hy : y ∈ q13P t tau x₁ x₂ rho om)
    (heq : ((⟨x, hx⟩ : ↥(q13P t tau x₁ x₂ rho om)) : q13eQP t tau x₁ x₂ rho om) =
      (⟨y, hy⟩ : ↥(q13P t tau x₁ x₂ rho om))) :
    x * y⁻¹ ∈ ctxN tau x₁ x₂ := by
  haveI : IsMulCommutative ↥(q13P t tau x₁ x₂ rho om) := q13e_isMulCommutative_P h hD
  have hmem := QuotientGroup.eq_iff_div_mem.mp heq
  simpa [Subgroup.mem_subgroupOf, div_eq_mul_inv] using hmem

private lemma q13e_mod_mul (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {a b c d : G}
    (ha : a ∈ q13P t tau x₁ x₂ rho om) (hb : b ∈ q13P t tau x₁ x₂ rho om)
    (hc : c ∈ q13P t tau x₁ x₂ rho om) (hd : d ∈ q13P t tau x₁ x₂ rho om)
    (hab : a * b⁻¹ ∈ ctxN tau x₁ x₂) (hcd : c * d⁻¹ ∈ ctxN tau x₁ x₂) :
    (a * c) * (b * d)⁻¹ ∈ ctxN tau x₁ x₂ := by
  haveI : IsMulCommutative ↥(q13P t tau x₁ x₂ rho om) := q13e_isMulCommutative_P h hD
  have h1 := q13e_quot_eq_of_mul_inv_mem h hD ha hb hab
  have h2 := q13e_quot_eq_of_mul_inv_mem h hD hc hd hcd
  have heq : (((⟨a, ha⟩ : ↥(q13P t tau x₁ x₂ rho om)) *
        (⟨c, hc⟩ : ↥(q13P t tau x₁ x₂ rho om))) : q13eQP t tau x₁ x₂ rho om) =
      (((⟨b, hb⟩ : ↥(q13P t tau x₁ x₂ rho om)) *
        (⟨d, hd⟩ : ↥(q13P t tau x₁ x₂ rho om))) : q13eQP t tau x₁ x₂ rho om) := by
    calc (((⟨a, ha⟩ : ↥(q13P t tau x₁ x₂ rho om)) *
            (⟨c, hc⟩ : ↥(q13P t tau x₁ x₂ rho om))) : q13eQP t tau x₁ x₂ rho om)
        = ((⟨a, ha⟩ : ↥(q13P t tau x₁ x₂ rho om)) : q13eQP t tau x₁ x₂ rho om) *
          ((⟨c, hc⟩ : ↥(q13P t tau x₁ x₂ rho om)) : q13eQP t tau x₁ x₂ rho om) :=
          QuotientGroup.mk_mul _ _ _
      _ = ((⟨b, hb⟩ : ↥(q13P t tau x₁ x₂ rho om)) : q13eQP t tau x₁ x₂ rho om) *
          ((⟨d, hd⟩ : ↥(q13P t tau x₁ x₂ rho om)) : q13eQP t tau x₁ x₂ rho om) := by
          rw [h1, h2]
      _ = (((⟨b, hb⟩ : ↥(q13P t tau x₁ x₂ rho om)) *
            (⟨d, hd⟩ : ↥(q13P t tau x₁ x₂ rho om))) : q13eQP t tau x₁ x₂ rho om) :=
          (QuotientGroup.mk_mul _ _ _).symm
  exact q13e_mul_inv_mem_of_quot_eq h hD _ _ heq

private lemma q13e_mod_trans (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {x y z : G}
    (hx : x ∈ q13P t tau x₁ x₂ rho om) (hy : y ∈ q13P t tau x₁ x₂ rho om)
    (hz : z ∈ q13P t tau x₁ x₂ rho om)
    (hxy : x * y⁻¹ ∈ ctxN tau x₁ x₂) (hyz : y * z⁻¹ ∈ ctxN tau x₁ x₂) :
    x * z⁻¹ ∈ ctxN tau x₁ x₂ := by
  have h1 := q13e_quot_eq_of_mul_inv_mem h hD hx hy hxy
  have h2 := q13e_quot_eq_of_mul_inv_mem h hD hy hz hyz
  exact q13e_mul_inv_mem_of_quot_eq h hD hx hz (h1.trans h2)

private lemma q13e_mod_symm {x y : G} (hxy : x * y⁻¹ ∈ ctxN tau x₁ x₂) :
    y * x⁻¹ ∈ ctxN tau x₁ x₂ := by
  have h1 := Subgroup.inv_mem (ctxN tau x₁ x₂) hxy
  rwa [show (x * y⁻¹)⁻¹ = y * x⁻¹ by group] at h1

private lemma q13e_mod_conj (h : Q13Om t L S x₁ x₂ lam rho tau om) {g x y : G}
    (hg : g ∈ q13L t tau x₁ x₂ rho om) (hxy : x * y⁻¹ ∈ ctxN tau x₁ x₂) :
    (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ ∈ ctxN tau x₁ x₂ := by
  have h1 := q13d_N_normal_L h g hg (x * y⁻¹) hxy
  rwa [show g * (x * y⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ by group] at h1

theorem q13e_card_B_ne (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    Nat.card (q13B t tau x₁ x₂ rho om) ≠ 2 ^ 8 := by
  intro hcard
  have hE0leB : q13E0 t tau x₁ x₂ rho om ≤ q13B t tau x₁ x₂ rho om := hD.E0_le_B
  have hrel : (q13E0 t tau x₁ x₂ rho om).relIndex (q13B t tau x₁ x₂ rho om) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := q13E0 t tau x₁ x₂ rho om)
      (K := q13B t tau x₁ x₂ rho om)
    rw [inf_of_le_left hE0leB, q13d_card_E0 h, hcard] at h1
    omega
  have hE0index : ((q13E0 t tau x₁ x₂ rho om).subgroupOf (q13B t tau x₁ x₂ rho om)).index =
      2 := hrel
  obtain ⟨b, hbB, hbE0⟩ : ∃ b ∈ q13B t tau x₁ x₂ rho om, b ∉ q13E0 t tau x₁ x₂ rho om := by
    by_contra hcon
    have hle : q13B t tau x₁ x₂ rho om ≤ q13E0 t tau x₁ x₂ rho om := by
      intro x hx
      by_contra hxE0
      exact hcon ⟨x, hx, hxE0⟩
    have heq : q13B t tau x₁ x₂ rho om = q13E0 t tau x₁ x₂ rho om :=
      le_antisymm hle hE0leB
    rw [heq, q13d_card_E0 h] at hcard
    norm_num at hcard
  have hbL : b ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hbB).1
  have hbE0inv : b⁻¹ ∉ q13E0 t tau x₁ x₂ rho om :=
    fun hx => hbE0 (by simpa using (q13E0 t tau x₁ x₂ rho om).inv_mem hx)
  have hwP : ⁅t, b⁆ ∈ q13P t tau x₁ x₂ rho om := q13e_kap_mem_P h hD b hbL
  have hgoal : ∀ g ∈ ctxM t tau x₁ x₂, g * ⁅t, b⁆ * g⁻¹ * (⁅t, b⁆)⁻¹ ∈ ctxN tau x₁ x₂ := by
    intro g hgM
    have hgL : g ∈ q13L t tau x₁ x₂ rho om := hD.M_le_L hgM
    have hgbB : g * b * g⁻¹ ∈ q13B t tau x₁ x₂ rho om := hD.B_normal.2 g hgL b hbB
    have hgbE0 : g * b * g⁻¹ ∉ q13E0 t tau x₁ x₂ rho om := by
      intro hmem
      apply hbE0
      have h1 := q13e_E0_normal_L g⁻¹ ((q13L t tau x₁ x₂ rho om).inv_mem hgL)
        (g * b * g⁻¹) hmem
      rwa [show g⁻¹ * (g * b * g⁻¹) * (g⁻¹)⁻¹ = b by group] at h1
    have hprod : ((⟨b⁻¹, (q13B t tau x₁ x₂ rho om).inv_mem hbB⟩ :
          ↥(q13B t tau x₁ x₂ rho om)) * ⟨g * b * g⁻¹, hgbB⟩) ∈
        (q13E0 t tau x₁ x₂ rho om).subgroupOf (q13B t tau x₁ x₂ rho om) := by
      rw [Subgroup.mul_mem_iff_of_index_two hE0index]
      simp only [Subgroup.mem_subgroupOf]
      exact ⟨fun hx => absurd hx hbE0inv, fun hx => absurd hx hgbE0⟩
    have heE0 : b⁻¹ * (g * b * g⁻¹) ∈ q13E0 t tau x₁ x₂ rho om :=
      Subgroup.mem_subgroupOf.mp hprod
    have heB : b⁻¹ * (g * b * g⁻¹) ∈ q13B t tau x₁ x₂ rho om := hE0leB heE0
    have heL : b⁻¹ * (g * b * g⁻¹) ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp heB).1
    have hge : g * b * g⁻¹ = b * (b⁻¹ * (g * b * g⁻¹)) := by group
    have hbeB : b * (b⁻¹ * (g * b * g⁻¹)) ∈ q13B t tau x₁ x₂ rho om :=
      (q13B t tau x₁ x₂ rho om).mul_mem hbB heB
    have hA_P : ⁅t, b * (b⁻¹ * (g * b * g⁻¹))⁆ ∈ q13P t tau x₁ x₂ rho om :=
      q13e_kap_mem_P h hD _ (Subgroup.mem_inf.mp hbeB).1
    have hB1_P : g * ⁅t, b⁆ * g⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
      q13d_P_normal_L h hD.A_cent g hgL ⁅t, b⁆ hwP
    have hkeN : ⁅t, b⁻¹ * (g * b * g⁻¹)⁆ ∈ ctxN tau x₁ x₂ := q13e_kap_E0 h hD _ heE0
    have hkeP : ⁅t, b⁻¹ * (g * b * g⁻¹)⁆ ∈ q13P t tau x₁ x₂ rho om :=
      q13d_N_le_P h hkeN
    have hC_P : ⁅t, b⁆ * ⁅t, b⁻¹ * (g * b * g⁻¹)⁆ ∈ q13P t tau x₁ x₂ rho om :=
      (q13P t tau x₁ x₂ rho om).mul_mem hwP hkeP
    have hconj := q13e_kap_conj h hD g hgL b hbB
    have hconj' : ⁅t, b * (b⁻¹ * (g * b * g⁻¹))⁆ * (g * ⁅t, b⁆ * g⁻¹)⁻¹ ∈
        ctxN tau x₁ x₂ := by
      rwa [hge] at hconj
    have hmul := q13e_kap_mul_B h hD b hbB (b⁻¹ * (g * b * g⁻¹)) heB
    have h1 : (g * ⁅t, b⁆ * g⁻¹) * ⁅t, b * (b⁻¹ * (g * b * g⁻¹))⁆⁻¹ ∈ ctxN tau x₁ x₂ :=
      q13e_mod_symm hconj'
    have h3 : (⁅t, b⁆ * ⁅t, b⁻¹ * (g * b * g⁻¹)⁆) * (⁅t, b⁆)⁻¹ ∈ ctxN tau x₁ x₂ := by
      have heq : (⁅t, b⁆ * ⁅t, b⁻¹ * (g * b * g⁻¹)⁆) * (⁅t, b⁆)⁻¹ =
          ⁅t, b⁻¹ * (g * b * g⁻¹)⁆ := by
        rw [q13d_P_comm h hD.A_cent ⁅t, b⁆ hwP _ hkeP]
        group
      rw [heq]
      exact hkeN
    exact q13e_mod_trans h hD hB1_P hC_P hwP
      (q13e_mod_trans h hD hB1_P hA_P hC_P h1 hmul) h3
  have hM3 : ⁅t, b⁆ ∈ ctxN tau x₁ x₂ := q13e_M3 h hD hwP hgoal
  exact hbE0 ((q13e_kap_N_iff h hB hD b hbB).mp hM3)

theorem q13e_kap_mem_AN_of_card_le (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) (hD : Q13D t x₁ x₂ lam rho tau om)
    (hcard : Nat.card (q13B t tau x₁ x₂ rho om) ≤ 2 ^ 9) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om, ⁅t, b⁆ ∈ q13AN t tau x₁ x₂ rho := by
  intro b₀ hb₀
  by_contra hb₀AN
  let T : Set G :=
    {p | p ∈ q13P t tau x₁ x₂ rho om ∧
      ∃ b ∈ q13B t tau x₁ x₂ rho om, ⁅t, b⁆ * p⁻¹ ∈ ctxN tau x₁ x₂}
  have hTmul : ∀ {p q : G}, p ∈ T → q ∈ T → p * q ∈ T := by
    rintro p q ⟨hpP, bp, hbpB, hbpn⟩ ⟨hqP, bq, hbqB, hbqn⟩
    refine ⟨(q13P t tau x₁ x₂ rho om).mul_mem hpP hqP, bp * bq,
      (q13B t tau x₁ x₂ rho om).mul_mem hbpB hbqB, ?_⟩
    have hκbpP : ⁅t, bp⁆ ∈ q13P t tau x₁ x₂ rho om :=
      q13e_kap_mem_P h hD bp (Subgroup.mem_inf.mp hbpB).1
    have hκbqP : ⁅t, bq⁆ ∈ q13P t tau x₁ x₂ rho om :=
      q13e_kap_mem_P h hD bq (Subgroup.mem_inf.mp hbqB).1
    have hpqP : p * q ∈ q13P t tau x₁ x₂ rho om :=
      (q13P t tau x₁ x₂ rho om).mul_mem hpP hqP
    have hκprodP : ⁅t, bp⁆ * ⁅t, bq⁆ ∈ q13P t tau x₁ x₂ rho om :=
      (q13P t tau x₁ x₂ rho om).mul_mem hκbpP hκbqP
    have hmul := q13e_kap_mul_B h hD bp hbpB bq hbqB
    have hprod : (⁅t, bp⁆ * ⁅t, bq⁆) * (p * q)⁻¹ ∈ ctxN tau x₁ x₂ :=
      q13e_mod_mul h hD hκbpP hpP hκbqP hqP hbpn hbqn
    have hκbpbqP : ⁅t, bp * bq⁆ ∈ q13P t tau x₁ x₂ rho om :=
      q13e_kap_mem_P h hD (bp * bq)
        (Subgroup.mem_inf.mp ((q13B t tau x₁ x₂ rho om).mul_mem hbpB hbqB)).1
    exact q13e_mod_trans h hD hκbpbqP hκprodP hpqP hmul hprod
  have hTone : (1 : G) ∈ T := by
    refine ⟨one_mem _, 1, one_mem _, ?_⟩
    simpa using (one_mem (ctxN tau x₁ x₂) : (1 : G) ∈ ctxN tau x₁ x₂)
  have hTinv : ∀ {p : G}, p ∈ T → p⁻¹ ∈ T := by
    rintro p ⟨hpP, bp, hbpB, hbpn⟩
    refine ⟨(q13P t tau x₁ x₂ rho om).inv_mem hpP, bp⁻¹,
      (q13B t tau x₁ x₂ rho om).inv_mem hbpB, ?_⟩
    have hκbpP : ⁅t, bp⁆ ∈ q13P t tau x₁ x₂ rho om :=
      q13e_kap_mem_P h hD bp (Subgroup.mem_inf.mp hbpB).1
    have hκbpinvP : ⁅t, bp⁻¹⁆ ∈ q13P t tau x₁ x₂ rho om :=
      q13e_kap_mem_P h hD bp⁻¹
        (Subgroup.mem_inf.mp ((q13B t tau x₁ x₂ rho om).inv_mem hbpB)).1
    have hmulBP := q13e_kap_mul_B h hD bp hbpB bp⁻¹
      ((q13B t tau x₁ x₂ rho om).inv_mem hbpB)
    have hkprod : ⁅t, bp⁆ * ⁅t, bp⁻¹⁆ ∈ ctxN tau x₁ x₂ := by
      have h := hmulBP
      rw [mul_inv_cancel, commutatorElement_one_right, one_mul] at h
      simpa using Subgroup.inv_mem (ctxN tau x₁ x₂) h
    have hpk : p * ⁅t, bp⁻¹⁆ ∈ ctxN tau x₁ x₂ := by
      simpa using q13e_mod_trans h hD hpP hκbpP
        ((q13P t tau x₁ x₂ rho om).inv_mem hκbpinvP) (q13e_mod_symm hbpn)
        (by simpa using hkprod)
    have heq : ⁅t, bp⁻¹⁆ * p = p * ⁅t, bp⁻¹⁆ :=
      q13d_P_comm h hD.A_cent ⁅t, bp⁻¹⁆ hκbpinvP p hpP
    rw [inv_inv, heq]
    exact hpk
  let W : Subgroup G :=
    { carrier := T
      mul_mem' := fun hp hq => hTmul hp hq
      one_mem' := hTone
      inv_mem' := fun hp => hTinv hp }
  have hWP : W ≤ q13P t tau x₁ x₂ rho om := fun p hp => hp.1
  have hNW : ctxN tau x₁ x₂ ≤ W := by
    intro n hn
    refine ⟨q13d_N_le_P h hn, 1, one_mem _, ?_⟩
    simpa using Subgroup.inv_mem (ctxN tau x₁ x₂) hn
  have hWM : ∀ g ∈ ctxM t tau x₁ x₂, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hgM w hw
    obtain ⟨hwP, b', hb'B, hb'n⟩ := hw
    have hgL : g ∈ q13L t tau x₁ x₂ rho om := hD.M_le_L hgM
    have hgb'B : g * b' * g⁻¹ ∈ q13B t tau x₁ x₂ rho om := hD.B_normal.2 g hgL b' hb'B
    refine ⟨q13d_P_normal_L h hD.A_cent g hgL w hwP, g * b' * g⁻¹, hgb'B, ?_⟩
    have hκgbgP : ⁅t, g * b' * g⁻¹⁆ ∈ q13P t tau x₁ x₂ rho om :=
      q13e_kap_mem_P h hD (g * b' * g⁻¹) (Subgroup.mem_inf.mp hgb'B).1
    have hgκbgP : g * ⁅t, b'⁆ * g⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
      q13d_P_normal_L h hD.A_cent g hgL ⁅t, b'⁆
        (q13e_kap_mem_P h hD b' (Subgroup.mem_inf.mp hb'B).1)
    have hgwgP : g * w * g⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
      q13d_P_normal_L h hD.A_cent g hgL w hwP
    exact q13e_mod_trans h hD hκgbgP hgκbgP hgwgP
      (q13e_kap_conj h hD g hgL b' hb'B) (q13e_mod_conj h hgL hb'n)
  have hw₀W : ⁅t, b₀⁆ ∈ W :=
    ⟨q13e_kap_mem_P h hD b₀ (Subgroup.mem_inf.mp hb₀).1, b₀, hb₀, by
      rw [mul_inv_cancel]
      exact one_mem _⟩
  have hMP : ∀ p ∈ q13P t tau x₁ x₂ rho om, p ∈ W :=
    q13e_M1 h hD hWP hNW hWM hw₀W hb₀AN
  have hsurj : ∀ p ∈ q13P t tau x₁ x₂ rho om,
      ∃ k ∈ q13B t tau x₁ x₂ rho om, ⁅t, k⁆ * p⁻¹ ∈ ctxN tau x₁ x₂ := by
    intro p hp
    have hpW : p ∈ W := hMP p hp
    exact hpW.2
  have hNP : ctxN tau x₁ x₂ ≤ q13P t tau x₁ x₂ rho om := q13d_N_le_P h
  have hNn : ∀ p ∈ q13P t tau x₁ x₂ rho om, ∀ n ∈ ctxN tau x₁ x₂,
      p * n * p⁻¹ ∈ ctxN tau x₁ x₂ := by
    intro p hp n hn
    rw [q13d_P_comm h hD.A_cent p hp n (hNP hn)]
    simpa using hn
  have hφ : ∀ k ∈ q13B t tau x₁ x₂ rho om, ⁅t, k⁆ ∈ q13P t tau x₁ x₂ rho om := by
    intro k hk
    exact q13e_kap_mem_P h hD k (Subgroup.mem_inf.mp hk).1
  have hcard_eq := q13e_card_mul_eq_of_hom_mod (K := q13B t tau x₁ x₂ rho om)
    (H := q13E0 t tau x₁ x₂ rho om) (P' := q13P t tau x₁ x₂ rho om)
    (N' := ctxN tau x₁ x₂) (φ := fun g => ⁅t, g⁆)
    hD.E0_le_B hNP hNn hφ (q13e_kap_mul_B h hD) (q13e_kap_N_iff h hB hD) hsurj
  have hBcard : Nat.card (q13B t tau x₁ x₂ rho om) = 2 ^ 10 := by
    have hh := hcard_eq
    rw [q13b_card_N h, q13d_card_P h hD.A_cent, q13d_card_E0 h] at hh
    norm_num at hh
    omega
  rw [hBcard] at hcard
  norm_num at hcard

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
