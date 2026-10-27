module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S1b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S1c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


variable (hc : Ctx4L t L S x₁ x₂ lam rho tau)
include hc

theorem q_mem_normalizer_O : t * lam ∈ normalizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact q_conj_O hc hh
  · intro hh
    have hq1 : (t * lam) * (t * lam) = 1 := q_mul_self hc.toCtx4Q
    have hqi : (t * lam)⁻¹ = t * lam := inv_eq_of_mul_eq_one_right hq1
    have hthis : (t * lam) * ((t * lam) * h * (t * lam)⁻¹) * (t * lam)⁻¹ = h := by
      rw [hqi]
      calc (t * lam) * ((t * lam) * h * (t * lam)) * (t * lam)
          = ((t * lam) * (t * lam)) * h * ((t * lam) * (t * lam)) := by group
        _ = h := by rw [hq1]; group
    rw [← hthis]
    exact q_conj_O hc hh

theorem claim1 {w : G} (hw : w ∈ ctxO t tau x₁ x₂) (hq : (t * lam * w) * (t * lam * w) = 1) :
    ∃ b ∈ ctxO t tau x₁ x₂, (t * lam)⁻¹ * (b⁻¹ * (t * lam * w) * b) ∈ ctxX t tau x₁ x₂ := by
  classical
  let O : Subgroup G := ctxO t tau x₁ x₂
  let X : Subgroup G := ctxX t tau x₁ x₂
  let q : G := t * lam
  let N : Subgroup ↥O := X.subgroupOf O
  have hq1 : q * q = 1 := q_mul_self hc.toCtx4Q
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq1
  have hqN : q ∈ normalizer (O : Set G) := q_mem_normalizer_O hc
  let σ : ↥O →* ↥O := (Outside.conjAut O q hqN).toMonoidHom
  have hσ_coe : ∀ a : ↥O, ((σ a : ↥O) : G) = q * (a : G) * q⁻¹ :=
    fun a => Outside.conjAut_coe O q hqN a
  haveI : N.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa only [Subgroup.coe_mul, InvMemClass.coe_inv] using X_normal_O hc g.2 hx⟩
  have hσN : ∀ x ∈ N, σ x ∈ N := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hσ_coe x]
    exact q_conj_X hc hx
  have hσσ : ∀ a : ↥O, σ (σ a) = a := fun a => by
    apply Subtype.ext
    rw [hσ_coe (σ a), hσ_coe a]
    rw [hqi]
    calc q * (q * (a : G) * q) * q = (q * q) * (a : G) * (q * q) := by group
      _ = (a : G) := by rw [hq1]; group
  have hsq : ∀ a : ↥O, a * a ∈ N := fun a => by
    rw [Subgroup.mem_subgroupOf]
    have := hc.O_quot.1 (a : G) a.2
    simpa only [Subgroup.coe_mul, pow_two] using this
  have hcm : ∀ a b : ↥O, a * b * a⁻¹ * b⁻¹ ∈ N := fun a b => by
    rw [Subgroup.mem_subgroupOf]
    have := hc.O_quot.2 (a : G) a.2 (b : G) b.2
    simpa only [Subgroup.coe_mul, InvMemClass.coe_inv] using this
  have hNX : Nat.card ↥N = Nat.card ↥X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (X_le_O hc)).toEquiv
  have hcard : Nat.card ↥O = 16 * Nat.card ↥N := by
    rw [hNX, card_X hc, hc.card_O]
    norm_num
  have hfix : Nat.card {a : ↥O // σ a * a⁻¹ ∈ N} ≤ 4 * Nat.card ↥N := by
    have hcard_le : Nat.card {a : ↥O // σ a * a⁻¹ ∈ N} ≤
        Nat.card {a : G // a ∈ ctxO t tau x₁ x₂ ∧
          (t * lam) * a * (t * lam)⁻¹ * a⁻¹ ∈ ctxX t tau x₁ x₂} :=
      Nat.card_le_card_of_injective
        (fun a : {a : ↥O // σ a * a⁻¹ ∈ N} =>
          ⟨(a.1 : G), a.1.2, by
            have haX : (((σ a.1) * a.1⁻¹ : ↥O) : G) ∈ X :=
              Subgroup.mem_subgroupOf.mp a.2
            have heq : (((σ a.1) * a.1⁻¹ : ↥O) : G) =
                (t * lam) * (a.1 : G) * (t * lam)⁻¹ * (a.1 : G)⁻¹ := by
              rw [Subgroup.coe_mul, InvMemClass.coe_inv, hσ_coe a.1]
            rw [← heq]
            exact haX⟩)
        (by
          intro a b hab
          have h1 : (a.1 : G) = (b.1 : G) := by
            have := congrArg (fun x : {y : G // y ∈ ctxO t tau x₁ x₂ ∧
              (t * lam) * y * (t * lam)⁻¹ * y⁻¹ ∈ ctxX t tau x₁ x₂} => (x : G)) hab
            simpa using this
          exact Subtype.ext (Subtype.ext h1))
    calc Nat.card {a : ↥O // σ a * a⁻¹ ∈ N} ≤ 64 := hcard_le.trans (card_fix_le hc)
      _ = 4 * Nat.card ↥N := by rw [hNX, card_X hc]
  have hw2 : (q * w * q) * w = 1 := by
    rw [← show (q * w) * (q * w) = (q * w * q) * w by group]
    exact hq
  have hw1 : σ ⟨w, hw⟩ * ⟨w, hw⟩ = 1 := by
    apply Subtype.ext
    show (((σ ⟨w, hw⟩ : ↥O) : G) * w) = 1
    rw [hσ_coe ⟨w, hw⟩, hqi]
    simpa only [Subgroup.coe_mk] using hw2
  obtain ⟨b, hb⟩ := lemmaR_grp N σ hσN hσσ hsq hcm hcard hfix ⟨w, hw⟩ hw1
  refine ⟨(b : G), b.2, ?_⟩
  have hbX : (((σ b)⁻¹ * ⟨w, hw⟩ * b : ↥O) : G) ∈ X := Subgroup.mem_subgroupOf.mp hb
  have heq : q⁻¹ * ((b : G)⁻¹ * (q * w) * (b : G)) =
      (((σ b)⁻¹ * ⟨w, hw⟩ * b : ↥O) : G) := by
    conv_rhs => simp only [Subgroup.coe_mul, InvMemClass.coe_inv, Subgroup.coe_mk, hσ_coe b]
    rw [show (q * (b : G) * q⁻¹)⁻¹ = q * (b : G)⁻¹ * q⁻¹ by group]
    rw [hqi]
    group
  change q⁻¹ * ((b : G)⁻¹ * (q * w) * (b : G)) ∈ X
  rw [heq]
  exact hbX

end CFSG.OddStandard.SmallF3.HarrisU33.L34
