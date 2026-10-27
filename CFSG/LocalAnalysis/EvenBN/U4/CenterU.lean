module

public import CFSG.LocalAnalysis.EvenBN.U4.LayersSwap
public import CFSG.LocalAnalysis.EvenBN.U4.CenterUPrelim
public import CFSG.LocalAnalysis.EvenBN.Common.SL2Module
public import CFSG.LocalAnalysis.EvenBN.U4.LayersPerfect
public import CFSG.LocalAnalysis.EvenBN.U4.LayersPerfectTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_sup
  mem_normalizer_inf)
open scoped MatrixGroups

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

theorem exists_I1_mul_D (hS : Setting h L η t Q T) {i : G} (hi : i ∈ miyamotoIG h L η) :
    ∃ i₁ ∈ miyamotoI1G h L η, ∃ d ∈ miyamotoDG h L η, i = i₁ * d := by
  have : CharP K 2 := h.charP
  obtain ⟨p, hp, rfl⟩ := hS.exists_torusElt_eq hi
  have hs := (miyamotoIParam_eq_one_iff h p).1 hp
  set s : Kˣ := p.1 * p.2 with hsdef
  set u : Kˣ := s ^ (2 ^ (f - 1)) with hudef
  have hf1 : 1 ≤ f := h.one_le
  have hq : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hsbar : (s : K) ^ 2 ^ f = s := by
    rw [← h.bar_apply]
    simpa [hsdef] using hs
  have hu2 : u ^ 2 = s := by
    apply Units.ext
    rw [hudef, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, ← hq,
      hsbar]
  have hubar : h.bar (u : K) = u := by
    rw [h.bar_apply, hudef, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hsbar]
  have hp₁ : miyamotoIParam h (u, u) = 1 :=
    (miyamotoIHom_mem_miyamotoI_iff h (u, u)).1 (miyamotoI1_le_I h ((mem_miyamotoI1 h).2
      ⟨u, hubar, rfl⟩))
  refine ⟨hS.torusElt (u, u) hp₁, hS.torusElt_mem_pull (u, u) hp₁
    ((mem_miyamotoI1 h).2 ⟨u, hubar, rfl⟩), miyamotoDHom h L η (p.1 * u⁻¹),
    miyamotoDHom_mem h L η _, ?_⟩
  rw [hS.miyamotoDHom_eq_torusElt, hS.torusElt_mul]
  have e : p = (u, u) * (p.1 * u⁻¹, (p.1 * u⁻¹)⁻¹) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul]
      rw [mul_comm p.1, ← mul_assoc, mul_inv_cancel, one_mul]
    · simp only [Prod.snd_mul, mul_inv_rev, inv_inv]
      have h2 : u * u = p.1 * p.2 := by rw [← sq, hu2]
      calc p.2 = p.1⁻¹ * (p.1 * p.2) := by rw [inv_mul_cancel_left]
        _ = p.1⁻¹ * (u * u) := by rw [h2]
        _ = u * (u * p.1⁻¹) := by rw [mul_comm p.1⁻¹, mul_assoc]
  have key : ∀ (p p' : Kˣ × Kˣ) (hp : miyamotoIParam h p = 1)
      (hp' : miyamotoIParam h p' = 1), p = p' → hS.torusElt p hp = hS.torusElt p' hp' := by
    rintro p p' hp hp' rfl
    rfl
  exact key _ _ _ _ e

section SwapFree

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

theorem U_le_RG (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ) ≤ miyamotoRG h L η t Q :=
  sup_le (le_sup_left.trans hS.P1_le_miyamotoRG) (inf_le_left.trans inf_le_left)

theorem E_le_centerIn_U (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ≤ CFSG.centerIn (miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)) := by
  intro e he
  refine mem_inf.2 ⟨mem_sup_left (hS.E_le_F1 he), mem_centralizer_iff.2 fun y hy => ?_⟩
  exact (mem_centralizer_iff.1 (hS.RG_le_centralizer_E (hS.U_le_RG hy)) e he).symm

theorem centerIn_U_le_F1 (hS : Setting h L η t Q T) :
    CFSG.centerIn (miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)) ≤ miyamotoF1G h L η t := by
  intro z hz
  obtain ⟨hzU, hzC⟩ := mem_inf.1 hz
  rw [← hS.RG_inf_centralizer_F]
  refine mem_inf.2 ⟨hS.U_le_RG hzU, centralizer_le (SetLike.coe_subset_coe.2
    (hS.F_le_F1.trans le_sup_left)) hzC⟩

end SwapFree

theorem not_le_centralizer_E (hS : Setting h L η t Q T) {M : Subgroup G}
    (hN : miyamotoN1G h L η ≤ M) : ¬ M ≤ centralizer (miyamotoEG h L η Q : Set G) := by
  intro hM
  have hr : miyamotoR1G h L η ∈ centralizer (miyamotoEG h L η Q : Set G) :=
    hM (hN (hS.R1G_mem_N1))
  have hE : (miyamotoEG h L η Q).map (MulAut.conj (miyamotoR1G h L η)⁻¹).toMonoidHom =
      miyamotoEG h L η Q := by
    ext e
    constructor
    · rintro ⟨e', he', rfl⟩
      have hc := mem_centralizer_iff.1 (inv_mem hr) e' he'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hc, inv_inv, inv_mul_cancel_right]
      exact he'
    · intro he
      refine ⟨e, he, ?_⟩
      have hc := mem_centralizer_iff.1 (inv_mem hr) e he
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hc, inv_inv, inv_mul_cancel_right]
  have h1 := hS.E_r1_inf_F
  rw [hE, inf_eq_left.2 hS.E_le_F] at h1
  have := hS.card_E
  rw [h1, card_bot] at this
  have h4 := hS.four_le
  have : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
  omega

section Swap

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

theorem M1_le_centralizer_I1 (hS : Setting h L η t Q T) :
    miyamotoM1G h L η t ≤ centralizer (miyamotoI1G h L η : Set G) :=
  hS.sec3_12_one.1.trans inf_le_right

theorem M1_le_normalizer_F1 (hS : Setting h L η t Q T) :
    miyamotoM1G h L η t ≤ normalizer (miyamotoF1G h L η t : Set G) :=
  hS.sec3_12_one.1.trans inf_le_left

theorem IG_le_normalizer_X1 (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (prodFactorOne ψ : Set G) := by
  intro i hi
  obtain ⟨i₁, hi₁, d, hd, rfl⟩ := hS.exists_I1_mul_D hi
  refine mul_mem ?_ (Common.le_normalizer_prodFactorOne ψ
    (hS.sec3_12_one.2.2.1 (hS.DG_le_N1G hd)))
  have hc : ∀ x ∈ prodFactorOne ψ, i₁ * x = x * i₁ := fun x hx =>
    mem_centralizer_iff.1 (hS.M1_le_centralizer_I1 (Common.prodFactorOne_le ψ hx)) i₁ hi₁
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hc x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have e := hc _ hx
    have : x = i₁ * x * i₁⁻¹ := by
      calc x = i₁⁻¹ * ((i₁ * x * i₁⁻¹) * i₁) := by group
        _ = i₁⁻¹ * (i₁ * (i₁ * x * i₁⁻¹)) := by rw [e]
        _ = i₁ * x * i₁⁻¹ := by group
    rw [this]
    exact hx

theorem X2_le_normalizer_U (hS : Setting h L η t Q T) :
    prodFactorTwo ψ ≤
      normalizer ((miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ) : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_sup (hS.M1_le_normalizer_F1 (Common.prodFactorTwo_le ψ hx)) ?_
  have hc : ∀ w ∈ 𝓦 ⊓ prodFactorOne ψ, w * x = x * w := fun w hw =>
    (mem_centralizer_iff.1 (Common.prodFactorTwo_le_centralizer ψ hx) w (mem_inf.1 hw).2)
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [← hc w hw, mul_inv_cancel_right]
    exact hw
  · intro hw
    have e := hc _ hw
    have : w = x * w * x⁻¹ := by
      calc w = x⁻¹ * ((x * w * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * w * x⁻¹)) := by rw [e]
        _ = x * w * x⁻¹ := by group
    rw [this]
    exact hw

theorem card_centerIn_U_ge [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    (2 ^ f) ^ 4 ≤ Nat.card (CFSG.centerIn (miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hk, ← pow_mul, mul_comm])
  set Z := CFSG.centerIn (miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)) with hZ
  have hZ2 : IsPGroup 2 Z := hS.isPGroup_RG.to_le (inf_le_left.trans hS.U_le_RG)
  obtain ⟨d, hd⟩ := hZ2.exists_card_eq
  by_contra hlt
  push Not at hlt
  have hd' : d < 2 * (2 * f) := by
    rw [hd, show (2 ^ f) ^ 4 = 2 ^ (2 * (2 * f)) by rw [← pow_mul]; ring_nf] at hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  have hk' : Nat.card k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
  have hX2Z : prodFactorTwo ψ ≤ normalizer (Z : Set G) := fun x hx =>
    normalizer_le_normalizer_centerIn _ (hS.X2_le_normalizer_U hx)
  have hX2C : prodFactorTwo ψ ≤ centralizer (Z : Set G) :=
    Common.le_centralizer_of_card_lt (Common.prodFactorTwoEquiv ψ) hk'
      (by have := hS.two_le; omega) (by omega) hX2Z hd hd'
  have hX2E : prodFactorTwo ψ ≤ centralizer (miyamotoEG h L η Q : Set G) :=
    hX2C.trans (centralizer_le (SetLike.coe_subset_coe.2 hS.E_le_centerIn_U))
  have htE : t ∈ normalizer (miyamotoEG h L η Q : Set G) :=
    hS.normalizer_P1_le_normalizer_E hS.t_mem_normalizer_P1
  have htt : t * t = 1 := hS.t_mul_t
  have hX1E : prodFactorOne ψ ≤ centralizer (miyamotoEG h L η Q : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro e he
    have hy := hS.t_conj_mem_X2 hψt hx
    have he' : t⁻¹ * e * t ∈ miyamotoEG h L η Q := by
      have := (mem_normalizer_iff.1 (inv_mem htE) e).1 he
      rwa [inv_inv] at this
    have hc := mem_centralizer_iff.1 (hX2E hy) _ he'
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    calc e * x = t * ((t⁻¹ * e * t) * (t⁻¹ * x * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * x * t) * (t⁻¹ * e * t)) * t⁻¹ := by rw [hc]
      _ = x * e := by group
  have hM : miyamotoM1G h L η t ≤ centralizer (miyamotoEG h L η Q : Set G) := by
    rw [← Common.prodFactorOne_sup_prodFactorTwo ψ]
    exact sup_le hX1E hX2E
  exact hS.not_le_centralizer_E hS.sec3_12_one.2.2.1 hM

end Swap

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
