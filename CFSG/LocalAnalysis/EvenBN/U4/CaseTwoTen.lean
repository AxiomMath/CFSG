module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoNine

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  mem_normalizer_sup card_sup_mul_card_inf_eq)
open scoped MatrixGroups Pointwise commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

local notation "𝓥" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

local notation "𝓨" => CFSG.centerIn 𝓤 ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (miyamotoR1G h L η))) (CFSG.centerIn 𝓤)

local notation "𝓨t" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨

local notation "𝓚" => 𝓨t ⊔ prodFactorOne ψ

local notation "𝓦'" => miyamotoRG h L η t Q ⊓ 𝓚

local notation "𝓦'ᵗ" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦'

local notation "𝓦₂" => 𝓦' ⊓ miyamotoF2G h L η t Q

local notation "𝓔₂" => miyamotoEG h L η Q ⊓ 𝓦'ᵗ

theorem mem_N2_of_mem_M2 (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂]
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)} {α₂ : miyamotoN2G h L η ≃* SL(2, k₂)}
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a))
    (hψt₂ : ∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k₂)), (y : G) = t⁻¹ * x * t →
      ψ₂ x = (y₁, y₂) → ψ₂ y = (y₂, y₁))
    {m : G} (hm : m ∈ miyamotoM2G h L η t Q) (hmt : t⁻¹ * m * t = m) :
    m ∈ miyamotoN2G h L η := by
  have h1 := hψt₂ ⟨m, hm⟩ ⟨m, hm⟩ (ψ₂ ⟨m, hm⟩).1 (ψ₂ ⟨m, hm⟩).2 hmt.symm (Prod.mk.eta).symm
  have hab : (ψ₂ ⟨m, hm⟩).1 = (ψ₂ ⟨m, hm⟩).2 := congrArg Prod.fst h1
  set n := α₂.symm (ψ₂ ⟨m, hm⟩).1 with hn
  have hnM : (n : G) ∈ miyamotoM2G h L η t Q := hS.sec3_12_two.2.2.1 n.2
  have e : ψ₂ ⟨n, hnM⟩ = ψ₂ ⟨m, hm⟩ := by
    rw [hψα₂ n ⟨n, hnM⟩ rfl, hn, MulEquiv.apply_symm_apply]
    exact Prod.ext rfl hab
  have e' : (n : G) = m := congrArg Subtype.val (ψ₂.injective e)
  rw [← e']
  exact n.2

theorem exists_W2_of_mem_A2 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) {a : G} (ha : a ∈ miyamotoA2G h L η) :
    ∃ x ∈ 𝓦₂, a = x * (t * x * t) := by
  obtain ⟨-, hC, hinf, -, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  obtain ⟨hW2t, hF2, -⟩ := hS.sec5_2_two hk hψA hψt hZ
  have haF : a ∈ miyamotoF2G h L η t Q ⊓ centralizer ({t} : Set G) := by
    rw [hS.F2_inf_C]
    exact ha
  have hat : t * a = a * t := (mem_centralizer_singleton_iff.1 (mem_inf.1 haF).2).symm
  have hinf2 : 𝓦₂ ⊓ (𝓦₂).map (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [hW2t]
    exact eq_bot_iff.2 (hinf ▸ inf_le_inf inf_le_left inf_le_left)
  have hcW : ∀ x ∈ 𝓦₂, ∀ y ∈ (𝓦₂).map (MulAut.conj t).toMonoidHom, x * y = y * x := by
    rw [hW2t]
    exact fun x hx y hy => mem_centralizer_iff.1 (hC (mem_inf.1 hy).1) x (mem_inf.1 hx).1
  have haW : a ∈ 𝓦₂ ⊔ (𝓦₂).map (MulAut.conj t).toMonoidHom := by
    rw [hW2t, ← hF2]
    exact (mem_inf.1 haF).1
  exact exists_eq_mul_conj_of_mem_sup hS.t_mul_t hcW hinf2 haW hat

theorem W'_le_D [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)} {α₂ : miyamotoN2G h L η ≃* SL(2, k₂)}
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a))
    {j : G} (hj : j ∈ miyamotoJ2G h L η t Q) (hj1 : j ≠ 1)
    (hjC : j ∈ centralizer ((𝓚 : Subgroup G) : Set G)) (hjY : j ∈ prodFactorTwo ψ₂) :
    𝓦' ≤ 𝓦₂ ⊔ prodFactorOne ψ₂ :=
  (hS.W'_eq_sup hk hψA hψt hZ hk₂ hψα₂ hj hj1 hjC hjY).le.trans (sup_le_sup_left inf_le_right _)

theorem Y2_le_centralizer_D [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)}
    {j : G} (hj : j ∈ miyamotoJ2G h L η t Q) (hj1 : j ≠ 1)
    (hjC : j ∈ centralizer ((𝓚 : Subgroup G) : Set G)) (hjY : j ∈ prodFactorTwo ψ₂) :
    prodFactorTwo ψ₂ ≤ centralizer ((𝓦₂ ⊔ prodFactorOne ψ₂ : Subgroup G) : Set G) := by
  have hY2 := hS.Y2_le_centralizer_W2E hk hψA hψt hZ hk₂ hj hj1 hjC hjY
  intro y hy
  have hle : 𝓦₂ ⊔ prodFactorOne ψ₂ ≤ centralizer ({y} : Set G) :=
    sup_le (fun x hx => mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 (hY2 hy) x (mem_sup_left hx)))
      (fun x hx => mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 (Common.prodFactorOne_le_centralizer ψ₂ hx) y hy).symm)
  exact mem_centralizer_iff.2 fun x hx => mem_centralizer_singleton_iff.1 (hle hx)

theorem R2G_mem_normalizer_D [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)}
    {j : G} (hj : j ∈ miyamotoJ2G h L η t Q) (hj1 : j ≠ 1)
    (hjC : j ∈ centralizer ((𝓚 : Subgroup G) : Set G)) (hjY : j ∈ prodFactorTwo ψ₂) :
    miyamotoR2G h L η ∈ normalizer ((𝓦₂ ⊔ prodFactorOne ψ₂ : Subgroup G) : Set G) := by
  obtain ⟨y, hy, y', hy', hr⟩ :=
    Common.exists_mul_of_mem ψ₂ (hS.sec3_12_two.2.2.1 hS.R2G_mem_N2)
  have hy'c := hS.Y2_le_centralizer_D hk hψA hψt hZ hk₂ hj hj1 hjC hjY hy'
  refine mem_normalizer_of_conj_le fun x hx => ?_
  have e : miyamotoR2G h L η * x * (miyamotoR2G h L η)⁻¹ = y * x * y⁻¹ := by
    rw [hr]
    have h1 : x * y' = y' * x := mem_centralizer_iff.1 hy'c x hx
    calc y * y' * x * (y * y')⁻¹ = y * (y' * x) * y'⁻¹ * y⁻¹ := by group
      _ = y * (x * y') * y'⁻¹ * y⁻¹ := by rw [h1]
      _ = y * x * y⁻¹ := by group
  rw [e]
  have hyD : y ∈ 𝓦₂ ⊔ prodFactorOne ψ₂ := mem_sup_right hy
  exact mul_mem (mul_mem hyD hx) (inv_mem hyD)

theorem commutator_D_eq_bot [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)}
    (hψt₂ : ∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k₂)), (y : G) = t⁻¹ * x * t →
      ψ₂ x = (y₁, y₂) → ψ₂ y = (y₂, y₁))
    {j : G} (hj : j ∈ miyamotoJ2G h L η t Q) (hj1 : j ≠ 1)
    (hjC : j ∈ centralizer ((𝓚 : Subgroup G) : Set G)) (hjY : j ∈ prodFactorTwo ψ₂) :
    ⁅𝓦₂ ⊔ prodFactorOne ψ₂, (𝓦₂ ⊔ prodFactorOne ψ₂).map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥ := by
  obtain ⟨-, hC, -, -, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  obtain ⟨hW2t, -, -⟩ := hS.sec5_2_two hk hψA hψt hZ
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right hS.t_mul_t
  have htM : t ∈ normalizer (miyamotoM2G h L η t Q : Set G) := hS.sec3_12_two.2.1 hS.t_mem_H2
  have hY2C := hS.Y2_le_centralizer_D hk hψA hψt hZ hk₂ hj hj1 hjC hjY
  have hDt : (𝓦₂ ⊔ prodFactorOne ψ₂).map (MulAut.conj t⁻¹).toMonoidHom =
      (𝓦'ᵗ ⊓ miyamotoF2G h L η t Q) ⊔ prodFactorTwo ψ₂ := by
    rw [hti, Subgroup.map_sup, hW2t, hS.map_conj_t_Y1 hψt₂]
  rw [hDt, commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
  refine sup_le ?_ hY2C
  rw [← le_centralizer_iff]
  refine sup_le (fun x hx => mem_centralizer_iff.2 fun v hv =>
    (mem_centralizer_iff.1 (hC (mem_inf.1 hv).1) x (mem_inf.1 hx).1).symm) fun y hy => ?_
  refine mem_centralizer_iff.2 fun v hv => ?_
  have hyt : t⁻¹ * y * t ∈ prodFactorTwo ψ₂ :=
    Common.conj_mem_prodFactorTwo_of_swap ψ₂ htM hψt₂ hy
  have hvt : t⁻¹ * v * t ∈ 𝓦₂ := by
    rw [← hW2t] at hv
    exact mem_map_conj_iff.1 hv
  have hc : (t⁻¹ * v * t) * (t⁻¹ * y * t) = (t⁻¹ * y * t) * (t⁻¹ * v * t) :=
    mem_centralizer_iff.1 (hY2C hyt) _ (mem_sup_left hvt)
  have e : t⁻¹ * (v * y) * t = t⁻¹ * (y * v) * t := by
    calc t⁻¹ * (v * y) * t = (t⁻¹ * v * t) * (t⁻¹ * y * t) := by group
      _ = (t⁻¹ * y * t) * (t⁻¹ * v * t) := hc
      _ = t⁻¹ * (y * v) * t := by group
  exact mul_left_cancel (mul_right_cancel e)

theorem D_inf_eq_bot [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)} {α₂ : miyamotoN2G h L η ≃* SL(2, k₂)}
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a))
    (hψt₂ : ∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k₂)), (y : G) = t⁻¹ * x * t →
      ψ₂ x = (y₁, y₂) → ψ₂ y = (y₂, y₁))
    {j : G} (hj : j ∈ miyamotoJ2G h L η t Q) (hj1 : j ≠ 1)
    (hjC : j ∈ centralizer ((𝓚 : Subgroup G) : Set G)) (hjY : j ∈ prodFactorTwo ψ₂) :
    (𝓦₂ ⊔ prodFactorOne ψ₂) ⊓ (𝓦₂ ⊔ prodFactorOne ψ₂).map (MulAut.conj t⁻¹).toMonoidHom =
      ⊥ := by
  obtain ⟨-, -, hinf, -, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  obtain ⟨hW2t, -, -⟩ := hS.sec5_2_two hk hψA hψt hZ
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right hS.t_mul_t
  have htM : t ∈ normalizer (miyamotoM2G h L η t Q : Set G) := hS.sec3_12_two.2.1 hS.t_mem_H2
  have hY1N := hS.Y1_le_normalizer_W2 hk hψA hψt hZ hk₂ hψα₂ hj hj1 hjC hjY
  have e1 : ((𝓦₂ ⊔ prodFactorOne ψ₂ : Subgroup G) : Set G) =
      ((𝓦₂ : Subgroup G) : Set G) * (prodFactorOne ψ₂ : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ hY1N
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  have hx1' : x ∈ ((𝓦₂ : Subgroup G) : Set G) * (prodFactorOne ψ₂ : Set G) := by
    rw [← e1]
    exact hx1
  obtain ⟨w, hw, y, hy, rfl⟩ := hx1'
  have hx2' : t * (w * y) * t⁻¹ ∈ ((𝓦₂ : Subgroup G) : Set G) * (prodFactorOne ψ₂ : Set G) := by
    rw [← e1]
    exact Common.mem_map_conj_inv_iff.1 hx2
  obtain ⟨w', hw', y', hy', e⟩ := hx2'
  have e' : w * y = (t⁻¹ * w' * t) * (t⁻¹ * y' * t) := by
    calc w * y = t⁻¹ * (t * (w * y) * t⁻¹) * t := by group
      _ = t⁻¹ * (w' * y') * t := by rw [← e]
      _ = (t⁻¹ * w' * t) * (t⁻¹ * y' * t) := by group
  have hw't : t⁻¹ * w' * t ∈ 𝓦'ᵗ ⊓ miyamotoF2G h L η t Q := by
    rw [← hW2t]
    exact ⟨w', hw', by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hti]⟩
  have hy't : t⁻¹ * y' * t ∈ prodFactorTwo ψ₂ :=
    Common.conj_mem_prodFactorTwo_of_swap ψ₂ htM hψt₂ hy'
  have hm : (t⁻¹ * w' * t)⁻¹ * w ∈ miyamotoF2G h L η t Q ⊓ miyamotoM2G h L η t Q := by
    refine mem_inf.2 ⟨mul_mem (inv_mem (mem_inf.1 hw't).2) (mem_inf.1 hw).2, ?_⟩
    have e2 : (t⁻¹ * w' * t)⁻¹ * w = (t⁻¹ * y' * t) * y⁻¹ := by
      calc (t⁻¹ * w' * t)⁻¹ * w = (t⁻¹ * w' * t)⁻¹ * (w * y) * y⁻¹ := by group
        _ = (t⁻¹ * w' * t)⁻¹ * ((t⁻¹ * w' * t) * (t⁻¹ * y' * t)) * y⁻¹ := by rw [e']
        _ = (t⁻¹ * y' * t) * y⁻¹ := by group
    rw [e2]
    exact mul_mem (Common.prodFactorTwo_le ψ₂ hy't) (inv_mem (Common.prodFactorOne_le ψ₂ hy))
  rw [hS.F2_inf_M2, mem_bot] at hm
  have hww : w = t⁻¹ * w' * t := (inv_mul_eq_one.1 hm).symm
  have hw1 : w = 1 := by
    have hmem : w ∈ 𝓦' ⊓ 𝓦'ᵗ := by
      refine mem_inf.2 ⟨(mem_inf.1 hw).1, ?_⟩
      rw [hww]
      exact (mem_inf.1 hw't).1
    rwa [hinf, mem_bot] at hmem
  have hyy : y = t⁻¹ * y' * t := by
    rw [← hww] at e'
    exact mul_left_cancel e'
  have hy1 : y = 1 := by
    have hmem : y ∈ prodFactorOne ψ₂ ⊓ prodFactorTwo ψ₂ := by
      refine mem_inf.2 ⟨hy, ?_⟩
      rw [hyy]
      exact hy't
    rwa [Common.prodFactorOne_inf_prodFactorTwo, mem_bot] at hmem
  show w * y ∈ (⊥ : Subgroup G)
  rw [hw1, hy1, mul_one]
  exact one_mem _

theorem range_diagonalHom_W2_sup_Y1 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)} {α₂ : miyamotoN2G h L η ≃* SL(2, k₂)}
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a))
    (hψt₂ : ∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k₂)), (y : G) = t⁻¹ * x * t →
      ψ₂ x = (y₁, y₂) → ψ₂ y = (y₂, y₁))
    {j : G} (hj : j ∈ miyamotoJ2G h L η t Q) (hj1 : j ≠ 1)
    (hjC : j ∈ centralizer ((𝓚 : Subgroup G) : Set G)) (hjY : j ∈ prodFactorTwo ψ₂)
    (hcomm : ⁅𝓦₂ ⊔ prodFactorOne ψ₂,
      (𝓦₂ ⊔ prodFactorOne ψ₂).map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    (Common.diagonalHom (𝓦₂ ⊔ prodFactorOne ψ₂) t hcomm).range =
      miyamotoA2G h L η ⊔ miyamotoN2G h L η := by
  have ht := hS.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hY1N := hS.Y1_le_normalizer_W2 hk hψA hψt hZ hk₂ hψα₂ hj hj1 hjC hjY
  have e1 : ((𝓦₂ ⊔ prodFactorOne ψ₂ : Subgroup G) : Set G) =
      ((𝓦₂ : Subgroup G) : Set G) * (prodFactorOne ψ₂ : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ hY1N
  have htF2 : t⁻¹ ∈ normalizer (miyamotoF2G h L η t Q : Set G) :=
    inv_mem (mem_inf.1 hS.t_mem_H2).1
  have htM : t ∈ normalizer (miyamotoM2G h L η t Q : Set G) := hS.sec3_12_two.2.1 hS.t_mem_H2
  apply le_antisymm
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    have hx' : x ∈ ((𝓦₂ : Subgroup G) : Set G) * (prodFactorOne ψ₂ : Set G) := by
      rw [← e1]
      exact hx
    obtain ⟨w, hw, y, hy, rfl⟩ := hx'
    have e : (⟨w * y, hx⟩ : (𝓦₂ ⊔ prodFactorOne ψ₂ : Subgroup G)) =
        ⟨w, mem_sup_left hw⟩ * ⟨y, mem_sup_right hy⟩ := rfl
    rw [e, map_mul]
    refine mul_mem_sup ?_ ?_
    · rw [← hS.F2_inf_C]
      refine mem_inf.2 ⟨?_, Common.range_diagonalHom_le hcomm ht ⟨_, rfl⟩⟩
      rw [Common.diagonalHom_apply]
      have hwF : w ∈ miyamotoF2G h L η t Q := (mem_inf.1 hw).2
      refine mul_mem hwF ?_
      have := (mem_normalizer_iff.1 htF2 w).1 hwF
      rwa [inv_inv] at this
    · have hyM : y ∈ miyamotoM2G h L η t Q := Common.prodFactorOne_le ψ₂ hy
      have hδy := Common.range_diagonalHom_le hcomm ht ⟨⟨y, mem_sup_right hy⟩, rfl⟩
      refine hS.mem_N2_of_mem_M2 hψα₂ hψt₂ ?_ ?_
      · rw [Common.diagonalHom_apply]
        refine mul_mem hyM ?_
        have := (mem_normalizer_iff.1 (inv_mem htM) y).1 hyM
        rwa [inv_inv] at this
      · have hc := mem_centralizer_singleton_iff.1 hδy
        rw [mul_assoc, hc, inv_mul_cancel_left]
  · refine sup_le (fun a ha => ?_) (fun n hn => ?_)
    · obtain ⟨x, hx, rfl⟩ := hS.exists_W2_of_mem_A2 hk hψA hψt hZ ha
      exact ⟨⟨x, mem_sup_left hx⟩, by rw [Common.diagonalHom_apply, hti]⟩
    · have hnM : n ∈ miyamotoM2G h L η t Q := hS.sec3_12_two.2.2.1 hn
      set a := α₂ ⟨n, hn⟩ with ha
      have hy : ((ψ₂.symm (a, 1) : miyamotoM2G h L η t Q) : G) ∈ prodFactorOne ψ₂ :=
        Common.symm_inl_mem_prodFactorOne ψ₂ a
      have hyM : ((ψ₂.symm (a, 1) : miyamotoM2G h L η t Q) : G) ∈ miyamotoM2G h L η t Q :=
        (ψ₂.symm (a, 1)).2
      have hy'M : t⁻¹ * ((ψ₂.symm (a, 1) : miyamotoM2G h L η t Q) : G) * t ∈
          miyamotoM2G h L η t Q := by
        have := (mem_normalizer_iff.1 (inv_mem htM) _).1 hyM
        rwa [inv_inv] at this
      have hψy' : ψ₂ ⟨_, hy'M⟩ = (1, a) :=
        hψt₂ (ψ₂.symm (a, 1)) ⟨_, hy'M⟩ a 1 rfl (MulEquiv.apply_symm_apply ψ₂ (a, 1))
      have hprod : (ψ₂.symm (a, 1) * ⟨_, hy'M⟩ : miyamotoM2G h L η t Q) = ⟨n, hnM⟩ := by
        apply ψ₂.injective
        rw [map_mul, MulEquiv.apply_symm_apply, hψy', hψα₂ ⟨n, hn⟩ ⟨n, hnM⟩ rfl, ← ha]
        simp
      refine ⟨⟨_, mem_sup_right hy⟩, ?_⟩
      rw [Common.diagonalHom_apply]
      exact congrArg Subtype.val hprod

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
