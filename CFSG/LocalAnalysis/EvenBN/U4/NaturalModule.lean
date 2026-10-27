module

public import CFSG.LocalAnalysis.EvenBN.U4.TorusExclusion
public import CFSG.LocalAnalysis.EvenBN.Common.NaturalModule

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  card_sup_mul_card_inf_eq)
open scoped MatrixGroups

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

theorem F1_inf_centralizer_W1_le (_hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊓ centralizer ((𝓦 ⊓ prodFactorOne ψ : Subgroup G) : Set G) ≤
      CFSG.centerIn 𝓤 := by
  intro y hy
  obtain ⟨hyF, hyC⟩ := mem_inf.1 hy
  refine mem_inf.2 ⟨mem_sup_left hyF, ?_⟩
  have hC : 𝓤 ≤ centralizer ({y} : Set G) := by
    refine sup_le (fun u hu => ?_) (fun w hw => ?_)
    · exact mem_centralizer_singleton_iff.2 (_hS.F1_comm hu hyF)
    · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hyC w hw)
  exact mem_centralizer_iff.2 fun u hu => mem_centralizer_singleton_iff.1 (hC hu)


theorem F1_inf_centralizer_M1 (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊓ centralizer (miyamotoM1G h L η t : Set G) = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨hzF, hzC⟩ := mem_inf.1 hz
  have hWM : 𝓦 ≤ miyamotoM1G h L η t := hS.sec3_12_one.2.2.2.2.1
  have hzE : z ∈ miyamotoEG h L η Q := by
    rw [← hS.centerIn_RG]
    refine mem_inf.2 ⟨le_sup_left.trans hS.P1_le_miyamotoRG hzF,
      mem_centralizer_iff.2 fun r hr => ?_⟩
    obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hr
    have h1 : w * z = z * w := mem_centralizer_iff.1 hzC w (hWM hw)
    have h2 : y * z = z * y := hS.F1_comm hy hzF
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have hr : miyamotoR1G h L η * z = z * miyamotoR1G h L η :=
    mem_centralizer_iff.1 hzC _ hS.R1G_mem_M1
  rw [← hS.E_r1_inf_F]
  refine mem_inf.2 ⟨?_, hS.E_le_F hzE⟩
  rw [mem_map_conj_inv_iff, hr, mul_inv_cancel_right]
  exact hzE

theorem F1_inf_centralizer_X1 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : Nat.card (CFSG.centerIn 𝓤) = (2 ^ f) ^ 4) :
    miyamotoF1G h L η t ⊓ centralizer (prodFactorOne ψ : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hk, ← pow_mul, mul_comm])
  set Y := miyamotoF1G h L η t ⊓ centralizer (prodFactorOne ψ : Set G) with hY
  have hYZ : Y ≤ CFSG.centerIn 𝓤 := fun y hy => hS.F1_inf_centralizer_W1_le (mem_inf.2
    ⟨(mem_inf.1 hy).1, centralizer_le (SetLike.coe_subset_coe.2 inf_le_right) (mem_inf.1 hy).2⟩)
  have hX2Y : prodFactorTwo ψ ≤ normalizer (Y : Set G) := fun x hx =>
    mem_normalizer_inf (hS.M1_le_normalizer_F1 (Common.prodFactorTwo_le ψ hx))
      (mem_normalizer_centralizer (mem_normalizer_of_mem_centralizer'
        (Common.prodFactorTwo_le_centralizer ψ hx)))
  have hY2 : IsPGroup 2 Y :=
    hS.isPGroup_RG.to_le (inf_le_left.trans (le_sup_left.trans hS.P1_le_miyamotoRG))
  obtain ⟨e, he⟩ := hY2.exists_card_eq
  have hk' : Nat.card k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
  by_cases hlt : e < 2 * (2 * f)
  ·
    have hX2C := Common.le_centralizer_of_card_lt (Common.prodFactorTwoEquiv ψ) hk'
      (by have := hS.two_le; omega) (by omega) hX2Y he hlt
    refine eq_bot_iff.2 fun y hy => ?_
    rw [← hS.F1_inf_centralizer_M1]
    refine mem_inf.2 ⟨(mem_inf.1 hy).1, ?_⟩
    rw [← Common.prodFactorOne_sup_prodFactorTwo ψ]
    refine mem_centralizer_iff.2 fun x hx => ?_
    have hC : prodFactorOne ψ ⊔ prodFactorTwo ψ ≤ centralizer ({y} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hy).2 x hx)
      · exact mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 (hX2C hx) y hy).symm
    exact mem_centralizer_singleton_iff.1 (hC hx)
  ·
    exfalso
    push Not at hlt
    have hYeq : Y = CFSG.centerIn 𝓤 := by
      refine Subgroup.eq_of_le_of_card_ge hYZ ?_
      rw [hZ, he]
      calc (2 ^ f) ^ 4 = 2 ^ (2 * (2 * f)) := by rw [← pow_mul]; ring_nf
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hlt
    have hX1E : prodFactorOne ψ ≤ centralizer (miyamotoEG h L η Q : Set G) := by
      intro x hx
      rw [mem_centralizer_iff]
      intro z hz
      have hzY : z ∈ Y := by rw [hYeq]; exact hS.E_le_centerIn_U hz
      exact (mem_centralizer_iff.1 (mem_inf.1 hzY).2 x hx).symm
    have htE : t ∈ normalizer (miyamotoEG h L η Q : Set G) :=
      hS.normalizer_P1_le_normalizer_E hS.t_mem_normalizer_P1
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right hS.t_mul_t
    have hX2E : prodFactorTwo ψ ≤ centralizer (miyamotoEG h L η Q : Set G) := by
      intro x hx
      rw [mem_centralizer_iff]
      intro z hz
      have hy := hS.t_conj_mem_X1 hψt hx
      have hz' : t⁻¹ * z * t ∈ miyamotoEG h L η Q := by
        have := (mem_normalizer_iff.1 (inv_mem htE) z).1 hz
        rwa [inv_inv] at this
      have hc := mem_centralizer_iff.1 (hX1E hy) _ hz'
      calc z * x = t * ((t⁻¹ * z * t) * (t⁻¹ * x * t)) * t⁻¹ := by group
        _ = t * ((t⁻¹ * x * t) * (t⁻¹ * z * t)) * t⁻¹ := by rw [hc]
        _ = x * z := by group
    have hM : miyamotoM1G h L η t ≤ centralizer (miyamotoEG h L η Q : Set G) := by
      rw [← Common.prodFactorOne_sup_prodFactorTwo ψ]
      exact sup_le hX1E hX2E
    exact hS.not_le_centralizer_E hS.sec3_12_one.2.2.1 hM

theorem F1_inf_centralizer_X2 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : Nat.card (CFSG.centerIn 𝓤) = (2 ^ f) ^ 4) :
    miyamotoF1G h L η t ⊓ centralizer (prodFactorTwo ψ : Set G) = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨hzF, hzC⟩ := mem_inf.1 hz
  have htF1 : t ∈ normalizer (miyamotoF1G h L η t : Set G) :=
    hS.normalizer_RG_le_normalizer_F1 hS.t_mem_normalizer_RG
  have hz' : t * z * t⁻¹ ∈ miyamotoF1G h L η t ⊓ centralizer (prodFactorOne ψ : Set G) := by
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 htF1 z).1 hzF, mem_centralizer_iff.2 fun x hx => ?_⟩
    have hx' := hS.t_conj_mem_X2 hψt hx
    have hc := mem_centralizer_iff.1 hzC _ hx'
    calc x * (t * z * t⁻¹) = t * ((t⁻¹ * x * t) * z) * t⁻¹ := by group
      _ = t * (z * (t⁻¹ * x * t)) * t⁻¹ := by rw [hc]
      _ = t * z * t⁻¹ * x := by group
  rw [hS.F1_inf_centralizer_X1 hk hψt hZ, mem_bot] at hz'
  rw [mem_bot]
  calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
    _ = 1 := by rw [hz']; group

theorem centerIn_U_inf_centralizer_W2 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) :
    CFSG.centerIn 𝓤 ⊓ centralizer ((𝓦 ⊓ prodFactorTwo ψ : Subgroup G) : Set G) =
      miyamotoEG h L η Q := by
  refine le_antisymm (fun z hz => hS.centerIn_U_inf_centralizer_W2_le_E hk (mem_inf.1 hz).1
    (mem_inf.1 hz).2) (le_inf hS.E_le_centerIn_U fun e he => ?_)
  exact mem_centralizer_iff.2 fun w hw =>
    (mem_centralizer_iff.1 (hS.RG_le_centralizer_E (mem_inf.1 (mem_inf.1 hw).1).1) e he).symm

theorem sec3_17_three [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : Nat.card (CFSG.centerIn 𝓤) = (2 ^ f) ^ 4) :
    (∀ a ∈ CFSG.centerIn 𝓤, ∀ b ∈ CFSG.centerIn 𝓤, a ≠ 1 → b ≠ 1 →
      ∃ x ∈ prodFactorTwo ψ, x * a * x⁻¹ = b) ∧
      (∀ e ∈ miyamotoEG h L η Q, e ≠ 1 →
        prodFactorTwo ψ ⊓ centralizer ({e} : Set G) = 𝓦 ⊓ prodFactorTwo ψ) ∧
      prodFactorTwo ψ ⊓ centralizer ((CFSG.centerIn 𝓤 : Subgroup G) : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hk, ← pow_mul, mul_comm])
  have hk' : Nat.card k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
  have hZF1 : CFSG.centerIn 𝓤 ≤ miyamotoF1G h L η t := hS.centerIn_U_le_F1
  have hcomm : ∀ a ∈ CFSG.centerIn 𝓤, ∀ b ∈ CFSG.centerIn 𝓤, a * b = b * a :=
    fun a ha b hb => hS.F1_comm (hZF1 ha) (hZF1 hb)
  have hXA : prodFactorTwo ψ ≤ normalizer ((CFSG.centerIn 𝓤 : Subgroup G) : Set G) :=
    fun x hx => normalizer_le_normalizer_centerIn _ (hS.X2_le_normalizer_U hx)
  have hcard : Nat.card (CFSG.centerIn 𝓤) = (2 ^ (2 * f)) ^ 2 := by
    rw [hZ, ← pow_mul, ← pow_mul]
    ring_nf
  have hfix : CFSG.centerIn 𝓤 ⊓ centralizer (prodFactorTwo ψ : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    rw [← hS.F1_inf_centralizer_X2 hk hψt hZ]
    exact mem_inf.2 ⟨hZF1 (mem_inf.1 hz).1, (mem_inf.1 hz).2⟩
  have hSX : 𝓦 ⊓ prodFactorTwo ψ ≤ prodFactorTwo ψ := inf_le_right
  have hScard : Nat.card (𝓦 ⊓ prodFactorTwo ψ : Subgroup G) = Nat.card k := by
    rw [(hS.W_eq_sup (ψ := ψ) hk).2.2, Nat.card_eq_fintype_card, hk]
  have hfixS : Nat.card (CFSG.centerIn 𝓤 ⊓ centralizer ((𝓦 ⊓ prodFactorTwo ψ : Subgroup G) :
      Set G) : Subgroup G) = 2 ^ (2 * f) := by
    rw [hS.centerIn_U_inf_centralizer_W2 hk, hS.card_E, ← pow_mul, mul_comm]
  obtain ⟨htrans, hstab, hfaith⟩ := Common.natural_module_of_card hk'
    (Common.prodFactorTwoEquiv ψ) hcomm hXA hcard hfix hSX hScard hfixS
  refine ⟨htrans, fun e he he1 => hstab e ?_ he1, hfaith⟩
  rw [hS.centerIn_U_inf_centralizer_W2 hk]
  exact he

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
