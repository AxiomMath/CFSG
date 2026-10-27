module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoFour

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  mem_normalizer_sup card_sup_mul_card_inf_eq)
open scoped MatrixGroups Pointwise

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

local notation "𝓨" => CFSG.centerIn 𝓤 ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (miyamotoR1G h L η))) (CFSG.centerIn 𝓤)

local notation "𝓨t" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨

local notation "𝓚" => 𝓨t ⊔ prodFactorOne ψ

local notation "𝓦'" => miyamotoRG h L η t Q ⊓ 𝓚

theorem map_conj_t_RG (hS : Setting h L η t Q T) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (miyamotoRG h L η t Q) =
      miyamotoRG h L η t Q :=
  mem_normalizer_iff_map_conj_eq.1 hS.t_mem_normalizer_RG


theorem not_X1_le_centralizer_Yt [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    ¬ prodFactorOne ψ ≤ centralizer ((𝓨t : Subgroup G) : Set G) := by
  intro hC
  have h1 := hS.commutator_Yt_X1 hk hψA hψt hZ
  rw [commutator_eq_bot_iff_le_centralizer.2 (le_centralizer_iff.1 hC)] at h1
  apply hS.Y_ne_bot hZ
  have e := map_conj_map_conj_of_mul_self hS.t_mul_t (𝓨 : Subgroup G)
  rw [← h1, Subgroup.map_bot] at e
  exact e.symm

theorem K1'_inf_centralizer [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    𝓚 ⊓ centralizer ((𝓚 : Subgroup G) : Set G) = ⊥ := by
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hk, ← pow_mul, mul_comm])
  have h4 : 4 ≤ Nat.card k := by
    rw [Nat.card_eq_fintype_card, hk]
    have := hS.four_le
    nlinarith
  have : IsSimpleGroup SL(2, k) := Common.sl2_isSimpleGroup_of_charTwo h4
  have hX : IsSimpleGroup (prodFactorOne ψ) := (Common.prodFactorOneEquiv ψ).isSimpleGroup
  have hX1N := hS.X1_le_normalizer_Yt hψt
  have hnc := hS.not_X1_le_centralizer_Yt hk hψA hψt hZ
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨hzK, hzC⟩ := mem_inf.1 hz
  have e1 : ((𝓚 : Subgroup G) : Set G) =
      ((𝓨t : Subgroup G) : Set G) * (prodFactorOne ψ : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ hX1N
  have hz' : z ∈ ((𝓨t : Subgroup G) : Set G) * (prodFactorOne ψ : Set G) := by
    rw [← e1]; exact hzK
  obtain ⟨a, ha, x, hx, rfl⟩ := hz'
  have hxC : x ∈ centralizer ((𝓨t : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 : y * (a * x) = a * x * y := mem_centralizer_iff.1 hzC y (mem_sup_left hy)
    have h2 : a * y = y * a := hS.F1_comm (hS.Yt_le_F1 ha) (hS.Yt_le_F1 hy)
    calc y * x = a⁻¹ * (a * y) * x := by group
      _ = a⁻¹ * (y * a) * x := by rw [h2]
      _ = a⁻¹ * (y * (a * x)) := by group
      _ = a⁻¹ * (a * x * y) := by rw [h1]
      _ = x * y := by group
  set Cx : Subgroup (prodFactorOne ψ) :=
    (centralizer ((𝓨t : Subgroup G) : Set G)).subgroupOf (prodFactorOne ψ) with hCx
  have hCxN : Cx.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hCx, mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ normalizer (centralizer ((𝓨t : Subgroup G) : Set G) : Set G) :=
      mem_normalizer_centralizer (hX1N g.2)
    exact (mem_normalizer_iff.1 hg n).1 hn
  have hx1 : x = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Cx with h0 | htop
    · have : (⟨x, hx⟩ : prodFactorOne ψ) ∈ Cx := hxC
      rw [h0, mem_bot] at this
      exact congrArg Subtype.val this
    · exact absurd (fun y hy => (subgroupOf_eq_top.1 htop) hy) hnc
  subst hx1
  have hzC' : a ∈ centralizer ((𝓚 : Subgroup G) : Set G) := by simpa using hzC
  simp only [mul_one]
  set V₀ := (𝓨t : Subgroup G) ⊓ centralizer (prodFactorOne ψ : Set G) with hV₀
  have hKV : miyamotoF1G h L η t ⊔ prodFactorOne ψ ≤ normalizer (V₀ : Set G) :=
    sup_le (hS.le_normalizer_of_le_F1 (inf_le_left.trans hS.Yt_le_F1) le_rfl) fun x hx =>
      mem_normalizer_inf (hX1N hx) (mem_normalizer_centralizer (le_normalizer hx))
  rcases (hS.sec5_1_two hk hψA hψt hZ).2 V₀ inf_le_left hKV with h0 | h1
  · have : a ∈ V₀ := mem_inf.2 ⟨ha, centralizer_le
      (SetLike.coe_subset_coe.2 (le_sup_right : prodFactorOne ψ ≤ 𝓚)) hzC'⟩
    rwa [h0, mem_bot] at this
  · exfalso
    apply hnc
    rw [le_centralizer_iff, ← h1]
    exact inf_le_right

theorem sec5_2_one [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦' =
        miyamotoRG h L η t Q ⊓ (𝓨 ⊔ prodFactorTwo ψ) ∧
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦' ≤
        centralizer ((𝓦' : Subgroup G) : Set G) ∧
      𝓦' ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦' = ⊥ ∧
      miyamotoRG h L η t Q = 𝓦' ⊔ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦' ∧
      Nat.card (𝓦' : Subgroup G) = (2 ^ f) ^ 6 := by
  have hWt : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦' =
      miyamotoRG h L η t Q ⊓ (𝓨 ⊔ prodFactorTwo ψ) := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective, hS.map_conj_t_RG,
      hS.map_conj_t_K1' hψt]
  have hC : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦' ≤
      centralizer ((𝓦' : Subgroup G) : Set G) := by
    rw [hWt]
    exact (inf_le_right.trans (hS.K1't_le_centralizer hk hψA hψt)).trans
      (centralizer_le (SetLike.coe_subset_coe.2 inf_le_right))
  have hinf : 𝓦' ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦' = ⊥ := by
    rw [hWt, eq_bot_iff, ← hS.K1'_inf hk hψt]
    exact inf_le_inf inf_le_right inf_le_right
  have hYF1 : (𝓨 : Subgroup G) ≤ miyamotoF1G h L η t := inf_le_left.trans hS.centerIn_U_le_F1
  have hF1R : miyamotoF1G h L η t ≤ miyamotoRG h L η t Q :=
    le_sup_left.trans hS.P1_le_miyamotoRG
  have hR : miyamotoRG h L η t Q ≤ 𝓦' ⊔ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦' := by
    rw [hWt]
    intro r hr
    obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hr
    refine mul_mem ?_ ?_
    · rw [← (hS.W_eq_sup (ψ := ψ) hk).1] at hw
      have hle : (𝓦 ⊓ prodFactorOne ψ) ⊔ (𝓦 ⊓ prodFactorTwo ψ) ≤
          𝓦' ⊔ miyamotoRG h L η t Q ⊓ (𝓨 ⊔ prodFactorTwo ψ) :=
        sup_le (fun x hx => mem_sup_left (mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).1,
          mem_sup_right (mem_inf.1 hx).2⟩)) fun x hx => mem_sup_right
          (mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).1, mem_sup_right (mem_inf.1 hx).2⟩)
      exact hle hw
    · have hy' := (hS.sec5_1_one hk hψt hZ).2.1.le hy
      have hle : 𝓨 ⊔ 𝓨t ≤ 𝓦' ⊔ miyamotoRG h L η t Q ⊓ (𝓨 ⊔ prodFactorTwo ψ) :=
        sup_le (fun x hx => mem_sup_right (mem_inf.2 ⟨hF1R (hYF1 hx), mem_sup_left hx⟩))
          fun x hx => mem_sup_left (mem_inf.2 ⟨hF1R (hS.Yt_le_F1 hx), mem_sup_left hx⟩)
      exact hle hy'
  have hReq : miyamotoRG h L η t Q =
      𝓦' ⊔ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦' :=
    le_antisymm hR (sup_le inf_le_left (hWt ▸ inf_le_left))
  refine ⟨hWt, hC, hinf, hReq, ?_⟩
  have h1 := card_sup_mul_card_inf_eq (fun x hx => mem_normalizer_of_mem_centralizer' (hC hx))
  rw [hinf, card_bot, mul_one, ← hReq, hS.card_miyamotoRG,
    card_map_of_injective (MulAut.conj t).injective] at h1
  have h2 : (2 ^ f) ^ 12 = (2 ^ f) ^ 6 * (2 ^ f) ^ 6 := by ring
  rw [h2] at h1
  exact (Nat.mul_self_inj.1 h1.symm)

theorem RG_inf_centralizer_K1'_le [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    miyamotoRG h L η t Q ⊓ centralizer ((𝓚 : Subgroup G) : Set G) ≤
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦' := by
  obtain ⟨hWt, hC, -, hReq, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  intro r hr
  obtain ⟨hrR, hrC⟩ := mem_inf.1 hr
  rw [hReq] at hrR
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun x hx y hy => mem_centralizer_iff.1 (hC hy) x hx) hrR
  have hw'C : w' ∈ centralizer ((𝓚 : Subgroup G) : Set G) := by
    rw [hWt] at hw'
    exact hS.K1't_le_centralizer hk hψA hψt (mem_inf.1 hw').2
  have hwC : w ∈ centralizer ((𝓚 : Subgroup G) : Set G) := by
    have := mul_mem hrC (inv_mem hw'C)
    rwa [mul_inv_cancel_right] at this
  have hw1 : w = 1 := by
    have := mem_inf.2 ⟨(mem_inf.1 hw).2, hwC⟩
    rwa [hS.K1'_inf_centralizer hk hψA hψt hZ, mem_bot] at this
  rw [hw1, one_mul]
  exact hw'

theorem RG_le_normalizer_K1' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    miyamotoRG h L η t Q ≤ normalizer ((𝓚 : Subgroup G) : Set G) := by
  rw [← hS.commutator_K1 hk hψA hψt hZ]
  intro r hr
  have hrK : r ∈ normalizer ((miyamotoF1G h L η t ⊔ prodFactorOne ψ : Subgroup G) : Set G) := by
    obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hr
    refine mul_mem (mem_normalizer_sup (hS.normalizer_RG_le_normalizer_F1 ?_)
      (Common.le_normalizer_prodFactorOne ψ (hS.sec3_12_one.2.2.2.2.1 hw))) ?_
    · exact le_normalizer (mem_inf.1 hw).1
    · exact le_normalizer (mem_sup_left hy)
  exact mem_normalizer_commutator hrK hrK

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
