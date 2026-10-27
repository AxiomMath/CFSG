module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoSix

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

local notation "𝓥" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)

theorem isCyclic_I2G (_hS : Setting h L η t Q T) : IsCyclic (miyamotoI2G h L η) := by
  have := h.finite
  have h1 : IsCyclic (miyamotoI2 h) := by
    rw [miyamotoI2]
    exact isCyclic_of_surjective _ (miyamotoI2Hom h).rangeRestrict_surjective
  have h2 : IsCyclic ((miyamotoI2 h).subgroupOf (gramSU h (miyamotoJ4 K))) :=
    isCyclic_of_surjective _ (subgroupOfEquivOfLe (miyamotoI2_le_SU h)).symm.surjective
  have h3 : IsCyclic (((miyamotoI2 h).subgroupOf (gramSU h (miyamotoJ4 K))).map
      η.symm.toMonoidHom) :=
    isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
  exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective L.subtype _)

theorem exists_I2_fpf (hS : Setting h L η t Q T) :
    ∃ i ∈ miyamotoI2G h L η,
      miyamotoF2G h L η t Q ⊓ centralizer ({i} : Set G) = ⊥ := by
  have := hS.isCyclic_I2G
  obtain ⟨i, hi⟩ := IsCyclic.exists_generator (α := miyamotoI2G h L η)
  refine ⟨i, i.2, eq_bot_iff.2 fun x hx => ?_⟩
  obtain ⟨hxF, hxC⟩ := mem_inf.1 hx
  rw [← hS.F2_inf_centralizer_I2]
  refine mem_inf.2 ⟨hxF, mem_centralizer_iff.2 fun y hy => ?_⟩
  obtain ⟨n, hn⟩ := hi ⟨y, hy⟩
  have hyn : y = (i : G) ^ n := by
    have := congrArg Subtype.val hn
    simp only [SubgroupClass.coe_zpow] at this
    exact this.symm
  rw [hyn]
  exact (Commute.zpow_left (mem_centralizer_singleton_iff.1 hxC).symm n).eq

theorem inv_mul_conj_mem_F2 (hS : Setting h L η t Q T) {r i : G}
    (hr : r ∈ miyamotoRG h L η t Q) (hi : i ∈ miyamotoI2G h L η) :
    r⁻¹ * (i * r * i⁻¹) ∈ miyamotoF2G h L η t Q := by
  have hVN : (𝓥 : Subgroup G) ≤ normalizer (miyamotoF2G h L η t Q : Set G) :=
    inf_le_left.trans hS.RG_le_normalizer_F2
  have e1 : ((miyamotoF2G h L η t Q ⊔ 𝓥 : Subgroup G) : Set G) =
      (miyamotoF2G h L η t Q : Set G) * ((𝓥 : Subgroup G) : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ hVN
  have hr' : r ∈ (miyamotoF2G h L η t Q : Set G) * ((𝓥 : Subgroup G) : Set G) := by
    rw [← e1, hS.F2_sup_V2]; exact hr
  obtain ⟨φ, hφ, v, hv, rfl⟩ := hr'
  have hiN : i ∈ normalizer (miyamotoF2G h L η t Q : Set G) := hS.I2N2_le_normalizer_F2
    (mem_sup_left hi)
  have hvi : i * v * i⁻¹ = v := by
    rw [mem_centralizer_iff.1 (mem_inf.1 hv).2 i hi, mul_inv_cancel_right]
  have h1 : φ⁻¹ * (i * φ * i⁻¹) ∈ miyamotoF2G h L η t Q :=
    mul_mem (inv_mem hφ) ((mem_normalizer_iff.1 hiN φ).1 hφ)
  have h2 : v⁻¹ * (φ⁻¹ * (i * φ * i⁻¹)) * v⁻¹⁻¹ ∈ miyamotoF2G h L η t Q :=
    (mem_normalizer_iff.1 (hVN (inv_mem hv)) _).1 h1
  have e2 : (fun x1 x2 => x1 * x2) φ v = φ * v := rfl
  rw [e2, show (φ * v)⁻¹ * (i * (φ * v) * i⁻¹) = v⁻¹ * (φ⁻¹ * (i * φ * i⁻¹)) * (i * v * i⁻¹) by
    group, hvi, ← inv_inv v]
  simpa using h2

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

local notation "𝓨" => CFSG.centerIn 𝓤 ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (miyamotoR1G h L η))) (CFSG.centerIn 𝓤)

local notation "𝓨t" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨

local notation "𝓚" => 𝓨t ⊔ prodFactorOne ψ

local notation "𝓦'" => miyamotoRG h L η t Q ⊓ 𝓚

local notation "𝓦'ᵗ" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦'

omit [Finite G] in
theorem mem_normalizer_map_conj_t {H : Subgroup G} {g : G} (hgt : g * t = t * g)
    (hg : g ∈ normalizer (H : Set G)) :
    g ∈ normalizer ((Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) H : Subgroup G) :
      Set G) := by
  refine mem_normalizer_map_conj ?_
  rw [show t⁻¹ * g * t = g by rw [mul_assoc, hgt, inv_mul_cancel_left]]
  exact hg


theorem IG_le_normalizer_K1' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    miyamotoIG h L η ≤ normalizer ((𝓚 : Subgroup G) : Set G) := by
  rw [← hS.commutator_K1 hk hψA hψt hZ]
  intro i hi
  have hK := mem_normalizer_sup (hS.IG_le_normalizer_F1 hi) (hS.IG_le_normalizer_X1 (ψ := ψ) hi)
  exact mem_normalizer_commutator hK hK

theorem IG_le_normalizer_W' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    miyamotoIG h L η ≤ normalizer ((𝓦' : Subgroup G) : Set G) ∧
      miyamotoIG h L η ≤ normalizer ((𝓦'ᵗ : Subgroup G) : Set G) := by
  have h1 : miyamotoIG h L η ≤ normalizer ((𝓦' : Subgroup G) : Set G) := fun i hi =>
    mem_normalizer_inf (hS.IG_le_normalizer_RG hi) (hS.IG_le_normalizer_K1' hk hψA hψt hZ hi)
  exact ⟨h1, fun i hi => mem_normalizer_map_conj_t
    (hS.comm_t_of_mem_L (miyamotoPull_le h L η _ hi)) (h1 hi)⟩

theorem sec5_2_two [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (𝓦' ⊓ miyamotoF2G h L η t Q) =
        𝓦'ᵗ ⊓ miyamotoF2G h L η t Q ∧
      miyamotoF2G h L η t Q = (𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ (𝓦'ᵗ ⊓ miyamotoF2G h L η t Q) ∧
      Nat.card (𝓦' ⊓ miyamotoF2G h L η t Q : Subgroup G) = (2 ^ f) ^ 5 := by
  obtain ⟨-, hC, hinf, hReq, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  obtain ⟨hIW, hIWt⟩ := hS.IG_le_normalizer_W' hk hψA hψt hZ
  have htF2 : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (miyamotoF2G h L η t Q) =
      miyamotoF2G h L η t Q :=
    mem_normalizer_iff_map_conj_eq.1 (mem_inf.1 hS.t_mem_H2).1
  have hW2t : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (𝓦' ⊓ miyamotoF2G h L η t Q) =
      𝓦'ᵗ ⊓ miyamotoF2G h L η t Q := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective, htF2]
  have hc : ∀ x ∈ (𝓦' : Subgroup G), ∀ y ∈ (𝓦'ᵗ : Subgroup G), x * y = y * x :=
    fun x hx y hy => mem_centralizer_iff.1 (hC hy) x hx
  obtain ⟨i, hiI2, hfp⟩ := hS.exists_I2_fpf
  have hiI : i ∈ miyamotoIG h L η := hS.tori_le_IG.2.2.2 hiI2
  have hiN : i ∈ normalizer (miyamotoF2G h L η t Q : Set G) :=
    hS.I2N2_le_normalizer_F2 (mem_sup_left hiI2)
  have hF2R : miyamotoF2G h L η t Q ≤ miyamotoRG h L η t Q := hS.F2_le_RG
  have hle : miyamotoF2G h L η t Q ≤
      (𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ (𝓦'ᵗ ⊓ miyamotoF2G h L η t Q) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := exists_eq_inv_mul_conj_of_inf_centralizer_eq_bot hiN hfp hx
    have hbR : b ∈ 𝓦' ⊔ 𝓦'ᵗ := hReq ▸ hF2R hb
    obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_of_mem_sup_of_commute hc hbR
    have ha : i * w * i⁻¹ ∈ (𝓦' : Subgroup G) := (mem_normalizer_iff.1 (hIW hiI) w).1 hw
    have ha' : i * w' * i⁻¹ ∈ (𝓦'ᵗ : Subgroup G) := (mem_normalizer_iff.1 (hIWt hiI) w').1 hw'
    have e : (w * w')⁻¹ * (i * (w * w') * i⁻¹) =
        (w⁻¹ * (i * w * i⁻¹)) * (w'⁻¹ * (i * w' * i⁻¹)) := by
      have h1 : w'⁻¹ * (w⁻¹ * (i * w * i⁻¹)) = (w⁻¹ * (i * w * i⁻¹)) * w'⁻¹ :=
        (hc _ (mul_mem (inv_mem hw) ha) _ (inv_mem hw')).symm
      calc (w * w')⁻¹ * (i * (w * w') * i⁻¹)
          = w'⁻¹ * (w⁻¹ * (i * w * i⁻¹)) * (i * w' * i⁻¹) := by group
        _ = (w⁻¹ * (i * w * i⁻¹)) * w'⁻¹ * (i * w' * i⁻¹) := by rw [h1]
        _ = (w⁻¹ * (i * w * i⁻¹)) * (w'⁻¹ * (i * w' * i⁻¹)) := by group
    rw [e]
    refine mul_mem (mem_sup_left (mem_inf.2 ⟨mul_mem (inv_mem hw) ha, ?_⟩))
      (mem_sup_right (mem_inf.2 ⟨mul_mem (inv_mem hw') ha', ?_⟩))
    · exact hS.inv_mul_conj_mem_F2 (mem_inf.1 hw).1 hiI2
    · exact hS.inv_mul_conj_mem_F2 (hReq.symm ▸ mem_sup_right hw' :
        w' ∈ miyamotoRG h L η t Q) hiI2
  have hF2eq : miyamotoF2G h L η t Q =
      (𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ (𝓦'ᵗ ⊓ miyamotoF2G h L η t Q) :=
    le_antisymm hle (sup_le inf_le_right inf_le_right)
  refine ⟨hW2t, hF2eq, ?_⟩
  have hN : 𝓦'ᵗ ⊓ miyamotoF2G h L η t Q ≤
      normalizer ((𝓦' ⊓ miyamotoF2G h L η t Q : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_of_mem_centralizer' (centralizer_le
      (SetLike.coe_subset_coe.2 inf_le_left) (hC (mem_inf.1 hy).1))
  have h1 := card_sup_mul_card_inf_eq hN
  have hinf2 : (𝓦' ⊓ miyamotoF2G h L η t Q) ⊓ (𝓦'ᵗ ⊓ miyamotoF2G h L η t Q) = ⊥ :=
    eq_bot_iff.2 (hinf ▸ inf_le_inf inf_le_left inf_le_left)
  rw [hinf2, card_bot, mul_one, ← hF2eq, hS.card_F2, ← hW2t,
    card_map_of_injective (MulAut.conj t).injective] at h1
  have h2 : (2 ^ f) ^ 10 = (2 ^ f) ^ 5 * (2 ^ f) ^ 5 := by ring
  rw [h2] at h1
  exact Nat.mul_self_inj.1 h1.symm

theorem V2_eq_sup_W' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    (𝓥 : Subgroup G) = (𝓥 ⊓ 𝓦') ⊔ (𝓥 ⊓ 𝓦'ᵗ) := by
  obtain ⟨-, hC, hinf, hReq, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  obtain ⟨hIW, hIWt⟩ := hS.IG_le_normalizer_W' hk hψA hψt hZ
  have hc : ∀ x ∈ (𝓦' : Subgroup G), ∀ y ∈ (𝓦'ᵗ : Subgroup G), x * y = y * x :=
    fun x hx y hy => mem_centralizer_iff.1 (hC hy) x hx
  refine le_antisymm (fun v hv => ?_) (sup_le inf_le_left inf_le_left)
  obtain ⟨hvR, hvC⟩ := mem_inf.1 hv
  have hvR' : v ∈ 𝓦' ⊔ 𝓦'ᵗ := hReq ▸ hvR
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_of_mem_sup_of_commute hc hvR'
  have hwR : w ∈ miyamotoRG h L η t Q := (mem_inf.1 hw).1
  have hw'R : w' ∈ miyamotoRG h L η t Q := hReq.symm ▸ mem_sup_right hw'
  have key : ∀ i ∈ miyamotoI2G h L η, i * w * i⁻¹ = w ∧ i * w' * i⁻¹ = w' := by
    intro i hi
    have hiI : i ∈ miyamotoIG h L η := hS.tori_le_IG.2.2.2 hi
    have ha : i * w * i⁻¹ ∈ (𝓦' : Subgroup G) := (mem_normalizer_iff.1 (hIW hiI) w).1 hw
    have ha' : i * w' * i⁻¹ ∈ (𝓦'ᵗ : Subgroup G) := (mem_normalizer_iff.1 (hIWt hiI) w').1 hw'
    have hfix : (i * w * i⁻¹) * (i * w' * i⁻¹) = w * w' := by
      rw [show (i * w * i⁻¹) * (i * w' * i⁻¹) = i * (w * w') * i⁻¹ by group,
        mem_centralizer_iff.1 hvC i hi, mul_inv_cancel_right]
    have e : w⁻¹ * (i * w * i⁻¹) = w' * (i * w' * i⁻¹)⁻¹ := by
      calc w⁻¹ * (i * w * i⁻¹) = w⁻¹ * ((i * w * i⁻¹) * (i * w' * i⁻¹)) * (i * w' * i⁻¹)⁻¹ := by
            group
        _ = w' * (i * w' * i⁻¹)⁻¹ := by rw [hfix]; group
    have h1 : w⁻¹ * (i * w * i⁻¹) ∈ 𝓦' ⊓ 𝓦'ᵗ :=
      mem_inf.2 ⟨mul_mem (inv_mem hw) ha, e ▸ mul_mem hw' (inv_mem ha')⟩
    rw [hinf, mem_bot] at h1
    have h2 : i * w * i⁻¹ = w := by
      calc i * w * i⁻¹ = w * (w⁻¹ * (i * w * i⁻¹)) := by group
        _ = w := by rw [h1, mul_one]
    refine ⟨h2, ?_⟩
    rw [h1] at e
    calc i * w' * i⁻¹ = (w' * (i * w' * i⁻¹)⁻¹)⁻¹ * w' := by group
      _ = w' := by rw [← e, inv_one, one_mul]
  have hwC : w ∈ centralizer (miyamotoI2G h L η : Set G) := mem_centralizer_iff.2 fun i hi => by
    have := (key i hi).1
    calc i * w = i * w * i⁻¹ * i := by group
      _ = w * i := by rw [this]
  have hw'C : w' ∈ centralizer (miyamotoI2G h L η : Set G) := mem_centralizer_iff.2 fun i hi => by
    have := (key i hi).2
    calc i * w' = i * w' * i⁻¹ * i := by group
      _ = w' * i := by rw [this]
  exact mul_mem (mem_sup_left (mem_inf.2 ⟨mem_inf.2 ⟨hwR, hwC⟩, hw⟩))
    (mem_sup_right (mem_inf.2 ⟨mem_inf.2 ⟨hw'R, hw'C⟩, hw'⟩))

theorem V2_eq_sup_Y (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂] [Fintype k₂]
    (hk₂ : Fintype.card k₂ = 2 ^ f) (ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)) :
    (𝓥 : Subgroup G) = (𝓥 ⊓ prodFactorOne ψ₂) ⊔ (𝓥 ⊓ prodFactorTwo ψ₂) ∧
      Nat.card (𝓥 ⊓ prodFactorOne ψ₂ : Subgroup G) = 2 ^ f ∧
      Nat.card (𝓥 ⊓ prodFactorTwo ψ₂ : Subgroup G) = 2 ^ f := by
  obtain ⟨-, -, -, -, hVM, -, -, -⟩ := hS.sec3_12_two
  have hk₂' : Nat.card k₂ = 2 ^ f := by rw [Nat.card_eq_fintype_card, hk₂]
  have hf := hS.two_le
  have h1 := card_le_card_inf_prodFactorOne_mul ψ₂ hk₂' (by omega) hVM hS.isPGroup_V2
  have h2 := card_le_card_inf_prodFactorTwo_mul ψ₂ hk₂' (by omega) hVM hS.isPGroup_V2
  rw [hS.card_V2, hk₂'] at h1 h2
  have hN : 𝓥 ⊓ prodFactorTwo ψ₂ ≤
      normalizer ((𝓥 ⊓ prodFactorOne ψ₂ : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_of_mem_centralizer' (centralizer_le (SetLike.coe_subset_coe.2 inf_le_right)
      (Common.prodFactorTwo_le_centralizer ψ₂ (mem_inf.1 hy).2))
  have h3 := card_sup_mul_card_inf_eq hN
  have hinf : (𝓥 ⊓ prodFactorOne ψ₂) ⊓ (𝓥 ⊓ prodFactorTwo ψ₂) = ⊥ :=
    eq_bot_iff.2 ((Common.prodFactorOne_inf_prodFactorTwo ψ₂) ▸ inf_le_inf inf_le_right
      inf_le_right)
  rw [hinf, card_bot, mul_one] at h3
  have hle : (𝓥 ⊓ prodFactorOne ψ₂) ⊔ (𝓥 ⊓ prodFactorTwo ψ₂) ≤ 𝓥 :=
    sup_le inf_le_left inf_le_left
  have h4 := card_le_of_le hle
  rw [h3, hS.card_V2] at h4
  set a := Nat.card (𝓥 ⊓ prodFactorOne ψ₂ : Subgroup G)
  set b := Nat.card (𝓥 ⊓ prodFactorTwo ψ₂ : Subgroup G)
  have hq : 0 < 2 ^ f := by positivity
  have ha : a = 2 ^ f := by
    refine le_antisymm ?_ (Nat.le_of_mul_le_mul_right (by nlinarith) hq)
    nlinarith
  have hb : b = 2 ^ f := by
    refine le_antisymm ?_ (Nat.le_of_mul_le_mul_right (by nlinarith) hq)
    nlinarith
  refine ⟨(eq_of_le_of_card_ge hle ?_).symm, ha, hb⟩
  rw [h3, hS.card_V2, ha, hb, sq]

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
