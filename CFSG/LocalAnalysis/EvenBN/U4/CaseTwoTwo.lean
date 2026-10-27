module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  card_sup_mul_card_inf_eq)
open scoped MatrixGroups commutatorElement Pointwise

theorem map_conj_map_conj_of_mul_self {G : Type*} [Group G] {t : G} (ht : t * t = 1)
    (H : Subgroup G) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t))
      (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) H) = H := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  ext x
  rw [mem_map_conj_iff, mem_map_conj_iff, hti]
  constructor
  · intro hx
    rwa [show t * (t * x * t) * t = (t * t) * x * (t * t) by group, ht, one_mul, mul_one] at hx
  · intro hx
    rwa [show t * (t * x * t) * t = (t * t) * x * (t * t) by group, ht, one_mul, mul_one]

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

theorem Yt_le_F1 (hS : Setting h L η t Q T) : 𝓨t ≤ miyamotoF1G h L η t := by
  rintro _ ⟨y, hy, rfl⟩
  exact (mem_normalizer_iff.1 hS.t_mem_normalizer_F1 y).1
    ((inf_le_left.trans hS.centerIn_U_le_F1) hy)


theorem commutator_X1 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) :
    ⁅prodFactorOne ψ, prodFactorOne ψ⁆ = prodFactorOne ψ := by
  have h4 : 4 ≤ Nat.card k := by
    rw [Nat.card_eq_fintype_card, hk]
    have := hS.four_le
    nlinarith
  have : Group.IsPerfect SL(2, k) :=
    LinearGroups.special_linear_dimension_two_perfect (Common.exists_finset_card_four h4)
  have : Group.IsPerfect (prodFactorOne ψ) :=
    Group.IsPerfect.ofSurjective (f := (Common.prodFactorOneEquiv ψ).symm.toMonoidHom)
      (Common.prodFactorOneEquiv ψ).symm.surjective
  exact Subgroup.isPerfect_iff.1 this


theorem X1_le_normalizer_Yt (hS : Setting h L η t Q T)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    prodFactorOne ψ ≤ normalizer ((𝓨t : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_map_conj (hS.X2_le_normalizer_Y (hS.t_conj_mem_X2 hψt hx))

theorem X2_le_centralizer_Yt [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    prodFactorTwo ψ ≤ centralizer ((𝓨t : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have hc := mem_centralizer_iff.1 (hS.X1_le_centralizer_Y hk hψA (hS.t_conj_mem_X1 hψt hx)) y hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc t * y * t⁻¹ * x = t * (y * (t⁻¹ * x * t)) * t⁻¹ := by group
    _ = t * ((t⁻¹ * x * t) * y) * t⁻¹ := by rw [hc]
    _ = x * (t * y * t⁻¹) := by group

theorem commutator_Yt_X1 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    ⁅𝓨t, prodFactorOne ψ⁆ = 𝓨t := by
  have hX1N := hS.X1_le_normalizer_Yt hψt
  have hVle : ⁅𝓨t, prodFactorOne ψ⁆ ≤ 𝓨t := by
    rw [commutator_le]
    intro y hy x hx
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc x]
    exact mul_mem hy ((mem_normalizer_iff.1 (hX1N hx) _).1 (inv_mem hy))
  have hKV : miyamotoF1G h L η t ⊔ prodFactorOne ψ ≤
      normalizer ((⁅𝓨t, prodFactorOne ψ⁆ : Subgroup G) : Set G) :=
    sup_le (hS.le_normalizer_of_le_F1 (hVle.trans hS.Yt_le_F1) le_rfl)
      fun x hx => mem_normalizer_commutator (hX1N hx) (le_normalizer hx)
  rcases (hS.sec5_1_two hk hψA hψt hZ).2 _ hVle hKV with h0 | h1
  · exfalso
    have hC : prodFactorOne ψ ≤ centralizer ((𝓨t : Subgroup G) : Set G) :=
      le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h0)
    apply hS.Y_ne_bot hZ
    rw [← hS.Y_inf_centralizer_X2 hk]
    refine (inf_eq_left.2 fun y hy => ?_).symm
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : t * x * t⁻¹ ∈ prodFactorOne ψ := by
      have := hS.t_conj_mem_X1 hψt hx
      rw [hS.t_inv] at this ⊢
      exact this
    have hc := mem_centralizer_iff.1 (hC hx') (t * y * t⁻¹) ⟨y, hy, rfl⟩
    calc x * y = t⁻¹ * ((t * x * t⁻¹) * (t * y * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * y * t⁻¹) * (t * x * t⁻¹)) * t := by rw [hc]
      _ = y * x := by group
  · exact h1

theorem commutator_K1' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    ⁅𝓨t ⊔ prodFactorOne ψ, 𝓨t ⊔ prodFactorOne ψ⁆ = 𝓨t ⊔ prodFactorOne ψ := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · calc 𝓨t = ⁅𝓨t, prodFactorOne ψ⁆ := (hS.commutator_Yt_X1 hk hψA hψt hZ).symm
      _ ≤ _ := commutator_mono le_sup_left le_sup_right
  · calc prodFactorOne ψ = ⁅prodFactorOne ψ, prodFactorOne ψ⁆ := (hS.commutator_X1 hk).symm
      _ ≤ _ := commutator_mono le_sup_right le_sup_right

theorem commutator_K1 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    ⁅miyamotoF1G h L η t ⊔ prodFactorOne ψ, miyamotoF1G h L η t ⊔ prodFactorOne ψ⁆ =
      𝓨t ⊔ prodFactorOne ψ := by
  have hK' := hS.commutator_K1' hk hψA hψt hZ
  have hK'K : 𝓨t ⊔ prodFactorOne ψ ≤ miyamotoF1G h L η t ⊔ prodFactorOne ψ :=
    sup_le_sup_right hS.Yt_le_F1 _
  refine le_antisymm ?_ (hK'.symm.le.trans (commutator_mono hK'K hK'K))
  have hF1 : miyamotoF1G h L η t = 𝓨 ⊔ 𝓨t := (hS.sec5_1_one hk hψt hZ).2.1
  have hYF1 : (𝓨 : Subgroup G) ≤ miyamotoF1G h L η t := inf_le_left.trans hS.centerIn_U_le_F1
  have hKY : 𝓨t ⊔ prodFactorOne ψ ≤ centralizer ((𝓨 : Subgroup G) : Set G) :=
    sup_le (fun x hx => mem_centralizer_iff.2 fun y hy => hS.F1_comm (hYF1 hy) (hS.Yt_le_F1 hx))
      (hS.X1_le_centralizer_Y hk hψA)
  have hc : ∀ y ∈ (𝓨 : Subgroup G), ∀ z ∈ 𝓨t ⊔ prodFactorOne ψ, y * z = z * y :=
    fun y hy z hz => (mem_centralizer_iff.1 (hKY hz) y hy)
  have hle : miyamotoF1G h L η t ⊔ prodFactorOne ψ ≤ 𝓨 ⊔ (𝓨t ⊔ prodFactorOne ψ) :=
    sup_le (hF1.le.trans (sup_le_sup_left le_sup_left _)) (le_sup_right.trans le_sup_right)
  refine (commutator_mono hle hle).trans ?_
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨y₁, hy₁, k₁, hk₁, rfl⟩ := exists_mul_of_mem_sup_of_commute hc ha
  obtain ⟨y₂, hy₂, k₂, hk₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hb
  rw [hc y₁ hy₁ k₁ hk₁, hc y₂ hy₂ k₂ hk₂, commutatorElement_mul_mul_eq_of_commute (hc y₁ hy₁ k₂ hk₂)
    (hS.F1_comm (hYF1 hy₁) (hYF1 hy₂)) ((hc y₂ hy₂ k₁ hk₁)), commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hk₁ hk₂) (inv_mem hk₁)) (inv_mem hk₂)

theorem map_conj_t_X1 (hS : Setting h L η t Q T)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (prodFactorOne ψ) = prodFactorTwo ψ := by
  refine le_antisymm ?_ fun x hx => ⟨t⁻¹ * x * t, hS.t_conj_mem_X1 hψt hx, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := hS.t_conj_mem_X2 hψt hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hS.t_inv] at this ⊢
    exact this
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_conj_t_K1' (hS : Setting h L η t Q T)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (𝓨t ⊔ prodFactorOne ψ) =
      𝓨 ⊔ prodFactorTwo ψ := by
  rw [Subgroup.map_sup, map_conj_map_conj_of_mul_self hS.t_mul_t, hS.map_conj_t_X1 hψt]

theorem K1'_inf [Fintype k] (hS : Setting h L η t Q T) (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    (𝓨t ⊔ prodFactorOne ψ) ⊓ (𝓨 ⊔ prodFactorTwo ψ) = ⊥ := by
  have hYF1 : (𝓨 : Subgroup G) ≤ miyamotoF1G h L η t := inf_le_left.trans hS.centerIn_U_le_F1
  have e1 : ((𝓨t ⊔ prodFactorOne ψ : Subgroup G) : Set G) =
      ((𝓨t : Subgroup G) : Set G) * (prodFactorOne ψ : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ (hS.X1_le_normalizer_Yt hψt)
  have e2 : ((𝓨 ⊔ prodFactorTwo ψ : Subgroup G) : Set G) =
      ((𝓨 : Subgroup G) : Set G) * (prodFactorTwo ψ : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ hS.X2_le_normalizer_Y
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨hz₁, hz₂⟩ := mem_inf.1 hz
  have hz₁' : z ∈ ((𝓨t : Subgroup G) : Set G) * (prodFactorOne ψ : Set G) := by
    rw [← e1]; exact hz₁
  have hz₂' : z ∈ ((𝓨 : Subgroup G) : Set G) * (prodFactorTwo ψ : Set G) := by
    rw [← e2]; exact hz₂
  obtain ⟨a, ha, x₁, hx₁, rfl⟩ := hz₁'
  obtain ⟨b, hb, x₂, hx₂, hab⟩ := hz₂'
  have hab' : a * x₁ = b * x₂ := hab.symm
  have hM : b⁻¹ * a = x₂ * x₁⁻¹ := by
    calc b⁻¹ * a = b⁻¹ * (a * x₁) * x₁⁻¹ := by group
      _ = b⁻¹ * (b * x₂) * x₁⁻¹ := by rw [hab']
      _ = x₂ * x₁⁻¹ := by group
  have hF : b⁻¹ * a ∈ miyamotoF1G h L η t := mul_mem (inv_mem (hYF1 hb)) (hS.Yt_le_F1 ha)
  have hC : b⁻¹ * a ∈ centralizer (miyamotoI1G h L η : Set G) := by
    rw [hM]
    exact hS.M1_le_centralizer_I1 (mul_mem (Common.prodFactorTwo_le ψ hx₂)
      (inv_mem (Common.prodFactorOne_le ψ hx₁)))
  have h1 : b⁻¹ * a = 1 := by
    have := mem_inf.2 ⟨hF, hC⟩
    rwa [hS.F1_inf_centralizer_I1, mem_bot] at this
  have hab' : a = b := (inv_mul_eq_one.1 h1).symm
  have hx : x₂ = x₁ := by rw [h1] at hM; exact (mul_inv_eq_one.1 hM.symm)
  subst hab' hx
  have ha1 : a = 1 := by
    have := mem_inf.2 ⟨hb, ha⟩
    rwa [hS.Y_inf_Y_t hk hψt, mem_bot] at this
  have hx1 : x₂ = 1 := by
    have := mem_inf.2 ⟨hx₁, hx₂⟩
    rwa [Common.prodFactorOne_inf_prodFactorTwo, mem_bot] at this
  simp only [ha1, hx1, mul_one]
  exact one_mem _

theorem K1't_le_centralizer [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    𝓨 ⊔ prodFactorTwo ψ ≤ centralizer ((𝓨t ⊔ prodFactorOne ψ : Subgroup G) : Set G) := by
  have hYF1 : (𝓨 : Subgroup G) ≤ miyamotoF1G h L η t := inf_le_left.trans hS.centerIn_U_le_F1
  refine sup_le (le_centralizer_iff.2 (sup_le (fun x hx => mem_centralizer_iff.2 fun y hy =>
    hS.F1_comm (hYF1 hy) (hS.Yt_le_F1 hx)) (hS.X1_le_centralizer_Y hk hψA)))
    (le_centralizer_iff.2 (sup_le (le_centralizer_iff.1 (hS.X2_le_centralizer_Yt hk hψA hψt))
      (Common.prodFactorOne_le_centralizer ψ)))

theorem sec5_1_three [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    ⁅miyamotoF1G h L η t ⊔ prodFactorOne ψ, miyamotoF1G h L η t ⊔ prodFactorOne ψ⁆ =
        𝓨t ⊔ prodFactorOne ψ ∧
      ⁅𝓨t ⊔ prodFactorOne ψ, 𝓨t ⊔ prodFactorOne ψ⁆ = 𝓨t ⊔ prodFactorOne ψ ∧
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (𝓨t ⊔ prodFactorOne ψ) =
        𝓨 ⊔ prodFactorTwo ψ ∧
      (𝓨t ⊔ prodFactorOne ψ) ⊔ (𝓨 ⊔ prodFactorTwo ψ) =
        miyamotoF1G h L η t ⊔ miyamotoM1G h L η t ∧
      (𝓨t ⊔ prodFactorOne ψ) ⊓ (𝓨 ⊔ prodFactorTwo ψ) = ⊥ ∧
      𝓨 ⊔ prodFactorTwo ψ ≤ centralizer ((𝓨t ⊔ prodFactorOne ψ : Subgroup G) : Set G) := by
  refine ⟨hS.commutator_K1 hk hψA hψt hZ, hS.commutator_K1' hk hψA hψt hZ,
    hS.map_conj_t_K1' hψt, ?_, hS.K1'_inf hk hψt, hS.K1't_le_centralizer hk hψA hψt⟩
  have hYF1 : (𝓨 : Subgroup G) ≤ miyamotoF1G h L η t := inf_le_left.trans hS.centerIn_U_le_F1
  refine le_antisymm (sup_le (sup_le (hS.Yt_le_F1.trans le_sup_left)
    ((Common.prodFactorOne_le ψ).trans le_sup_right)) (sup_le (hYF1.trans le_sup_left)
    ((Common.prodFactorTwo_le ψ).trans le_sup_right))) (sup_le ?_ ?_)
  · exact (hS.sec5_1_one hk hψt hZ).2.1.le.trans
      (sup_le (le_sup_left.trans le_sup_right) (le_sup_left.trans le_sup_left))
  · exact (Common.prodFactorOne_sup_prodFactorTwo ψ).ge.trans
      (sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right))

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
