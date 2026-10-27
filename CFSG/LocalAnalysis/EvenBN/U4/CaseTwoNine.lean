module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoEight
public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  mem_normalizer_sup card_sup_mul_card_inf_eq)
open scoped MatrixGroups Pointwise commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem commutator_inf_eq_bot_of_central [Finite G] {p : ℕ} [Fact p.Prime]
    {H V S W : Subgroup G} (hVH : V ≤ H) (hHV : H ≤ centralizer (V : Set G))
    (hVp : IsPGroup p V) (hSH : S ≤ H) (hSp : IsPGroup p S) (hidx : ¬ p ∣ S.relIndex H)
    (hWS : W ≤ S) (hVW : V ⊓ W = ⊥) (hVWS : V ⊔ W = S) :
    ⁅H, H⁆ ⊓ V = ⊥ := by
  have hcent : ∀ v : H, (v : G) ∈ V → ∀ x : H, v * x = x * v := fun v hv x =>
    Subtype.ext (mem_centralizer_iff.1 (hHV x.2) v hv)
  set V' : Subgroup H := V.subgroupOf H with hV'
  have hV'n : V'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have e : g * n * g⁻¹ = n := by
      rw [← hcent n (mem_subgroupOf.1 hn) g, mul_inv_cancel_right]
    rw [e]
    exact hn
  have hV'c : IsMulCommutative V' :=
    ⟨⟨fun a b => Subtype.ext (hcent a (mem_subgroupOf.1 a.2) b)⟩⟩
  have hV'p : IsPGroup p V' := hVp.comap_subtype
  have hS'p : IsPGroup p (S.subgroupOf H) := hSp.comap_subtype
  have hS'idx : ¬ p ∣ (S.subgroupOf H).index := hidx
  set P : Sylow p H := hS'p.toSylow hS'idx with hP
  have hPS : (P : Subgroup H) = S.subgroupOf H := IsPGroup.toSylow_coe hS'p hS'idx
  have hsplit : ∃ K : Subgroup H, K ≤ P ∧ V' ⊓ K = ⊥ ∧ V' ⊔ K = P := by
    refine ⟨W.subgroupOf H, ?_, ?_, ?_⟩
    · rw [hPS]
      intro x hx
      exact mem_subgroupOf.2 (hWS (mem_subgroupOf.1 hx))
    · refine eq_bot_iff.2 fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
      have : (x : G) ∈ V ⊓ W := mem_inf.2 ⟨mem_subgroupOf.1 hx1, mem_subgroupOf.1 hx2⟩
      rw [hVW, mem_bot] at this
      exact (mem_bot).2 (Subtype.ext this)
    · rw [hPS, ← hVWS, Subgroup.subgroupOf_sup hVH (hWS.trans hSH)]
  obtain ⟨K, hVK, hVKt⟩ := (CFSG.Quasithin.gaschutz hV'p P).2 hsplit
  have hc1 : ∀ c x y : H, (∀ z : H, c * z = z * c) → ⁅c * x, y⁆ = ⁅x, y⁆ := by
    intro c x y hc
    have e : c * (x * y * x⁻¹) * c⁻¹ = x * y * x⁻¹ := by
      rw [hc (x * y * x⁻¹), mul_inv_cancel_right]
    calc ⁅c * x, y⁆ = c * (x * y * x⁻¹) * c⁻¹ * y⁻¹ := by
          rw [commutatorElement_def]; group
      _ = ⁅x, y⁆ := by rw [e, commutatorElement_def]
  have hc2 : ∀ c x y : H, (∀ z : H, c * z = z * c) → ⁅x, c * y⁆ = ⁅x, y⁆ := by
    intro c x y hc
    rw [← commutatorElement_inv, hc1 c y x hc, commutatorElement_inv]
  have hcomm : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    have ha : a ∈ ((V' ⊔ K : Subgroup H) : Set H) := by rw [hVKt]; trivial
    have hb : b ∈ ((V' ⊔ K : Subgroup H) : Set H) := by rw [hVKt]; trivial
    rw [Subgroup.normal_mul] at ha hb
    obtain ⟨v, hv, k, hk, rfl⟩ := ha
    obtain ⟨v', hv', k', hk', rfl⟩ := hb
    rw [hc1 v k _ (hcent v (mem_subgroupOf.1 hv)), hc2 v' k k' (hcent v' (mem_subgroupOf.1 hv')),
      commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hk hk') (inv_mem hk)) (inv_mem hk')
  have hmap : Subgroup.map H.subtype ⁅(⊤ : Subgroup H), ⊤⁆ = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxc, hxV⟩ := mem_inf.1 hx
  rw [← hmap] at hxc
  obtain ⟨a, ha, rfl⟩ := hxc
  have : a ∈ V' ⊓ K := mem_inf.2 ⟨mem_subgroupOf.2 hxV, hcomm ha⟩
  rw [hVK, mem_bot] at this
  rw [this, map_one]
  exact one_mem _

theorem exists_eq_mul_conj_of_mem_sup {X : Subgroup G} {t : G} (ht : t * t = 1)
    (hc : ∀ x ∈ X, ∀ y ∈ X.map (MulAut.conj t).toMonoidHom, x * y = y * x)
    (hinf : X ⊓ X.map (MulAut.conj t).toMonoidHom = ⊥) {a : G}
    (ha : a ∈ X ⊔ X.map (MulAut.conj t).toMonoidHom) (hat : t * a = a * t) :
    ∃ x ∈ X, a = x * (t * x * t) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hc ha
  have hy' : t * y * t ∈ X := by
    have := mem_map_conj_iff.1 hy
    rwa [hti] at this
  have hxt : t * x * t ∈ X.map (MulAut.conj t).toMonoidHom := by
    rw [mem_map_conj_iff, hti]
    have e : t * (t * x * t) * t = x := by
      calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [ht, one_mul, mul_one]
    rw [e]
    exact hx
  have h1 : (t * x * t) * (t * y * t) = t * (x * y * t) := by
    calc (t * x * t) * (t * y * t) = t * x * (t * t) * y * t := by group
      _ = t * (x * y * t) := by rw [ht, mul_one]; group
  have h2 : t * (x * y * t) = x * y := by
    rw [← hat, ← mul_assoc, ht, one_mul]
  have e2 : x * y = (t * y * t) * (t * x * t) := by
    rw [← h2, ← h1]
    exact (hc _ hy' _ hxt).symm
  have hm : (t * y * t)⁻¹ * x ∈ X ⊓ X.map (MulAut.conj t).toMonoidHom := by
    refine mem_inf.2 ⟨mul_mem (inv_mem hy') hx, ?_⟩
    have e : (t * y * t)⁻¹ * x = (t * x * t) * y⁻¹ := by
      calc (t * y * t)⁻¹ * x = (t * y * t)⁻¹ * (x * y) * y⁻¹ := by group
        _ = (t * y * t)⁻¹ * ((t * y * t) * (t * x * t)) * y⁻¹ := by rw [← e2]
        _ = (t * x * t) * y⁻¹ := by group
    rw [e]
    exact mul_mem hxt (inv_mem hy)
  rw [hinf, mem_bot] at hm
  have hxy : x = t * y * t := (inv_mul_eq_one.1 hm).symm
  have hyx : y = t * x * t := by
    rw [hxy]
    calc y = (t * t) * y * (t * t) := by rw [ht, one_mul, mul_one]
      _ = t * (t * y * t) * t := by group
  exact ⟨x, hx, by rw [← hyx]⟩

end Generic

section Model

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem mem_miyamotoZ_of_IN2_commutator {β : (h.fixedField)ˣ} (hβ : β ≠ 1)
    {z : GL (Fin 4) K} (hz : z ∈ miyamotoA2 h)
    (hc : (miyamotoIHom h (1, Units.map h.fixedField.subtype.toMonoidHom β))⁻¹ * z *
      miyamotoIHom h (1, Units.map h.fixedField.subtype.toMonoidHom β) * z⁻¹ ∈ miyamotoZ h) :
    z ∈ miyamotoZ h := by
  obtain ⟨a, c, d, hd, rfl⟩ := (mem_A2 h).1 hz
  set b : Kˣ := Units.map h.fixedField.subtype.toMonoidHom β with hb
  have hbb : h.bar (b : K) = b := (h.mem_fixedField).1 (β : h.fixedField).2
  have hb1 : (b : K) ≠ 1 := by
    intro e
    apply hβ
    exact Units.ext (Subtype.ext e)
  have hconj : (miyamotoIHom h (1, b))⁻¹ * miyamotoXGL h a 0 c d * miyamotoIHom h (1, b) =
      miyamotoXGL h ((b : K)⁻¹ * a) 0 ((b : K) * c) d := by
    rw [miyamotoIHom_conj, miyamotoXGL_inj]
    refine ⟨by simp, by simp, by simp [hbb], by simp⟩
  rw [hconj, miyamotoXGL_inv h (map_zero _), miyamotoXGL_mul h (map_zero _)] at hc
  obtain ⟨d₀, -, e⟩ := hc
  rw [miyamotoXGL_inj] at e
  obtain ⟨ea, -, ec, -⟩ := e
  simp only [zero_mul, add_zero] at ea ec
  have ha0 : a = 0 := by
    have h1 : ((b : K)⁻¹ + 1) * a = 0 := by rw [add_mul, one_mul]; exact ea
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exfalso
      apply hb1
      have h3 : (b : K)⁻¹ = 1 := by
        rw [eq_neg_of_add_eq_zero_left h2, CharTwo.neg_eq]
      exact inv_eq_one.1 h3
    · exact h2
  have hc0 : c = 0 := by
    have h1 : ((b : K) + 1) * c = 0 := by rw [add_mul, one_mul]; exact ec
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exfalso
      apply hb1
      rw [eq_neg_of_add_eq_zero_left h2, CharTwo.neg_eq]
    · exact h2
  subst ha0 hc0
  refine ⟨d, ?_, rfl⟩
  simp only [mul_zero, add_zero, map_zero] at hd
  rw [eq_neg_of_add_eq_zero_right hd, CharTwo.neg_eq]

end Model

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem mem_ZG_of_IN2_commutator (_hS : Setting h L η t Q T) {β : (h.fixedField)ˣ}
    (hβ : β ≠ 1) {z : G} (hz : z ∈ miyamotoA2G h L η)
    (hc : (miyamotoIN2Hom h L η β)⁻¹ * z * miyamotoIN2Hom h L η β * z⁻¹ ∈ miyamotoZG h L η) :
    z ∈ miyamotoZG h L η := by
  have : CharP K 2 := h.charP
  obtain ⟨y, hy, rfl⟩ := (mem_miyamotoPull h L η).1 hz
  have e : (miyamotoIN2Hom h L η β)⁻¹ * ((η.symm y : L) : G) * miyamotoIN2Hom h L η β *
      ((η.symm y : L) : G)⁻¹ = ((η.symm ((miyamotoIN2HomSU h β)⁻¹ * y *
        miyamotoIN2HomSU h β * y⁻¹) : L) : G) := by
    show ((η.symm (miyamotoIN2HomSU h β) : L) : G)⁻¹ * ((η.symm y : L) : G) *
      ((η.symm (miyamotoIN2HomSU h β) : L) : G) * ((η.symm y : L) : G)⁻¹ = _
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e, symm_mem_miyamotoPull_iff] at hc
  have hc' : (miyamotoIHom h (1, Units.map h.fixedField.subtype.toMonoidHom β))⁻¹ *
      (y : GL (Fin 4) K) * miyamotoIHom h (1, Units.map h.fixedField.subtype.toMonoidHom β) *
      (y : GL (Fin 4) K)⁻¹ ∈ miyamotoZ h := by
    rw [← coe_miyamotoIN2HomSU]
    exact hc
  exact (symm_mem_miyamotoPull_iff h L η).2 (mem_miyamotoZ_of_IN2_commutator h hβ hy hc')

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


theorem E_le_W2_sup_E2 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    miyamotoEG h L η Q ≤ 𝓦₂ ⊔ 𝓔₂ := by
  obtain ⟨-, hC, -, -, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  obtain ⟨-, hF2, -⟩ := hS.sec5_2_two hk hψA hψt hZ
  have hEF2 : miyamotoEG h L η Q ≤ miyamotoF2G h L η t Q := hS.E_le_F.trans hS.F_le_F2
  have hc : ∀ x ∈ 𝓦₂, ∀ y ∈ 𝓦'ᵗ ⊓ miyamotoF2G h L η t Q, x * y = y * x :=
    fun x hx y hy => mem_centralizer_iff.1 (hC (mem_inf.1 hy).1) x (mem_inf.1 hx).1
  intro e he
  have heF : e ∈ 𝓦₂ ⊔ (𝓦'ᵗ ⊓ miyamotoF2G h L η t Q) := hF2 ▸ hEF2 he
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hc heF
  have hZ2 : a * b ∈ CFSG.centerIn (miyamotoF2G h L η t Q) := by
    rw [hS.centerIn_F2]
    exact he
  have hab : ∀ z ∈ miyamotoF2G h L η t Q, z * (a * b) = (a * b) * z :=
    fun z hz => mem_centralizer_iff.1 (mem_inf.1 hZ2).2 z hz
  have hbE : b ∈ miyamotoEG h L η Q := by
    rw [← hS.centerIn_F2]
    refine mem_inf.2 ⟨(mem_inf.1 hb).2, mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨c, hc', d, hd, rfl⟩ := exists_mul_of_mem_sup_of_commute hc (hF2 ▸ hy)
    have h1 : c * b = b * c := hc c hc' b hb
    have h2 : d * (a * b) = (a * b) * d := hab d (mem_inf.1 hd).2
    have h3 : a * d = d * a := hc a ha d hd
    have h4 : d * b = b * d := by
      have : a * (d * b) = a * (b * d) := by
        calc a * (d * b) = (a * d) * b := by group
          _ = (d * a) * b := by rw [h3]
          _ = d * (a * b) := by group
          _ = (a * b) * d := h2
          _ = a * (b * d) := by group
      exact mul_left_cancel this
    calc c * d * b = c * (d * b) := by group
      _ = c * (b * d) := by rw [h4]
      _ = (c * b) * d := by group
      _ = (b * c) * d := by rw [h1]
      _ = b * (c * d) := by group
  exact mul_mem (mem_sup_left ha) (mem_sup_right (mem_inf.2 ⟨hbE, (mem_inf.1 hb).1⟩))

theorem W2_sup_E_eq [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    𝓦₂ ⊔ miyamotoEG h L η Q = 𝓦₂ ⊔ 𝓔₂ :=
  le_antisymm (sup_le le_sup_left (hS.E_le_W2_sup_E2 hk hψA hψt hZ))
    (sup_le_sup_left inf_le_left _)

theorem le_centralizer_E2 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] (ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)) :
    (𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ prodFactorOne ψ₂ ≤ centralizer ((𝓔₂ : Subgroup G) : Set G) := by
  obtain ⟨-, hC, -, -, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  have hEF2 : miyamotoEG h L η Q ≤ miyamotoF2G h L η t Q := hS.E_le_F.trans hS.F_le_F2
  refine sup_le (sup_le (fun w hw => ?_) (fun x hx => ?_)) (fun y hy => ?_)
  · exact mem_centralizer_iff.2 fun e he =>
      (mem_centralizer_iff.1 (hC (mem_inf.1 he).2) w (mem_inf.1 hw).1).symm
  · rw [← hS.centerIn_F2] at hx
    exact mem_centralizer_iff.2 fun e he =>
      mem_centralizer_iff.1 (mem_inf.1 hx).2 e (hEF2 (mem_inf.1 he).1)
  · exact mem_centralizer_iff.2 fun e he =>
      mem_centralizer_iff.1 (hS.M2G_le_centralizer_E (Common.prodFactorOne_le ψ₂ hy)) e
        (mem_inf.1 he).1

theorem F2_inf_M2 (hS : Setting h L η t Q T) :
    miyamotoF2G h L η t Q ⊓ miyamotoM2G h L η t Q = ⊥ :=
  eq_bot_iff.2 fun _ hx => hS.F2_inf_centralizer_I2 ▸
    mem_inf.2 ⟨(mem_inf.1 hx).1, (mem_inf.1 (hS.sec3_12_two.1 (mem_inf.1 hx).2)).2⟩

theorem not_two_dvd_relIndex [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    (ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)) :
    ¬ 2 ∣ ((𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ (𝓥 ⊓ prodFactorOne ψ₂)).relIndex
      ((𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ prodFactorOne ψ₂) := by
  set X := 𝓦₂ ⊔ miyamotoEG h L η Q with hX
  have hN : miyamotoM2G h L η t Q ≤ normalizer (X : Set G) :=
    hS.M2_le_normalizer_W2E hk hψA hψt hZ
  have hY1M := Common.prodFactorOne_le ψ₂
  have hXF2 : X ≤ miyamotoF2G h L η t Q := sup_le inf_le_right (hS.E_le_F.trans hS.F_le_F2)
  have hinf1 : X ⊓ prodFactorOne ψ₂ = ⊥ :=
    eq_bot_iff.2 (hS.F2_inf_M2 ▸ inf_le_inf hXF2 hY1M)
  have hinf2 : X ⊓ (𝓥 ⊓ prodFactorOne ψ₂) = ⊥ :=
    eq_bot_iff.2 (hinf1 ▸ inf_le_inf_left _ inf_le_right)
  have h1 := card_sup_mul_card_inf_eq (A := X) (B := prodFactorOne ψ₂) fun y hy => hN (hY1M hy)
  have h2 := card_sup_mul_card_inf_eq (A := X) (B := 𝓥 ⊓ prodFactorOne ψ₂) fun y hy =>
    hN (hY1M (mem_inf.1 hy).2)
  rw [hinf1, card_bot, mul_one] at h1
  rw [hinf2, card_bot, mul_one, (hS.V2_eq_sup_Y hk₂ ψ₂).2.1] at h2
  have hcardY : Nat.card (prodFactorOne ψ₂) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr (Common.prodFactorOneEquiv ψ₂).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card, hk₂]
  have hle : X ⊔ (𝓥 ⊓ prodFactorOne ψ₂) ≤ X ⊔ prodFactorOne ψ₂ :=
    sup_le_sup_left inf_le_right _
  have h3 := Subgroup.relIndex_mul_card (H := X ⊔ (𝓥 ⊓ prodFactorOne ψ₂))
    (K := X ⊔ prodFactorOne ψ₂)
  rw [inf_eq_left.2 hle, h2, h1, hcardY] at h3
  have hX0 : 0 < Nat.card X := Nat.card_pos
  have hq0 : 0 < 2 ^ f := by positivity
  have hr : (X ⊔ (𝓥 ⊓ prodFactorOne ψ₂)).relIndex (X ⊔ prodFactorOne ψ₂) =
      (2 ^ f) ^ 2 - 1 := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hX0 hq0) ?_
    rw [h3]
    ring
  rw [hr]
  have hev : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by have := hS.two_le; omega)) two_ne_zero
  have hpos : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ hq0
  generalize (2 ^ f) ^ 2 = n at hev hpos ⊢
  omega

theorem commutator_inf_E2 [Fintype k] (hS : Setting h L η t Q T)
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
    ⁅(𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ prodFactorOne ψ₂,
      (𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ prodFactorOne ψ₂⁆ ⊓ 𝓔₂ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWt, -, hinf, -, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  have hW' := hS.W'_eq_sup hk hψA hψt hZ hk₂ hψα₂ hj hj1 hjC hjY
  have hXE := hS.W2_sup_E_eq hk hψA hψt hZ
  have hR2 := hS.isPGroup_RG
  have hWtR : 𝓦'ᵗ ≤ miyamotoRG h L η t Q := hWt.le.trans inf_le_left
  have hXR : 𝓦₂ ⊔ miyamotoEG h L η Q ≤ miyamotoRG h L η t Q :=
    sup_le (inf_le_right.trans hS.F2_le_RG) (hS.E_le_F.trans (hS.F_le_F2.trans hS.F2_le_RG))
  have hE2W : 𝓔₂ ≤ (𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ (𝓥 ⊓ prodFactorOne ψ₂) :=
    (inf_le_left.trans le_sup_right).trans le_sup_left
  have hVH : 𝓔₂ ≤ (𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ prodFactorOne ψ₂ :=
    (inf_le_left.trans le_sup_right).trans le_sup_left
  have hVp : IsPGroup 2 (𝓔₂ : Subgroup G) := hR2.to_le (inf_le_right.trans hWtR)
  have hSH : (𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ (𝓥 ⊓ prodFactorOne ψ₂) ≤
      (𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ prodFactorOne ψ₂ := sup_le_sup_left inf_le_right _
  have hSp : IsPGroup 2
      ((𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ (𝓥 ⊓ prodFactorOne ψ₂) : Subgroup G) :=
    hR2.to_le (sup_le hXR (inf_le_left.trans inf_le_left))
  have hWS : 𝓦' ≤ (𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ (𝓥 ⊓ prodFactorOne ψ₂) :=
    hW'.le.trans (sup_le_sup_right le_sup_left _)
  have hVW : 𝓔₂ ⊓ 𝓦' = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rw [← hinf]
    exact mem_inf.2 ⟨(mem_inf.1 hx).2, (mem_inf.1 (mem_inf.1 hx).1).2⟩
  have hVWS : 𝓔₂ ⊔ 𝓦' = (𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ (𝓥 ⊓ prodFactorOne ψ₂) := by
    refine le_antisymm (sup_le hE2W hWS) (sup_le (sup_le ?_ ?_) ?_)
    · exact inf_le_left.trans le_sup_right
    · exact (hS.E_le_W2_sup_E2 hk hψA hψt hZ).trans
        (sup_le (inf_le_left.trans le_sup_right) le_sup_left)
    · exact (le_sup_right.trans hW'.ge).trans le_sup_right
  exact commutator_inf_eq_bot_of_central hVH (hS.le_centralizer_E2 hk hψA hψt hZ ψ₂) hVp hSH
    hSp (hS.not_two_dvd_relIndex hk hψA hψt hZ hk₂ ψ₂) hWS hVW hVWS

theorem mem_commutator_W2_of_commute [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) {β : (h.fixedField)ˣ} (hβ : β ≠ 1)
    {c : G} (hc : c ∈ 𝓦₂) (hcd : c * miyamotoIN2Hom h L η β = miyamotoIN2Hom h L η β * c) :
    c ∈ ⁅𝓦₂, 𝓦₂⁆ := by
  obtain ⟨-, hC, hinf, -, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  obtain ⟨hW2t, hF2, -⟩ := hS.sec5_2_two hk hψA hψt hZ
  have ht := hS.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hW2t' : (𝓦₂).map (MulAut.conj t⁻¹).toMonoidHom = 𝓦'ᵗ ⊓ miyamotoF2G h L η t Q := by
    rw [hti]
    exact hW2t
  have hcW : ∀ x ∈ 𝓦₂, ∀ y ∈ 𝓦'ᵗ ⊓ miyamotoF2G h L η t Q, x * y = y * x :=
    fun x hx y hy => mem_centralizer_iff.1 (hC (mem_inf.1 hy).1) x (mem_inf.1 hx).1
  have hcomm : ⁅𝓦₂, (𝓦₂).map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥ := by
    rw [hW2t', commutator_eq_bot_iff_le_centralizer]
    exact fun x hx => mem_centralizer_iff.2 fun y hy => (hcW x hx y hy).symm
  set δ := Common.diagonalHom 𝓦₂ t hcomm with hδ
  have htF2 : t⁻¹ ∈ normalizer (miyamotoF2G h L η t Q : Set G) :=
    inv_mem (mem_inf.1 hS.t_mem_H2).1
  have hrange : δ.range = miyamotoA2G h L η := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      rw [← hS.F2_inf_C]
      refine mem_inf.2 ⟨?_, Common.range_diagonalHom_le hcomm ht ⟨a, rfl⟩⟩
      rw [Common.diagonalHom_apply]
      have ha : (a : G) ∈ miyamotoF2G h L η t Q := (mem_inf.1 a.2).2
      refine mul_mem ha ?_
      have := (mem_normalizer_iff.1 htF2 a).1 ha
      rwa [inv_inv] at this
    · intro a ha
      have haF : a ∈ miyamotoF2G h L η t Q ⊓ centralizer ({t} : Set G) := hS.F2_inf_C ▸ ha
      have hat : t * a = a * t := (mem_centralizer_singleton_iff.1 (mem_inf.1 haF).2).symm
      have hinf2 : 𝓦₂ ⊓ (𝓦₂).map (MulAut.conj t).toMonoidHom = ⊥ := by
        rw [hW2t]
        exact eq_bot_iff.2 (hinf ▸ inf_le_inf inf_le_left inf_le_left)
      have hcW' : ∀ x ∈ 𝓦₂, ∀ y ∈ (𝓦₂).map (MulAut.conj t).toMonoidHom, x * y = y * x := by
        rw [hW2t]
        exact hcW
      have haW : a ∈ 𝓦₂ ⊔ (𝓦₂).map (MulAut.conj t).toMonoidHom := by
        rw [hW2t, ← hF2]
        exact (mem_inf.1 haF).1
      obtain ⟨x, hx, rfl⟩ := exists_eq_mul_conj_of_mem_sup ht hcW' hinf2 haW hat
      refine ⟨⟨x, hx⟩, ?_⟩
      rw [Common.diagonalHom_apply, hti]
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hk : a ∈ δ.ker := ha
    have hmem : (a : G) ∈ 𝓦₂ ⊓ (𝓦₂).map (MulAut.conj t⁻¹).toMonoidHom :=
      Common.map_ker_diagonalHom_le hcomm ⟨a, hk, rfl⟩
    rw [hW2t'] at hmem
    have h1 : (a : G) ∈ 𝓦' ⊓ 𝓦'ᵗ :=
      mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hmem).1).1, (mem_inf.1 (mem_inf.1 hmem).2).1⟩
    rw [hinf, mem_bot] at h1
    exact Subtype.ext h1
  set d := miyamotoIN2Hom h L η β with hd
  have hdL : d ∈ L := miyamotoPull_le h L η _ (mem_inf.1 (miyamotoIN2Hom_mem h L η β)).1
  have hdt : Commute d t := hS.comm_t_of_mem_L hdL
  have hdc : Commute d c := hcd.symm
  have hδc : δ ⟨c, hc⟩ ∈ miyamotoA2G h L η := hrange ▸ ⟨⟨c, hc⟩, rfl⟩
  have hcom : Commute d (δ ⟨c, hc⟩) := by
    rw [Common.diagonalHom_apply]
    exact hdc.mul_right ((hdt.inv_right.mul_right hdc).mul_right hdt)
  have hZc : δ ⟨c, hc⟩ ∈ miyamotoZG h L η := by
    refine hS.mem_ZG_of_IN2_commutator hβ hδc ?_
    rw [show d⁻¹ * δ ⟨c, hc⟩ * d = δ ⟨c, hc⟩ by
      rw [mul_assoc, ← hcom.eq, inv_mul_cancel_left], mul_inv_cancel]
    exact one_mem _
  have hZcomm : miyamotoZG h L η ≤ Subgroup.map δ ⁅(⊤ : Subgroup ↥(𝓦₂ : Subgroup G)), ⊤⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange,
      commutator_miyamotoA2G h L η]
  obtain ⟨c', hc', hc'c⟩ := hZcomm hZc
  have hcc : c' = ⟨c, hc⟩ := hinj hc'c
  have hmap : Subgroup.map (𝓦₂).subtype ⁅(⊤ : Subgroup ↥(𝓦₂ : Subgroup G)), ⊤⁆ = ⁅𝓦₂, 𝓦₂⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hmap]
  exact ⟨c', hc', by rw [hcc]; rfl⟩

theorem W2_le_commutator [Fintype k] (hS : Setting h L η t Q T)
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
    𝓦₂ ≤ ⁅𝓦₂ ⊔ prodFactorOne ψ₂, 𝓦₂ ⊔ prodFactorOne ψ₂⁆ := by
  have hY2 := hS.Y2_le_centralizer_W2E hk hψA hψt hZ hk₂ hj hj1 hjC hjY
  obtain ⟨hIW, -⟩ := hS.IG_le_normalizer_W' hk hψA hψt hZ
  obtain ⟨-, -, hcardW2⟩ := hS.sec5_2_two hk hψA hψt hZ
  have hcard : Nat.card (h.fixedField)ˣ = 2 ^ f - 1 := by
    rw [Nat.card_units, h.card_fixedField]
  have := h.finite
  have : Nontrivial (h.fixedField)ˣ :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; have := hS.four_le; omega)
  obtain ⟨β, hβ⟩ := exists_ne (1 : (h.fixedField)ˣ)
  set d := miyamotoIN2Hom h L η β with hd
  have hdIN := miyamotoIN2Hom_mem h L η β
  have hdI : d ∈ miyamotoIG h L η := (mem_inf.1 hdIN).1
  have hdN2 : d ∈ miyamotoN2G h L η := (mem_inf.1 hdIN).2
  have hdM : d ∈ miyamotoM2G h L η t Q := hS.sec3_12_two.2.2.1 hdN2
  have hdN : d ∈ normalizer ((𝓦₂ : Subgroup G) : Set G) :=
    mem_normalizer_inf (hIW hdI) (hS.I2N2_le_normalizer_F2 (mem_sup_right hdN2))
  obtain ⟨y, hy, y₂, hy₂, hdy⟩ := Common.exists_mul_of_mem ψ₂ hdM
  have hy₂c : ∀ w ∈ 𝓦₂, w * y₂ = y₂ * w := fun w hw =>
    mem_centralizer_iff.1 (hY2 hy₂) w (mem_sup_left hw)
  have hyy : Commute y y₂ :=
    (mem_centralizer_iff.1 (Common.prodFactorOne_le_centralizer ψ₂ hy) y₂ hy₂).symm
  have hyN : y ∈ normalizer ((𝓦₂ : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_le fun w hw => ?_
    have e : y * w * y⁻¹ = d * w * d⁻¹ := by
      rw [hdy]
      calc y * w * y⁻¹ = y * (w * y₂) * y₂⁻¹ * y⁻¹ := by group
        _ = y * (y₂ * w) * y₂⁻¹ * y⁻¹ := by rw [hy₂c w hw]
        _ = (y * y₂) * w * (y * y₂)⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 hdN w).1 hw
  have hdodd : Odd (orderOf d) := by
    refine Odd.of_dvd_nat hS.odd_card_IG ?_
    have := orderOf_dvd_natCard (⟨d, hdI⟩ : miyamotoIG h L η)
    rwa [← Subgroup.orderOf_coe] at this
  have hyodd : Odd (orderOf y) := by
    refine Odd.of_dvd_nat hdodd (orderOf_dvd_of_pow_eq_one ?_)
    have hpow : d ^ orderOf d = y ^ orderOf d * y₂ ^ orderOf d := by rw [hdy, hyy.mul_pow]
    rw [pow_orderOf_eq_one] at hpow
    have hmem : y ^ orderOf d ∈ prodFactorOne ψ₂ ⊓ prodFactorTwo ψ₂ := by
      refine mem_inf.2 ⟨pow_mem hy _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hpow.symm]
      exact inv_mem (pow_mem hy₂ _)
    rwa [Common.prodFactorOne_inf_prodFactorTwo, mem_bot] at hmem
  set D₀ := 𝓦₂ ⊔ prodFactorOne ψ₂ with hD₀
  have hW2p : IsPGroup 2 (𝓦₂ : Subgroup G) :=
    hS.isPGroup_RG.to_le (inf_le_right.trans hS.F2_le_RG)
  have hsolv : Group.IsSolvable (𝓦₂ : Subgroup G) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := hW2p.isNilpotent
    infer_instance
  have hcop : (Nat.card (zpowers y)).Coprime (Nat.card (𝓦₂ : Subgroup G)) := by
    rw [Nat.card_zpowers, hcardW2]
    exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hyodd))
  have hSM : zpowers y ≤ normalizer ((𝓦₂ : Subgroup G) : Set G) := zpowers_le.2 hyN
  have hD₀N : ∀ x ∈ D₀, x ∈ normalizer ((⁅D₀, D₀⁆ : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_commutator (le_normalizer hx) (le_normalizer hx)
  have hyD : y ∈ D₀ := mem_sup_right hy
  intro m hm
  obtain ⟨c, hcC, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (M := 𝓦₂) (N := ⁅D₀, D₀⁆ ⊓ 𝓦₂) (S := zpowers y) inf_le_right
    (fun w hw => mem_normalizer_inf (hD₀N w (mem_sup_left hw)) (le_normalizer hw)) hSM
    (zpowers_le.2 (mem_normalizer_inf (hD₀N y hyD) hyN)) hsolv hcop hm (fun s hs => by
      have hsD : s ∈ D₀ := zpowers_le.2 hyD hs
      refine mem_inf.2 ⟨?_, mul_mem (inv_mem hm) ((mem_normalizer_iff.1 (hSM hs) m).1 hm)⟩
      have e : m⁻¹ * (s * m * s⁻¹) = ⁅m⁻¹, s⁆ := by rw [commutatorElement_def, inv_inv]; group
      rw [e]
      exact commutator_mem_commutator (inv_mem (mem_sup_left hm)) hsD)
  obtain ⟨hcW, hcy⟩ := mem_inf.1 hcC
  have hcy' : c * y = y * c := (mem_centralizer_iff.1 hcy y (mem_zpowers y)).symm
  have hcd : c * d = d * c := by
    rw [hdy]
    calc c * (y * y₂) = (c * y) * y₂ := by group
      _ = (y * c) * y₂ := by rw [hcy']
      _ = y * (c * y₂) := by group
      _ = y * (y₂ * c) := by rw [hy₂c c hcW]
      _ = (y * y₂) * c := by group
  have hcc := hS.mem_commutator_W2_of_commute hk hψA hψt hZ hβ hcW hcd
  exact mul_mem (commutator_mono le_sup_left le_sup_left hcc) (mem_inf.1 hn).1

theorem Y1_le_normalizer_W2 [Fintype k] (hS : Setting h L η t Q T)
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
    prodFactorOne ψ₂ ≤ normalizer ((𝓦₂ : Subgroup G) : Set G) := by
  obtain ⟨-, hC, -, -, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  set H := (𝓦₂ ⊔ miyamotoEG h L η Q) ⊔ prodFactorOne ψ₂ with hH
  have h1 := hS.commutator_inf_E2 hk hψA hψt hZ hk₂ hψα₂ hj hj1 hjC hjY
  have hD₀H : 𝓦₂ ⊔ prodFactorOne ψ₂ ≤ H := sup_le_sup_right le_sup_left _
  have h2 : 𝓦₂ ≤ ⁅H, H⁆ := (hS.W2_le_commutator hk hψA hψt hZ hk₂ hj hj1 hjC hjY).trans
    (commutator_mono hD₀H hD₀H)
  have hXE := hS.W2_sup_E_eq hk hψA hψt hZ
  have hN := hS.M2_le_normalizer_W2E hk hψA hψt hZ
  have hc : ∀ x ∈ 𝓦₂, ∀ e ∈ 𝓔₂, x * e = e * x :=
    fun x hx e he => mem_centralizer_iff.1 (hC (mem_inf.1 he).2) x (mem_inf.1 hx).1
  intro y hy
  refine mem_normalizer_of_conj_le fun w hw => ?_
  have hyH : y ∈ H := mem_sup_right hy
  have hyw1 : y * w * y⁻¹ ∈ 𝓦₂ ⊔ 𝓔₂ := hXE ▸
    (mem_normalizer_iff.1 (hN (Common.prodFactorOne_le ψ₂ hy)) w).1 (mem_sup_left hw)
  have hyw2 : y * w * y⁻¹ ∈ ⁅H, H⁆ :=
    (mem_normalizer_iff.1 (mem_normalizer_commutator (le_normalizer hyH) (le_normalizer hyH))
      w).1 (h2 hw)
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hc hyw1
  have hb' : b ∈ ⁅H, H⁆ ⊓ 𝓔₂ := by
    refine mem_inf.2 ⟨?_, hb⟩
    rw [show b = a⁻¹ * (y * w * y⁻¹) by rw [hab]; group]
    exact mul_mem (inv_mem (h2 ha)) hyw2
  rw [h1, mem_bot] at hb'
  rw [hab, hb', mul_one]
  exact ha

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
