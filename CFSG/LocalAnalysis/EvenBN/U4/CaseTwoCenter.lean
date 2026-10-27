module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseOneOuter
public import CFSG.LocalAnalysis.EvenBN.U4.CaseOneOuterSwap
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusNine

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  mem_normalizer_sup card_sup_mul_card_inf_eq)
open scoped MatrixGroups

section Generic

theorem card_le_two_pow_of_isPGroup_SL2 {k : Type*} [Field k] [Fintype k] {f : ℕ} (hf : 1 ≤ f)
    (hk : Fintype.card k = 2 ^ f) {P : Subgroup SL(2, k)} (hP : IsPGroup 2 P) :
    Nat.card P ≤ 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hSL : Nat.card SL(2, k) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card, hk]
  have hdvd : Nat.card P ∣ Nat.card SL(2, k) := Subgroup.card_subgroup_dvd_card P
  rw [hm, hSL] at hdvd
  have hodd : Odd ((2 ^ f) ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity))
      ((Nat.even_pow.2 ⟨even_two, by omega⟩).pow_of_ne_zero two_ne_zero) odd_one
  have hcop : Nat.Coprime (2 ^ m) ((2 ^ f) ^ 2 - 1) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hodd)
  rw [hm]
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)

theorem card_le_of_inf_prodFactorTwo_eq_bot {G : Type*} [Group G] {M : Subgroup G}
    {k : Type*} [Field k] [Fintype k] {f : ℕ} (hf : 1 ≤ f) (hk : Fintype.card k = 2 ^ f)
    (ψ : M ≃* SL(2, k) × SL(2, k)) {V : Subgroup G} (hVM : V ≤ M) (hV2 : IsPGroup 2 V)
    (hV : V ⊓ prodFactorTwo ψ = ⊥) : Nat.card V ≤ 2 ^ f := by
  set φ : V →* SL(2, k) :=
    (MonoidHom.fst _ _).comp (ψ.toMonoidHom.comp (Subgroup.inclusion hVM)) with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hv2 : (v : G) ∈ prodFactorTwo ψ := (Common.mem_prodFactorTwo_iff ψ).2 ⟨hVM v.2, hv⟩
    have hvb : (v : G) ∈ V ⊓ prodFactorTwo ψ := mem_inf.2 ⟨v.2, hv2⟩
    rw [hV, mem_bot] at hvb
    exact Subtype.ext hvb
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact card_le_two_pow_of_isPGroup_SL2 hf hk
    (hV2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)

theorem card_le_of_inf_prodFactorOne_eq_bot {G : Type*} [Group G] {M : Subgroup G}
    {k : Type*} [Field k] [Fintype k] {f : ℕ} (hf : 1 ≤ f) (hk : Fintype.card k = 2 ^ f)
    (ψ : M ≃* SL(2, k) × SL(2, k)) {V : Subgroup G} (hVM : V ≤ M) (hV2 : IsPGroup 2 V)
    (hV : V ⊓ prodFactorOne ψ = ⊥) : Nat.card V ≤ 2 ^ f := by
  set φ : V →* SL(2, k) :=
    (MonoidHom.snd _ _).comp (ψ.toMonoidHom.comp (Subgroup.inclusion hVM)) with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hv1 : (v : G) ∈ prodFactorOne ψ := (Common.mem_prodFactorOne_iff ψ).2 ⟨hVM v.2, hv⟩
    have hvb : (v : G) ∈ V ⊓ prodFactorOne ψ := mem_inf.2 ⟨v.2, hv1⟩
    rw [hV, mem_bot] at hvb
    exact Subtype.ext hvb
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact card_le_two_pow_of_isPGroup_SL2 hf hk
    (hV2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)

theorem mem_normalizer_prodFactor_of_odd {G : Type*} [Group G] {k : Type*} [Field k] [Finite k]
    [CharP k 2] (h4 : 4 ≤ Nat.card k) {M : Subgroup G} (ψ : M ≃* SL(2, k) × SL(2, k)) {g : G}
    (hg : g ∈ normalizer (M : Set G)) (hodd : Odd (orderOf g)) :
    g ∈ normalizer (prodFactorOne ψ : Set G) ∧ g ∈ normalizer (prodFactorTwo ψ : Set G) := by
  have hsq : ∀ H : Subgroup G, H.map (MulAut.conj (g * g)).toMonoidHom =
      (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    intro H
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
      Function.comp_apply]
    group
  rcases Common.conj_prodFactor_eq_or_swap h4 ψ hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨mem_normalizer_iff_map_conj_eq.2 h1, mem_normalizer_iff_map_conj_eq.2 h2⟩
  · have hg1 : g * g ∈ normalizer (prodFactorOne ψ : Set G) :=
      mem_normalizer_iff_map_conj_eq.2 (by rw [hsq, h1, h2])
    have hg2 : g * g ∈ normalizer (prodFactorTwo ψ : Set G) :=
      mem_normalizer_iff_map_conj_eq.2 (by rw [hsq, h2, h1])
    obtain ⟨n, hn⟩ := hodd
    have e : g = (g * g) ^ (n + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (n + 1) = orderOf g + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [e]
    exact ⟨pow_mem hg1 _, pow_mem hg2 _⟩

end Generic

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

local notation "𝓥" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

omit [Finite G] in
theorem DG_comm {a b : G} (ha : a ∈ miyamotoDG h L η) (hb : b ∈ miyamotoDG h L η) :
    a * b = b * a := by
  rw [← range_miyamotoDHom] at ha hb
  obtain ⟨α₁, rfl⟩ := ha
  obtain ⟨β₁, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

omit [Finite G] in
theorem conj_prodSnd_of_mem (m' x : miyamotoM1G h L η t) :
    (m' : G) * prodSnd ψ x * (m' : G)⁻¹ = prodSnd ψ (m' * x * m'⁻¹) := by
  rw [map_mul, map_mul, map_inv]
  have hb : prodSnd ψ m' * prodSnd ψ x * (prodSnd ψ m')⁻¹ ∈ prodFactorTwo ψ :=
    mul_mem (mul_mem (prodSnd_mem m') (prodSnd_mem x)) (inv_mem (prodSnd_mem m'))
  have hc : prodFst ψ m' * (prodSnd ψ m' * prodSnd ψ x * (prodSnd ψ m')⁻¹) =
      (prodSnd ψ m' * prodSnd ψ x * (prodSnd ψ m')⁻¹) * prodFst ψ m' :=
    mem_centralizer_iff.1 (Common.prodFactorTwo_le_centralizer ψ hb) _ (prodFst_mem m')
  calc (m' : G) * prodSnd ψ x * (m' : G)⁻¹ =
      prodFst ψ m' * (prodSnd ψ m' * prodSnd ψ x * (prodSnd ψ m')⁻¹) * (prodFst ψ m')⁻¹ := by
        rw [eq_prodFst_mul_prodSnd (ψ := ψ) m']
        group
    _ = prodSnd ψ m' * prodSnd ψ x * (prodSnd ψ m')⁻¹ := by
        rw [hc]
        group

theorem prodSnd_mem_normalizer_W2 (hS : Setting h L η t Q T) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) :
    prodSnd ψ m ∈ normalizer ((𝓦 ⊓ prodFactorTwo ψ : Subgroup G) : Set G) := by
  have hdW : (m : G) ∈ normalizer ((𝓦 ⊓ prodFactorTwo ψ : Subgroup G) : Set G) :=
    mem_normalizer_inf (hS.DG_le_normalizer_W hm) (Common.le_normalizer_prodFactorTwo ψ m.2)
  have e : prodSnd ψ m = (prodFst ψ m)⁻¹ * m := by
    rw [eq_inv_mul_iff_mul_eq, ← eq_prodFst_mul_prodSnd]
  rw [e]
  refine mem_normalizer_fintype fun w hw => ?_
  have hdw : (m : G) * w * (m : G)⁻¹ ∈ 𝓦 ⊓ prodFactorTwo ψ := (mem_normalizer_iff.1 hdW w).1 hw
  have hc : prodFst ψ m * ((m : G) * w * (m : G)⁻¹) =
      ((m : G) * w * (m : G)⁻¹) * prodFst ψ m :=
    mem_centralizer_iff.1 (Common.prodFactorTwo_le_centralizer ψ (mem_inf.1 hdw).2) _
      (prodFst_mem m)
  have : (prodFst ψ m)⁻¹ * m * w * ((prodFst ψ m)⁻¹ * m)⁻¹ = (m : G) * w * (m : G)⁻¹ := by
    calc (prodFst ψ m)⁻¹ * m * w * ((prodFst ψ m)⁻¹ * m)⁻¹ =
        (prodFst ψ m)⁻¹ * ((m : G) * w * (m : G)⁻¹) * prodFst ψ m := by group
      _ = (prodFst ψ m)⁻¹ * (prodFst ψ m * ((m : G) * w * (m : G)⁻¹)) := by rw [mul_assoc, hc]
      _ = (m : G) * w * (m : G)⁻¹ := by group
  rw [this]
  exact hdw

theorem odd_orderOf_prodSnd (hS : Setting h L η t Q T) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) : Odd (orderOf (prodSnd ψ m)) := by
  have hev : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by have := hS.two_le; omega⟩
  have hodd : Odd (Nat.card (miyamotoDG h L η)) := by
    rw [card_miyamotoDG]
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) (hev.pow_of_ne_zero two_ne_zero)
      odd_one
  have h1 : orderOf (m : G) ∣ Nat.card (miyamotoDG h L η) := by
    have := orderOf_dvd_natCard (⟨m, hm⟩ : miyamotoDG h L η)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf (prodSnd ψ m) ∣ orderOf (m : G) := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_map_dvd _ m
  exact Odd.of_dvd_nat hodd (h2.trans h1)


theorem DG_le_M1G (hS : Setting h L η t Q T) : miyamotoDG h L η ≤ miyamotoM1G h L η t :=
  hS.DG_le_N1G.trans hS.sec3_12_one.2.2.1

theorem prodSnd_commute_IG (hS : Setting h L η t Q T) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) {i : G} (hi : i ∈ miyamotoIG h L η) :
    prodSnd ψ m * i = i * prodSnd ψ m := by
  obtain ⟨i₁, hi₁, d, hd, rfl⟩ := hS.exists_I1_mul_D hi
  have hτ2 : prodSnd ψ m ∈ prodFactorTwo ψ := prodSnd_mem m
  have h1 : i₁ * prodSnd ψ m = prodSnd ψ m * i₁ :=
    mem_centralizer_iff.1 (hS.M1_le_centralizer_I1 (Common.prodFactorTwo_le ψ hτ2)) i₁ hi₁
  set m' : miyamotoM1G h L η t := ⟨d, hS.DG_le_M1G hd⟩ with hm'
  have hd' : d = prodFst ψ m' * prodSnd ψ m' := eq_prodFst_mul_prodSnd m'
  have h2 : prodSnd ψ m * prodFst ψ m' = prodFst ψ m' * prodSnd ψ m :=
    mem_centralizer_iff.1 (Common.prodFactorOne_le_centralizer ψ (prodFst_mem m')) _ hτ2
  have h3 : prodSnd ψ m * prodSnd ψ m' = prodSnd ψ m' * prodSnd ψ m := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (DG_comm hm hd)
  rw [hd']
  calc prodSnd ψ m * (i₁ * (prodFst ψ m' * prodSnd ψ m')) =
      (prodSnd ψ m * i₁) * prodFst ψ m' * prodSnd ψ m' := by group
    _ = i₁ * (prodSnd ψ m * prodFst ψ m') * prodSnd ψ m' := by rw [← h1]; group
    _ = i₁ * prodFst ψ m' * (prodSnd ψ m * prodSnd ψ m') := by rw [h2]; group
    _ = i₁ * (prodFst ψ m' * prodSnd ψ m') * prodSnd ψ m := by rw [h3]; group

theorem prodSnd_mem_centralizer_I2 (hS : Setting h L η t Q T) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) :
    prodSnd ψ m ∈ centralizer (miyamotoI2G h L η : Set G) := by
  rw [mem_centralizer_iff]
  intro i hi
  exact (hS.prodSnd_commute_IG hm (hS.tori_le_IG.2.2.2 hi)).symm

theorem prodSnd_mem_normalizer_W [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) :
    prodSnd ψ m ∈ normalizer ((𝓦 : Subgroup G) : Set G) := by
  rw [← (hS.W_eq_sup (ψ := ψ) hk).1]
  refine mem_normalizer_sup (mem_normalizer_of_mem_centralizer' ?_)
    (hS.prodSnd_mem_normalizer_W2 hm)
  rw [mem_centralizer_iff]
  intro w hw
  exact (mem_centralizer_iff.1 (Common.prodFactorOne_le_centralizer ψ (mem_inf.1 hw).2) _
    (prodSnd_mem m)).symm

theorem prodSnd_mem_normalizer_centerIn_U (hS : Setting h L η t Q T)
    (m : miyamotoM1G h L η t) :
    prodSnd ψ m ∈ normalizer ((CFSG.centerIn 𝓤 : Subgroup G) : Set G) :=
  normalizer_le_normalizer_centerIn _ (hS.X2_le_normalizer_U (prodSnd_mem m))

theorem prodSnd_mem_normalizer_E [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) :
    prodSnd ψ m ∈ normalizer (miyamotoEG h L η Q : Set G) := by
  rw [← hS.centerIn_U_inf_centralizer_W2 (ψ := ψ) hk]
  exact mem_normalizer_inf (hS.prodSnd_mem_normalizer_centerIn_U m)
    (mem_normalizer_centralizer (hS.prodSnd_mem_normalizer_W2 hm))

theorem prodSnd_mem_normalizer_RG [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) :
    prodSnd ψ m ∈ normalizer (miyamotoRG h L η t Q : Set G) := by
  have hW := hS.prodSnd_mem_normalizer_W (ψ := ψ) hk hm
  have hF1 := hS.M1_le_normalizer_F1 (Common.prodFactorTwo_le ψ (prodSnd_mem m))
  refine mem_normalizer_fintype fun r hr => ?_
  obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hr
  have e : prodSnd ψ m * (w * y) * (prodSnd ψ m)⁻¹ =
      (prodSnd ψ m * w * (prodSnd ψ m)⁻¹) * (prodSnd ψ m * y * (prodSnd ψ m)⁻¹) := by group
  rw [e]
  exact mul_mem (mem_inf.1 ((mem_normalizer_iff.1 hW w).1 hw)).1
    (le_sup_left.trans hS.P1_le_miyamotoRG ((mem_normalizer_iff.1 hF1 y).1 hy))

theorem prodSnd_mem_normalizer_F [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) :
    prodSnd ψ m ∈ normalizer (miyamotoFG h L η t Q : Set G) := by
  rw [hS.F_eq_E_sup]
  have hC : prodSnd ψ m ∈ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G) := by
    rw [mem_centralizer_iff]
    intro i hi
    exact (hS.prodSnd_commute_IG hm (hS.tori_le_IG.2.1 hi)).symm
  exact mem_normalizer_sup (hS.prodSnd_mem_normalizer_E hk hm)
    (mem_normalizer_inf (hS.prodSnd_mem_normalizer_RG hk hm)
      (mem_normalizer_centralizer (mem_normalizer_of_mem_centralizer' hC)))

theorem prodSnd_mem_normalizer_V2 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) :
    prodSnd ψ m ∈ normalizer ((𝓥 : Subgroup G) : Set G) :=
  mem_normalizer_inf (hS.prodSnd_mem_normalizer_RG hk hm)
    (mem_normalizer_centralizer (mem_normalizer_of_mem_centralizer'
      (hS.prodSnd_mem_centralizer_I2 hm)))

theorem prodSnd_mem_normalizer_F2 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) :
    prodSnd ψ m ∈ normalizer (miyamotoF2G h L η t Q : Set G) := by
  rw [hS.F2_eq]
  exact mem_normalizer_sup (hS.prodSnd_mem_normalizer_F hk hm)
    (hS.prodSnd_mem_normalizer_W hk hm)

theorem prodSnd_mem_normalizer_M2 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) :
    prodSnd ψ m ∈ normalizer (miyamotoM2G h L η t Q : Set G) :=
  hS.sec3_12_two.2.1
    (mem_inf.2 ⟨hS.prodSnd_mem_normalizer_F2 hk hm, hS.prodSnd_mem_centralizer_I2 hm⟩)

theorem exists_R1G_conj_prodSnd (hS : Setting h L η t Q T) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) :
    ∃ m' : miyamotoM1G h L η t, (m' : G) ∈ miyamotoDG h L η ∧
      miyamotoR1G h L η * prodSnd ψ m * (miyamotoR1G h L η)⁻¹ = prodSnd ψ m' := by
  refine ⟨⟨miyamotoR1G h L η, hS.R1G_mem_M1⟩ * m * ⟨miyamotoR1G h L η, hS.R1G_mem_M1⟩⁻¹, ?_,
    conj_prodSnd_of_mem (ψ := ψ) ⟨miyamotoR1G h L η, hS.R1G_mem_M1⟩ m⟩
  show miyamotoR1G h L η * (m : G) * (miyamotoR1G h L η)⁻¹ ∈ miyamotoDG h L η
  rw [← range_miyamotoDHom] at hm ⊢
  obtain ⟨α, hα⟩ := hm
  refine ⟨α⁻¹, ?_⟩
  rw [← hS.R1G_conj_miyamotoDHom α, hα, inv_eq_of_mul_eq_one_right hS.R1G_mul_self]

theorem eq_one_of_prodSnd_conj_eq [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : Nat.card (CFSG.centerIn 𝓤) = (2 ^ f) ^ 4) {m : miyamotoM1G h L η t}
    (hm : (m : G) ∈ miyamotoDG h L η) (hm1 : prodSnd ψ m ≠ 1) {v : G} (hv : v ∈ 𝓥)
    (hfix : prodSnd ψ m * v * (prodSnd ψ m)⁻¹ = v) : v = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnat := hS.sec3_17_three hk hψt hZ
  have hR2 : IsPGroup 2 (miyamotoRG h L η t Q) := hS.isPGroup_RG
  have hodd2 : ∀ x ∈ miyamotoRG h L η t Q, Odd (orderOf x) → x = 1 := by
    intro x hx hodd
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hR2) ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hn
    rw [hn] at hodd
    rcases n with _ | n
    · rw [pow_zero] at hn
      exact orderOf_eq_one_iff.1 hn
    · exact absurd hodd (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, n.succ_ne_zero⟩))
  have hrM : miyamotoR1G h L η ∈ miyamotoM1G h L η t := hS.R1G_mem_M1
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G,
      C = (miyamotoEG h L η Q).map (MulAut.conj (miyamotoR1G h L η)⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hCF1 : C ≤ miyamotoF1G h L η t := by
    rw [hC]
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
    have := (mem_normalizer_iff.1 (hS.M1_le_normalizer_F1 (inv_mem hrM)) e).1 (hS.E_le_F1 he)
    simpa [MulAut.conj_apply] using this
  have hFN : miyamotoF1G h L η t ≤ normalizer (miyamotoFG h L η t Q : Set G) :=
    (le_sup_left.trans hS.P1_le_miyamotoRG).trans hS.RG_le_normalizer_F
  have hCN : C ≤ normalizer (miyamotoFG h L η t Q : Set G) := hCF1.trans hFN
  have hFC : C ⊓ miyamotoFG h L η t Q = ⊥ := by
    rw [hC]
    exact hS.E_r1_inf_F
  have hCcard : Nat.card C = (2 ^ f) ^ 2 := by
    rw [hC, Subgroup.card_map_of_injective (MulAut.conj _).injective, hS.card_E]
  have hF1eq : miyamotoF1G h L η t = miyamotoFG h L η t Q ⊔ C := by
    have e := card_sup_mul_card_inf_eq hCN
    rw [inf_comm, hFC, card_bot, mul_one, hS.card_F, hCcard] at e
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hS.F_le_F1 hCF1) ?_).symm
    rw [e, hS.card_F1]
    exact le_of_eq (by ring)
  have hFV : miyamotoFG h L η t Q ⊓ 𝓥 = ⊥ := by
    have hVN : (𝓥 : Subgroup G) ≤ normalizer (miyamotoFG h L η t Q : Set G) :=
      inf_le_left.trans hS.RG_le_normalizer_F
    have e := card_sup_mul_card_inf_eq hVN
    rw [← hS.F1_eq_F_sup, hS.card_F1, hS.card_F, hS.card_V2] at e
    refine Subgroup.card_eq_one.1 ?_
    have hpos : 0 < (2 ^ f) ^ 8 := by positivity
    exact Nat.eq_of_mul_eq_mul_left hpos (e.trans (by ring))
  have hτF := hS.prodSnd_mem_normalizer_F (ψ := ψ) hk hm
  obtain ⟨m', hm', hσ⟩ := hS.exists_R1G_conj_prodSnd (ψ := ψ) hm
  have hσE := hS.prodSnd_mem_normalizer_E (ψ := ψ) hk hm'
  have hτC : prodSnd ψ m ∈ normalizer (C : Set G) := by
    rw [hC]
    refine mem_normalizer_fintype fun x hx => ?_
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨prodSnd ψ m' * e * (prodSnd ψ m')⁻¹, (mem_normalizer_iff.1 hσE e).1 he, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hσ]
    group
  have hfreeC : ∀ c ∈ C, prodSnd ψ m * c * (prodSnd ψ m)⁻¹ = c → c = 1 := by
    intro c hc hcfix
    rw [hC] at hc
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hc
    by_contra hne
    have he1 : e ≠ 1 := fun h1 => hne (by rw [h1, map_one])
    have e1 : (MulAut.conj (miyamotoR1G h L η)⁻¹).toMonoidHom e =
        (miyamotoR1G h L η)⁻¹ * e * miyamotoR1G h L η := by
      simp
    rw [e1] at hcfix
    have h' : prodSnd ψ m' * e * (prodSnd ψ m')⁻¹ = e := by
      rw [← hσ]
      calc miyamotoR1G h L η * prodSnd ψ m * (miyamotoR1G h L η)⁻¹ * e *
            (miyamotoR1G h L η * prodSnd ψ m * (miyamotoR1G h L η)⁻¹)⁻¹ =
          miyamotoR1G h L η * (prodSnd ψ m * ((miyamotoR1G h L η)⁻¹ * e * miyamotoR1G h L η) *
            (prodSnd ψ m)⁻¹) * (miyamotoR1G h L η)⁻¹ := by group
        _ = e := by rw [hcfix]; group
    have hfixe : prodSnd ψ m' * e = e * prodSnd ψ m' := by
      calc prodSnd ψ m' * e = prodSnd ψ m' * e * (prodSnd ψ m')⁻¹ * prodSnd ψ m' := by group
        _ = e * prodSnd ψ m' := by rw [h']
    have hσW : prodSnd ψ m' ∈ 𝓦 ⊓ prodFactorTwo ψ := by
      rw [← hnat.2.1 e he he1]
      exact mem_inf.2 ⟨prodSnd_mem m', mem_centralizer_singleton_iff.2 hfixe⟩
    have hσ1 : prodSnd ψ m' = 1 :=
      hodd2 _ (mem_inf.1 (mem_inf.1 hσW).1).1 (hS.odd_orderOf_prodSnd hm')
    apply hm1
    calc prodSnd ψ m = (miyamotoR1G h L η)⁻¹ *
          (miyamotoR1G h L η * prodSnd ψ m * (miyamotoR1G h L η)⁻¹) * miyamotoR1G h L η := by
          group
      _ = 1 := by rw [hσ, hσ1]; group
  have hvF1 : v ∈ miyamotoF1G h L η t := by
    have hv' := hv
    rw [hS.RG_inf_centralizer_I2] at hv'
    exact (mem_inf.1 hv').1
  rw [hF1eq] at hvF1
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hCN hvF1
  have ha' : prodSnd ψ m * a * (prodSnd ψ m)⁻¹ ∈ miyamotoFG h L η t Q :=
    (mem_normalizer_iff.1 hτF a).1 ha
  have hc' : prodSnd ψ m * c * (prodSnd ψ m)⁻¹ ∈ C := (mem_normalizer_iff.1 hτC c).1 hc
  have e1 : (prodSnd ψ m * a * (prodSnd ψ m)⁻¹) * (prodSnd ψ m * c * (prodSnd ψ m)⁻¹) =
      a * c := by
    rw [← hfix]
    group
  have hmem : a⁻¹ * (prodSnd ψ m * a * (prodSnd ψ m)⁻¹) ∈ C ⊓ miyamotoFG h L η t Q := by
    refine mem_inf.2 ⟨?_, mul_mem (inv_mem ha) ha'⟩
    have : a⁻¹ * (prodSnd ψ m * a * (prodSnd ψ m)⁻¹) =
        c * (prodSnd ψ m * c * (prodSnd ψ m)⁻¹)⁻¹ := by
      calc a⁻¹ * (prodSnd ψ m * a * (prodSnd ψ m)⁻¹) =
          a⁻¹ * ((prodSnd ψ m * a * (prodSnd ψ m)⁻¹) * (prodSnd ψ m * c * (prodSnd ψ m)⁻¹)) *
            (prodSnd ψ m * c * (prodSnd ψ m)⁻¹)⁻¹ := by group
        _ = c * (prodSnd ψ m * c * (prodSnd ψ m)⁻¹)⁻¹ := by rw [e1]; group
    rw [this]
    exact mul_mem hc (inv_mem hc')
  rw [hFC, mem_bot] at hmem
  have haa : prodSnd ψ m * a * (prodSnd ψ m)⁻¹ = a := by
    calc prodSnd ψ m * a * (prodSnd ψ m)⁻¹ = a * (a⁻¹ * (prodSnd ψ m * a * (prodSnd ψ m)⁻¹)) := by
          group
      _ = a := by rw [hmem, mul_one]
  rw [haa] at e1
  have hc1 : c = 1 := hfreeC c hc (mul_left_cancel e1)
  subst hc1
  rw [mul_one] at hv ⊢
  have : a ∈ miyamotoFG h L η t Q ⊓ 𝓥 := mem_inf.2 ⟨ha, hv⟩
  rwa [hFV, mem_bot] at this

theorem card_centerIn_U_gt_of_case_two [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψα : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    (ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)) :
    (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k₂ 2 := charP_of_card_eq_prime_pow (f := f) hk₂
  have hq4 := hS.four_le
  have hf1 : 1 ≤ f := by have := hS.two_le; omega
  refine lt_of_le_of_ne (hS.card_centerIn_U_ge hk hψt) fun hZ' => ?_
  have hZ : Nat.card (CFSG.centerIn 𝓤) = (2 ^ f) ^ 4 := hZ'.symm
  have hDM := hS.DG_le_M1G
  set D' : Subgroup (miyamotoM1G h L η t) :=
    (miyamotoDG h L η).subgroupOf (miyamotoM1G h L η t) with hD'
  set π : D' →* G := (prodSnd ψ).comp D'.subtype with hπ
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    rintro ⟨d, hd⟩ hd1
    have hdD : (d : G) ∈ miyamotoDG h L η := hd
    have hdN : (d : G) ∈ miyamotoN1G h L η := hS.DG_le_N1G hdD
    have e1 : ψ.symm (1, (ψ d).2) = 1 := Subtype.ext hd1
    have e2 : (ψ d).2 = 1 := by
      have := congrArg ψ e1
      rw [MulEquiv.apply_symm_apply, map_one] at this
      exact (Prod.mk.inj this).2
    rw [hψα ⟨d, hdN⟩ d rfl] at e2
    have e3 : (⟨d, hdN⟩ : miyamotoN1G h L η) = 1 := by
      rw [← map_one α] at e2
      exact α.injective e2
    have e4 : (d : G) = 1 := congrArg Subtype.val e3
    exact Subtype.ext (Subtype.ext e4)
  set T₂ : Subgroup G := π.range with hT₂
  have hT2card : Nat.card T₂ = (2 ^ f) ^ 2 - 1 := by
    rw [hT₂, Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv.symm, hD',
      Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv, card_miyamotoDG]
  have h4 : 4 ≤ Nat.card k₂ := by rw [Nat.card_eq_fintype_card, hk₂]; exact hq4
  obtain ⟨-, -, -, -, hVM, -, -, -⟩ := hS.sec3_12_two
  have hV2 : IsPGroup 2 (𝓥 : Subgroup G) := hS.isPGroup_RG.to_le inf_le_left
  have hVcard : Nat.card (𝓥 : Subgroup G) = (2 ^ f) ^ 2 := hS.card_V2
  have hqlt : 2 ^ f < (2 ^ f) ^ 2 := by nlinarith
  obtain ⟨k₀, hk₀, hk₀1⟩ : ∃ k₀ ∈ (𝓥 : Subgroup G) ⊓ prodFactorTwo ψ₂, k₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : (𝓥 : Subgroup G) ⊓ prodFactorTwo ψ₂ = ⊥ :=
      eq_bot_iff.2 fun x hx => mem_bot.2 (hcon x hx)
    have := card_le_of_inf_prodFactorTwo_eq_bot hf1 hk₂ ψ₂ hVM hV2 hbot
    omega
  have hKY : ∀ τ ∈ T₂, τ * k₀ * τ⁻¹ ∈ (𝓥 : Subgroup G) ⊓ prodFactorTwo ψ₂ := by
    rintro _ ⟨⟨m, hm⟩, rfl⟩
    have hmD : (m : G) ∈ miyamotoDG h L η := hm
    show prodSnd ψ m * k₀ * (prodSnd ψ m)⁻¹ ∈ _
    have hNY := (mem_normalizer_prodFactor_of_odd h4 ψ₂
      (hS.prodSnd_mem_normalizer_M2 (ψ := ψ) hk hmD) (hS.odd_orderOf_prodSnd (ψ := ψ) hmD)).2
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 (hS.prodSnd_mem_normalizer_V2 (ψ := ψ) hk hmD) k₀).1
      (mem_inf.1 hk₀).1, (mem_normalizer_iff.1 hNY k₀).1 (mem_inf.1 hk₀).2⟩
  have hfree : ∀ τ ∈ T₂, τ * k₀ * τ⁻¹ = k₀ → τ = 1 := by
    rintro _ ⟨⟨m, hm⟩, rfl⟩ hfix
    have hmD : (m : G) ∈ miyamotoDG h L η := hm
    show prodSnd ψ m = 1
    by_contra hm1
    exact hk₀1 (hS.eq_one_of_prodSnd_conj_eq hk hψt hZ hmD hm1 (mem_inf.1 hk₀).1 hfix)
  set φ : T₂ → ((𝓥 : Subgroup G) ⊓ prodFactorTwo ψ₂ : Subgroup G) :=
    fun τ => ⟨(τ : G) * k₀ * (τ : G)⁻¹, hKY τ τ.2⟩ with hφ
  have hφinj : Function.Injective φ := by
    rintro ⟨τ, hτ⟩ ⟨τ', hτ'⟩ e
    have e' : τ * k₀ * τ⁻¹ = τ' * k₀ * τ'⁻¹ := congrArg Subtype.val e
    have hfix : (τ'⁻¹ * τ) * k₀ * (τ'⁻¹ * τ)⁻¹ = k₀ := by
      calc (τ'⁻¹ * τ) * k₀ * (τ'⁻¹ * τ)⁻¹ = τ'⁻¹ * (τ * k₀ * τ⁻¹) * τ' := by group
        _ = k₀ := by rw [e']; group
    have h1 := hfree _ (mul_mem (inv_mem hτ') hτ) hfix
    exact Subtype.ext (inv_mul_eq_one.1 h1).symm
  have hφ1 : (1 : ((𝓥 : Subgroup G) ⊓ prodFactorTwo ψ₂ : Subgroup G)) ∉ Set.range φ := by
    rintro ⟨τ, hτ⟩
    have e' : τ * k₀ * (τ : G)⁻¹ = 1 := congrArg Subtype.val hτ
    apply hk₀1
    calc k₀ = (τ : G)⁻¹ * (τ * k₀ * (τ : G)⁻¹) * τ := by group
      _ = 1 := by rw [e']; group
  have hlt : Nat.card T₂ < Nat.card ((𝓥 : Subgroup G) ⊓ prodFactorTwo ψ₂ : Subgroup G) := by
    classical
    have := Fintype.ofFinite T₂
    have := Fintype.ofFinite ((𝓥 : Subgroup G) ⊓ prodFactorTwo ψ₂ : Subgroup G)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_lt_of_injective_of_notMem φ hφinj hφ1
  have hKle : Nat.card ((𝓥 : Subgroup G) ⊓ prodFactorTwo ψ₂ : Subgroup G) ≤ 2 ^ f := by
    refine card_le_of_inf_prodFactorOne_eq_bot hf1 hk₂ ψ₂ (inf_le_left.trans hVM)
      (hV2.to_le inf_le_left) (eq_bot_iff.2 fun x hx => ?_)
    have hx' : x ∈ prodFactorOne ψ₂ ⊓ prodFactorTwo ψ₂ :=
      mem_inf.2 ⟨(mem_inf.1 hx).2, (mem_inf.1 (mem_inf.1 hx).1).2⟩
    rwa [Common.prodFactorOne_inf_prodFactorTwo] at hx'
  rw [hT2card] at hlt
  omega

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
