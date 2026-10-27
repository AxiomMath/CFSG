module

public import CFSG.LocalAnalysis.EvenBN.U4.Layers
public import CFSG.LocalAnalysis.EvenBN.Common.ProdFactors
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Foundations
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearStageZero
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Walter.J1
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import CFSG.Walter.W67.W2Lemma26A
public import Certificates.Certificate110
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8026Base
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo card_sup_mul_card_inf_eq)
open scoped MatrixGroups

theorem card_le_of_isPGroup_of_sl2 {X : Type*} [Group X] [Finite X] {k : Type*} [Field k]
    [Finite k] {m : ℕ} (e : X ≃* SL(2, k)) (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m)
    {P : Subgroup X} (hP : IsPGroup 2 P) : Nat.card P ≤ Nat.card k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : Nat.card P ∣ Nat.card k * (Nat.card k ^ 2 - 1) := by
    rw [← CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, ← Nat.card_congr e.toEquiv]
    exact Subgroup.card_subgroup_dvd_card P
  have hodd : Odd (Nat.card k ^ 2 - 1) := by
    have h1 : Even (Nat.card k ^ 2) := by
      rw [hk]
      exact (Nat.even_pow.2 ⟨even_two, by omega⟩).pow_of_ne_zero two_ne_zero
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by rw [hk]; positivity)) h1 odd_one
  have hcop : Nat.Coprime (Nat.card P) (Nat.card k ^ 2 - 1) := by
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd)
  exact Nat.le_of_dvd (by rw [hk]; positivity) (hcop.dvd_of_dvd_mul_right hdvd)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

section SwapGeneral

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

theorem W2_le_normalizer_W1 (_hS : Setting h L η t Q T) :
    𝓦 ⊓ prodFactorTwo ψ ≤
      normalizer ((𝓦 ⊓ prodFactorOne ψ : Subgroup G) : Set G) := by
  intro x hx
  have hxC : x ∈ centralizer (prodFactorOne ψ : Set G) :=
    Common.prodFactorTwo_le_centralizer ψ (mem_inf.1 hx).2
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hc : y * x = x * y := mem_centralizer_iff.1 hxC y (mem_inf.1 hy).2
    rw [← hc, mul_inv_cancel_right]
    exact hy
  · intro hy
    have hc : (x * y * x⁻¹) * x = x * (x * y * x⁻¹) :=
      mem_centralizer_iff.1 hxC _ (mem_inf.1 hy).2
    have e : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * ((x * y * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [hc]
        _ = x * y * x⁻¹ := by group
    rw [e]
    exact hy

theorem W1_inf_W2 (_hS : Setting h L η t Q T) :
    (𝓦 ⊓ prodFactorOne ψ) ⊓ (𝓦 ⊓ prodFactorTwo ψ) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  rw [← Common.prodFactorOne_inf_prodFactorTwo ψ]
  exact mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).2, (mem_inf.1 (mem_inf.1 hx).2).2⟩

end SwapGeneral

section Swap

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

theorem t_mem_normalizer_M1 (hS : Setting h L η t Q T) :
    t ∈ normalizer (miyamotoM1G h L η t : Set G) :=
  hS.sec3_12_one.2.1 hS.t_mem_H1

theorem t_conj_mem_X2 (hS : Setting h L η t Q T)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    {x : G} (hx : x ∈ prodFactorOne ψ) : t⁻¹ * x * t ∈ prodFactorTwo ψ :=
  Common.conj_mem_prodFactorTwo_of_swap ψ hS.t_mem_normalizer_M1 hψt hx

theorem t_conj_mem_X1 (hS : Setting h L η t Q T)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    {x : G} (hx : x ∈ prodFactorTwo ψ) : t⁻¹ * x * t ∈ prodFactorOne ψ :=
  Common.conj_mem_prodFactorOne_of_swap ψ hS.t_mem_normalizer_M1 hψt hx

theorem card_W_inf_X2_ge [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) :
    (2 ^ f) ^ 2 ≤ Nat.card (𝓦 ⊓ prodFactorTwo ψ : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWM : 𝓦 ≤ miyamotoM1G h L η t := hS.sec3_12_one.2.2.2.2.1
  let φ : (𝓦 : Subgroup G) →* SL(2, k) :=
    (MonoidHom.fst _ _).comp (ψ.toMonoidHom.comp (Subgroup.inclusion hWM))
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hW2 : IsPGroup 2 (𝓦 : Subgroup G) := hS.isPGroup_RG.to_le inf_le_left
  have hk' : Nat.card k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
  have hrange : Nat.card φ.range ≤ (2 ^ f) ^ 2 := by
    have := card_le_of_isPGroup_of_sl2 (MulEquiv.refl _) hk' (by have := hS.two_le; omega)
      (P := φ.range) (hW2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
    rwa [hk', mul_comm, pow_mul] at this
  have hker : Nat.card φ.ker = Nat.card (𝓦 ⊓ prodFactorTwo ψ : Subgroup G) := by
    have e : φ.ker.map (𝓦 : Subgroup G).subtype = 𝓦 ⊓ prodFactorTwo ψ := by
      ext g
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine mem_inf.2 ⟨w.2, (Common.mem_prodFactorTwo_iff ψ).2 ⟨hWM w.2, ?_⟩⟩
        exact hw
      · intro hg
        obtain ⟨hgW, hg2⟩ := mem_inf.1 hg
        obtain ⟨hgM, hg1⟩ := (Common.mem_prodFactorTwo_iff ψ).1 hg2
        exact ⟨⟨g, hgW⟩, hg1, rfl⟩
    rw [← e, card_map_of_injective (𝓦 : Subgroup G).subtype_injective]
  rw [hker, hS.card_W] at h1
  have h2 : (2 ^ f) ^ 4 ≤ Nat.card (𝓦 ⊓ prodFactorTwo ψ : Subgroup G) * (2 ^ f) ^ 2 := by
    rw [← h1]
    exact Nat.mul_le_mul_left _ hrange
  have : (2 ^ f) ^ 4 = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by ring
  rw [this] at h2
  exact Nat.le_of_mul_le_mul_right h2 (by positivity)

theorem card_W_inf_X1_ge [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) :
    (2 ^ f) ^ 2 ≤ Nat.card (𝓦 ⊓ prodFactorOne ψ : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWM : 𝓦 ≤ miyamotoM1G h L η t := hS.sec3_12_one.2.2.2.2.1
  let φ : (𝓦 : Subgroup G) →* SL(2, k) :=
    (MonoidHom.snd _ _).comp (ψ.toMonoidHom.comp (Subgroup.inclusion hWM))
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hW2 : IsPGroup 2 (𝓦 : Subgroup G) := hS.isPGroup_RG.to_le inf_le_left
  have hk' : Nat.card k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
  have hrange : Nat.card φ.range ≤ (2 ^ f) ^ 2 := by
    have := card_le_of_isPGroup_of_sl2 (MulEquiv.refl _) hk' (by have := hS.two_le; omega)
      (P := φ.range) (hW2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
    rwa [hk', mul_comm, pow_mul] at this
  have hker : Nat.card φ.ker = Nat.card (𝓦 ⊓ prodFactorOne ψ : Subgroup G) := by
    have e : φ.ker.map (𝓦 : Subgroup G).subtype = 𝓦 ⊓ prodFactorOne ψ := by
      ext g
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine mem_inf.2 ⟨w.2, (Common.mem_prodFactorOne_iff ψ).2 ⟨hWM w.2, ?_⟩⟩
        exact hw
      · intro hg
        obtain ⟨hgW, hg1⟩ := mem_inf.1 hg
        obtain ⟨hgM, hg2⟩ := (Common.mem_prodFactorOne_iff ψ).1 hg1
        exact ⟨⟨g, hgW⟩, hg2, rfl⟩
    rw [← e, card_map_of_injective (𝓦 : Subgroup G).subtype_injective]
  rw [hker, hS.card_W] at h1
  have h2 : (2 ^ f) ^ 4 ≤ Nat.card (𝓦 ⊓ prodFactorOne ψ : Subgroup G) * (2 ^ f) ^ 2 := by
    rw [← h1]
    exact Nat.mul_le_mul_left _ hrange
  have : (2 ^ f) ^ 4 = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by ring
  rw [this] at h2
  exact Nat.le_of_mul_le_mul_right h2 (by positivity)

theorem W_eq_sup [Fintype k] (hS : Setting h L η t Q T) (hk : Fintype.card k = (2 ^ f) ^ 2) :
    (𝓦 ⊓ prodFactorOne ψ) ⊔ (𝓦 ⊓ prodFactorTwo ψ) = 𝓦 ∧
      Nat.card (𝓦 ⊓ prodFactorOne ψ : Subgroup G) = (2 ^ f) ^ 2 ∧
      Nat.card (𝓦 ⊓ prodFactorTwo ψ : Subgroup G) = (2 ^ f) ^ 2 := by
  have h1 := card_sup_mul_card_inf_eq (hS.W2_le_normalizer_W1 (ψ := ψ))
  rw [hS.W1_inf_W2, card_bot, mul_one] at h1
  have hle : (𝓦 ⊓ prodFactorOne ψ) ⊔ (𝓦 ⊓ prodFactorTwo ψ) ≤ 𝓦 :=
    sup_le inf_le_left inf_le_left
  have hcardle := Subgroup.card_le_of_le hle
  rw [h1, hS.card_W] at hcardle
  have g1 := hS.card_W_inf_X1_ge (ψ := ψ) hk
  have g2 := hS.card_W_inf_X2_ge (ψ := ψ) hk
  set a := Nat.card (𝓦 ⊓ prodFactorOne ψ : Subgroup G)
  set b := Nat.card (𝓦 ⊓ prodFactorTwo ψ : Subgroup G)
  set q2 := (2 ^ f) ^ 2 with hq2
  have hq4 : (2 ^ f) ^ 4 = q2 * q2 := by rw [hq2]; ring
  rw [hq4] at hcardle
  have hpos : 0 < q2 := by positivity
  have ha : a = q2 := by
    refine le_antisymm ?_ g1
    have : a * q2 ≤ q2 * q2 := (Nat.mul_le_mul_left a g2).trans hcardle
    exact Nat.le_of_mul_le_mul_right this hpos
  have hb : b = q2 := by
    refine le_antisymm ?_ g2
    have : q2 * b ≤ q2 * q2 := (Nat.mul_le_mul_right b g1).trans hcardle
    exact Nat.le_of_mul_le_mul_left this hpos
  refine ⟨Subgroup.eq_of_le_of_card_ge hle ?_, ha, hb⟩
  rw [h1, hS.card_W, ha, hb, hq4]

theorem t_conj_mem_W1 (hS : Setting h L η t Q T)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    {w : G} (hw : w ∈ 𝓦 ⊓ prodFactorTwo ψ) : t⁻¹ * w * t ∈ 𝓦 ⊓ prodFactorOne ψ := by
  obtain ⟨hwW, hw2⟩ := mem_inf.1 hw
  obtain ⟨hwR, hwC⟩ := mem_inf.1 hwW
  have hR : t⁻¹ * w * t ∈ miyamotoRG h L η t Q := by
    have := (mem_normalizer_iff.1 (inv_mem hS.t_mem_normalizer_RG) w).1 hwR
    rwa [inv_inv] at this
  have hC : t⁻¹ * w * t ∈ centralizer (miyamotoI1G h L η : Set G) := by
    have := (mem_normalizer_iff.1 (inv_mem hS.t_mem_normalizer_centralizer_I1) w).1 hwC
    rwa [inv_inv] at this
  exact mem_inf.2 ⟨mem_inf.2 ⟨hR, hC⟩, hS.t_conj_mem_X1 hψt hw2⟩

end Swap

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
