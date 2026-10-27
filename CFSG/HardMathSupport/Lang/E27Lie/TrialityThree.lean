module

public import CFSG.HardMathSupport.Lang.E27Lie.TrialityThreeBound
public import CFSG.HardMathSupport.Lang.Triality.Char3Sylow
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.Sporadic.Suz.Simple

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E27Lie

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.Triality
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem card_layerN_zero {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) :
    Nat.card (layerN σ 0) = (3 ^ f) ^ 12 := by
  classical
  have hsub : (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = layerN σ 0 := by
    ext x
    rw [Subgroup.mem_subgroupOf, mem_layerN, Nat.cast_one, heightSeries_one]
    constructor
    · intro hx
      exact (Subgroup.mem_inf.1 hx).1
    · intro hx
      exact Subgroup.mem_inf.2 ⟨hx, graphFixedRootGroup_le _ K σ.toRingHom x.2⟩
  rw [← hsub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).toEquiv,
    CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedPosUnipotent σ.surjective
      (CFSG.Timmesfeld.ExceptionalOrders.card_orbitField Nat.prime_three hf hK
        (σ := σ.toRingHom) hσ),
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_twistedD4]

theorem card_fixed_layerN_zero_ge {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    [CharP K 3] (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
    {u : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hu : (u : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    (hβ3 : betaAut σ u ^ 3 = 1) :
    (3 ^ f) ^ 3 ≤ Nat.card {x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) //
      x ∈ layerN σ 0 ∧ betaAut σ u x = x} := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Fintype.ofFinite _
  have hq : Nat.card {c : K // σ c = c} = 3 ^ f := by
    have h := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ
    rw [← h]
    exact Nat.card_congr (Equiv.refl _)
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    exact ringEquiv_cube_apply_eq hK hσ c
  have hσ1 : σ ≠ 1 := by
    intro h
    have hc : Nat.card K = 3 ^ f := by
      rw [← hq]
      refine Nat.card_congr (Equiv.subtypeUnivEquiv fun c => ?_).symm
      simp [h]
    have hp1 : 1 < 3 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
    rw [hK] at hc
    nlinarith [hp1, pow_pos (lt_trans Nat.zero_lt_one hp1) 2]
  have hKq : Nat.card K = Nat.card {c : K // σ c = c} ^ 3 := by rw [hq, hK]
  have huP : (u : ModGL TwistTag.D4.tag K) ∈ posUnipotent TwistTag.D4.tag K :=
    (Subgroup.mem_inf.1 hu).1
  have hcardN := card_layerN_zero hf hK σ hσ
  set d := (maxHeight TwistTag.D4.tag).toNat with hd
  set b : ℕ → ℕ := fun k => (3 ^ f) ^ ∑ O ∈ orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ),
    orbitWeight O with hb
  have hbd : ∀ k, k < d → Nat.card {a : LayerCoord (K := K) k // a ∈ (layerPhi σ k).range ∧
      a * layerTau σ k a * layerTau σ k (layerTau σ k a) = 1} ≤ b k := fun k _ => by
    have := layer_bound σ hσ3 hσ1 hKq k
    rwa [hq] at this
  have hcd := (cocycleData_layers σ huP b hbd).card_cocycle_le
  have hq0 : 0 < 3 ^ f := by positivity
  have hprod : ∏ j ∈ Finset.range d, b j ≤ (3 ^ f) ^ 9 := by
    rw [hb]
    simp only
    rw [Finset.prod_pow_eq_pow_sum]
    refine Nat.pow_le_pow_right hq0 ?_
    have h9 := sum_orbitWeight_le d
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) h9
    rw [orbitsAt_D4_eq _ (by positivity)]
  have hZ := hcd.trans hprod
  have hH : ∀ x ∈ layerN σ 0, betaAut σ u x ∈ layerN σ 0 := fun x hx =>
    betaAut_mem_layerN σ huP 0 hx
  have hmain := card_le_card_cocycle_mul_card_fixed (betaAut σ u) hβ3 (layerN σ 0) hH
  rw [hcardN] at hmain
  have h3 : (3 ^ f) ^ 9 * (3 ^ f) ^ 3 ≤ (3 ^ f) ^ 9 * Nat.card {x : ↥(graphFixedRootGroup
      TwistTag.D4 K σ.toRingHom) // x ∈ layerN σ 0 ∧ betaAut σ u x = x} := by
    calc (3 ^ f) ^ 9 * (3 ^ f) ^ 3 = (3 ^ f) ^ 12 := by rw [← pow_add]
      _ ≤ _ := hmain
      _ ≤ _ := Nat.mul_le_mul_right _ hZ
  exact Nat.le_of_mul_le_mul_left h3 (by positivity)

theorem twentySeven_dvd_fixedSubgroup_trialityD4_three {f : ℕ} (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] [CharP K 3] (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (3 ^ f))
    (α : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    27 ∣ Nat.card ↥(fixedSubgroup α) := by
  classical
  obtain ⟨u, hu, hβ3, hcard⟩ := exists_unipotent_conj_fieldActor_of_order_three hf hK σ hσ α hα3
    hαin
  have hβ3' : betaAut σ u ^ 3 = 1 := hβ3
  have hge := card_fixed_layerN_zero_ge hf hK σ hσ hu hβ3'
  rw [hcard]
  set β := betaAut σ u with hβ
  set S : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    layerN σ 0 ⊓ fixedSubgroup β with hS
  have hSc : Nat.card S = Nat.card {x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) //
      x ∈ layerN σ 0 ∧ β x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Subgroup.mem_inf)
  have hN := card_layerN_zero hf hK σ hσ
  have hdvd : Nat.card S ∣ (3 ^ f) ^ 12 := by
    rw [← hN]
    exact Subgroup.card_dvd_of_le inf_le_left
  rw [← pow_mul] at hdvd
  obtain ⟨j, hj, hjS⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have h27 : 27 ≤ 3 ^ j := by
    rw [← hjS, hSc]
    refine le_trans ?_ (pow_mul 3 f 3 ▸ hge)
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (f * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hj3 : 3 ≤ j := by
    by_contra hlt
    have : 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine dvd_trans ?_ (Subgroup.card_dvd_of_le (inf_le_right : S ≤ fixedSubgroup β))
  rw [hjS]
  exact (pow_dvd_pow 3 hj3 : 3 ^ 3 ∣ 3 ^ j)

theorem twentySeven_dvd_fixedSubgroup_trialityD4_three_model {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Group K] [Finite K] (hmodel : CFSG.Blueprint.TwistedChevalleyModel K .D4 (3 ^ f))
    (α : MulAut K) (hα3 : α ^ 3 = 1) (hαin : α ∉ inner K) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  obtain ⟨K', _, _, σ, hcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_three hf hmodel
  have hcard' : Nat.card K' = (3 ^ f) ^ 3 := hcard
  have : CharP K' 3 := by
    have : Fintype K' := Fintype.ofFinite K'
    have h : Fintype.card K' = 3 ^ (f * 3) := by
      rw [← Nat.card_eq_fintype_card, hcard', ← pow_mul]
    exact charP_of_card_eq_prime_pow h
  have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβout : MulAut.congr e α ∉ inner (graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) :=
    fun hin => hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e α).mp hin)
  rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr e α]
  exact twentySeven_dvd_fixedSubgroup_trialityD4_three hf hcard' σ hσ _ hβ3 hβout

end CFSG.HardMathSupport.Lang.E27Lie
