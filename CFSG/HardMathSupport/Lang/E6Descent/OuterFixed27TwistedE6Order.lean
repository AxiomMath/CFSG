module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27Arith
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import Certificates.Data.ExceptionalSL3

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Classical2
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.E6Pilot (numTwistedE6)

set_option linter.unusedSectionVars false


theorem card_graphFixedRootGroup_E6_mul_gcd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (graphFixedRootGroup TwistTag.E6 K σ) * Nat.gcd 3 (ℓ ^ f + 1) =
      numTwistedE6 (ℓ ^ f) := by
  classical
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have : Fintype (WeylGroup TwistTag.E6.tag) := Fintype.ofFinite _
  have hC0 := card_graphFixedRootGroup hσsurj
    (card_orbitField (t := TwistTag.E6) hℓ hf hK hσ)
  rw [sum_length_relWeylTwist_E6, ncard_posRoots_twistedE6] at hC0
  have hcompat := natCard_compatTorus_E6_mul hℓ hf hK hσ
  unfold numTwistedE6
  rw [hC0, ← ordTwistedE6_mul _ hq1]
  have e : ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 2 - 1) * (ℓ ^ f - 1) * (ℓ ^ f - 1) =
      Nat.card (compatTorus (t := TwistTag.E6) σ) * Nat.gcd 3 (ℓ ^ f + 1) := by
    rw [hcompat]
    ring
  rw [e]
  ring

theorem twentySeven_dvd_card_twistedE6RootGroup {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    27 ∣ Nat.card (graphFixedRootGroup TwistTag.E6 K σ) := by
  have h := card_graphFixedRootGroup_E6_mul_gcd hℓ hf hK hσ
  have h81 := CFSG.HardMathSupport.Lang.E6Descent.eightyOne_dvd_numTwistedE6 (ℓ ^ f)
    (Nat.one_le_pow _ _ hℓ.pos)
  rw [← h] at h81
  have h3 : Nat.card (graphFixedRootGroup TwistTag.E6 K σ) * Nat.gcd 3 (ℓ ^ f + 1) ∣
      Nat.card (graphFixedRootGroup TwistTag.E6 K σ) * 3 :=
    Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_left 3 _)
  have := h81.trans h3
  rwa [show (81 : ℕ) = 27 * 3 by norm_num, Nat.mul_dvd_mul_iff_right (by norm_num)] at this

theorem fieldAut_four_data {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ (2 * (d * 3))) (ε : K ≃+* K)
    (hε : ∀ c, ε c = c ^ ℓ ^ (d * (3 + 1))) :
    orderOf ε = 3 ∧ ∀ c, ε c = c → c ^ ℓ ^ (2 * d) = c := by
  have h6 : 1 ≤ 2 * (d * 3) := by omega
  obtain ⟨fr, hfr, hord, -, -, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ h6 hK
  have hεfr : ε = fr ^ (d * (3 + 1)) :=
    RingEquiv.ext fun c => by rw [hε, ringAut_pow_apply_of_frobenius hfr]
  have hε3 : ε ^ 3 = 1 := by
    rw [hεfr, ← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hord]; exact ⟨2, by ring⟩)
  have hε1 : ε ≠ 1 := by
    intro h1
    rw [hεfr] at h1
    have := Nat.le_of_dvd (by omega) (hord ▸ orderOf_dvd_iff_pow_eq_one.2 h1)
    omega
  refine ⟨orderOf_eq_prime hε3 hε1, fun c hc => ?_⟩
  have h2 : (fr ^ (2 * d)) c = c := by
    have e : fr ^ (2 * d) = ε ^ 2 := by
      rw [hεfr, ← pow_mul]
      have h6' : fr ^ (2 * (d * 3)) = 1 := hord ▸ pow_orderOf_eq_one fr
      have : d * (3 + 1) * 2 = 2 * d + 2 * (d * 3) := by ring
      rw [this, pow_add, h6', mul_one]
    rw [e, pow_two, RingAut.mul_apply, hc, hc]
  rwa [ringAut_pow_apply_of_frobenius hfr] at h2

theorem twentySeven_dvd_card_fixedSubgroup_fieldActor {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * (d * 3))) (σ ε : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ ℓ ^ (d * 3)) (hε : ∀ c, ε c = c ^ ℓ ^ (d * (3 + 1))) :
    27 ∣ Nat.card (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)) := by
  classical
  have h6 : 1 ≤ 2 * (d * 3) := by omega
  obtain ⟨hεo, hεS⟩ := fieldAut_four_data hℓ hd K hK ε hε
  obtain ⟨-, hSc⟩ := card_fixSubfield hℓ h6 hK ε
  set S := fixSubfield ε with hS
  have hSQ : Nat.card S = (ℓ ^ d) ^ 2 := by
    rw [hSc, hεo, ← pow_mul, show 2 * (d * 3) / 3 = d * 2 by omega]
  have : Finite S := inferInstance
  let σ₀ : S ≃+* S := fixSubfieldRestrict σ ε
  have hσ₀ : ∀ c, σ₀ c = c ^ ℓ ^ d := fun c => by
    refine Subtype.ext ?_
    have hc : (c : K) ^ ℓ ^ (2 * d) = c := hεS c c.2
    change σ (c : K) = ((c : K)) ^ ℓ ^ d
    rw [hσ, show d * 3 = 2 * d + d by ring, pow_add, pow_mul, hc]
  have hle : (graphFixedRootGroup TwistTag.E6 S σ₀.toRingHom).map
      (baseChangeGL (τ := TwistTag.E6.tag) S.subtype) ≤
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    map_baseChangeGL_graphFixedRootGroup_le (σ := σ₀.toRingHom) (Fr := σ.toRingHom)
      (ι := S.subtype) σ₀.surjective fun _ => rfl
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  set J := (graphFixedRootGroup TwistTag.E6 S σ₀.toRingHom).map
    (baseChangeGL (τ := TwistTag.E6.tag) S.subtype) with hJ
  have hJfix : J.subgroupOf C ≤ fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.1 hx
    refine Subtype.ext ?_
    change Units.map (entrywiseHom ε.toRingHom) (x : ModGL TwistTag.E6.tag K) = x
    rw [← hyx, units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL]
    congr 2
    exact RingHom.ext fun c => c.2
  have hcardJ : Nat.card J = Nat.card (graphFixedRootGroup TwistTag.E6 S σ₀.toRingHom) :=
    Subgroup.card_map_of_injective (baseChangeGL_injective _)
  have h27 := twentySeven_dvd_card_twistedE6RootGroup hℓ hd hSQ (σ := σ₀.toRingHom) hσ₀
  have hsub : Nat.card (J.subgroupOf C) = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [← hcardJ, ← hsub] at h27
  exact h27.trans (Subgroup.card_dvd_of_le hJfix)

end CFSG.HardMathSupport.Lang.Coordinator
