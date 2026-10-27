module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableHN
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNLeaf
public import CFSG.Sporadic.HNOddCore.AlmostSimple
public import CFSG.GH74.Uniqueness.Bender.Aut
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdReduction

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem card_quotient_fusionZStar_eq' {K : Type*} [Group K] (hK : pPrimeCore 2 K = ⊥) :
    Nat.card (K ⧸ Open.fusionZStar K) = Nat.card (K ⧸ center K) :=
  Nat.card_congr ((Sol78.coreQuotientCenterEquiv K).symm.trans (Sol78.centerQuotCongr
    ((QuotientGroup.quotientMulEquivOfEq hK).trans QuotientGroup.quotientBot))).toEquiv

private theorem pPrimeCore_eq_bot_of_isSubnormal' {X : Type*} [Group X] [Finite X]
    (hX : pPrimeCore 2 X = ⊥) {N : Subgroup X} (hN : N.IsSubnormal) : pPrimeCore 2 N = ⊥ := by
  have h := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hN
  rw [hX, inf_bot_eq] at h
  exact (map_eq_bot_iff_of_injective _ N.subtype_injective).mp h

private theorem isSimpleGroup_of_hn'
    {S : Type} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .HN) :
    IsSimpleGroup S ∧ ∃ a b : S, a * b ≠ b * a := by
  have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .HN) :=
    Sporadic.HNSchreier.fam_hn_certified_simplicity.2
  have hS : IsSimpleGroup S := e.isSimpleGroup
  refine ⟨hS, CatFC.nonabelian_of_simple_of_card_ne_prime ?_⟩
  rw [Nat.card_congr e.toEquiv, EvenPump.card_carrier_HN]
  norm_num

@[expose] def HNInnerFixedComponents : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .HN) →
    ∀ u : S, orderOf u = 2 → ∀ T : Subgroup S, T ≤ centralizer ({u} : Set S) →
      IsPComponent 2 (T.subgroupOf (centralizer ({u} : Set S))) →
      Nat.card (↥T ⧸ Open.fusionZStar ↥T) = 44352000

theorem hnInnerFixedComponents_holds :
    HNInnerFixedComponents := by
  intro S _ _ ⟨e⟩ u hu T hTC hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS, hna⟩ := isSimpleGroup_of_hn' e
  have hZ : center S = ⊥ := BMCase.center_eq_bot_of_isSimpleGroup hna
  have hO : pPrimeCore 2 ↥(centralizer ({u} : Set S)) = ⊥ := by
    have h := (Sporadic.HNOddCore.ctuc_hn_almost_simple_involution_centralizer_odd_core_trivial
      (⊤ : Subgroup S) ⟨Subgroup.topEquiv.trans e⟩
      (by rw [Subgroup.coe_top, Subgroup.centralizer_univ, hZ])).2 u hu
    rw [← Sol78.oddCore_eq_pPrimeCore]
    exact h
  have hD : IsComponent (T.subgroupOf (centralizer ({u} : Set S))) :=
    RestrictedStd.isComponent_of_isPComponent_two hO hT
  have hc : Nat.card (↥T ⧸ Open.fusionZStar ↥T) =
      Nat.card (↥(T.subgroupOf (centralizer ({u} : Set S))) ⧸
        center ↥(T.subgroupOf (centralizer ({u} : Set S)))) := by
    rw [← card_quotient_fusionZStar_eq' (pPrimeCore_eq_bot_of_isSubnormal' hO hD.2)]
    exact Nat.card_congr (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hTC).symm).toEquiv
  have hσ : orderOf (MulAut.conj u) = 2 := by
    have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := fun g g' h => by
      have hc : g'⁻¹ * g ∈ center S := Subgroup.mem_center_iff.2 fun x => by
        have hx := congrArg (fun φ : MulAut S => φ x) h
        simp only [MulAut.conj_apply] at hx
        calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
          _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
          _ = g'⁻¹ * g * x := by group
      rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
      exact hc.symm
    rw [orderOf_injective _ hinj u, hu]
  have hF : fixedSubgroup (MulAut.conj u) = centralizer ({u} : Set S) :=
    SeitzReduction.F4Pilot.fixedSubgroup_conj u
  have hD' : IsComponent (T.subgroupOf (fixedSubgroup (MulAut.conj u))) := by
    rw [hF]
    exact hD
  obtain ⟨hin, -⟩ := CatFC.sporadic_rows_hn hS hna e hσ hD'
  have h1 := hin ⟨u, rfl⟩
  rw [hc]
  have h2 : Nat.card (↥(T.subgroupOf (fixedSubgroup (MulAut.conj u))) ⧸
      center ↥(T.subgroupOf (fixedSubgroup (MulAut.conj u)))) = 44352000 := h1
  rw [hF] at h2
  exact h2

@[expose] def HNOuterIndex : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .HN) →
    (MulAut.conj : S →* MulAut S).range.index ≤ 2

theorem hnOuterIndex_holds :
    HNOuterIndex := by
  intro S _ _ ⟨e⟩
  obtain ⟨-, hna⟩ := isSimpleGroup_of_hn' e
  have := (isSimpleGroup_of_hn' e).1
  have hZ : center S = ⊥ := BMCase.center_eq_bot_of_isSimpleGroup hna
  have : Finite (MulAut S) := Finite.of_injective (fun f : MulAut S => f.toEquiv)
    fun _ _ h => MulEquiv.ext fun x => congrArg (fun f : S ≃ S => f x) h
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := fun g g' h => by
    have hc : g'⁻¹ * g ∈ center S := Subgroup.mem_center_iff.2 fun x => by
      have hx := congrArg (fun φ : MulAut S => φ x) h
      simp only [MulAut.conj_apply] at hx
      calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
        _ = g'⁻¹ * g * x := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc.symm
  have : ((MulAut.conj : S →* MulAut S).range).Normal :=
    CFSG.GH74.Uniqueness.Bender.normal_range_conj S
  have hC : Subgroup.centralizer (((MulAut.conj : S →* MulAut S).range : Subgroup (MulAut S)) :
      Set (MulAut S)) = ⊥ := by
    rw [eq_bot_iff]
    intro α hα
    rw [Subgroup.mem_bot]
    ext s
    have h1 : MulAut.conj s * α = α * MulAut.conj s :=
      Subgroup.mem_centralizer_iff.1 hα (MulAut.conj s) ⟨s, rfl⟩
    have h2 : MulAut.conj (α s) = MulAut.conj s := by
      have h3 : α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := by
        ext x
        simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
      rw [← h3, ← h1]
      group
    exact hinj h2
  have hS : Nonempty (↥(MulAut.conj : S →* MulAut S).range ≃* Blueprint.NativeSporadic.HN) :=
    ⟨(MonoidHom.ofInjective hinj).symm.trans e⟩
  rcases (Sporadic.HNOddCore.ctuc_hn_almost_simple_involution_centralizer_odd_core_trivial
    ((MulAut.conj : S →* MulAut S).range) hS hC).1 with h | h <;> omega

end CFSG.ComponentClassification.GSThmB.A10T
