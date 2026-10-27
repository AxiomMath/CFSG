module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8Cfg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T6D

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

private theorem quotMk_injective_of_isPGroup {Ht R : Subgroup T} (hRHt : R ≤ Ht)
    (hR : IsPGroup 2 R) :
    Function.Injective ((QuotientGroup.mk' (classicalInvolutionOddCore ↥Ht)).comp
      (Subgroup.inclusion hRHt)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : Subgroup.inclusion hRHt a ∈ classicalInvolutionOddCore ↥Ht :=
    (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨k, hk⟩ := hR a
  have hodd : Odd (orderOf (Subgroup.inclusion hRHt a)) :=
    (CFSG.ComponentClassification.OddCore.odd_card ↥Ht).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ h1)
  have hk' : (Subgroup.inclusion hRHt a) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have h3 : Subgroup.inclusion hRHt a = 1 :=
    orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow hodd (orderOf_dvd_of_pow_eq_one hk'))
  exact Subgroup.inclusion_injective hRHt (by rw [h3, map_one])

theorem exists_inner_mod (cfg : L3E8Cfg K z J zJ H Q E S) {U : Subgroup T} (hU : IsElemAbelian 2 U)
    (h4 : Nat.card U = 4) (hUN : U ≤ Subgroup.normalizer (firstFactor K : Set T)) :
    ∃ u ∈ U, u ≠ 1 ∧ ∃ x ∈ firstFactor K, ∃ R₀ : Subgroup T, IsSylow2In R₀ K ∧ ∃ k ∈ R₀,
      orderOf k = 4 ∧ u * (x * k * x⁻¹) * u⁻¹ * (x * k * x⁻¹)⁻¹ ∈ oddCoreOf (firstFactor K) := by
  classical
  obtain ⟨F, hF⟩ := cfg.faithful
  let ρ : ↥U →* MulAut (SecQuot (firstFactor K)) :=
    (s26Act (firstFactor K)).comp (Subgroup.inclusion hUN)
  obtain ⟨u, hu1, y, hy⟩ :
      ∃ u : ↥U, u ≠ 1 ∧ ∃ y : SecQuot (firstFactor K), ρ u = MulAut.conj y := by
    by_cases hinj : Function.Injective ρ
    · have hA : Nat.card ρ.range = 4 :=
        (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans h4
      obtain ⟨φ, ⟨u, rfl⟩, hφ1, ⟨y, hy⟩⟩ := FaithfulL3E8.exists_inner hF ρ.range hA
      exact ⟨u, fun h => hφ1 (by rw [h, map_one]), y, hy.symm⟩
    · obtain ⟨u, hu, hu1⟩ : ∃ u : ↥U, ρ u = 1 ∧ u ≠ 1 := by
        by_contra hcon
        apply hinj
        rw [injective_iff_map_eq_one]
        intro a ha
        by_contra ha1
        exact hcon ⟨a, ha, ha1⟩
      exact ⟨u, hu1, 1, by rw [hu, map_one]⟩
  have hu2 : u * u = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq]
    exact hU.2 u u.2)
  have hyy : y * y = 1 := by
    have h1 : MulAut.conj (y * y) = 1 := by rw [map_mul, ← hy, ← map_mul, hu2, map_one]
    have h2 : y * y ∈ Subgroup.center (SecQuot (firstFactor K)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun φ : MulAut (SecQuot (firstFactor K)) => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * (y * y) = (y * y) * g * (y * y)⁻¹ * (y * y) := by rw [h3]
        _ = (y * y) * g := by group
    rw [FaithfulL3E8.center_eq_bot hF] at h2
    exact Subgroup.mem_bot.mp h2
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup T))
    (bot_le : (⊥ : Subgroup T) ≤ K)
  have hKHt : K ≤ firstFactor K :=
    (le_omegaGen (Relation.ReflTransGen.refl :
      K ∈ aStar (CoreAssembly.conjClass K) K)).trans le_sup_left
  have hR₀Ht : R₀ ≤ firstFactor K := hR₀.1.trans hKHt
  set φ : ↥R₀ →* SecQuot (firstFactor K) :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))).comp
      (Subgroup.inclusion hR₀Ht)
  have hφinj : Function.Injective φ := quotMk_injective_of_isPGroup hR₀Ht hR₀.2.1
  obtain ⟨e8⟩ := cfg.datum.quat R₀ hR₀
  have hP : Nonempty (↥φ.range ≃* QuaternionGroup 2) :=
    ⟨(MonoidHom.ofInjective hφinj).symm.trans e8⟩
  obtain ⟨xb, kb, hkbP, hkb4, hcomm⟩ := FaithfulL3E8.involution_cent_order_four hF hP hyy
  obtain ⟨k, rfl⟩ := hkbP
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  refine ⟨u, u.2, fun h => hu1 (Subtype.ext h), x, x.2, R₀, hR₀, k, k.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, ← orderOf_injective φ hφinj k]
    exact hkb4
  ·
    set w : ↥(firstFactor K) := x * Subgroup.inclusion hR₀Ht k * x⁻¹ with hw
    have huw : (u : T) * (w : T) * (u : T)⁻¹ ∈ firstFactor K :=
      (Subgroup.mem_normalizer_iff.mp (hUN u.2) (w : T)).mp w.2
    set w' : ↥(firstFactor K) := ⟨(u : T) * (w : T) * (u : T)⁻¹, huw⟩
    have hact : ρ u (w : SecQuot (firstFactor K)) = (w' : SecQuot (firstFactor K)) :=
      s26Act_mk (firstFactor K) (Subgroup.inclusion hUN u) w w' rfl
    have hwb : (w : SecQuot (firstFactor K)) =
        (x : SecQuot (firstFactor K)) * φ k * (x : SecQuot (firstFactor K))⁻¹ := by
      rw [hw, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rfl
    have heq : (w' : SecQuot (firstFactor K)) = (w : SecQuot (firstFactor K)) := by
      rw [← hact, hy, MulAut.conj_apply, hwb, hcomm, mul_inv_cancel_right]
    have hc : (w' * w⁻¹ : ↥(firstFactor K)) ∈ classicalInvolutionOddCore ↥(firstFactor K) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, heq,
        mul_inv_cancel]
    exact mem_oddCoreOf_iff.mpr ⟨(w' * w⁻¹).2, hc⟩

theorem inner (cfg : L3E8Cfg K z J zJ H Q E S) {U : Subgroup T} (hU : IsElemAbelian 2 U)
    (h4 : Nat.card U = 4) (hUN : U ≤ Subgroup.normalizer (firstFactor K : Set T)) :
    ∃ u ∈ U, u ≠ 1 ∧ ∃ M' ∈ sigmaOf K, ∃ X' ∈ USet (CoreAssembly.conjClass K),
      X' ≤ M' ∧ X' ≤ Subgroup.centralizer ({u} : Set T) := by
  obtain ⟨u, huU, hu1, x, hx, R₀, hR₀, k, hk, hk4, hc⟩ := cfg.exists_inner_mod hU h4 hUN
  have hu2 : u * u = 1 := by rw [← pow_two]; exact hU.2 u huU
  obtain ⟨M', hM', X', hX', h1, h2⟩ :=
    cfg.toFrameCfg.cent_of_mod_odd hu2 (hUN huU) hx hR₀ hk hk4 hc
  exact ⟨u, huU, hu1, M', hM', X', hX', h1, h2⟩

end L3E8Cfg

section ClashLemmas

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem l3e8_clash (cfg : L3E8Cfg K z J zJ H Q E S) {g : T} {U : Subgroup T}
    (hU : IsElemAbelian 2 U) (h4 : Nat.card U = 4)
    (hUN : U ≤ Subgroup.normalizer (firstFactor K : Set T)) (hUE : U ≤ rightConjugate E g) :
    g ∈ sigmaNorm K := by
  obtain ⟨u, huU, hu1, M', hM', X', hX', hX'M', hX'c⟩ := cfg.inner hU h4 hUN
  have hu2 : u * u = 1 := by rw [← pow_two]; exact hU.2 u huU
  exact cfg.toFrameQCfg.clash cfg.efacts hu2 hu1 ((mem_rightConjugate_iff E g u).mp (hUE huU))
    hM' hX' hX'M' hX'c

end ClashLemmas

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
