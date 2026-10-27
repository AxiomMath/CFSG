module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33ReeTools
public import CFSG.LieType.Ree.LargeReeInvolutionIntermediateOddCore

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.Ree

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.LargeReeInvolution

theorem largeRee_not_isPGroup
    {m : ℕ} (hm : 1 ≤ m) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * m + 1))
    (α : MulAut ↥(ReeTag.F4.reeGamma K m)) (hα : orderOf α = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints α) ⧸ pPrimeCore 2 ↥(fixedPoints α)) := by
  have := finite_modGL (τ := ReeTag.F4.tag) (K := K)
  obtain ⟨hinn, -⟩ :=
    large_Ree_all_intermediate_involution_centralizers_odd_core_free m hm K hK
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (hinn ⊤ le_top α (mem_top α) hα).1
  have hx : orderOf x = 2 := by
    rw [← orderOf_injective _ (ReeTag.conj_injective_of_center_eq_bot
      (ReeTag.large_Ree_fixed_group_center_trivial m K hK)) x]
    exact hα
  have hx2 : (x : ModGL ReeTag.F4.tag K) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
  have hx1 : (x : ModGL ReeTag.F4.tag K) ≠ 1 := by
    intro h
    have h1 : x = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hq : (2 : ℕ) ∣ 2 ^ (2 * m + 1) := dvd_pow_self 2 (by omega)
  rw [fixedPoints_conj]
  intro hP
  obtain ⟨hz, -, -, -, ⟨eSz⟩, ht, -, -, -, -, ⟨eSL⟩, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  rcases (large_Ree_every_involution_fuses m hm K hK).1 _ x.2 hx2 hx1 with
    ⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩
  · have hP' := isPGroup_centralizer_conj x ⟨y, hy⟩ hP
    set x' : ReeTag.F4.reeGamma K m := ⟨y, hy⟩ * x * ⟨y, hy⟩⁻¹ with hx'
    have hx'v : (x' : ModGL ReeTag.F4.tag K) = centralZ K m 1 := by
      rw [hx', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hyx.trans (sylowH_zero_eq_centralZ 1)
    have hle : rankOneGroupTwo K m ≤ ReeTag.F4.reeGamma K m ⊓
        centralizer {(x' : ModGL ReeTag.F4.tag K)} := by
      rw [hx'v, hz]
      exact le_sup_right
    have heven : 2 ∣ Nat.card (CFSG.Blueprint.suzukiGroup m K) := by
      rw [CFSG.LieType.Ree.suzuki_order hK]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow hq (by norm_num)) _) _
    exact not_isPGroup_centralizer x' hle eSz (CFSG.LieType.Ree.suzuki_perfect hm hK).1 heven hP'
  · have hP' := isPGroup_centralizer_conj x ⟨y, hy⟩ hP
    set x' : ReeTag.F4.reeGamma K m := ⟨y, hy⟩ * x * ⟨y, hy⟩⁻¹ with hx'
    have hx'v : (x' : ModGL ReeTag.F4.tag K) = sylowL m K 1 := by
      rw [hx', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hyx
    have hle : rankOneGroupOne K m ≤ ReeTag.F4.reeGamma K m ⊓
        centralizer {(x' : ModGL ReeTag.F4.tag K)} := by
      rw [hx'v, ht]
      exact le_sup_right
    have heven : 2 ∣ Nat.card (SL2 K) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num : 1 ≤ 2), hK]
      exact Dvd.dvd.mul_right (dvd_pow hq (by norm_num)) _
    exact not_isPGroup_centralizer x' hle eSL
      (commutator_eq_top_of_simple (CFSG.LieType.Ree.LargeReeInvolution.isSimpleGroup_SL2 hm hK)
        (exists_SL2_mul_ne_mul (K := K))) heven hP'

theorem largeRee_not_isPGroup_of_model
    (Y : Type) [Group Y] [Finite Y] {p f : ℕ} (hY : Blueprint.ReeTitsModel Y .twistedF4 p f)
    (a : MulAut Y) (ha : orderOf a = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) := by
  obtain ⟨-, -, -, hp, -, hiso⟩ := ReeTag.large_Ree_model_Schreier Y p f hY
  obtain ⟨hadm, m, hfm, K, _, _, hK, ⟨e⟩⟩ := hY
  subst hp
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso m K hfm hK ⟨e⟩
  exact not_isPGroup_of_mulEquiv E
    (largeRee_not_isPGroup (by omega) K (by rw [hK, hfm])) a ha

end CFSG.ComponentClassification.HarrisLit.L33.Ree
