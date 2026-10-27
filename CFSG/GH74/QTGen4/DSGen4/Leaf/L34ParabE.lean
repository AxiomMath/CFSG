module

public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabA
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabB
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34Levi

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.QuasithinUnique.Fin257.L3

theorem parabE_card_of_core_index {Y : Type} [Group Y] (N V : Subgroup Y)
    (hV : CFSG.Open.pCoreOf 2 N = V) (hcard : Nat.card V = 16)
    (hidx : Nat.card (CFSG.Quasithin.oTwoQuot ↥N) = 60) : Nat.card ↥N = 960 := by
  have e1 : Nat.card ↥(CFSG.Open.pCoreOf 2 N) = Nat.card ↥(CFSG.pCore 2 ↥N) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥N) N.subtype
      N.subtype_injective).toEquiv.symm
  have h1 : Nat.card ↥(CFSG.pCore 2 ↥N) = 16 := by
    rw [← e1, hV]
    exact hcard
  have hidx' : (CFSG.pCore 2 ↥N).index = 60 := hidx
  have hmul := Subgroup.card_mul_index (CFSG.pCore 2 ↥N)
  rw [h1, hidx'] at hmul
  omega

theorem card_normalizer_V2 {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F = 4) :
    Nat.card ↥(Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F))) = 960 :=
  parabE_card_of_core_index _ _ pCoreOf_normalizer_V2
    (by rw [card_V2, hq] <;> norm_num) (natCard_oTwoQuot_normalizer_V2 hq)

theorem card_normalizer_V1 {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F = 4) :
    Nat.card ↥(Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F))) = 960 :=
  parabE_card_of_core_index _ _ pCoreOf_normalizer_V1
    (by rw [card_V1, hq] <;> norm_num) (natCard_oTwoQuot_normalizer_V1 hq)

theorem parabE_exists_conj_zpow {Y : Type} [Group Y] (N : Subgroup Y) (hN : Nat.card N = 960)
    {x d : Y} (hx : x ∈ N) (hxo : orderOf x = 3) (hd : d ∈ N) (hdo : orderOf d = 3) :
    ∃ g ∈ N, ∃ k : ℤ, x ^ k = g * d * g⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite N := Nat.finite_of_card_ne_zero (by omega)
  have key : ∀ z : N, orderOf z = 3 → ∃ Q : Sylow 3 N, Subgroup.zpowers z = (Q : Subgroup N) := by
    intro z hz
    have hP : IsPGroup 3 (Subgroup.zpowers z) :=
      IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hz, pow_one]⟩
    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hP
    refine ⟨Q, Subgroup.eq_of_le_of_card_ge hQ ?_⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have hdvd : 3 ^ n ∣ 960 := by
      rw [← hn, ← hN]
      exact Subgroup.card_subgroup_dvd_card _
    have hn1 : n ≤ 1 := by
      by_contra h
      have h9 : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
      have h960 : 3 ^ 2 ∣ 960 := h9.trans hdvd
      norm_num at h960
    rw [Nat.card_zpowers, hz, hn]
    exact le_trans (Nat.pow_le_pow_right (by norm_num : 3 > 0) hn1) (le_of_eq (pow_one 3))
  have hxs : orderOf (⟨x, hx⟩ : N) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hxo
  have hds : orderOf (⟨d, hd⟩ : N) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hdo
  obtain ⟨Qd, hQd⟩ := key ⟨d, hd⟩ hds
  obtain ⟨Qx, hQx⟩ := key ⟨x, hx⟩ hxs
  haveI : Finite (Sylow 3 N) := Sylow.finite_of_finiteIndex Qd
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N Qd Qx
  have hdQd : (⟨d, hd⟩ : N) ∈ (Qd : Subgroup N) := by
    rw [← hQd]
    exact Subgroup.mem_zpowers _
  have hcj : MulAut.conj g • (⟨d, hd⟩ : N) ∈ (Qx : Subgroup N) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hdQd
  rw [← hQx, Subgroup.mem_zpowers_iff] at hcj
  obtain ⟨k, hk⟩ := hcj
  have hsmul : MulAut.conj g • (⟨d, hd⟩ : N) = g * ⟨d, hd⟩ * g⁻¹ := rfl
  rw [hsmul] at hk
  refine ⟨(g : Y), g.2, k, ?_⟩
  have hk' := congrArg Subtype.val hk
  simpa using hk'

theorem parabE_natSec_of_centralizer {Y : Type} [Group Y] (V : Subgroup Y)
    (hN : Nat.card ↥(Subgroup.normalizer (V : Set Y)) = 960) {d : Y}
    (hd : d ∈ Subgroup.normalizer (V : Set Y)) (hdo : orderOf d = 3)
    (hC : ∀ e ∈ V, d * e = e * d → e = 1) :
    NatSec (Subgroup.normalizer (V : Set Y)) ⊥ V := by
  intro x hx hxo e he hcomm
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcomm
  rw [Subgroup.mem_bot]
  have hcx : Commute e x := hcomm
  obtain ⟨g, hgN, k, hk⟩ := parabE_exists_conj_zpow _ hN hx hxo hd hdo
  have hc2 : Commute e (g * d * g⁻¹) := by
    rw [← hk]
    exact hcx.zpow_right k
  have hc3 : (g⁻¹ * e * g) * d = d * (g⁻¹ * e * g) := by
    calc (g⁻¹ * e * g) * d = g⁻¹ * (e * (g * d * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * d * g⁻¹) * e) * g := by rw [hc2.eq]
      _ = d * (g⁻¹ * e * g) := by group
  have hmem : g⁻¹ * e * g ∈ V := by
    refine (Subgroup.mem_normalizer_iff.mp hgN (g⁻¹ * e * g)).mpr ?_
    have h2 : g * (g⁻¹ * e * g) * g⁻¹ = e := by group
    rw [h2]
    exact he
  have h1 : g⁻¹ * e * g = 1 := hC _ hmem hc3.symm
  have h2 : e = g * (g⁻¹ * e * g) * g⁻¹ := by group
  rw [h1, mul_one, mul_inv_cancel] at h2
  exact h2

theorem parabE_orderOf_dMat {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F = 4)
    {ω : Fˣ} (hω : ω ≠ 1) :
    orderOf (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1)) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · rw [← map_pow, CFSG.QuasithinUnique.Fin257.L3.dMat_pow, unit_pow_three_of_card_four hq ω,
      one_pow, CFSG.QuasithinUnique.Fin257.L3.dMat_one, map_one]
  · intro h
    obtain ⟨c, -, h1, h2⟩ := CFSG.QuasithinUnique.Fin257.L3.proj_dMat_eq_one h
    exact hω (Units.ext (h1.trans h2.symm))

theorem parabE_dMat_mem_normalizer_V2 {F : Type} [Field F] [Finite F] [CharP F 2] (ω : Fˣ) :
    proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1) ∈
      Subgroup.normalizer
        ((CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :
          Set (projectiveSL 3 F)) := by
  have hQ : (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1 : Matrix.SpecialLinearGroup (Fin 3) F) ∈
      CFSG.QuasithinUnique.Setup.X7a.Q3 F 1 := by
    rw [CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_one_iff]
    simp [CFSG.QuasithinUnique.Fin257.L3.coe_dMat, Matrix.diagonal_apply]
  exact CFSG.Quasithin.H13.F431.L3.P3.projQ3_le_normalizer_V2 (Subgroup.mem_map_of_mem _ hQ)

theorem parabE_dMat_mem_normalizer_V1 {F : Type} [Field F] [Finite F] [CharP F 2] (ω : Fˣ) :
    proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1) ∈
      Subgroup.normalizer
        ((CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :
          Set (projectiveSL 3 F)) := by
  have hQ : (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1 : Matrix.SpecialLinearGroup (Fin 3) F) ∈
      CFSG.QuasithinUnique.Setup.X7a.Q3 F 0 := by
    rw [CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_zero_iff]
    simp [CFSG.QuasithinUnique.Fin257.L3.coe_dMat, Matrix.diagonal_apply]
  exact CFSG.Quasithin.H13.F431.L3.P3.projQ3_le_normalizer_V1 (Subgroup.mem_map_of_mem _ hQ)

theorem parabE_eq_one_of_commute_V2 {F : Type} [Field F] [CharP F 2] {ω : Fˣ} (hω : ω ≠ 1)
    {e : projectiveSL 3 F} (he : e ∈ CFSG.QuasithinUnique.Fin257.L3.V2)
    (hc : proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1) * e =
      e * proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1)) : e = 1 := by
  obtain ⟨b, c, rfl⟩ := CFSG.QuasithinUnique.Fin257.L3.mem_V2.mp he
  have hD1 := CFSG.Quasithin.H13.F431.L3.P3.dP_conj_yP ω 1 b
  have hD2 := CFSG.QuasithinUnique.Fin257.L3.dP_conj_wP ω 1 c
  simp only [Units.val_one, mul_one] at hD1 hD2
  have hconj : proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1) * (yP b * wP c) *
      (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1))⁻¹ = yP b * wP c := by
    rw [hc]
    group
  have key : yP ((ω : F) * b) * wP ((ω : F) * (ω : F) * c) = yP b * wP c := by
    calc yP ((ω : F) * b) * wP ((ω : F) * (ω : F) * c)
        = (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1) * yP b *
            (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1))⁻¹) *
          (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1) * wP c *
            (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1))⁻¹) := by
          rw [hD1, hD2]
      _ = proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1) * (yP b * wP c) *
            (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1))⁻¹ := by group
      _ = yP b * wP c := hconj
  obtain ⟨h1, h2⟩ := yP_mul_wP_inj key
  have hω' : (ω : F) ≠ 1 := fun h => hω (Units.ext (by rw [Units.val_one]; exact h))
  have hb : b = 0 := by
    have h' : ((ω : F) - 1) * b = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hω')
  have hc0 : c = 0 := by
    have hsq : (ω : F) * (ω : F) - 1 ≠ 0 := by
      intro h0
      apply CFSG.Quasithin.H13.F431.L3.P3.unit_ne_one_sq hω
      linear_combination h0
    have h' : ((ω : F) * (ω : F) - 1) * c = 0 := by linear_combination h2
    exact (mul_eq_zero.mp h').resolve_left hsq
  rw [hb, hc0, yP_zero, wP_zero, mul_one]

theorem parabE_eq_one_of_commute_V1 {F : Type} [Field F] [CharP F 2] {ω : Fˣ} (hω : ω ≠ 1)
    {e : projectiveSL 3 F} (he : e ∈ CFSG.QuasithinUnique.Fin257.L3.V1)
    (hc : proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1) * e =
      e * proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1)) : e = 1 := by
  obtain ⟨a, c, rfl⟩ := CFSG.QuasithinUnique.Fin257.L3.mem_V1.mp he
  have hD1 := CFSG.Quasithin.H13.F431.L3.P3.dP_conj_xP ω 1 a
  have hD2 := CFSG.QuasithinUnique.Fin257.L3.dP_conj_wP ω 1 c
  simp only [Units.val_one, inv_one, mul_one] at hD1 hD2
  have hconj : proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1) * (xP a * wP c) *
      (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1))⁻¹ = xP a * wP c := by
    rw [hc]
    group
  have key : xP ((ω : F) * a) * wP ((ω : F) * (ω : F) * c) = xP a * wP c := by
    calc xP ((ω : F) * a) * wP ((ω : F) * (ω : F) * c)
        = (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1) * xP a *
            (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1))⁻¹) *
          (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1) * wP c *
            (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1))⁻¹) := by
          rw [hD1, hD2]
      _ = proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1) * (xP a * wP c) *
            (proj 3 F (CFSG.QuasithinUnique.Fin257.L3.dMat ω 1))⁻¹ := by group
      _ = xP a * wP c := hconj
  obtain ⟨h1, h2⟩ := xP_mul_wP_inj key
  have hω' : (ω : F) ≠ 1 := fun h => hω (Units.ext (by rw [Units.val_one]; exact h))
  have ha : a = 0 := by
    have h' : ((ω : F) - 1) * a = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hω')
  have hc0 : c = 0 := by
    have hsq : (ω : F) * (ω : F) - 1 ≠ 0 := by
      intro h0
      apply CFSG.Quasithin.H13.F431.L3.P3.unit_ne_one_sq hω
      linear_combination h0
    have h' : ((ω : F) * (ω : F) - 1) * c = 0 := by linear_combination h2
    exact (mul_eq_zero.mp h').resolve_left hsq
  rw [ha, hc0, xP_zero, wP_zero, mul_one]

theorem natSec_normalizer_V2 {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F = 4) :
    NatSec (Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)))
      ⊥ (CFSG.Open.pCoreOf 2 (Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)))) := by
  rw [pCoreOf_normalizer_V2]
  obtain ⟨ω, hω⟩ := CFSG.Quasithin.H13.F431.L3.P3.exists_unit_ne_one (F := F) (by omega)
  exact parabE_natSec_of_centralizer _ (card_normalizer_V2 hq)
    (parabE_dMat_mem_normalizer_V2 (F := F) ω) (parabE_orderOf_dMat hq hω)
    (fun e he hc => parabE_eq_one_of_commute_V2 hω he hc)

theorem natSec_normalizer_V1 {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F = 4) :
    NatSec (Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)))
      ⊥ (CFSG.Open.pCoreOf 2 (Subgroup.normalizer
      ((CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)))) := by
  rw [pCoreOf_normalizer_V1]
  obtain ⟨ω, hω⟩ := CFSG.Quasithin.H13.F431.L3.P3.exists_unit_ne_one (F := F) (by omega)
  exact parabE_natSec_of_centralizer _ (card_normalizer_V1 hq)
    (parabE_dMat_mem_normalizer_V1 (F := F) ω) (parabE_orderOf_dMat hq hω)
    (fun e he hc => parabE_eq_one_of_commute_V1 hω he hc)

end CFSG.GH74.QTGen4.DSGen4.L34
