module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovPGU
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PG
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93W

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.Sp4Rec
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
  CFSG.ComponentClassification.OddClassSelector
open scoped MatrixGroups

theorem Ivk93W.exists_unitary {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)
    [Finite (StatedProj (StatedSU (2 * r + ε) (p ^ f) K))]
    {x : StatedProj (StatedSU (2 * r + ε) (p ^ f) K)} {q : ℕ}
    {B : Subgroup (StatedProj (StatedSU (2 * r + ε) (p ^ f) K))} (h : Ivk93W x q B) :
    ∃ hud : UnitaryFieldData p f K, ∃ A : sesqUnitaryGroup (hypForm hud r ε),
      orderOf (QuotientGroup.mk A : sesqProjUnitary hud (hypForm hud r ε)) = 2 ∧
      ∃ M : Subgroup (centralizer
          ({QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε)) A} :
            Set (sesqProjUnitary hud (hypForm hud r ε)))),
        IsPComponent 2 M ∧ Nonempty (↥B ≃* ↥M) := by
  classical
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨φ, hφ, hnorm⟩ := ivk93cov_psu_embedding hud hr hε
  have hK₁ := isPComponent_map_of_normal φ hφ h.le h.comp.2
  obtain ⟨A, hA⟩ := QuotientGroup.mk'_surjective (sesqNormOneScalars hud (hypForm hud r ε)) (φ x)
  rw [← hA] at hK₁
  refine ⟨hud, A, ?_, _, hK₁.2, ⟨(B.equivMapOfInjective φ hφ).trans
    (Subgroup.subgroupOfEquivOfLe hK₁.1).symm⟩⟩
  change orderOf ((QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε))) A) = 2
  rw [hA, orderOf_injective φ hφ x, h.ord]

theorem ivk93w_quaternion_psu {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) {d : ℕ} (hd : 3 ≤ d) :
    ∃ φ : QuaternionGroup 2 →* StatedProj (StatedSU d (p ^ f) E), Function.Injective φ := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  have : CharP E p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq h.card_eq_sq
  have hE2 : (2 : E) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq E p]; exact hp)
  obtain ⟨hsigma, hne, hk0⟩ := CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f h.card_eq_sq
  have hsig := CatalogueBUnitaryTwo.unitaryFieldConjugation_apply p f h.card_eq_sq
  obtain ⟨a, b, ha, hb, hab'⟩ := exists_antifixed_sq_add_sq h hp
  have hsigU : CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq =
      CFSG.LieType.BorelTits.unitaryInvolution E p f :=
    RingEquiv.ext fun z => by rw [hsig, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  have hSU : CFSG.LieType.Universal.Unitary.SUid
      (CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq) d =
      StatedSU d (p ^ f) E := by
    rw [hsigU]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq _
  exact exists_quaternion_statedProj hE2 _ hd hSU ha hb hab'

namespace Ivk93W

variable {J : Type} [Group J] [Finite J] {x : J} {q : ℕ} {B : Subgroup J}

theorem q_eq_of_equiv_sl2 (h : Ivk93W x q B) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (e : SL(2, F) ≃* ↥B) : Nat.card F = q := by
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  have hO : pPrimeCore 2 ↥B = ⊥ := by
    rw [← CFSG.pPrimeCore_map_iso 2 e, CatFactsSp4.pPrimeCore_SL2 h2 (by omega), Subgroup.map_bot]
  have h1 : Nat.card ↥B = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F]
  have h3 := h.card
  rw [hO, Subgroup.card_bot, mul_one] at h3
  exact sl2_card_inj h5 h.five (h1.symm.trans h3)

theorem false_of_quaternion (h : Ivk93W x q B) {M : Type} [Group M] (e : ↥B ≃* M)
    (hM : CFSG.IsQuasisimple M) (φ : QuaternionGroup 2 →* M ⧸ center M)
    (hφ : Function.Injective φ) : False := by
  classical
  have : Finite M := Finite.of_equiv _ e.toEquiv
  obtain ⟨F, _, _, hFq, ⟨eF⟩⟩ := exists_sl2_equiv_of_hasSL2Model h.sl
  have eS : SL(2, F) ≃* (M ⧸ pPrimeCore 2 M) :=
    eF.trans (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e)
  have hcard : Nat.card (M ⧸ pPrimeCore 2 M) = q * (q ^ 2 - 1) := by
    rw [← Nat.card_congr eS.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hFq]
  have hker : pPrimeCore 2 M ≤ center M := by
    rcases LocalCores.quasisimple_normal_subgroups hM (inferInstance : (pPrimeCore 2 M).Normal) with
      htop | hle
    · exfalso
      have h1 : Nat.card (M ⧸ pPrimeCore 2 M) = 1 := by
        rw [htop]
        exact Subgroup.index_top
      have := h.sl2_card_ge
      omega
    · exact hle
  have hker' : (QuotientGroup.mk' (pPrimeCore 2 M)).ker ≤ center M := by
    rw [QuotientGroup.ker_mk']
    exact hker
  obtain ⟨eC⟩ := center_quotient_equiv_of_surjective hM (QuotientGroup.mk' (pPrimeCore 2 M))
    (QuotientGroup.mk'_surjective _) hker'
  let eQ : M ⧸ center M ≃* StatedProj (StatedSL 2 F) :=
    eC.trans ((QuotientGroup.congr (center (M ⧸ pPrimeCore 2 M)) (center SL(2, F)) eS.symm
      (Subgroup.map_center_eq eS.symm)).trans (projectiveSpecialLinearGroupEquivStatedProj 2 F))
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card F (ringChar F)
  have hk : Nat.card F = ringChar F ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  have hq5 := h.five
  have hodd := h.odd
  have hℓ2 : ringChar F ≠ 2 := by
    intro h2
    rw [h2] at hk
    have : 2 ∣ q := by
      rw [← hFq, hk]
      exact dvd_pow_self 2 (PNat.ne_zero n)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  have hX : StatedClassicalModel (M ⧸ center M) .PSL 2 (ringChar F) n :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv eQ
      (OddSelector.statedClassicalModel_psl_two hℓ n.pos hk (by omega) (by omega))
  exact OddSelector.not_psl_two_odd_of_quaternion φ hφ hℓ2 hX

end Ivk93W

theorem ivk93w_sylow_contra {q N : ℕ} (hq : Odd q) (h3 : 3 ≤ q) (hN0 : N ≠ 0)
    (hN : (q ^ 2 - 1) * (q ^ 4 - 1) ∣ N)
    (hb : N.factorization 2 ≤ (q * (q ^ 2 - 1)).factorization 2 + 3) : False := by
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq2 : q ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    omega
  have hfac : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    have h1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
    zify [h1, hq1]
    ring
  obtain ⟨k, rfl⟩ := hq
  have h8 : 8 ∣ (2 * k + 1) ^ 2 - 1 := by
    have h1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
      have : 1 ≤ (2 * k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [this]
      ring
    rw [h1]
    have : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
    obtain ⟨m, hm⟩ := this
    exact ⟨m, by rw [hm]; ring⟩
  have hodd : ¬ 2 ∣ 2 * k + 1 := by omega
  have ha3 : 3 ≤ ((2 * k + 1) ^ 2 - 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hq2).1 (by simpa using h8)
  have hqa : ((2 * k + 1) * ((2 * k + 1) ^ 2 - 1)).factorization 2 =
      ((2 * k + 1) ^ 2 - 1).factorization 2 := by
    rw [Nat.factorization_mul (by omega) hq2]
    simp [Nat.factorization_eq_zero_of_not_dvd hodd]
  set a := ((2 * k + 1) ^ 2 - 1).factorization 2 with ha
  have hdvd : 2 ^ (2 * a + 1) ∣ N := by
    refine dvd_trans ?_ hN
    obtain ⟨u, hu⟩ := Nat.ordProj_dvd ((2 * k + 1) ^ 2 - 1) 2
    obtain ⟨w, hw⟩ : 2 ∣ (2 * k + 1) ^ 2 + 1 := by
      have : (2 * k + 1) ^ 2 + 1 = 2 * (2 * k ^ 2 + 2 * k + 1) := by ring
      exact ⟨_, this⟩
    rw [hfac]
    refine ⟨u * u * w, ?_⟩
    have e1 : (2 * k + 1) ^ 2 - 1 = 2 ^ a * u := by rw [ha]; exact hu
    rw [e1, hw]
    ring
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).1 hdvd
  omega

theorem ivk93w_toNat_five (q : ℕ) : (((q : ℕ) : ℤ) ^ 5 - (-1) ^ 5).toNat = q ^ 5 + 1 := by
  have : (((q : ℕ) : ℤ) ^ 5 - (-1) ^ 5) = ((q ^ 5 + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [this, Int.toNat_natCast]

theorem ivk93w_dvd_card_psu {p f d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = (p ^ f) ^ 2) (hd : d = 4 ∨ d = 5) :
    ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1) ∣ Nat.card (StatedProj (StatedSU d (p ^ f) K)) := by
  have hq3 : 3 ≤ p ^ f := by
    have h1 := hp.two_le
    have h2 : 3 ≤ p := by omega
    exact h2.trans (Nat.le_self_pow (by omega) p)
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hf hK (by omega)]
  generalize p ^ f = q at hq3 ⊢
  have hg : ∀ g : ℕ, g ∣ q + 1 → g ∣ q ^ 3 + 1 := fun g hg =>
    hg.trans (by simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3))
  rcases hd with rfl | rfl
  · have hI : Finset.Icc 2 4 = {2, 3, 4} := by decide
    rw [hI, Finset.prod_insert (by simp), Finset.prod_pair (by norm_num : (3 : ℕ) ≠ 4),
      ivk93cov_toNat_two q (by omega), ivk93cov_toNat_three q, ivk93cov_toNat_four q (by omega)]
    obtain ⟨c, hc⟩ := hg (Nat.gcd 4 (q + 1)) (Nat.gcd_dvd_right _ _)
    have hgpos : 0 < Nat.gcd 4 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have : q ^ (4 * (4 - 1) / 2) * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) /
        Nat.gcd 4 (q + 1) = (q ^ 6 * c) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
      apply Nat.div_eq_of_eq_mul_left hgpos
      rw [hc]
      norm_num
      ring
    rw [this]
    exact Dvd.intro_left _ rfl
  · have hI : Finset.Icc 2 5 = {2, 3, 4, 5} := by decide
    rw [hI, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
      Finset.prod_pair (by norm_num : (4 : ℕ) ≠ 5), ivk93cov_toNat_two q (by omega),
      ivk93cov_toNat_three q, ivk93cov_toNat_four q (by omega), ivk93w_toNat_five q]
    obtain ⟨c, hc⟩ := hg (Nat.gcd 5 (q + 1)) (Nat.gcd_dvd_right _ _)
    have hgpos : 0 < Nat.gcd 5 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have : q ^ (5 * (5 - 1) / 2) * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) /
        Nat.gcd 5 (q + 1) = (q ^ 10 * c * (q ^ 5 + 1)) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
      apply Nat.div_eq_of_eq_mul_left hgpos
      rw [hc]
      norm_num
      ring
    rw [this]
    exact Dvd.intro_left _ rfl

theorem ivk93w_five_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : p ^ f ≠ 3) :
    5 ≤ p ^ f := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h1 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega) p)
  have h2 : p ^ f % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  omega

theorem ivk93w_false_of_bound {p f d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = (p ^ f) ^ 2) (hd : d = 4 ∨ d = 5)
    [Finite (StatedProj (StatedSU d (p ^ f) K))]
    (hb : Ivk93WBound (StatedProj (StatedSU d (p ^ f) K)) (p ^ f)) : False := by
  have hq3 : 3 ≤ p ^ f := by
    have h1 := hp.two_le
    have h2 : 3 ≤ p := by omega
    exact h2.trans (Nat.le_self_pow (by omega) p)
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  exact ivk93w_sylow_contra hqodd hq3 Nat.card_pos.ne' (ivk93w_dvd_card_psu hp hp2 hf hK hd) hb

end CFSG.GH74.GLS.IVK.Proofs2
