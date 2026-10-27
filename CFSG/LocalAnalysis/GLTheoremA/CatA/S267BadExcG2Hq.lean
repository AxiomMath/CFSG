module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcG2Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankSL2
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3G2
import CFSG.LieType.SeitzGeneration.ExcPlaneG2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley

theorem dvd_card_of_elemAbelian_mulAut {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) {p n : ℕ} (hp : p.Prime)
    (hX : ∀ F : Subgroup X, IsElemAbelian p F → Nat.card F ≤ p ^ n) {C : Type} [Group C]
    [Finite C] (Θ : MulAut X →* C) (hΘ : Θ.ker = (MulAut.conj : X →* MulAut X).range)
    {E : Subgroup (MulAut X)} (hE : IsElemAbelian p E) (hEc : p ^ (n + 1) ≤ Nat.card E) :
    p ∣ Nat.card C := by
  by_contra hpC
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.LocalAnalysis.RankFourTheoremC.conj_injective_of_center_eq_bot hZ
  have hEker : E ≤ (MulAut.conj : X →* MulAut X).range := by
    rw [← hΘ]
    intro x hx
    rw [MonoidHom.mem_ker]
    have h1 : orderOf (Θ x) ∣ p :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hE.2 x hx, map_one])
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ orderOf_dvd_natCard (Θ x)) hpC
  set F := E.comap (MulAut.conj : X →* MulAut X) with hF
  have hFE : F.map (MulAut.conj : X →* MulAut X) = E := Subgroup.map_comap_eq_self hEker
  have hFc : Nat.card F = Nat.card E := by
    rw [← hFE, Subgroup.card_map_of_injective hinj]
  have hFel : IsElemAbelian p F := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have := congrArg Subtype.val (hE.1.is_comm.comm (⟨MulAut.conj (a : X), a.2⟩ : E)
        ⟨MulAut.conj (b : X), b.2⟩)
      simpa only [Subgroup.coe_mul, map_mul] using this
    · rw [map_pow, hE.2 _ hx, map_one]
  have h1 := hX F hFel
  rw [hFc] at h1
  have := Nat.pow_lt_pow_right hp.one_lt (by omega : n < n + 1)
  omega

section Hq

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem exists_surjective_of_pquot {p : ℕ} {K' : Type} [Group K']
    (eK : PQuot p (⊤ : Subgroup K') ≃* ↥S) {F : Type} [Group F] (eF : PSimple p S ≃* F) :
    ∃ φ : K' →* F, Function.Surjective φ := by
  refine ⟨eF.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (PQuot p S))).comp
      ((QuotientGroup.mk' (GLAPPrimeCore p ↥S)).comp (eK.toMonoidHom.comp
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup K'))).comp
          Subgroup.topEquiv.symm.toMonoidHom)))), ?_⟩
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact eF.surjective.comp ((QuotientGroup.mk'_surjective _).comp
    ((QuotientGroup.mk'_surjective _).comp (eK.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp Subgroup.topEquiv.symm.surjective))))

theorem false_of_hq_of_section {p q : ℕ} (hq : q.Prime) (hBr : CFSG.Open.pRank p B ≤ 4)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B)
    {F : Type} [Group F] (eF : PSimple p S ≃* F) {J U₀ : Subgroup F} (hU₀ : IsPGroup 2 U₀)
    (hU₀ne : U₀ ≠ ⊥) (hJU : J ≤ Subgroup.normalizer (U₀ : Set F))
    (hJ : ∀ (X' : Type) [Group X'] [Finite X'] (φ' : X' →* J), Function.Surjective φ' →
      5 ≤ CFSG.Open.pRank q (⊤ : Subgroup X')) : False := by
  obtain ⟨K', _, _, ⟨eK⟩, hrk⟩ := hHq
  obtain ⟨φ, hφ⟩ := exists_surjective_of_pquot eK eF
  have h5 := CFSG.LocalAnalysis.GLTheoremA.S267.HqRank.le_twoLocalRank_of_section hq hU₀ hU₀ne hJU
    hJ φ hφ
  omega

theorem five_le_pRank_of_mulEquiv_sl2
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {L : Type} [Field L]
    [Finite L] {m : ℕ} (hm : 5 ≤ m) (hL : Nat.card L = q ^ m) {F : Type} [Group F]
    {J : Subgroup F} (eJ : Matrix.SpecialLinearGroup (Fin 2) L ≃* J) :
    ∀ (X' : Type) [Group X'] [Finite X'] (φ' : X' →* J), Function.Surjective φ' →
      5 ≤ CFSG.Open.pRank q (⊤ : Subgroup X') := by
  intro X' _ _ φ' hφ'
  haveI : Fintype L := Fintype.ofFinite L
  exact CFSG.LocalAnalysis.GLTheoremA.S267.HqRank.le_pRank_of_surj_SL2 hq hq2
    (by rw [← Nat.card_eq_fintype_card]; exact hL) (by omega) hm (by norm_num; omega)
    (eJ.symm.toMonoidHom.comp φ') (eJ.symm.surjective.comp hφ')

end Hq

section G2


variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem dvd_exponent_of_elemAbelian_mulAut_G2 {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hK4 : ringChar K ≠ 3 → 4 ≤ Nat.card K)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    {E : Subgroup (MulAut ↥(adjointGroup .G2 K))} (hE : IsElemAbelian p E)
    (hEc : p ^ 3 ≤ Nat.card E) : p ∣ f := by
  classical
  haveI : Finite ↥(adjointGroup .G2 K) := by
    have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
    infer_instance
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hX : ∀ F : Subgroup ↥(adjointGroup .G2 K), IsElemAbelian p F → Nat.card F ≤ p ^ 2 :=
    CFSG.LieType.SeitzGeneration.rankLE2_adjointGroup_G2 K hp hp5 hpK
  by_cases h3 : ringChar K = 3
  ·
    haveI : CharP K 3 := ringChar.of_eq h3
    have hℓ3 : ℓ = 3 := by
      haveI : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        hℓ hf hK
      rw [← ringChar.eq K ℓ, h3]
    subst hℓ3
    haveI : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := ‹CharP K 3›
    haveI : NeZero (2 * f) := ⟨by omega⟩
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
      CFSG.LieType.Chevalley.G2_three_exact_automorphism_normal_form hf K hK
    have h := dvd_card_of_elemAbelian_mulAut hZ hp hX Θ hker hE hEc
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
    exact (Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.coprime_primes hp Nat.prime_two).2 (by omega)) h)
  ·
    obtain ⟨hnf, -⟩ :=
      CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form h3 (hK4 h3) (K := K)
    set N := CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup .G2 K) with hN
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' N).comp (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K)) := by
      intro y
      obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective N y
      obtain ⟨g, σ, rfl⟩ := hnf α
      refine ⟨σ, ?_⟩
      have h1 : QuotientGroup.mk' N (MulAut.conj g) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact ⟨g, rfl⟩
      rw [MonoidHom.comp_apply, map_mul, h1, one_mul]
    have h := dvd_card_of_elemAbelian_mulAut hZ hp hX (QuotientGroup.mk' N)
      (QuotientGroup.ker_mk' N) hE hEc
    have h2 := Subgroup.card_dvd_of_surjective hsurj
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf hK
    rw [hcard] at h2
    exact h.trans h2

theorem false_of_badExcLie_G2_hq {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hS : S.Normal)
    (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B) (hB4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {Q : TauCeti.PrimePower} (hQ2 : Q.p ≠ 2)
    (hQp : Q.p ≠ p) (hv : (TauCeti.LieTypeIndex.G2 Q).Valid)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 Q, hv⟩).Group)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank Q.p K' ≤ CFSG.Open.pRank p B) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, hKc, ⟨eX⟩⟩ := exists_adjointGroup_G2_equiv_psimple hQ2 hv e
  haveI : Finite ↥(adjointGroup .G2 K) := by
    have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
    infer_instance
  have hchar : ringChar K = Q.p := ringChar.eq K Q.p
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hQp ((Nat.prime_dvd_prime_iff_eq hp Q.prime_p).1 (hp.dvd_of_dvd_pow h)).symm
  have hX : ∀ F : Subgroup ↥(adjointGroup .G2 K), IsElemAbelian p F → Nat.card F ≤ p ^ 2 :=
    CFSG.LieType.SeitzGeneration.rankLE2_adjointGroup_G2 K hp hp5 hpK
  have hK4 : ringChar K ≠ 3 → 4 ≤ Nat.card K := by
    intro h3
    have hQ3 : Q.p ≠ 3 := fun h => h3 (hchar.trans h)
    have h2 := Q.prime_p.two_le
    have h4 : Q.p ≠ 4 := by
      intro h4
      have := Q.prime_p
      rw [h4] at this
      exact absurd this (by norm_num)
    rw [hK]
    calc 4 ≤ Q.p := by omega
      _ = Q.p ^ 1 := (pow_one _).symm
      _ ≤ Q.p ^ Q.exponent := Nat.pow_le_pow_right Q.prime_p.pos Q.exponent_pos
  have hrk := pRank_mulAut_adjointGroup_G2_le hK4 hp hX
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr eX)] at hrk
  have hBle := card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC hrk
  have hBr : CFSG.Open.pRank p B ≤ 4 :=
    CFSG.SectionRank.pRank_le hp.one_lt fun _ hEB _ => (Subgroup.card_le_of_le hEB).trans hBle
  obtain ⟨A, hA, hAc⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.exists_elemAbelian_aut_cube hp hS hperf hB hB4 hBC
  have hA' : IsElemAbelian p (A.map (MulAut.congr eX.symm).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hA _
  have hA'c : p ^ 3 ≤ Nat.card (A.map (MulAut.congr eX.symm).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.congr eX.symm).injective]
    exact hAc
  have hpf := dvd_exponent_of_elemAbelian_mulAut_G2 Q.prime_p Q.exponent_pos hK hK4 hp hp5 hpK
    hA' hA'c
  have hf5 : 5 ≤ Q.exponent := hp5.trans (Nat.le_of_dvd Q.exponent_pos hpf)
  have hK2 : ringChar K ≠ 2 := by rw [hchar]; exact hQ2
  obtain ⟨t, -, ht1, ht2, -, htc⟩ := CFSG.LocalAnalysis.GLTheoremA.S267.P3.exists_g2_involution hK2
  obtain ⟨eJ⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2LongSL2 (K := K)
  refine false_of_hq_of_section Q.prime_p hBr hHq eX.symm
    (CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.isPGroup_two_zpowers_of_sq ht2)
    (CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.zpowers_ne_bot_of_ne_one ht1) (fun m hm => ?_)
    (five_le_pRank_of_mulEquiv_sl2 Q.prime_p hQ2 hf5 hK eJ)
  refine CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.mem_normalizer_of_forall_comm fun k hk => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  exact (Commute.zpow_right (htc m hm) n).eq

theorem false_of_badExcCore_G2 {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B) (hB4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hp3B : ¬ (p = 3 ∧ Nat.card B = 3 ^ 4))
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.G2 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.G2 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 Q, hv⟩).Group)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) : False := by
  rw [TauCeti.LieTypeIndex.characteristic_G2] at hchar
  subst hchar
  rcases eq_or_ne p 3 with rfl | hp3
  · exact false_of_badExcLie_G2_three hS hperf hB hB4 hBC (fun h => hp3B ⟨rfl, h⟩) hq2 hqp hv e
  · exact false_of_badExcLie_G2_hq hp (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hS hperf hB hB4
      hBC hq2 hqp hv e hHq

end G2

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
