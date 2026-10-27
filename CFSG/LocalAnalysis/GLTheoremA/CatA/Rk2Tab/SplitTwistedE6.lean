module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.PRankSmall
public import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.TwistedE6
open CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.PartTwo.Census.Exceptional
open CFSG.RankThree.CentralCover CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
open scoped MatrixGroups Pointwise

theorem rk2_card_center_dvd_twE6 {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twE6) (hn : 2 ≤ lab.n) :
    Nat.card (Subgroup.center K) ∣ Nat.gcd 3 (2 ^ lab.n + 1) := by
  classical
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n :=
    lieModel_of_markedModel_twE6 htag hM
  obtain ⟨-, -, hT⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedChevalleyModel_of_lieModel hM'
  obtain ⟨k, hkfield, hkfin, hkcard, σ, hσ, ⟨e⟩⟩ := hT
  letI : Field k := hkfield
  letI : Finite k := hkfin
  have hMcardF : Nat.card (CFSG.Open.griessHopfMultiplier
      (DerivedCentralQuotient (twistedFixedGroup .E6 k σ))) = Nat.gcd 3 (2 ^ lab.n + 1) :=
    card_griessHopfMultiplier_twE6 (q := 2 ^ lab.n) (by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn) hkcard hσ
  have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) =
      Nat.gcd 3 (2 ^ lab.n + 1) := by
    rw [Nat.card_congr
      (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv, hMcardF]
  haveI : Finite (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
    Nat.finite_of_card_ne_zero
      (by rw [hcardM]; exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
  have hZk := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ'
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  rwa [hcardM] at hZk

theorem rk2_split_low_twE6_strong {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .twE6) (hn : 2 ≤ lab.n) (hpq : p ∣ 2 ^ lab.n + 1) :
    4 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K ∧
      (p ≠ 3 → 5 ≤ CFSG.Open.twoLocalPrimeRank p K) ∧
      (Subgroup.center K ≠ ⊥ → 5 ≤ CFSG.Open.twoLocalPrimeRank p K) := by
  classical
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n :=
    lieModel_of_markedModel_twE6 htag hM
  obtain ⟨-, hf, hT⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedChevalleyModel_of_lieModel hM'
  obtain ⟨k, hkfield, hkfin, hkcard, σ, hσ, ⟨e⟩⟩ := hT
  letI : Field k := hkfield
  letI : Finite k := hkfin
  letI : Fintype k := Fintype.ofFinite k
  have hkcard' : Nat.card k = (2 ^ lab.n) ^ 2 := by
    rw [hkcard]
    rfl
  have h2n : 2 ≤ 2 ^ lab.n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk4 : 4 ≤ Nat.card k := by
    rw [hkcard']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ lab.n) ^ 2 := Nat.pow_le_pow_left h2n 2
  obtain ⟨σ₀, hσ₀, -, hσ₀2, S, hSmem, hScard⟩ :=
    CFSG.LinearGroups.finite_field_quadratic_frobenius (K := k) Nat.prime_two (by omega)
      hkcard'
  have hσeq : (σ : k →+* k) = (σ₀ : k →+* k) := by
    ext c
    exact (hσ c).trans (hσ₀ c).symm
  have hθ : ∀ c, σ (σ c) = c := by
    intro c
    change (σ : k →+* k) ((σ : k →+* k) c) = c
    rw [hσeq]
    have h2 := congrArg (fun f : k ≃+* k => f c) hσ₀2
    simpa [pow_two, RingAut.mul_apply] using h2
  have hSs : (σ : k →+* k).eqLocusField (RingHom.id k) = S := by
    ext c
    rw [RingHom.mem_eqLocusField, hSmem c, hσ c]
    exact Iff.rfl
  let j : S →+* k := S.subtype
  have hj : ∀ x, σ (j x) = j x := by
    intro x
    have hx : (x : k) ∈ (σ : k →+* k).eqLocusField (RingHom.id k) := by
      rw [hSs]; exact x.2
    exact RingHom.mem_eqLocusField.mp hx
  haveI : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * lab.n) (by
    rw [← Nat.card_eq_fintype_card, hkcard', ← pow_mul, mul_comm])
  haveI : CharP S 2 := (RingHom.charP_iff S.subtype S.subtype.injective 2).mpr inferInstance
  have hF2 : ringChar S = 2 := ringChar.eq S 2
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd2 : p ∣ 2 ^ (2 * lab.n) - 1 := by
    have h1 : (2 : ℕ) ^ (2 * lab.n) = (2 ^ lab.n) ^ 2 := by
      rw [mul_comm 2 lab.n, pow_mul]
    rw [h1]
    have h2 : (2 ^ lab.n) ^ 2 - 1 = (2 ^ lab.n + 1) * (2 ^ lab.n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ lab.n) 1
    rw [h2]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨g, hg⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecA.C10KH.exists_orderOf_sl2 (K := S) (n := lab.n) hScard hdvd2
  have hdvdK : p ∣ Nat.card k - 1 := by
    rw [hkcard']
    have hfac : (2 ^ lab.n) ^ 2 - 1 = (2 ^ lab.n + 1) * (2 ^ lab.n - 1) :=
      Nat.sq_sub_sq (2 ^ lab.n) 1
    rw [hfac]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨t, hμ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.exists_orderOf_units (K := k) hdvdK
  have htq : t ^ (2 ^ lab.n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hμ ▸ hpq)
  have hθt : Units.map (σ : k →* k) t = t⁻¹ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.units_map_eq_inv (σ := σ) hσ htq
  have ht : t * Units.map (σ : k →* k) t = 1 := by rw [hθt, mul_inv_cancel]
  let E : Subgroup (fixedGroup k σ) := te6WE σ hθ j hj g t
  let X : Subgroup (fixedGroup k σ) := te6WX σ (te6SL2 σ j hj 3 (sl2Upper (1 : S)))
  have hXne : X ≠ ⊥ := te6WX_ne_bot σ j hj hF2
  have hX2 : IsPGroup 2 X := isPGroup_te6WX σ j hj hF2
  have hE : IsElemAbelian p E := isElemAbelian_te6WE σ hθ j hj hp hp2 hF2 hg hμ ht
  have hEcard : Nat.card E = p ^ 5 := card_te6WE σ hθ j hj hp hp2 hF2 hg hμ ht
  have hEnorm : E ≤ Subgroup.normalizer (X : Set (fixedGroup k σ)) :=
    te6WE_le_normalizer_te6WX σ hθ j hj hF2 ht
  have hZcard :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
      (θ := σ) hkcard' hσ
  have hZodd : Odd (Nat.card (Subgroup.center (fixedGroup k σ))) := by
    rw [hZcard.1]
    exact Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _)
  have hZt : Subgroup.center ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.center_twDerived_eq_bot (σ := σ)
      Nat.prime_two (by omega) hkcard' hσ
  let θm : (K ⧸ Subgroup.center K) ≃*
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) :=
    e.trans (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.derivedCentralQuotientEquiv σ hZt)
  have hMcardF : Nat.card (CFSG.Open.griessHopfMultiplier
      (DerivedCentralQuotient (twistedFixedGroup .E6 k σ))) = Nat.gcd 3 (2 ^ lab.n + 1) :=
    card_griessHopfMultiplier_twE6 (q := 2 ^ lab.n) (by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn) hkcard' hσ
  have hZk3 : Nat.card (Subgroup.center K) ∣ 3 :=
    (rk2_card_center_dvd_twE6 hK htag hn).trans (Nat.gcd_dvd_left 3 _)
  have hzle : CFSG.Open.pRank p (Subgroup.center K) ≤ 1 :=
    pRank_le_one_of_card_dvd_prime hp Nat.prime_three hZk3
  have hperfF : Group.IsPerfect ↥(fixedGroup k σ) :=
    CFSG.LieType.Steinberg.TwistedE6.fixedGroup_isPerfect_of_four_le_card σ hθ hk4
  have hkertw : (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog σ hθ hk4).ker
      = Subgroup.center (fixedGroup k σ) := by
    refine le_antisymm (fun x hx =>
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_center_of_twIsog_eq_one σ hθ hk4 hx) ?_
    intro x hx
    rw [MonoidHom.mem_ker]
    have hc : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog σ hθ hk4 x ∈
        Subgroup.center ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ :=
        CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog_surjective σ hθ hk4 y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
    rw [hZt] at hc
    exact Subgroup.mem_bot.mp hc
  have hkertw_card : Nat.card (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog σ hθ hk4).ker
      = Nat.gcd 3 (2 ^ lab.n + 1) := by
    rw [hkertw, hZcard.1]
  have hhopf : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ))
      = Nat.gcd 3 (2 ^ lab.n + 1) := by
    rw [Nat.card_congr
      ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
          ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ)).symm.trans
        (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr
          (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.derivedCentralQuotientEquiv σ hZt).symm)).toEquiv,
      hMcardF]
  obtain ⟨α, hαsurj, hαcomp⟩ :=
    exists_surjective_of_hopfMultiplier_card (S₀ := ↥(fixedGroup k σ))
      (J := ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ)) (K := K)
      hperfF hQ'.1 (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog σ hθ hk4)
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog_surjective σ hθ hk4)
      (fun x hx =>
        CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_center_of_twIsog_eq_one σ hθ hk4 hx)
      θm (Nat.coprime_one_right (Nat.card (Subgroup.center K)))
      (by rw [hhopf, hkertw_card, mul_one])
  have hαker : α.ker ≤ Subgroup.center (fixedGroup k σ) := by
    intro x hx
    have h1 : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog σ hθ hk4 x = 1 := by
      have h2 := DFunLike.congr_fun hαcomp x
      rw [MonoidHom.mem_ker] at hx
      simp only [MonoidHom.comp_apply] at h2
      rw [hx, map_one] at h2
      simpa using h2.symm
    exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_center_of_twIsog_eq_one σ hθ hk4 h1
  have hXcenter : X ⊓ Subgroup.center (fixedGroup k σ) = ⊥ :=
    te6WX_inf_center_eq_bot σ j hj hF2 hZodd
  have hXker : X ⊓ α.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxX, hxK⟩ := Subgroup.mem_inf.1 hx
    have hmem : x ∈ X ⊓ Subgroup.center (fixedGroup k σ) := ⟨hxX, hαker hxK⟩
    rw [hXcenter] at hmem
    exact hmem
  have hXmap : X.map α ≠ ⊥ := by
    intro h
    have hle : X ≤ α.ker := (Subgroup.map_eq_bot_iff (f := α) (H := X)).1 h
    have hsub : X ≤ X ⊓ α.ker := fun y hy => ⟨hy, hle hy⟩
    rw [hXker] at hsub
    exact hXne (le_bot_iff.mp hsub)
  by_cases hp5 : 5 ≤ p
  ·
    have hpZF : ¬ p ∣ Nat.card (Subgroup.center (fixedGroup k σ)) := by
      rw [hZcard.1]
      intro h
      have h3 : p ∣ 3 := h.trans (Nat.gcd_dvd_left 3 _)
      have h3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
      omega
    have hEcenter : E ⊓ Subgroup.center (fixedGroup k σ) = ⊥ :=
      te6WE_inf_center_eq_bot σ hθ j hj hp hp2 hF2 hg hμ ht hpZF
    have hEker : E ⊓ α.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxE, hxK⟩ := Subgroup.mem_inf.1 hx
      have hmem : x ∈ E ⊓ Subgroup.center (fixedGroup k σ) := ⟨hxE, hαker hxK⟩
      rw [hEcenter] at hmem
      exact hmem
    have h5 : 5 ≤ CFSG.Open.twoLocalPrimeRank p K :=
      le_twoLocalPrimeRank_of_map α hp hp2 hX2 hXmap hE hEcard hEker hEnorm
    exact ⟨by omega, fun _ => h5, fun _ => h5⟩
  ·
    have hp3 : p = 3 := by
      have h2le : 2 ≤ p := hp.two_le
      have hlt : p < 5 := by omega
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · exact absurd hp (by norm_num)
    subst hp3
    have hZ3F : Nat.card (Subgroup.center (fixedGroup k σ)) = 3 := by
      rw [hZcard.1]
      exact Nat.gcd_eq_left hpq
    have hdvd : Nat.card ↥(E ⊓ α.ker) ∣ 3 := by
      have hle : E ⊓ α.ker ≤ Subgroup.center (fixedGroup k σ) :=
        le_trans inf_le_right hαker
      have h1 := Subgroup.card_subgroup_dvd_card
        ((E ⊓ α.ker).subgroupOf (Subgroup.center (fixedGroup k σ)))
      have h2 : Nat.card ((E ⊓ α.ker).subgroupOf (Subgroup.center (fixedGroup k σ)))
          = Nat.card ↥(E ⊓ α.ker) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      rw [h2, hZ3F] at h1
      exact h1
    have hcardmul := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker α E
    have hE'el : IsElemAbelian 3 (E.map α) := CFSG.SectionRank.isElemAbelian_map hE α
    have hX'2 : IsPGroup 2 (X.map α) := hX2.map α
    have hnorm : E.map α ≤ Subgroup.normalizer (X.map α : Set K) :=
      (Subgroup.map_mono hEnorm).trans (X.le_normalizer_map α)
    by_cases hZ1 : Nat.card (Subgroup.center K) = 1
    ·
      have hcenterbot : Subgroup.center K = ⊥ := Subgroup.card_eq_one.mp hZ1
      have hz0 : CFSG.Open.pRank 3 (Subgroup.center K) = 0 :=
        pRank_eq_zero_of_not_dvd_card Nat.prime_three
          (by rw [hZ1]; norm_num)
      have h4 : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 K := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
        · have hcard5 : Nat.card (E.map α) = 3 ^ 5 := by
            rw [h1, mul_one, hEcard] at hcardmul
            exact hcardmul
          have h5 : 5 ≤ CFSG.Open.twoLocalPrimeRank 3 K :=
            le_twoLocalPrimeRank_of_map (MonoidHom.id K) Nat.prime_three (by norm_num)
              (X := X.map α) (E := E.map α) hX'2 (by simpa using hXmap) hE'el hcard5
              (by simp) hnorm
          omega
        · have hcard4 : Nat.card (E.map α) = 3 ^ 4 := by
            rw [h3, hEcard] at hcardmul
            omega
          exact le_twoLocalPrimeRank_of_map (MonoidHom.id K) Nat.prime_three (by norm_num)
            (X := X.map α) (E := E.map α) hX'2 (by simpa using hXmap) hE'el hcard4
            (by simp) hnorm
      exact ⟨by rw [hz0]; omega, fun h => absurd rfl h, fun hc => absurd hcenterbot hc⟩
    ·
      have hZ3 : Nat.card (Subgroup.center K) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hZk3 with h1 | h3
        · exact absurd h1 hZ1
        · exact h3
      have hker3 : Nat.card (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog σ hθ hk4).ker
          = 3 := by
        rw [hkertw_card]
        exact Nat.gcd_eq_left hpq
      obtain ⟨eiso, -⟩ :=
        exists_mulEquiv_of_hopfMultiplier_card (S₀ := ↥(fixedGroup k σ))
          (J := ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ)) (K := K)
          hperfF hQ'.1 (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog σ hθ hk4)
          (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog_surjective σ hθ hk4)
          (fun x hx =>
            CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_center_of_twIsog_eq_one σ hθ hk4 hx)
          θm (by rw [hhopf, hker3]; exact Nat.gcd_eq_left hpq) (by rw [hZ3, hker3])
      have hαinj : Function.Injective eiso.toMonoidHom := eiso.injective
      have hXmap5 : X.map eiso.toMonoidHom ≠ ⊥ := by
        rw [Ne, Subgroup.map_eq_bot_iff_of_injective X hαinj]
        exact hXne
      have hkereiso : eiso.toMonoidHom.ker = ⊥ :=
        (MonoidHom.ker_eq_bot_iff eiso.toMonoidHom).mpr eiso.injective
      have h5 : 5 ≤ CFSG.Open.twoLocalPrimeRank 3 K :=
        le_twoLocalPrimeRank_of_map eiso.toMonoidHom Nat.prime_three (by norm_num)
          (X := X) (E := E) hX2 hXmap5 hE hEcard
          (by rw [hkereiso]; simp) hEnorm
      exact ⟨by omega, fun h => absurd rfl h, fun _ => h5⟩

theorem rk2_split_low_twE6_center {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .twE6) (hn : 2 ≤ lab.n) (hpq : p ∣ 2 ^ lab.n + 1) :
    4 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K ∧
      (Subgroup.center K ≠ ⊥ → 5 ≤ CFSG.Open.twoLocalPrimeRank p K) := by
  obtain ⟨h1, -, h2⟩ := rk2_split_low_twE6_strong hK hp hp2 htag hn hpq
  exact ⟨h1, h2⟩

theorem rk2_split_low_twE6 {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .twE6) (hn : 2 ≤ lab.n) (hpq : p ∣ 2 ^ lab.n + 1) :
    4 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K :=
  (rk2_split_low_twE6_center hK hp hp2 htag hn hpq).1

theorem rk2_split_low_twE6_cover {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .twE6) (hn : 2 ≤ lab.n) (hpq : p ∣ 2 ^ lab.n + 1)
    (hc : Subgroup.center K ≠ ⊥) :
    5 ≤ CFSG.Open.twoLocalPrimeRank p K :=
  (rk2_split_low_twE6_center hK hp hp2 htag hn hpq).2 hc



end CFSG.LocalAnalysis.GLTheoremA
