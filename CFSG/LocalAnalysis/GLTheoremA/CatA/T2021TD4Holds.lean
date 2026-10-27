module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021TD4Aut
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021TD4Quot
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021TD4Lift
import CFSG.LocalAnalysis.GLTheoremA.CatA.K148InnerCentA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I2015
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.RankThree.PartTwo.Sec4 (autFix mem_autFix)
open CFSG.LocalAnalysis.GLTheoremA.I2023 (isTD4Of)
open CFSG.LocalAnalysis.GLTheoremA.S10 (twoPart)

private theorem t2021TD4_twoPart_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) : twoPart a ≤ twoPart b := by
  unfold twoPart
  have ha : a ≠ 0 := fun h0 => hb (Nat.eq_zero_of_zero_dvd (h0 ▸ h))
  exact Nat.pow_le_pow_right (by norm_num) ((Nat.factorization_le_iff_dvd ha hb).2 h 2)

private theorem t2021TD4_index {S : Type} [Group S]
    (h : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | trialityD4 q => exact ⟨q, hv, ⟨e⟩⟩
  | _ => exact hP.elim


theorem t2021TD4Fact_holds : T2021TD4Fact := by
  intro H _ _ 𝔅 _ _ ψ T b hchev hT4 hexp hcomm hT2 hTinv hTO _ _ _ hcent
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (GLAPPrimeCore 3 H).Characteristic := CFSG.pPrimeCore_characteristic
  set N := GLAPPrimeCore 3 H with hN
  let ψQ : 𝔅 →* MulAut (ppQuot 3 H) := (MulAut.mapQuotient N).comp ψ
  have hψQ : ∀ (g : 𝔅) (l : H), ψQ g (QuotientGroup.mk l) = QuotientGroup.mk (ψ g l) :=
    fun g l => MulAut.mapQuotient_mk N (ψ g) l
  set Z := Subgroup.center (ppQuot 3 H) with hZ
  let ψS : 𝔅 →* MulAut (psimpleOf 3 H) := (MulAut.mapQuotient Z).comp ψQ
  set ρ : ppQuot 3 H →* psimpleOf 3 H := QuotientGroup.mk' Z with hρ
  have hρψ : ∀ (g : 𝔅) (x : ppQuot 3 H), ρ (ψQ g x) = ψS g (ρ x) := fun g x => by
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact (MulAut.mapQuotient_mk Z (ψQ g) x).symm
  have hcore : CFSG.pPrimeCore 3 (ppQuot 3 H) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hZodd : Odd (Nat.card Z) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 h2
    have hzn : (Subgroup.zpowers (z : ppQuot 3 H)).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 z.2 hx) g, mul_inv_cancel_right]
      exact hx
    have hzc : Nat.Coprime 3 (Nat.card (Subgroup.zpowers (z : ppQuot 3 H))) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
      norm_num
    have hbot := (CFSG.pPrimeCore_eq_bot_iff.1 hcore) _ hzn hzc
    have hz1 : (z : ppQuot 3 H) = 1 := by
      have : (z : ppQuot 3 H) ∈ Subgroup.zpowers (z : ppQuot 3 H) := Subgroup.mem_zpowers _
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have : z = 1 := Subtype.ext hz1
    rw [this, orderOf_one] at hz
    norm_num at hz
  obtain ⟨q, hv, ⟨eS⟩⟩ := t2021TD4_index hT4
  have hq2 : q.p = 2 := td4g2_p_two hv eS hchev
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hK' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, hq2]
  have hσ' : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ c, hq2]
  let e : psimpleOf 3 H ≃* td4g2C K σ := eS.trans eC
  have hcatS : catalogIs (psimpleOf 3 H) (isTD4Of q) :=
    ⟨.lie ⟨.trialityD4 q, hv⟩, (rfl : q.card = q.card), ⟨eS⟩⟩
  have hcatC : catalogIs (td4g2C K σ) (isTD4Of q) :=
    ⟨.lie ⟨.trialityD4 q, hv⟩, (rfl : q.card = q.card), ⟨eC.symm⟩⟩
  obtain ⟨hfinS, hsimpS, hnabS, h2S⟩ := t2021TD4_catalog_facts hq2 hcatS
  haveI := hfinS
  haveI := hsimpS
  have hcardQ : Nat.card (ppQuot 3 H) = Nat.card (psimpleOf 3 H) * Nat.card Z :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have h2Q : twoPart (Nat.card (ppQuot 3 H)) = (2 ^ q.exponent) ^ 12 := by
    rw [hcardQ, CFSG.LocalAnalysis.GLTheoremA.K148Inner.twoPart_mul_odd Nat.card_pos.ne'
      (by have := Nat.odd_iff.1 hZodd; omega : ¬ 2 ∣ Nat.card Z), h2S]
  have hsq : Nat.sqrt (twoPart (Nat.card (ppQuot 3 H))) = (2 ^ q.exponent) ^ 6 := by
    rw [h2Q, show (2 ^ q.exponent) ^ 12 = ((2 ^ q.exponent) ^ 6) ^ 2 by ring]
    exact Nat.sqrt_eq' _
  have hfixQ : Nat.card {x : ppQuot 3 H // relOfAut 3 (ψ b) x x} = Nat.card ↥(fixSub (ψQ b)) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun x => ?_
    show relOfAut 3 (ψ b) x x ↔ ψQ b x = x
    constructor
    · rintro ⟨l, l', hl, hl', hll'⟩
      rw [← hl, hψQ, hll', hl', hl]
    · intro hx
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨l, ψ b l, rfl, by rw [← hψQ, hx], rfl⟩
  have h6Q : twoPart (Nat.card ↥(fixSub (ψQ b))) = (2 ^ q.exponent) ^ 6 := by
    rw [← hfixQ, ← hsq]
    exact hcent
  have hρF : ∀ x ∈ fixSub (ψQ b), ρ x ∈ fixSub (ψS b) := fun x hx => by
    show ψS b (ρ x) = ρ x
    rw [← hρψ, show ψQ b x = x from hx]
  let φF : ↥(fixSub (ψQ b)) →* ↥(fixSub (ψS b)) :=
    (ρ.comp (fixSub (ψQ b)).subtype).codRestrict _ (fun x => hρF x x.2)
  have hkerodd : ¬ 2 ∣ Nat.card φF.ker := by
    intro h2
    have hle : φF.ker.map (fixSub (ψQ b)).subtype ≤ Z := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : ρ (x : ppQuot 3 H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      exact (QuotientGroup.eq_one_iff _).1 h1
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (fixSub (ψQ b)).subtype_injective] at h1
    have := Nat.odd_iff.1 hZodd
    have h3 := h2.trans h1
    omega
  have h6S : (2 ^ q.exponent) ^ 6 ≤ twoPart (Nat.card ↥(fixSub (ψS b))) := by
    have hcard := Subgroup.card_ker_mul_card_range φF
    rw [← h6Q, ← hcard, mul_comm, CFSG.LocalAnalysis.GLTheoremA.K148Inner.twoPart_mul_odd
      Nat.card_pos.ne' hkerodd]
    exact t2021TD4_twoPart_le_of_dvd Nat.card_pos.ne' (Subgroup.card_dvd_of_le le_top |>.trans
      (by rw [Subgroup.card_top]))
  have hlt : (2 ^ q.exponent) ^ 6 < (2 ^ q.exponent) ^ 12 :=
    Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by have := q.exponent_pos; omega)) (by norm_num)
  have hb1 : ψS b ≠ 1 := by
    intro h1
    have hall : ∀ x ∈ (⊤ : Subgroup (ppQuot 3 H)), x⁻¹ * ψQ b x ∈ Z := fun x _ =>
      t2021TD4_mem_center_of_fix (by
        show ψS b (QuotientGroup.mk x) = QuotientGroup.mk x
        rw [h1]
        rfl)
    set D : Subgroup (ppQuot 3 H) := ⁅(⊤ : Subgroup (ppQuot 3 H)), ⊤⁆ with hD
    have hle : D ≤ fixSub (ψQ b) := t2021TD4_commutator_le_fixSub hall
    have hmap : D.map ρ = ⊤ := by
      rw [hD, Subgroup.map_commutator, Subgroup.map_top_of_surjective ρ (QuotientGroup.mk'_surjective Z)]
      have := (TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnabS).commutator_eq_top
      rwa [commutator_def] at this
    have hdvd1 : Nat.card (psimpleOf 3 H) ∣ Nat.card ↥D := by
      have := Subgroup.card_map_dvd (H := D) ρ
      rwa [hmap, Subgroup.card_top] at this
    have h12 := t2021TD4_twoPart_le_of_dvd Nat.card_pos.ne'
      (hdvd1.trans (Subgroup.card_dvd_of_le hle))
    rw [h2S, h6Q] at h12
    omega
  let Ψ : 𝔅 →* MulAut (td4g2C K σ) := (MulAut.congr e).toMonoidHom.comp ψS
  have hΨ : ∀ (g : 𝔅) (x : psimpleOf 3 H), Ψ g (e x) = e (ψS g x) := fun g x =>
    td4g2_congr_apply e (ψS g) x
  have hΨb1 : Ψ b ≠ 1 := by
    intro h
    apply hb1
    apply (MulAut.congr e).injective
    rw [map_one]
    exact h
  have hFC : autFix (Ψ b) = (fixSub (ψS b)).map e.toMonoidHom := by
    have h := CFSG.RankThree.PartTwo.Sec4.autFix_congr e (ψS b)
    have h' : autFix (ψS b) = fixSub (ψS b) := Subgroup.ext fun _ => Iff.rfl
    rw [h'] at h
    exact h
  have hb6 : (2 ^ q.exponent) ^ 6 ≤ twoPart (Nat.card ↥(autFix (Ψ b))) := by
    rw [hFC, Subgroup.card_map_of_injective e.injective]
    exact h6S
  set TQ : Subgroup (ppQuot 3 H) := T.map (QuotientGroup.mk' N) with hTQ
  set TC : Subgroup (td4g2C K σ) := (TQ.map ρ).map e.toMonoidHom with hTC
  have hTC2 : IsPGroup 2 TC := ((hT2.map _).map _).map _
  have hTC1 : TC ≠ ⊥ := by
    intro h
    apply hTO
    have h1 : TQ.map ρ = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h
    have h2 : TQ ≤ Z := by
      intro x hx
      have hx' : ρ x ∈ TQ.map ρ := ⟨x, hx, rfl⟩
      rw [h1, Subgroup.mem_bot] at hx'
      exact (QuotientGroup.eq_one_iff x).1 hx'
    have h3 : TQ = ⊥ := by
      obtain ⟨k, hk⟩ := (hT2.map (QuotientGroup.mk' N)).exists_card_eq
      have hdvd : Nat.card TQ ∣ Nat.card Z := Subgroup.card_dvd_of_le h2
      rw [hk] at hdvd
      have hk0 : k = 0 := by
        by_contra hk0
        have h22 : 2 ∣ Nat.card Z := (dvd_pow_self 2 hk0).trans hdvd
        have := Nat.odd_iff.1 hZodd
        omega
      rw [hk0, pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    intro t ht
    have ht' : (QuotientGroup.mk' N) t ∈ TQ := ⟨t, ht, rfl⟩
    rw [h3, Subgroup.mem_bot] at ht'
    exact (QuotientGroup.eq_one_iff t).1 ht'
  have hTCinv : ∀ g : 𝔅, ∀ t ∈ TC, Ψ g t ∈ TC := by
    rintro g _ ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨ψ g t, hTinv g t ht, rfl⟩, rfl⟩, ?_⟩
    change e (ρ (QuotientGroup.mk (ψ g t))) = Ψ g (e (ρ (QuotientGroup.mk t)))
    rw [hΨ, ← hρψ, hψQ]
  obtain ⟨hKs, hKnab, hK3, UC, hUCle, hUC2, hUC1, hUCinv⟩ :=
    t2021TD4_aut hq2 hK' hσ' hcatC Ψ b hexp hcomm hΨb1 hb6 hTC2 hTC1 hTCinv
  have hKC : ⁅autFix (Ψ b), autFix (Ψ b)⁆ = (⁅fixSub (ψS b), fixSub (ψS b)⁆).map e.toMonoidHom := by
    rw [hFC, Subgroup.map_commutator]
  let eKb : ↥(⁅fixSub (ψS b), fixSub (ψS b)⁆) ≃* ↥⁅autFix (Ψ b), autFix (Ψ b)⁆ :=
    ((⁅fixSub (ψS b), fixSub (ψS b)⁆).equivMapOfInjective _ e.injective).trans
      (MulEquiv.subgroupCongr hKC.symm)
  haveI := hKs
  have hKbs : IsSimpleGroup ↥(⁅fixSub (ψS b), fixSub (ψS b)⁆) := MulEquiv.isSimpleGroup eKb
  have hKbnab : ¬ IsMulCommutative ↥(⁅fixSub (ψS b), fixSub (ψS b)⁆) := by
    rintro ⟨⟨hc⟩⟩
    apply hKnab
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eKb.symm.injective
    rw [map_mul, map_mul]
    exact hc _ _
  have hKb3 : 3 ∣ Nat.card ↥(⁅fixSub (ψS b), fixSub (ψS b)⁆) := by
    rw [Nat.card_congr eKb.toEquiv]
    exact hK3
  set Ub : Subgroup (psimpleOf 3 H) := UC.map e.symm.toMonoidHom with hUb
  have hUbK : Ub ≤ ⁅fixSub (ψS b), fixSub (ψS b)⁆ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hUCle hx
    rw [hKC] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    simpa using hy
  have hUb2 : IsPGroup 2 Ub := hUC2.map _
  have hUb1 : Ub ≠ ⊥ := by
    intro h
    apply hUC1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).1 h
  have hUbinv : ∀ g : 𝔅, ∀ u ∈ Ub, ψS g u ∈ Ub := by
    rintro g _ ⟨x, hx, rfl⟩
    refine ⟨Ψ g x, hUCinv g x hx, ?_⟩
    apply e.injective
    change e (e.symm (Ψ g x)) = e (ψS g (e.symm x))
    rw [MulEquiv.apply_symm_apply, ← hΨ, MulEquiv.apply_symm_apply]
  have hFSinv : ∀ g : 𝔅, ∀ x ∈ fixSub (ψS b), ψS g x ∈ fixSub (ψS b) := by
    intro g x hx
    show ψS b (ψS g x) = ψS g x
    have hc : ψS b * ψS g = ψS g * ψS b := by rw [← map_mul, ← map_mul, hcomm]
    have := congrArg (fun φ : MulAut (psimpleOf 3 H) => φ x) hc
    simp only [MulAut.mul_apply] at this
    rw [this, show ψS b x = x from hx]
  have hKfix : ⁅fixSub (ψS b), fixSub (ψS b)⁆ ≤ fixSub (ψS b) := t2021TD4_commutator_le_self _
  have hKn : ∀ c ∈ fixSub (ψS b), ∀ x ∈ ⁅fixSub (ψS b), fixSub (ψS b)⁆,
      c * x * c⁻¹ ∈ ⁅fixSub (ψS b), fixSub (ψS b)⁆ := by
    intro c hc x hx
    have hmap : (⁅fixSub (ψS b), fixSub (ψS b)⁆).map (MulAut.conj c).toMonoidHom ≤
        ⁅fixSub (ψS b), fixSub (ψS b)⁆ := by
      rw [Subgroup.map_commutator]
      have hF : (fixSub (ψS b)).map (MulAut.conj c).toMonoidHom ≤ fixSub (ψS b) := by
        rintro _ ⟨y, hy, rfl⟩
        exact (fixSub (ψS b)).mul_mem ((fixSub (ψS b)).mul_mem hc hy) ((fixSub (ψS b)).inv_mem hc)
      exact Subgroup.commutator_mono hF hF
    exact hmap ⟨x, hx, rfl⟩
  have hKinv : ∀ g : 𝔅, ∀ x ∈ ⁅fixSub (ψS b), fixSub (ψS b)⁆,
      ψS g x ∈ ⁅fixSub (ψS b), fixSub (ψS b)⁆ := by
    intro g x hx
    have hmap : (⁅fixSub (ψS b), fixSub (ψS b)⁆).map (ψS g).toMonoidHom ≤
        ⁅fixSub (ψS b), fixSub (ψS b)⁆ := by
      rw [Subgroup.map_commutator]
      have hF : (fixSub (ψS b)).map (ψS g).toMonoidHom ≤ fixSub (ψS b) := by
        rintro _ ⟨y, hy, rfl⟩
        exact hFSinv g y hy
      exact Subgroup.commutator_mono hF hF
    exact hmap ⟨x, hx, rfl⟩
  obtain ⟨KQ, UQ, hKQ, hKQq, hKQZ, hKQ3, hUQK, hUQ2, hUQ1, hUQinv⟩ :=
    t2021TD4_quot Nat.prime_three (fun g => ψQ g) b hZodd hKfix hKn hKinv hKbs hKbnab hKb3 hUbK hUb2 hUb1
      hUbinv
  exact t2021TD4_lift Nat.prime_three (by norm_num) ψ (fun g => ψQ g) hψQ b hexp hcomm hKQ hKQq hKQZ hKQ3
    hUQK hUQ2 hUQ1 hUQinv

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
