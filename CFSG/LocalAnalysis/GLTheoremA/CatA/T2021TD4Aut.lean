module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09TD4G2C
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021TD4G2
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021TD4Quot
import CFSG.LocalAnalysis.GLTheoremA.CatA.K148InnerCentA
import CFSG.LocalAnalysis.GLTheoremA.CatA.HD4RkI2023
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023T2021Holds
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (fieldActor)
open CFSG.RankThree.PartTwo.Sec4 (autFix mem_autFix)
open CFSG.LocalAnalysis.GLTheoremA.I2023 (isTD4Of)
open CFSG.LocalAnalysis.GLTheoremA.S10 (twoPart)

theorem t2021TD4_autFix_conj_eq {X : Type} [Group X] (c : X) :
    autFix (MulAut.conj c) = Subgroup.centralizer ({c} : Set X) := by
  ext x
  rw [mem_autFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * c = c * x * c⁻¹ * c := by rw [h]
      _ = c * x := by group
  · intro h
    rw [← h]
    group

private theorem t2021TD4_isElemAbelian_map {X Y : Type*} [Group X] [Group Y] {p : ℕ} {E : Subgroup X}
    (hE : IsElemAbelian p E) (φ : X →* Y) : IsElemAbelian p (E.map φ) := by
  obtain ⟨⟨⟨hc⟩⟩, hexp⟩ := hE
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hax, ← hby, ← map_mul, ← map_mul]
    exact congrArg φ (congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hexp a ha, map_one]


theorem t2021TD4_catalog_facts {S : Type} [Group S] {q : TauCeti.PrimePower} (hq2 : q.p = 2)
    (hcat : catalogIs S (isTD4Of q)) :
    Finite S ∧ IsSimpleGroup S ∧ ¬ IsMulCommutative S ∧
      twoPart (Nat.card S) = (2 ^ q.exponent) ^ 12 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases i with ⟨_, _⟩ | ⟨_, _⟩ | ⟨d, hv⟩ | _
  · exact hi.elim
  · exact hi.elim
  · cases d with
    | trialityD4 q' =>
      have hcard : q'.card = q.card := hi
      have hp' : q'.p = 2 ∧ q'.exponent = q.exponent := by
        have hcardq : q'.p ^ q'.exponent = 2 ^ q.exponent := by
          rw [← TauCeti.PrimePower.card_def, hcard, TauCeti.PrimePower.card_def, hq2]
        have hp2 : q'.p = 2 := by
          have hdvd : q'.p ∣ 2 ^ q.exponent := by
            rw [← hcardq]
            exact dvd_pow_self _ (Nat.pos_iff_ne_zero.1 q'.exponent_pos)
          exact (Nat.prime_dvd_prime_iff_eq q'.prime_p Nat.prime_two).1
            (q'.prime_p.dvd_of_dvd_pow hdvd)
        refine ⟨hp2, ?_⟩
        rw [hp2] at hcardq
        exact Nat.pow_right_injective (le_refl 2) hcardq
      obtain ⟨hfin, hsimp⟩ :=
        CFSG.LieType.SeitzGeneration.finite_isSimpleGroup_cat_trialityD4 hv
      haveI : Finite S := Finite.of_equiv _ e.symm.toEquiv
      haveI : IsSimpleGroup S := MulEquiv.isSimpleGroup e
      obtain ⟨-, hfac⟩ := CFSG.LocalAnalysis.GLTheoremA.td4g2_order hv e
      rw [hp'.1, hp'.2] at hfac
      have h2 : twoPart (Nat.card S) = (2 ^ q.exponent) ^ 12 := by
        unfold twoPart
        rw [hfac, ← pow_mul, mul_comm]
      refine ⟨inferInstance, inferInstance, ?_, h2⟩
      have h4 : 2 ^ 2 ∣ Nat.card S := by
        have hpos : 0 < Nat.card S := Nat.card_pos
        have : 2 ^ (Nat.card S).factorization 2 ∣ Nat.card S := Nat.ordProj_dvd _ _
        refine (Nat.pow_dvd_pow 2 ?_).trans this
        rw [hfac]
        have := q.exponent_pos
        omega
      rintro ⟨hc⟩
      obtain ⟨a, b, hab⟩ :=
        CFSG.AGLEmbedding.nonabelian_of_simple_of_sq_dvd Nat.prime_two h4
      exact hab (hc.comm a b)
    | _ => exact hi.elim
  · exact hi.elim

section Main


theorem t2021TD4_aut {q : TauCeti.PrimePower} (hq2 : q.p = 2) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ q.exponent) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ q.exponent)
    (hcat : catalogIs (td4g2C K σ) (isTD4Of q)) {𝔅 : Type} [Group 𝔅]
    (Ψ : 𝔅 →* MulAut (td4g2C K σ)) (b : 𝔅) (hexp : ∀ g : 𝔅, g ^ 3 = 1)
    (hcomm : ∀ g h : 𝔅, g * h = h * g) (hb1 : Ψ b ≠ 1)
    (hb6 : (2 ^ q.exponent) ^ 6 ≤ twoPart (Nat.card ↥(autFix (Ψ b))))
    {T : Subgroup (td4g2C K σ)} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTinv : ∀ g : 𝔅, ∀ t ∈ T, Ψ g t ∈ T) :
    IsSimpleGroup ↥⁅autFix (Ψ b), autFix (Ψ b)⁆ ∧
      ¬ IsMulCommutative ↥⁅autFix (Ψ b), autFix (Ψ b)⁆ ∧
      3 ∣ Nat.card ↥⁅autFix (Ψ b), autFix (Ψ b)⁆ ∧
      ∃ U : Subgroup (td4g2C K σ), U ≤ ⁅autFix (Ψ b), autFix (Ψ b)⁆ ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
        ∀ g : 𝔅, ∀ u ∈ U, Ψ g u ∈ U := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ q.exponent := q.exponent_pos
  obtain ⟨hfin, hsimp, hnab, -⟩ := t2021TD4_catalog_facts hq2 hcat
  haveI := hfin
  haveI := hsimp
  have hZ0 : ∀ z : td4g2C K σ, (∀ x, z * x = x * z) → z = 1 := by
    intro z hz
    have hc : z ∈ Subgroup.center (td4g2C K σ) := Subgroup.mem_center_iff.2 fun g => (hz g).symm
    rw [TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnab, Subgroup.mem_bot] at hc
    exact hc
  have hconjinj : Function.Injective (MulAut.conj : td4g2C K σ →* MulAut (td4g2C K σ)) := by
    intro x y hxy
    have h1 : y⁻¹ * x = 1 := by
      apply hZ0
      intro g
      have h := congrArg (fun φ : MulAut (td4g2C K σ) => φ g) hxy
      simp only [MulAut.conj_apply] at h
      calc y⁻¹ * x * g = y⁻¹ * (x * g * x⁻¹) * x := by group
        _ = y⁻¹ * (y * g * y⁻¹) * x := by rw [h]
        _ = g * (y⁻¹ * x) := by group
    exact (inv_mul_eq_one.1 h1).symm
  have hβ3 : Ψ b ^ 3 = 1 := by rw [← map_pow, hexp, map_one]
  have hΨ3 : ∀ g, Ψ g ^ 3 = 1 := fun g => by rw [← map_pow, hexp, map_one]
  have hΨc : ∀ g h, Ψ g * Ψ h = Ψ h * Ψ g := fun g h => by rw [← map_mul, ← map_mul, hcomm]
  have hlt : (2 ^ q.exponent) ^ 3 < (2 ^ q.exponent) ^ 6 := by
    have h2 : 1 < 2 ^ q.exponent := Nat.one_lt_two_pow (by omega)
    exact Nat.pow_lt_pow_right h2 (by norm_num)
  have hβout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut (Ψ b) := by
    rintro ⟨c, hc⟩
    have hc1 : c ≠ 1 := by
      rintro rfl
      exact hb1 (by rw [← hc, map_one])
    have hc3 : c ^ 3 = 1 := by
      apply hconjinj
      rw [map_pow, hc, hβ3, map_one]
    have hcent :=
      CFSG.LocalAnalysis.GLTheoremA.K148Inner.k148InnerCentFact_holds q.exponent hf K σ hK hσ c hc3 hc1
    rw [← t2021TD4_autFix_conj_eq, hc] at hcent
    rw [hcent] at hb6
    omega
  obtain ⟨eF⟩ : Nonempty (↥(autFix (Ψ b)) ≃* ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))) := by
    rcases CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv
        hf hK hσ hβ3 hβout with hstd | ⟨e2⟩
    · obtain ⟨g, hg⟩ := hstd
      rcases hg with h | h
      · rw [h]
        exact td4g2_autFix_conj g _
      · obtain ⟨e⟩ := td4g2_autFix_conj g (fieldActor (t := TwistTag.D4) σ σ)⁻¹
        rw [h]
        exact ⟨e.trans (MulEquiv.subgroupCongr (td4g2_autFix_inv _))⟩
    · exfalso
      obtain ⟨e2'⟩ := e2
      have h6 := td4g2_pgl_case_twoPart hf hK hσ e2'
      rw [h6] at hb6
      omega
  obtain ⟨hDs, hD3⟩ := t2021TD4_g2Core hf σ hK hσ
  have hcm : (commutator ↥(autFix (Ψ b))).map eF.toMonoidHom =
      commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eF.surjective]
  let eC1 : ↥(commutator ↥(autFix (Ψ b))) ≃*
      ↥(commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))) :=
    (eF.subgroupMap (commutator ↥(autFix (Ψ b)))).trans (MulEquiv.subgroupCongr hcm)
  let eD : ↥(commutator ↥(autFix (Ψ b))) ≃* ↥⁅autFix (Ψ b), autFix (Ψ b)⁆ :=
    ((commutator ↥(autFix (Ψ b))).equivMapOfInjective _ (autFix (Ψ b)).subtype_injective).trans
      (MulEquiv.subgroupCongr (t2021TD4_map_commutator_subtype (autFix (Ψ b))))
  let eK : ↥⁅autFix (Ψ b), autFix (Ψ b)⁆ ≃*
      ↥(commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))) := eD.symm.trans eC1
  haveI := hDs
  have hKs : IsSimpleGroup ↥⁅autFix (Ψ b), autFix (Ψ b)⁆ := MulEquiv.isSimpleGroup eK
  have hK3 : 3 ∣ Nat.card ↥⁅autFix (Ψ b), autFix (Ψ b)⁆ := by
    rw [Nat.card_congr eK.toEquiv]
    exact hD3
  have hnf : ∀ g : 𝔅, ∃ (k : ℕ) (v : td4g2C K σ), Ψ g = Ψ b ^ k * MulAut.conj v ∧
      Ψ b v = v ∧ MulAut.conj v ∈ Ψ.range := by
    intro g
    obtain ⟨k, v, hkv⟩ := td4g2_normal_form hf hK hσ hβ3 hβout (hΨ3 g)
    obtain ⟨hβv, -⟩ := td4g2_commute hZ0 hβ3 hkv (hΨc g b) (hΨ3 g)
    refine ⟨k, v, hkv, hβv, ⟨b⁻¹ ^ k * g, ?_⟩⟩
    rw [map_mul, map_pow, map_inv, hkv, inv_pow, inv_mul_cancel_left]
  set E₁ : Subgroup (td4g2C K σ) := Ψ.range.comap MulAut.conj with hE₁
  have hE₁F : E₁ ≤ autFix (Ψ b) := by
    intro v hv
    obtain ⟨g', hg'⟩ := hv
    have hα : MulAut.conj v = Ψ b ^ 0 * MulAut.conj v := by rw [pow_zero, one_mul]
    have hαβ : MulAut.conj v * Ψ b = Ψ b * MulAut.conj v := by
      rw [← hg', hΨc]
    have hα3 : MulAut.conj v ^ 3 = 1 := by
      rw [← hg', hΨ3]
    exact (td4g2_commute hZ0 hβ3 hα hαβ hα3).1
  have hE₁ab : IsElemAbelian 3 E₁ := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨g, hg⟩ := x.2
      obtain ⟨h, hh⟩ := y.2
      apply hconjinj
      simp only [Subgroup.coe_mul, map_mul]
      rw [← hg, ← hh, hΨc]
    · obtain ⟨g, hg⟩ := hx
      apply hconjinj
      rw [map_pow, ← hg, hΨ3, map_one]
  have hE₁3 : IsPGroup 3 E₁ := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE₁ab.2 x.1 x.2)⟩
  obtain ⟨n₁, hn₁⟩ := IsPGroup.iff_card.1 hE₁3
  have hE₁9 : Nat.card E₁ ≤ 9 :=
    CFSG.LocalAnalysis.GLTheoremA.I2023.I2023FactD4RankTwo_holds _ q hq2 hcat E₁ hE₁ab
  have hodd : Odd q.exponent → Nat.card E₁ ≤ 3 := by
    intro hfo
    set TA : Subgroup (MulAut (td4g2C K σ)) := T.map MulAut.conj with hTA
    have hTA2 : IsPGroup 2 TA := hT2.map _
    have hTA1 : TA ≠ ⊥ := by
      intro h
      apply hT1
      rw [eq_bot_iff]
      intro t ht
      have h1 : MulAut.conj t ∈ TA := ⟨t, ht, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact hconjinj (h1.trans (map_one _).symm)
    have hEab : IsElemAbelian 3 Ψ.range := by
      refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨g, hg⟩ := x.2
        obtain ⟨h, hh⟩ := y.2
        simp only [Subgroup.coe_mul]
        rw [← hg, ← hh, hΨc]
      · obtain ⟨g, rfl⟩ := hx
        exact hΨ3 g
    have hnorm : Ψ.range ≤ Subgroup.normalizer (TA : Set (MulAut (td4g2C K σ))) := by
      rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨Ψ g t, hTinv g t ht,
          (CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv (Ψ g) t).symm⟩
      · rintro ⟨t, ht, hth⟩
        refine ⟨Ψ g⁻¹ t, hTinv g⁻¹ t ht, ?_⟩
        change MulAut.conj (Ψ g⁻¹ t) = h
        rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, map_inv]
        change MulAut.conj t = Ψ g * h * (Ψ g)⁻¹ at hth
        rw [hth]
        group
    have hE9 := CFSG.LocalAnalysis.GLTheoremA.I2023.i2023FactD2LocalOdd_holds _ q hq2 hfo hcat
      Ψ.range TA hEab hTA2 hTA1 hnorm
    set I := Ψ.range ⊓ (MulAut.conj : td4g2C K σ →* MulAut (td4g2C K σ)).range with hI
    have hcardE₁ : Nat.card E₁ = Nat.card I := by
      have h1 : E₁.map MulAut.conj = I := by
        rw [hE₁, Subgroup.map_comap_eq, inf_comm]
      rw [← h1, Subgroup.card_map_of_injective hconjinj]
    have hIE : I ≤ Ψ.range := inf_le_left
    have hE3 : IsPGroup 3 Ψ.range := fun x => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa using hEab.2 x.1 x.2)⟩
    obtain ⟨nE, hnE⟩ := IsPGroup.iff_card.1 hE3
    have hidx := Subgroup.card_mul_index (I.subgroupOf Ψ.range)
    have hcardI : Nat.card (I.subgroupOf Ψ.range) = Nat.card I :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIE).toEquiv
    have hidx1 : (I.subgroupOf Ψ.range).index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one] at h1
      have hb : (⟨Ψ b, b, rfl⟩ : ↥Ψ.range) ∈ I.subgroupOf Ψ.range := by rw [h1]; trivial
      rw [Subgroup.mem_subgroupOf] at hb
      exact hβout hb.2
    have hidxdvd : (I.subgroupOf Ψ.range).index ∣ 3 ^ nE := by
      rw [← hnE]
      exact Subgroup.index_dvd_card _
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hidxdvd
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0, pow_zero] at hjeq
        exact absurd hjeq hidx1
      · exact h0
    have hidx3 : 3 ≤ (I.subgroupOf Ψ.range).index := by
      rw [hjeq]
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
    rw [hcardI] at hidx
    rw [hcardE₁]
    nlinarith
  have hcard : Nat.card E₁ ≤ 3 ∨ (Nat.card E₁ = 9 ∧ Even q.exponent) := by
    rcases Nat.even_or_odd q.exponent with hfe | hfo
    · rw [hn₁] at hE₁9 ⊢
      have hn2 : n₁ ≤ 2 := by
        by_contra hlt2
        have : 3 ^ 3 ≤ 3 ^ n₁ := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases n₁
      · left; norm_num
      · left; norm_num
      · right; exact ⟨by norm_num, hfe⟩
    · exact Or.inl (hodd hfo)
  set E₀ : Subgroup ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) :=
    (E₁.subgroupOf (autFix (Ψ b))).map eF.toMonoidHom with hE₀
  have hE₁' : IsElemAbelian 3 (E₁.subgroupOf (autFix (Ψ b))) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have := congrArg Subtype.val (hE₁ab.1.1.1 ⟨(x : td4g2C K σ), x.2⟩ ⟨(y : td4g2C K σ), y.2⟩)
      simpa using this
    · exact Subtype.ext (by simpa using hE₁ab.2 _ hx)
  have hE₀ab : IsElemAbelian 3 E₀ := t2021TD4_isElemAbelian_map hE₁' _
  have hE₀card : Nat.card E₀ = Nat.card E₁ := by
    rw [hE₀, Subgroup.card_map_of_injective eF.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁F).toEquiv
  obtain ⟨U', hU'le, hU'2, hU'1, hU'n⟩ :=
    t2021TD4_g2Two hf σ hK hσ E₀ hE₀ab (by rw [hE₀card]; exact hcard)
  set U : Subgroup (td4g2C K σ) := (U'.comap eF.toMonoidHom).map (autFix (Ψ b)).subtype with hU
  have hUle : U ≤ ⁅autFix (Ψ b), autFix (Ψ b)⁆ := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : eF w ∈ commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) := hU'le hw
    rw [← hcm] at hw'
    obtain ⟨w', hw'c, hw'w⟩ := hw'
    have hww : w' = w := eF.injective hw'w
    rw [← t2021TD4_map_commutator_subtype]
    exact ⟨w, hww ▸ hw'c, rfl⟩
  have hU2 : IsPGroup 2 U :=
    (hU'2.comap_of_injective eF.toMonoidHom eF.injective).map _
  have hU1 : U ≠ ⊥ := by
    intro hbot
    apply hU'1
    rw [eq_bot_iff]
    intro x hx
    have hmem : ((eF.symm x : ↥(autFix (Ψ b))) : td4g2C K σ) ∈ U :=
      ⟨eF.symm x, by show eF (eF.symm x) ∈ U'; rw [MulEquiv.apply_symm_apply]; exact hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    have h1 : eF.symm x = 1 := Subtype.ext hmem
    rw [← MulEquiv.apply_symm_apply eF x, h1, map_one]
  have hUinv : ∀ g : 𝔅, ∀ u ∈ U, Ψ g u ∈ U := by
    intro g u hu
    obtain ⟨w, hw, rfl⟩ := hu
    obtain ⟨k, v, hkv, hβv, hv⟩ := hnf g
    have hvE : v ∈ E₁ := hv
    set v' : ↥(autFix (Ψ b)) := ⟨v, hβv⟩ with hv'
    have hv'E : v' ∈ E₁.subgroupOf (autFix (Ψ b)) := hvE
    have hβw : Ψ b (w : td4g2C K σ) = w := w.2
    have happ : Ψ g (w : td4g2C K σ) = v * w * v⁻¹ := by
      rw [hkv]
      exact td4g2_fix_apply hβv hβw k
    have hconj : eF (v' * w * v'⁻¹) ∈ U' := by
      rw [map_mul, map_mul, map_inv]
      exact hU'n (eF v') ⟨v', hv'E, rfl⟩ (eF w) hw
    refine ⟨v' * w * v'⁻¹, hconj, ?_⟩
    show ((v' * w * v'⁻¹ : ↥(autFix (Ψ b))) : td4g2C K σ) = Ψ g (w : td4g2C K σ)
    rw [happ]
    rfl
  have hnabK : ¬ IsMulCommutative ↥⁅autFix (Ψ b), autFix (Ψ b)⁆ := by
    intro hc
    haveI := hc
    have hpr : (Nat.card ↥⁅autFix (Ψ b), autFix (Ψ b)⁆).Prime :=
      Group.is_simple_iff_prime_card.mp hKs
    have h2U : 2 ∣ Nat.card U := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hU2
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hm
        exact hU1 (Subgroup.eq_bot_of_card_eq U hm)
      rw [hm]
      exact dvd_pow_self 2 hm0
    have h2 : 2 ∣ Nat.card ↥⁅autFix (Ψ b), autFix (Ψ b)⁆ := h2U.trans (Subgroup.card_dvd_of_le hUle)
    have e2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).1 h2
    have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 hK3
    omega
  exact ⟨hKs, hnabK, hK3, U, hUle, hU2, hU1, hUinv⟩

end Main

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
