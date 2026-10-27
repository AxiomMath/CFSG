module

public import CFSG.LieType.SeitzGeneration.CubeCoverTwE6Rest
public import CFSG.LieType.SeitzGeneration.CoverDerivedPreimage
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz6
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.LieType.SeitzGeneration.CubeCoverE6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.CubeCoverLayer
  CFSG.LieType.SeitzGeneration.CoverDerivedPreimage
  CFSG.ComponentClassification.CatalogueBCentralQuotient
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LieType.SeitzGeneration.CubeCoverTwE6
  CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.LocalAnalysis.GLTheoremB

section QuasiAtTwo

theorem seitzQuasiAt_two_holds :
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz6.SeitzQuasiAt 2 :=
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz6.seitzQuasiAt_two
    CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
    (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz6.seitzCoverRest_two_of_famExcRest
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
      (CFSG.LieType.SeitzGeneration.QuasiHigh5.seitzCoverFamExcRest_two_of_rest
        (CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover.seitzCoverFamExcRest2Rest_of_diag
          CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest5.twE6ThreeOpenDiag_holds)))

end QuasiAtTwo

@[expose] def TwE6CoverComponentType {X : Type} [Group X] (J : Subgroup X) : Prop :=
  (∃ (d : TauCeti.ValidLieTypeIndex)
      (_ : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group),
      3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
        (QuasiHigh.CoverIndex 3 d.1 →
          ¬ ExcIndex 3 d.1 ∧ ¬ IsLThreeFour (J ⧸ Subgroup.center J))) ∨
    NoPlane3 (J ⧸ Subgroup.center J) ∨ ¬ 3 ∣ Nat.card J



section CoverComponent

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

theorem le_hyperGamma_of_plane_of_quasisimple
    (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) {X : Type} [Group X] [Finite X]
    (E : Subgroup (MulAut X)) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (f : MulAut X) (hf : f ∈ E) (hf1 : f ≠ 1)
    (J : Subgroup X)
    (hJfix : ∀ g ∈ Subgroup.zpowers f, ∀ y ∈ J, g y = y)
    (hperf : commutator J = ⊤) (hJ3 : ¬ 3 ∣ Nat.card (Subgroup.center J))
    (d : TauCeti.ValidLieTypeIndex)
    (e : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hdp : 3 ≠ d.1.characteristic) (hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1)
    (hJE : ∀ g ∈ E, J.map g.toMonoidHom = J) :
    J ≤ CFSG.LieType.Seitz.seitzHyperGamma 3 E := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ : ↥E →* MulAut J := resHom J E hJE with hρ
  have hρker : ∀ g : ↥E, g ∈ ρ.ker → ∀ y ∈ J, g.1 y = y := fun g hg y hy =>
    congrArg (fun φ : MulAut J => ((φ ⟨y, hy⟩ : J) : X)) (MonoidHom.mem_ker.1 hg)
  have hfker : (⟨f, hf⟩ : ↥E) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    ext y
    exact hJfix f (Subgroup.mem_zpowers f) y y.2
  have hcard : Nat.card ρ.ker * Nat.card ρ.range = 3 ^ 3 := by
    rw [Subgroup.card_ker_mul_card_range, hEc]
  by_cases hD9 : Nat.card ρ.range = 3 ^ 2
  · have hgen := closure_fixed_eq_top hS hperf hJ3 d e hdp hex ρ.range
      (@CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.isElemAbelian_range
        (MulAut X) _ 3 E hE (MulAut J) _ ρ) hD9
    have hsub : {x : J | ∃ δ ∈ ρ.range, δ ≠ 1 ∧ δ x = x} ⊆
        ((CFSG.LieType.Seitz.seitzHyperGamma 3 E).subgroupOf J : Set J) := by
      rintro x ⟨_, ⟨g, rfl⟩, hg1, hgx⟩
      have hgf : g.1 ∉ Subgroup.zpowers f := fun hmem =>
        hg1 (by ext y; exact hJfix g.1 hmem y y.2)
      have hf3 : f ^ 3 = 1 := hE.2 f hf
      have hg3 : g.1 ^ 3 = 1 := hE.2 g.1 g.2
      have hcomm : Commute f g.1 := congrArg Subtype.val (hE.1.is_comm.comm ⟨f, hf⟩ g)
      have hFc := card_zpowers_sup_zpowers hcomm hf1 hf3 hg3 hgf
      have hFE : Subgroup.zpowers f ⊔ Subgroup.zpowers g.1 ≤ E :=
        sup_le (Subgroup.zpowers_le.2 hf) (Subgroup.zpowers_le.2 g.2)
      have hxf : f x.1 = x.1 := hJfix f (Subgroup.mem_zpowers f) x x.2
      have hxg : g.1 x.1 = x.1 := congrArg Subtype.val hgx
      have hxfix : x.1 ∈ CFSG.LieType.Seitz.fixedPoints
          (Subgroup.zpowers f ⊔ Subgroup.zpowers g.1) := by
        have hle : Subgroup.zpowers f ⊔ Subgroup.zpowers g.1 ≤
            MulAction.stabilizer (MulAut X) x.1 :=
          sup_le (Subgroup.zpowers_le.2 hxf) (Subgroup.zpowers_le.2 hxg)
        exact fun φ hφ => hle hφ
      exact fixedPoints_le_hyperGamma hFE (relIndex_eq_three hFE hEc hFc) hxfix
    intro y hy
    have h1 : (⟨y, hy⟩ : J) ∈
        Subgroup.closure {x : J | ∃ δ ∈ ρ.range, δ ≠ 1 ∧ δ x = x} := by
      rw [hgen]; exact Subgroup.mem_top _
    exact ((Subgroup.closure_le _).2 hsub) h1
  · have hker1 : Nat.card ρ.ker ≠ 1 := by
      intro h1
      have h2 := Subgroup.card_eq_one.1 h1
      rw [h2] at hfker
      exact hf1 (congrArg Subtype.val (Subgroup.mem_bot.1 hfker))
    have hkerdvd : 3 ^ 2 ∣ Nat.card ρ.ker := by
      obtain ⟨i, hi, hDi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
        (Dvd.intro_left _ hcard : Nat.card ρ.range ∣ 3 ^ 3)
      rw [hDi] at hcard
      interval_cases i
      · norm_num at hcard ⊢; omega
      · norm_num at hcard ⊢; omega
      · exact absurd hDi hD9
      · norm_num at hcard; exact absurd hcard hker1
    obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ρ.ker) 3 hkerdvd
    set F : Subgroup (MulAut X) := (K₀.map ρ.ker.subtype).map E.subtype with hF
    have hFc : Nat.card F = 3 ^ 2 := by
      rw [hF, Subgroup.card_map_of_injective E.subtype_injective,
        Subgroup.card_map_of_injective ρ.ker.subtype_injective, hK₀]
    have hFE : F ≤ E := Subgroup.map_subtype_le _
    have hFfix : J ≤ CFSG.LieType.Seitz.fixedPoints F := by
      intro y hy φ hφ
      rw [hF, Subgroup.mem_map] at hφ
      obtain ⟨a, ha, rfl⟩ := hφ
      rw [Subgroup.mem_map] at ha
      obtain ⟨b, -, rfl⟩ := ha
      exact hρker _ b.2 y hy
    exact hFfix.trans (fixedPoints_le_hyperGamma hFE (relIndex_eq_three hFE hEc hFc))

theorem le_hyperGamma_of_range_top {X : Type} [Group X] [Finite X]
    (E : Subgroup (MulAut X)) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (J : Subgroup X)
    (hJE : ∀ g ∈ E, J.map g.toMonoidHom = J)
    (hgen : CFSG.LieType.Seitz.seitzHyperGamma 3 (resHom J E hJE).range = ⊤) :
    J ≤ CFSG.LieType.Seitz.seitzHyperGamma 3 E := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ : ↥E →* MulAut J := resHom J E hJE with hρ
  have hT : (⊤ : Subgroup J) ≤
      (CFSG.LieType.Seitz.seitzHyperGamma 3 E).comap J.subtype := by
    rw [← hgen]
    refine iSup₂_le fun B hB => ?_
    intro y hy
    set ρD : ↥E →* ρ.range := ρ.rangeRestrict with hρD
    set B' : Subgroup ρ.range := B.subgroupOf ρ.range with hB'
    have hB'index : B'.index = 3 := hB.2
    set F : Subgroup (MulAut X) := (B'.comap ρD).map E.subtype with hF
    have hFE : F ≤ E := Subgroup.map_subtype_le _
    have hrel : F.relIndex E = 3 := by
      have h1 : F.subgroupOf E = B'.comap ρD :=
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective _
      rw [Subgroup.relIndex, h1,
        Subgroup.index_comap_of_surjective B' ρ.rangeRestrict_surjective]
      exact hB'index
    have hfix : (y : X) ∈ CFSG.LieType.Seitz.fixedPoints F := by
      intro φ hφ
      rw [hF, Subgroup.mem_map] at hφ
      obtain ⟨b, hb, rfl⟩ := hφ
      have hbB : (ρD b : MulAut J) ∈ B :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hb)
      have hyJ : (ρD b : MulAut J) y = y := hy (ρD b : MulAut J) hbB
      exact congrArg (fun z : J => (z : X)) hyJ
    exact fixedPoints_le_hyperGamma hFE hrel hfix
  intro x hx
  exact hT (Subgroup.mem_top (⟨x, hx⟩ : J))

theorem coverComponent_le_hyperGamma
    (hS : CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz6.SeitzQuasiAt 2)
    (hKF : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K C : Type} [Group K] [Group C] [Finite K] {π : K →* C}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    (ind : MulAut K →* MulAut C)
    (hind : ∀ (ψ : MulAut K) (x : K), π (ψ x) = ind ψ (π x))
    {E : Subgroup (MulAut K)} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3)
    {φ : MulAut K} (hφE : φ ∈ E) (hφ1 : φ ≠ 1)
    {J : Subgroup C} (hJ : CFSG.Open.IsQuasisimple J)
    (hfix : ∀ c ∈ J, ind φ c = c)
    (hJnorm : ∀ ε ∈ E, J.map (ind ε).toMonoidHom = J)
    (hT : TwE6CoverComponentType J) :
    J ≤ (CFSG.LieType.Seitz.seitzHyperGamma 3 E).map π := by
  classical
  haveI : Group.IsPerfect J := ⟨hJ.1⟩
  set Jt := derivedPreimage π J with hJt
  have hJtQ : CFSG.Open.IsQuasisimple Jt :=
    derivedPreimage_isQuasisimple π hπ hker hJ
  have hJtmap : Jt.map π = J := derivedPreimage_map π hπ J
  have hφfix : ∀ x ∈ Jt, φ x = x :=
    derivedPreimage_fixed π hπ hker (ε := φ) (δ := ind φ)
      (fun g _ => hind φ g) hfix
  have hJtfix : ∀ g ∈ Subgroup.zpowers φ, ∀ y ∈ Jt, g y = y := by
    intro g hg y hy
    exact (Subgroup.zpowers_le.2 (hφfix y hy) :
      Subgroup.zpowers φ ≤ MulAction.stabilizer (MulAut K) y) hg
  have hJtE : ∀ ε ∈ E, Jt.map ε.toMonoidHom = Jt := fun ε hε =>
    derivedPreimage_map_of_map_eq π (J := J) (ε := ε) (δ := ind ε)
      (fun g _ => hind ε g)
      (fun g _ => by rw [hind ε⁻¹ g, map_inv])
      (hJnorm ε hε)
  obtain ⟨eqt⟩ := derivedPreimage_centerQuotientEquiv π hπ hker (J := J)
  have hmain : Jt ≤ CFSG.LieType.Seitz.seitzHyperGamma 3 E := by
    rcases hT with ⟨d, e, hdp, hexc, hci⟩ | hno | hcop
    · let e' : (Jt ⧸ Subgroup.center Jt) ≃* (TauCeti.CFSGIndex.lie d).Group := eqt.trans e
      set ρ : ↥E →* MulAut Jt := resHom Jt E hJtE with hρ
      have hDab : CFSG.Open.IsElemAbelian 3 ρ.range :=
          @CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.isElemAbelian_range
            (MulAut K) _ 3 E hE (MulAut Jt) _ ρ
      by_cases hZ : 3 ∣ Nat.card (Subgroup.center Jt)
      · by_cases hD9 : Nat.card ρ.range = 3 ^ 2
        · have hcov : QuasiHigh.CoverIndex 3 d.1 :=
            QuasiHigh.coverIndex_of_dvd_card_center hGA Nat.prime_three (by norm_num)
              hJtQ d e' hdp hZ
          have hExc : ¬ ExcIndex 3 d.1 := (hci hcov).1
          have hL34 : ¬ IsLThreeFour (Jt ⧸ Subgroup.center Jt) := by
            intro hL
            exact (hci hcov).2
              (CFSG.HardMathSupport.Solomon.LocalBalance.isLThreeFour_of_mulEquiv eqt hL)
          have hgenD : CFSG.LieType.Seitz.seitzHyperGamma 3 ρ.range = ⊤ :=
            hS 3 Nat.prime_three (by norm_num) Jt hJtQ d ⟨e'⟩ hdp
              (fun h => hL34 h.2) ρ.range hDab hD9 (Or.inl hExc)
          exact le_hyperGamma_of_range_top E hE hcard Jt hJtE hgenD
        · exact le_hyperGamma_of_range_ne E hE hcard φ hφE hφ1 Jt hJtfix hJtE hD9
      · exact le_hyperGamma_of_plane_of_quasisimple hKF E hE hcard φ hφE hφ1 Jt hJtfix
          hJtQ.1 hZ d e' hdp hexc hJtE
    · have hno' : NoPlane3 (Jt ⧸ Subgroup.center Jt) := noPlane3_of_equiv eqt.symm hno
      exact le_hyperGamma_of_range_ne E hE hcard φ hφE hφ1 Jt hJtfix hJtE
        (card_range_ne_nine E hE Jt hJtQ.1 hJtE hno')
    · have hquot : ¬ 3 ∣ Nat.card (Jt ⧸ Subgroup.center Jt) := by
        rw [Nat.card_congr eqt.toEquiv]
        exact fun h => hcop (dvd_trans h (Subgroup.card_quotient_dvd_card (Subgroup.center ↥J)))
      exact le_hyperGamma_of_coprime E hE hcard φ hφE hφ1 Jt hJtfix hJtE
        (not_three_dvd_card_of_perfect hJtQ.1 hquot)
  rw [← hJtmap]
  exact Subgroup.map_mono hmain

end CoverComponent

section Components


@[expose] def TwE6CoverComponents : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (σ : k ≃+* k) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup k σ))), TwE6Cube k σ q E → q ≠ 8 →
      ∀ f ∈ E, f ≠ 1 →
        (∀ s : twistedE6RootGroup k σ, f = MulAut.conj s → twE6FixDim k σ s ≠ 24) →
        ∀ J : Subgroup (twistedE6RootGroup k σ),
          CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f)) →
            (∀ g ∈ E, J.map g.toMonoidHom = J) ∧ TwE6CoverComponentType J

@[expose] def TwE6LineRGen : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (σ : k ≃+* k) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup k σ))), TwE6Cube k σ q E → q ≠ 8 →
      ∀ f ∈ E, f ≠ 1 →
        (∀ s : twistedE6RootGroup k σ, f = MulAut.conj s → twE6FixDim k σ s ≠ 24) →
        ∀ c : twistedE6RootGroup k σ, f c = c →
          (∃ n : ℕ, c ^ (ringChar k ^ n) = 1) →
            c ∈ sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))}

end Components

section DiagNotAll24

theorem seitzHyperGamma_eq_top_twE6_diag_notAll24 (hC : TwE6CoverComponents)
    (hR : TwE6LineRGen) {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] {σ : k ≃+* k} {q : ℕ}
    (hkq : Nat.card k = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hk3 : ringChar k ≠ 3)
    (hq3 : q % 3 = 2) (hq2 : q ≠ 2) (hq8 : q ≠ 8)
    (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hEd : coverImage θ E ≤ twistedE6Inn k σ ⊔ twistedE6Diag k σ)
    (hEi : ¬ coverImage θ E ≤ twistedE6Inn k σ)
    (hNR : ¬ TwE6NormalizesR k σ (coverImage θ E))
    (hA : ¬ TwE6InnerAll24 k σ (coverImage θ E)) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  let π : K →* twistedE6RootGroup k σ :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  let ind : MulAut K →* MulAut (twistedE6RootGroup k σ) :=
    (MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)
  have hind : ∀ (f : MulAut K) (g : K), π (f g) = ind f (π g) := by
    intro f g
    simp [π, ind, MulAut.congr, quotientCenterAut']
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : π.ker ≤ Subgroup.center K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact (QuotientGroup.eq_one_iff x).mp (θ.injective (by simpa [π] using hx))
  have h3 : 3 ∣ q + 1 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hcube : TwE6Cube k σ q (coverImage θ E) :=
    ⟨hk3, hσ, hkq, h3, hq2, isElemAbelian_coverImage θ hE,
      by rw [card_coverImage hperf θ E, hcard], hEd, hEi, hNR⟩
  have hinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup k σ →* MulAut (twistedE6RootGroup k σ)) :=
    mulAut_conj_injective_of_center_eq_bot (exceptional_fixed_center_trivial TwistTag.E6 k σ)
  unfold TwE6InnerAll24 at hA
  push Not at hA
  obtain ⟨s, hsE, hs1, hs24⟩ := hA
  have hc1 : (MulAut.conj s : MulAut (twistedE6RootGroup k σ)) ≠ 1 := fun h =>
    hs1 (hinj (by rw [h, map_one]))
  have hc3 : (MulAut.conj s : MulAut (twistedE6RootGroup k σ)) ^ 3 = 1 :=
    hcube.elemAbelian.2 _ hsE
  obtain ⟨F, hFE, hFc, hsF, hFi⟩ :=
    exists_plane_through_inner_outer (coverImage θ E) hcube.elemAbelian hcube.not_le_inn s hsE hc1
  have hty : ∀ f ∈ F, f ≠ 1 →
      ∀ s' : twistedE6RootGroup k σ, f = MulAut.conj s' → twE6FixDim k σ s' ≠ 24 := by
    rintro f hfF hf1 s' hs'
    have hmem : f ∈ Subgroup.zpowers (MulAut.conj s) :=
      mem_zpowers_of_mem_inf hFc hFi hsF ⟨s, rfl⟩ hc1 hc3 hfF (hs' ▸ ⟨s', rfl⟩)
    rcases eq_or_eq_inv_of_mem_zpowers hc3 hc1 hmem hf1 with h | h
    · rw [hinj (hs'.symm.trans h)]; exact hs24
    · rw [hinj (hs'.symm.trans (h.trans (map_inv _ s).symm)), twE6FixDim_inv]; exact hs24
  have hgen : CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.UniPlaneGen (ringChar k) F :=
    uniPlaneGen_twE6 hk3 hσ hkq hq3 hq2 F (hcube.elemAbelian.mono hFE) hFc
      (fun h => absurd h hq8)
  let Q : Subgroup (MulAut K) := E ⊓ F.comap ind
  have hFE' : F ≤ E.map ind := by dsimp only [ind]; exact hFE
  have hQmap : Q.map ind = F := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hFE' hy)
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  let L : MulAut K → Subgroup K := fun _ => seitzHyperGamma 3 E
  have hL : ∀ φ ∈ Q, ind φ ≠ 1 → L φ ≤ seitzHyperGamma 3 E := fun _ _ _ => le_rfl
  have hr : ∀ φ ∈ Q, ind φ ≠ 1 → ∀ c : twistedE6RootGroup k σ,
      ind φ c = c → (∃ n : ℕ, c ^ (ringChar k ^ n) = 1) →
      c ∈ (L φ).map π := by
    intro φ hφQ hφind1 c hfixc hpowc
    have hφF : ind φ ∈ F := Subgroup.mem_comap.mp hφQ.2
    have hφE : ind φ ∈ coverImage θ E := hFE hφF
    have hline := hty (ind φ) hφF hφind1
    have hmem := hR k σ q (coverImage θ E) hcube hq8 (ind φ) hφE hφind1 hline c hfixc hpowc
    have hle : sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers (ind φ)))} ≤
        (seitzHyperGamma 3 E).map π := by
      refine sSup_le ?_
      intro J hJ
      obtain ⟨hnorm, htype⟩ := hC k σ q (coverImage θ E) hcube hq8 (ind φ) hφE hφind1 hline J hJ
      have hφ1 : φ ≠ 1 := fun h => hφind1 (by rw [h, map_one])
      exact coverComponent_le_hyperGamma seitzQuasiAt_two_holds
        CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
        CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
        hπ hker ind hind hE hcard hφQ.1 hφ1 hJ.2.2
        (fun c hc => hJ.1 hc (ind φ) (Subgroup.mem_zpowers (ind φ)))
        (fun ε hε => hnorm (ind ε) (by
          dsimp only [ind]; exact Subgroup.mem_map_of_mem _ hε)) htype
    exact hle hmem
  exact seitzHyperGamma_eq_top_of_uniPlaneGen_layers (π := π) hperf hπ hker ind
    (p := 3) (r := ringChar k) (E := E) (P := Q) (by rw [hQmap]; exact hgen) L hL hr

theorem coverTwE6DiagNotAll24_of (hC : TwE6CoverComponents) (hR : TwE6LineRGen) :
    CoverTwE6DiagNotAll24 := by
  intro K _ _ hperf k _ _ σ q hkq hσ hk3 hq3 hq2 hq8 θ E hE hcard hEd hEi hNR hA
  exact seitzHyperGamma_eq_top_twE6_diag_notAll24 hC hR hperf hkq hσ hk3 hq3 hq2 hq8 θ
    (E := E) hE hcard hEd hEi hNR hA

end DiagNotAll24

end CFSG.LieType.SeitzGeneration.CubeCoverE6

end
