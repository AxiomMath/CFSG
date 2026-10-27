module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.Q8Twin
public import CFSG.ClassicalInvolution.AschTight.S19BEnd
public import CFSG.ClassicalInvolution.Q3.TL3SecOdd
public import CFSG.ClassicalInvolution.Q3.TL3TopRestrict

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem ofSylow (hd : Q8TwinDatum R S t) (S' : Sylow 2 R) : Q8TwinDatum R S' t := by
  classical
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R S S'
  refine ⟨?_, ?_, hd.order, hd.cent, hd.twoGroup⟩
  · obtain ⟨r, hr, ⟨e⟩⟩ := hd.quat
    exact ⟨r, hr, ⟨(Sylow.equiv S' S).trans e⟩⟩
  · obtain ⟨s, hs, hst⟩ := hd.mem
    have hsR : (s : Y) = t := hst
    rw [← hg]
    refine ⟨g * s * g⁻¹, ?_, ?_⟩
    · rw [Sylow.coe_subgroup_smul]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨s, hs, by
        simp [MulAut.smul_def, MulAut.conj_apply]⟩
    · show ((g : Y) * (s : Y) * (g : Y)⁻¹) = t
      rw [hsR]
      have hgt : (g : Y) * t = t * (g : Y) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hd.cent g.2)
      calc (g : Y) * t * (g : Y)⁻¹ = t * (g : Y) * (g : Y)⁻¹ := by rw [hgt]
        _ = t := by group

theorem exists_sylow_le_centralizer (hd : Q8TwinDatum R S t) {B : Subgroup Y}
    (hB2 : IsPGroup 2 ↥B) (hBR : B ≤ centralizerModOdd ⊤ R) :
    ∃ S' : Sylow 2 R, (S' : Subgroup R).map R.subtype ≤ Subgroup.centralizer (B : Set Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup Y := R ⊓ Subgroup.centralizer (B : Set Y) with hH
  set φ : ↥H →* ↥R ⧸ classicalInvolutionOddCore ↥R :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥R)).comp
      (Subgroup.inclusion (inf_le_left : H ≤ R)) with hφ
  have hsurj : Function.Surjective φ := S19B.surjective_mk_inf_centralizer hB2 hBR
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥H))
  have hP2 : IsPGroup 2 ↥((P : Subgroup H).map H.subtype) := P.isPGroup'.map _
  have hPR : (P : Subgroup H).map H.subtype ≤ R :=
    (Subgroup.map_subtype_le _).trans inf_le_left
  have hcardQ : Nat.card (↥R ⧸ classicalInvolutionOddCore ↥R) =
      Nat.card ↥((S : Subgroup R).map R.subtype) := by
    obtain ⟨e⟩ := QuaternionStructure.nonempty_mulEquiv_sylow_of_isPGroup_oddCore_quotient
      hd.twoGroup S
    exact (Nat.card_congr e.toEquiv).trans
      (Subgroup.card_map_of_injective R.subtype_injective).symm
  have hPtop : (P : Subgroup H).map φ = ⊤ := by
    have h2 : IsPGroup 2 (↥R ⧸ classicalInvolutionOddCore ↥R) := hd.twoGroup
    have := (P.mapSurjective hsurj).is_maximal' (h2.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at this
    exact this.symm
  have hle : Nat.card ↥((S : Subgroup R).map R.subtype) ≤
      Nat.card ↥((P : Subgroup H).map H.subtype) := by
    rw [← hcardQ, Subgroup.card_map_of_injective H.subtype_injective]
    calc Nat.card (↥R ⧸ classicalInvolutionOddCore ↥R)
        = Nat.card ↥((P : Subgroup H).map φ) := by rw [hPtop, Subgroup.card_top]
      _ ≤ Nat.card ↥(P : Subgroup H) :=
          Nat.card_le_card_of_surjective _ (φ.subgroupMap_surjective (P : Subgroup H))
  have hsyl := (isSylow2In_map_sylow R S).of_natCard_le hP2 hPR hle
  set P' : Subgroup Y := (P : Subgroup H).map H.subtype with hP'
  let S' : Sylow 2 ↥R :=
    { toSubgroup := P'.subgroupOf R
      isPGroup' := hP2.comap_subtype
      is_maximal' := by
        intro Q hQ hle'
        have hVQ : P' ≤ Q.map R.subtype := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hPR]
          exact Subgroup.map_mono hle'
        have := hsyl.2.2 (Q.map R.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
        rw [← Subgroup.comap_map_eq_self_of_injective R.subtype_injective Q, this]
        rfl }
  refine ⟨S', ?_⟩
  show (P'.subgroupOf R).map R.subtype ≤ _
  rw [Subgroup.map_subgroupOf_eq_of_le hPR]
  exact (Subgroup.map_subtype_le _).trans inf_le_right

theorem restrict (hd : Q8TwinDatum R S t) {H : Subgroup Y}
    (hSH : (S : Subgroup R).map R.subtype ≤ H) :
    ∃ S' : Sylow 2 (R.subgroupOf H),
      Q8TwinDatum (R.subgroupOf H) S' (⟨t, hSH hd.mem⟩ : H) ∧
        Nonempty ((S' : Subgroup (R.subgroupOf H)) ≃* (S : Subgroup R)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set SY : Subgroup Y := (S : Subgroup R).map R.subtype with hSY
  have hSR : SY ≤ R := Subgroup.map_subtype_le _
  have hle : SY.subgroupOf H ≤ R.subgroupOf H := Subgroup.subgroupOf_mono H hSR
  set P0 : Subgroup ↥(R.subgroupOf H) := (SY.subgroupOf H).subgroupOf (R.subgroupOf H) with hP0
  let e1 : ↥P0 ≃* ↥(SY.subgroupOf H) := Subgroup.subgroupOfEquivOfLe hle
  let e2 : ↥(SY.subgroupOf H) ≃* ↥SY := Subgroup.subgroupOfEquivOfLe hSH
  let e3 : ↥SY ≃* ↥(S : Subgroup R) :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm
  let e : ↥P0 ≃* ↥(S : Subgroup R) := e1.trans (e2.trans e3)
  have hb : 2 ^ (Nat.card ↥R).factorization 2 = Nat.card P0 := by
    rw [Nat.card_congr e.toEquiv, Sylow.card_eq_multiplicity S]
  have hdvdR : Nat.card ↥(R.subgroupOf H) ∣ Nat.card ↥R :=
    Subgroup.card_dvd_of_injective (subgroupOfToSub R H) (subgroupOfToSub_injective R H)
  have hP0dvd : Nat.card P0 ∣ Nat.card ↥(R.subgroupOf H) := Subgroup.card_subgroup_dvd_card P0
  have hle1 : (Nat.card ↥(R.subgroupOf H)).factorization 2 ≤ (Nat.card ↥R).factorization 2 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvdR 2
  have hle2 : (Nat.card ↥R).factorization 2 ≤ (Nat.card ↥(R.subgroupOf H)).factorization 2 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne', hb]
    exact hP0dvd
  have hcard : Nat.card P0 = 2 ^ (Nat.card ↥(R.subgroupOf H)).factorization 2 := by
    rw [le_antisymm hle1 hle2, hb]
  have hS'coe : ((Sylow.ofCard P0 hcard : Sylow 2 ↥(R.subgroupOf H)) :
      Subgroup ↥(R.subgroupOf H)) = P0 := rfl
  have htR : (⟨t, hSH hd.mem⟩ : H) ∈ R.subgroupOf H := Subgroup.mem_subgroupOf.mpr
    (Subgroup.map_subtype_le _ hd.mem)
  have hcent : R.subgroupOf H ≤ Subgroup.centralizer ({(⟨t, hSH hd.mem⟩ : H)} : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hd.cent hx))
  refine ⟨Sylow.ofCard P0 hcard, ?_, ⟨e⟩⟩
  obtain ⟨r, hr, ⟨f⟩⟩ := hd.quat
  refine ⟨⟨r, hr, ⟨e.trans f⟩⟩, ?_, ?_, hcent, ?_⟩
  · rw [hS'coe]
    exact ⟨⟨⟨t, hSH hd.mem⟩, htR⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hd.mem), rfl⟩
  · rw [Subgroup.orderOf_mk]
    exact hd.order
  · exact isPGroup_two_quotient_subgroupOf R H hd.twoGroup

omit [Finite Y] in
theorem tightCore_idem (R : Subgroup Y) : tightCore (tightCore R) = tightCore R := by
  refine le_antisymm (tightCore_le _) ((Subgroup.closure_le _).mpr fun x hx => ?_)
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩

theorem isPGroup_two_quotient_of_le {K : Subgroup Y} (hKR : K ≤ R)
    (h : IsPGroup 2 (R ⧸ classicalInvolutionOddCore R)) :
    IsPGroup 2 (K ⧸ classicalInvolutionOddCore K) := by
  have h1 := isPGroup_two_quotient_subgroupOf R K h
  have htop : R.subgroupOf K = ⊤ := Subgroup.subgroupOf_eq_top.mpr hKR
  let e : ↥(R.subgroupOf K) ≃* ↥K := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hO : (classicalInvolutionOddCore ↥(R.subgroupOf K)).map e.toMonoidHom =
      classicalInvolutionOddCore ↥K :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  exact h1.of_equiv (QuotientGroup.congr _ _ e hO)

@[expose] noncomputable def sylowOf {V P : Subgroup Y} (h : IsSylow2In V P) : Sylow 2 ↥P where
  toSubgroup := V.subgroupOf P
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : V ≤ Q.map P.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map P.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective P.subtype_injective Q, this]
    rfl

theorem toCore (hd : Q8TwinDatum R S t) :
    ∃ S₀ : Sylow 2 ↥(tightCore R), Q8TwinDatum (tightCore R) S₀ t ∧
      Nonempty ((S₀ : Subgroup ↥(tightCore R)) ≃* (S : Subgroup R)) := by
  have hs := hd.sylow_core
  refine ⟨sylowOf hs, ?_, ?_⟩
  · set e : ↥((sylowOf hs : Subgroup ↥(tightCore R))) ≃* ↥(S : Subgroup R) :=
      (Subgroup.subgroupOfEquivOfLe hs.1).trans
        (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm
    obtain ⟨r, hr, ⟨f⟩⟩ := hd.quat
    refine ⟨⟨r, hr, ⟨e.trans f⟩⟩, ?_, hd.order, (tightCore_le R).trans hd.cent,
      isPGroup_two_quotient_of_le (tightCore_le R) hd.twoGroup⟩
    show t ∈ ((_ : Subgroup Y).subgroupOf (tightCore R)).map (tightCore R).subtype
    rw [Subgroup.map_subgroupOf_eq_of_le hs.1]
    exact hd.mem
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hs.1).trans
      (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm⟩

theorem exists_sec (hd : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) :
    ∃ (ht : t ∈ subnormalClosure (tightCore R))
      (S' : Sylow 2 ↥(R.subgroupOf (subnormalClosure (tightCore R)))),
      Q8TwinDatum (R.subgroupOf (subnormalClosure (tightCore R))) S' ⟨t, ht⟩ ∧
      TightSelfGen (R.subgroupOf (subnormalClosure (tightCore R))) ∧
      Nonempty (↥(S' : Subgroup ↥(R.subgroupOf (subnormalClosure (tightCore R)))) ≃*
        QuaternionGroup 2) := by
  set H : Subgroup Y := subnormalClosure (tightCore R) with hH
  have hKH : tightCore R ≤ H := le_subnormalClosure _
  have hSK : (S : Subgroup R).map R.subtype ≤ tightCore R := hd.sylow_core.1
  have hSH : (S : Subgroup R).map R.subtype ≤ H := hSK.trans hKH
  obtain ⟨S', hd', ⟨eS⟩⟩ := restrict hd hSH
  have hgen : TightSelfGen (R.subgroupOf H) := by
    unfold TightSelfGen
    rw [tightCore_subgroupOf hKH]
    exact iSup_conjSub_eq_top_of_subnormalClosure (subnormalClosure_subgroupOf_subnormalClosure _)
  obtain ⟨e⟩ := hq8
  exact ⟨hSH hd.mem, S', hd', hgen, ⟨eS.trans e⟩⟩

section OddQuot

variable {N : Subgroup Y} [N.Normal]

noncomputable def sylowEquiv (hd : Q8TwinDatum R S t) (hNodd : Odd (Nat.card ↥N)) :
    ↥(S : Subgroup R) ≃* ↥((TwistQ.sylowMap N S : Sylow 2 _) :
      Subgroup ↥(R.map (QuotientGroup.mk' N))) :=
  MulEquiv.ofBijective (((QuotientGroup.mk' N).subgroupMap R).subgroupMap (S : Subgroup R))
    ⟨by
      intro a b hab
      have h : QuotientGroup.mk' N ((a : R) : Y) = QuotientGroup.mk' N ((b : R) : Y) := by
        have := congrArg (fun x => ((x : ↥(R.map (QuotientGroup.mk' N))) : Y ⧸ N))
          (congrArg Subtype.val hab)
        exact this
      have hS2 : IsPGroup 2 ↥((S : Subgroup R).map R.subtype) := hd.sylow_core.2.1
      have hSN := OddQ.inf_eq_bot_of_two hS2 hNodd
      have ha : ((a : R) : Y) ∈ (S : Subgroup R).map R.subtype := ⟨a, a.2, rfl⟩
      have hb : ((b : R) : Y) ∈ (S : Subgroup R).map R.subtype := ⟨b, b.2, rfl⟩
      have := TwistQ.mk_inj hSN ha hb h
      exact Subtype.ext (Subtype.ext this),
     ((QuotientGroup.mk' N).subgroupMap R).subgroupMap_surjective _⟩

omit [Finite Y] in
theorem t_mul_t (hd : Q8TwinDatum R S t) : t * t = 1 := by
  rw [← pow_two, ← hd.order, pow_orderOf_eq_one]

theorem oddQuot (hd : Q8TwinDatum R S t) (hNodd : Odd (Nat.card ↥N)) :
    Q8TwinDatum (R.map (QuotientGroup.mk' N)) (TwistQ.sylowMap N S) (QuotientGroup.mk' N t) := by
  have hcent : R.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hd.cent hr)]
  have htN : t ∉ N := by
    intro h
    have hZ : IsPGroup 2 ↥(Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order, pow_one])
    have := Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers t, h⟩
    rw [OddQ.inf_eq_bot_of_two hZ hNodd, Subgroup.mem_bot] at this
    have ho := hd.order
    rw [this, orderOf_one] at ho
    omega
  refine ⟨?_, ?_, ?_, hcent, ?_⟩
  · obtain ⟨r, hr, ⟨e⟩⟩ := hd.quat
    exact ⟨r, hr, ⟨(sylowEquiv hd hNodd).symm.trans e⟩⟩
  · rw [TwistQ.sylowMap_map_subtype]
    exact Subgroup.mem_map_of_mem _ hd.mem
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hd.order, pow_orderOf_eq_one, map_one]
    · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact htN
  · set f : ↥R →* ↥(R.map (QuotientGroup.mk' N)) := (QuotientGroup.mk' N).subgroupMap R
    have hf : Function.Surjective f := (QuotientGroup.mk' N).subgroupMap_surjective R
    have hle : classicalInvolutionOddCore ↥R ≤
        (classicalInvolutionOddCore ↥(R.map (QuotientGroup.mk' N))).comap f := by
      intro x hx
      have hmap : (classicalInvolutionOddCore ↥R).map f ≤
          classicalInvolutionOddCore ↥(R.map (QuotientGroup.mk' N)) :=
        le_sSup ⟨(classicalInvolutionOddCore_normal ↥R).map f hf,
          (CFSG.ComponentClassification.OddCore.odd_card ↥R).of_dvd_nat
            (Subgroup.card_map_dvd _ _)⟩
      exact hmap ⟨x, hx, rfl⟩
    exact hd.twoGroup.of_surjective (QuotientGroup.map _ _ f hle)
      (QuotientGroup.map_surjective_of_surjective _ _ f (QuotientGroup.mk_surjective.comp hf)
        hle)

omit [Finite Y] in
theorem oddQuot_selfGen (hgen : TightSelfGen R) :
    TightSelfGen (R.map (QuotientGroup.mk' N)) := by
  have hgen' : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hgen
  show (⨆ g : Y ⧸ N, conjSub g (tightCore (R.map (QuotientGroup.mk' N)))) = ⊤
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), ← hgen',
    Subgroup.map_iSup]
  refine iSup_le fun g => ?_
  rw [TwistQ.conjSub_map]
  refine le_trans ?_ (le_iSup (fun g : Y ⧸ N =>
    conjSub g (tightCore (R.map (QuotientGroup.mk' N)))) (QuotientGroup.mk' N g))
  refine conjSub_mono ?_
  unfold tightCore
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxR, hx2⟩, rfl⟩
  refine ⟨⟨x, hxR, rfl⟩, ?_⟩
  rw [← MonoidHom.map_zpowers]
  exact hx2.map _

end OddQuot

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
