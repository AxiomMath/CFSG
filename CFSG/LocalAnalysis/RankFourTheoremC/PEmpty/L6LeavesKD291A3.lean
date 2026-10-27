module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Model
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Fam
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesDeltaKD
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCField
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Mult
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291Zero
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankE7Final
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankE8Holds
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Final3

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.AGLEmbedding (CatalogSimpleSections)

namespace L6KD291

theorem centralizer_singleton_eq_zpowers' {G : Type*} [Group G] (w : G) :
    centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem hasNormalPComplement_of_ker_coprime {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (f : G →* H) (hker : Nat.Coprime p (Nat.card f.ker))
    (h : CFSG.HasNormalPComplement p H) : CFSG.HasNormalPComplement p G := by
  obtain ⟨N, hN, hNc, hNp⟩ := h
  refine ⟨N.comap f, inferInstance, ?_, ?_⟩
  · refine (Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hdvd => ?_
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hgN : f (g : G) ∈ N := g.2
    have h1 : orderOf (f (g : G)) ∣ p := by
      refine (orderOf_map_dvd f (g : G)).trans ?_
      rw [← hg, Subgroup.orderOf_coe]
    have h2 : orderOf (f (g : G)) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hgN
    have h3 : orderOf (f (g : G)) = 1 :=
      Nat.eq_one_of_dvd_coprimes hNc h1 h2
    have h4 : (g : G) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      exact orderOf_eq_one_iff.1 h3
    have h5 : p ∣ Nat.card f.ker := by
      have := Subgroup.orderOf_dvd_natCard f.ker h4
      rwa [Subgroup.orderOf_coe, hg] at this
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hker h5
  · intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hNp (QuotientGroup.mk (f g))
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_comap, map_pow]
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk

theorem hasNormalPComplement_centralizer_of_map {X Y : Type*} [Group X] [Finite X] [Group Y]
    {p : ℕ} [hp : Fact p.Prime] (π : X →* Y) (hπs : Function.Surjective π)
    (hker : Nat.Coprime p (Nat.card π.ker)) {x : X} (hxp : IsPGroup p (zpowers x))
    (h : CFSG.HasNormalPComplement p ↥(centralizer ({π x} : Set Y))) :
    CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set X)) := by
  have hmap :=
    CFSG.RankThreeEvenClassification.Helpers.centralizer_map_eq_of_pGroup_prime_complement_kernel
      p hp.out π hπs ((Nat.Prime.coprime_iff_not_dvd hp.out).1 hker) (zpowers x) hxp
  rw [MonoidHom.map_zpowers, ← centralizer_singleton_eq_zpowers',
    ← centralizer_singleton_eq_zpowers'] at hmap
  set C : Subgroup X := centralizer ({x} : Set X) with hC
  set C' : Subgroup Y := centralizer ({π x} : Set Y) with hC'
  let ρ : ↥C →* ↥C' := (π.comp C.subtype).codRestrict C'
    (fun c => hmap ▸ Subgroup.mem_map_of_mem π c.2)
  have hρ : Function.Surjective ρ := by
    rintro ⟨c, hc⟩
    rw [← hmap] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact ⟨⟨k, hk⟩, rfl⟩
  have hρker : Nat.Coprime p (Nat.card ρ.ker) := by
    refine Nat.Coprime.coprime_dvd_right ?_ hker
    let ι : ρ.ker →* π.ker :=
      { toFun := fun c => ⟨(c : ↥C).1, by
          have h1 : ρ (c : ↥C) = 1 := c.2
          have h2 := congrArg Subtype.val h1
          exact h2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Subgroup.card_dvd_of_injective ι fun a b hab => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : π.ker => (z : X)) hab))
  exact hasNormalPComplement_of_ker_coprime ρ hρker h

end L6KD291

section CrossAll


theorem crossAt_all (h7 : CrossE7SevenSplit) (h8 : CrossE8FiveFour) :
    ∀ d : TauCeti.ValidLieTypeIndex, CrossAt d := by
  have hBbig : ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B r q).Valid),
      CrossAtOn ⟨.B r q, hv⟩ (fun p => r < p) := by
    intro r q hv
    refine crossAtOn_of_forall_crossAtPrime fun p hrp => ?_
    have hr2 : 2 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    · obtain rfl : r = 2 := by omega
      exact crossAtPrime_B2 hv
    · by_cases hq : q.p = 2
      · exact crossAtPrime_B_even_of_lt hv hq hr3 hrp
      · exact crossAtPrime_B_odd_of_lt hv hq hr3 hrp
  have hCbig : ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.C r q).Valid),
      CrossAtOn ⟨.C r q, hv⟩ (fun p => r < p) :=
    fun r q hv => crossAtOn_of_forall_crossAtPrime fun p hrp => crossAtPrime_C_of_lt hv hrp
  have hDbig : ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D r q).Valid),
      CrossAtOn ⟨.D r q, hv⟩ (fun p => r < p) :=
    fun r q hv => crossAtOn_of_forall_crossAtPrime fun p hrp => crossAtPrime_D_of_lt hv hrp
  have htDbig : ∀ (r : ℕ) (q : TauCeti.PrimePower)
      (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid),
      CrossAtOn ⟨.twistedD r q, hv⟩ (fun p => r < p) :=
    fun r q hv => crossAtOn_of_forall_crossAtPrime fun p hrp => crossAtPrime_twistedD_of_lt hv hrp
  have hA : CrossFamLinear := crossFamLinear_of_geThree crossFamLinearGeThree
  have htA : CrossFamUnitary :=
    crossFamUnitary_of_geThree (crossFamUnitaryGeThree_of_large crossFamUnitaryLarge)
  have hB : CrossFamB :=
    crossFamB_of_large hBbig crossFamBSpLarge (crossFamBOrthLarge_of_even crossFamBOrthEvenLarge)
  have hC : CrossFamC := crossFamC_of_large hCbig crossFamCLarge
  have hD : CrossFamD := crossFamD_of_large hDbig (crossFamDLarge_of_even crossFamDEvenLarge)
  have htD : CrossFamTwistedD :=
    crossFamTwistedD_of_large htDbig (crossFamTwistedDLarge_of_even crossFamTwistedDEvenLarge)
  have hE6 : CrossFamE6 := crossFamE6_of_five crossFamE6Five_holds
  have htE6 : CrossFamTwistedE6 := crossFamTwistedE6_of_five crossFamTwistedE6Five_holds
  have hE7 : CrossFamE7 := crossFamE7_of_small (crossFamE7Small_of_split h7)
  have hE8 : CrossFamE8 := crossFamE8_of_small (crossFamE8Small_of_four h8)
  intro d
  obtain ⟨d, hv⟩ := d
  cases d with
  | A m q => exact hA m q hv
  | twistedA m q => exact htA m q hv
  | B r q => exact hB r q hv
  | C r q => exact hC r q hv
  | D r q => exact hD r q hv
  | twistedD r q => exact htD r q hv
  | E6 q => exact hE6 q hv
  | E7 q => exact hE7 q hv
  | E8 q => exact hE8 q hv
  | F4 q => exact crossAt_of_sylowAbelian (crossSylowAbelianF4_holds q hv)
  | G2 q => exact crossAt_of_sylowAbelian (crossSylowAbelianG2_holds q hv)
  | twistedE6 q => exact htE6 q hv
  | trialityD4 q => exact crossAt_of_sylowAbelian (crossSylowAbelianTrialityD4_holds q hv)
  | suzuki m => exact crossAt_suzuki hv
  | reeG2 m => exact crossAt_of_sylowAbelian (crossSylowAbelianReeG2_holds m hv)
  | reeF4 m => exact crossAt_of_sylowAbelian (crossSylowAbelianReeF4_holds m hv)
  | tits => exact crossFamTits hv

end CrossAll

section Assembly


theorem kd291a3_of_data (hMult : KDMultP5) (hFld : KDFieldP5) (hZero : KD291LinUniZero)
    (hModel : KD291LinUniModel) (hOut : SporadicOutOdd) (hR : SporadicCentralizerRank)
    (hAt : ∀ d : TauCeti.ValidLieTypeIndex, CrossAt d) (hNil : KD291Nilp)
    (hDef : KD291DefCharL) : KD291a3 := by
  intro X _ _ p P x z hpl L hL hLu
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp5 := hpl.five_le
  have hYD := I291.yData_of_plane63 hpl
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  have hD3 : ¬ p ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd hprime).mp (primeComplementCore_coprime p)
  set π : X →* X ⧸ D := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup X) := hpl.plane.isIsolatedPlane.1
  have hxP : x ∈ (P : Subgroup X) := hBP (Subgroup.mem_sup_left (mem_zpowers x))
  have hxp : IsPGroup p (zpowers x) := P.isPGroup'.to_le (zpowers_le.mpr hxP)
  have hcfg := hYD.cfg
  have hcat : CatalogSimpleSections (X ⧸ D) := hcfg.catalog
  have hcore : primeComplementCore (G := X ⧸ D) p = ⊥ := hcfg.core
  have hLn : L.Normal := I291.normal_of_unique hL hLu
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hcatQ : IsCatalogGroup (↥L ⧸ center ↥L) := hcat.isCatalogGroup_center_quotient hL
  refine L6KD291.hasNormalPComplement_centralizer_of_map π hπs
    ((Nat.Prime.coprime_iff_not_dvd hprime).2 (by rwa [hπ, QuotientGroup.ker_mk'])) hxp ?_
  by_cases hlu : IsLinearOrUnitaryAt p (↥L ⧸ center ↥L)
  ·
    have hLC : LinUniCfg p ((P : Subgroup X).map π) (x : X ⧸ D) (z : X ⧸ D) L :=
      ⟨hYD, hL, hLu, hlu⟩
    exact hNil p _ _ _ _ L hLC ⟨hZero p _ _ _ _ L hLC, hModel p _ _ _ _ L hLC⟩
  ·
    exfalso
    have hZ : center ↥L = ⊥ := by
      by_contra hZne
      exact hlu (hMult p hprime hp5 ↥L hq hcatQ hZne (I291.isPGroup_center hcore hL))
    obtain ⟨hsimp, hnonab, hcatL⟩ := hcat.isSimpleGroup_of_center_eq_bot hL hZ
    have hpc := I291.pCore_eq_bot hcfg hL hLn hZ
    have hC := I291.centralizer_eq_bot hcore hpc hL hLu hZ
    have hnlu : ¬ IsLinearOrUnitaryAt p ↥L := fun h => hlu (I291.isLinearOrUnitaryAt_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm h)
    have hx1 : (x : X ⧸ D) ≠ 1 := by
      intro h1
      have h2 := hYD.rank_cent
      rw [h1] at h2
      have h3 : centralizer ({(1 : X ⧸ D)} : Set (X ⧸ D)) = ⊤ := by simp
      rw [h3] at h2
      have := hYD.four_le
      omega
    have hxord : orderOf (x : X ⧸ D) = p := orderOf_eq_prime hcfg.x_pow hx1
    have hxL : (x : X ⧸ D) ∈ L := by
      by_contra hxL
      rcases hFld p hprime hp5 (X ⧸ D) hcat hcore L hLn hsimp hnonab hnlu hC hYD.four_le _ hxL
          hxord with h | ⟨N, hNn, hNidx⟩
      · have := hYD.rank_cent
        omega
      · haveI := hNn
        have hN : N = ⊤ := hYD.perf N (IsPGroup.of_card (n := 1)
          ((Subgroup.index_eq_card N).symm.trans (hNidx.trans (pow_one p).symm)))
        rw [hN, Subgroup.index_top] at hNidx
        exact hprime.one_lt.ne hNidx
    exact L6KD291.inner_false hOut hR hAt hDef hprime hp5 L hsimp hnonab hcatL hnlu hC hYD.four_le
      hxL hxord hYD.rank_cent

end Assembly

section CertificateInstances


theorem kd291a3_of_kdata (hNil : KD291Nilp) (hDef : KD291DefCharL) : KD291a3 :=
  kd291a3_of_data (kdMultP5_of_tables
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
    kdFieldP5_holds kd291LinUniZero_holds kd291LinUniModel_holds sporadicOutOdd_holds
    (sporadicCentralizerRank_of_data sporadicRankTable_holds
      (sporadicClassWitness_of_pairs sporadicClassWitnessAt_Co1_five sporadicClassWitnessAt_HN_five
        sporadicClassWitnessAt_Ly_five sporadicClassWitnessAt_B_five sporadicClassWitnessAt_M_five
        sporadicClassWitnessAt_M_seven))
    (crossAt_all
      (crossE7SevenSplit_of_rank
        RankThreeTheoremC.KFactProofs.Stroth.Bal3.i294CrossLargePrime_holds
        crossRankE7SevenSplit_holds)
      (crossE8FiveFour_of_rank
        RankThreeTheoremC.KFactProofs.Stroth.Bal3.i294CrossLargePrime_holds
        crossRankE8FiveFour_holds))
    hNil hDef

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
