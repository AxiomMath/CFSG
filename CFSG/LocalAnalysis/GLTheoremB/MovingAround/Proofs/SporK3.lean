module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs273c2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporK3

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

section Spor4K

open CFSG.Yardstones.Md0ec50421ce4 (PSimple)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA (chevAut)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicLocalOneData SporadicOuterLeTwo)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf innerAut)

@[expose] def Input27_4SporDownK : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ s : TauCeti.SporadicName, Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ α : MulAut S, α ^ p = 1 → α ≠ 1 →
      ∀ I : Subgroup S, GLAPComponent p (fixSubgroup α) I →
        IsLocallyOTwoBalancedWrtP p 1 (PSimple p I) ∨
          (CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) ≤ 2 ∧ (p = 3 ∨ ¬ p ^ 3 ∣ Nat.card S))

theorem isKGroup_spor_of_comp {X : Type} [Group X] (hX : CFSG.Open.IsKGroup X) (K : Subgroup X)
    {s : TauCeti.SporadicName} (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group :=
  ((hX.subgroup K).quotient _).of_surjective e.toMonoidHom e.surjective

theorem input27_4Spor_ofK (hOne : SporadicLocalOneData) (hCube : Inputs273.SporOneBalanceCube)
    (hOut : SporadicOuterLeTwo) (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hDown : Input27_4SporDownK) : Inputs273.Input27_4Spor := by
  intro p hp hp2 X _ _ hXK hO K hK hKh hT E A _ hA' _ _ _ _ _ _ _ _ _ hA2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hOK⟩ := Inputs273.comp_facts hO hK
  obtain ⟨s, ⟨e⟩⟩ := hT
  have hKs : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group := isKGroup_spor_of_comp hXK K e
  have hq : CFSG.Open.IsQuasisimple ↥K := hKh.1
  have hA2' : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2 →
      5 ≤ p ∧ (p ∣ (innerAut ↥K).index ∨ ∃ P : Sylow p ↥K, ¬ IsMulCommutative ↥(P : Subgroup ↥K)) :=
    fun h => ⟨(hA2 h).1, (hA2 h).2.2.2⟩
  have hO2K : IsLocallyOTwoBalancedWrtP p 1 (↥K ⧸ Subgroup.center ↥K) :=
    Inputs273.isLocallyOTwoBalancedWrtP_of_abs hp hp2
      (Inputs273.spor_balanced hOne hCube hOut hSpM hp hp2 hq hOK e hA2')
  refine Or.inr (Or.inr (Or.inl fun a ha ha1 J hJ => Or.inl ?_))
  have hqJ : CFSG.Open.IsQuasisimple (barOf p J) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
  refine Inputs123a.isLocallyOTwoBalancedWrtP_of_quot hqJ.1 ?_
  by_cases haN : a ∈ Subgroup.normalizer (K : Set X)
  · obtain ⟨g, -, haL, hJL⟩ := Inputs273.exists_conj_of_mem_normalizer hp hO hK hA'.2.1 ha haN hJ
    have hLc := Inputs273.glaPComponent_conj hK g
    obtain ⟨-, hOL⟩ := Inputs273.comp_facts hO hLc
    obtain ⟨eLK⟩ := Inputs273.nonempty_conj_center_quot K g
    have eS : PSimple p (GLBConj g K) ≃* ↥K ⧸ Subgroup.center ↥K :=
      (Lemma1315b.centerQuotEquiv (Inputs273.barOfEquivOfCore hOL)).trans eLK
    obtain ⟨hSs, hSna⟩ := CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian hp hLc
    haveI : IsSimpleGroup (PSimple p (GLBConj g K)) := hSs
    have hap3 : a ^ p = 1 := hA'.2.1.2 a ha
    have hap := Inputs273.isPGroup_zpowers_of_pow hap3
    have hI := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_chevTransfer hp haL hap hJL
    obtain ⟨eJI⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_chevTransfer hp haL hap hJL
    refine (Inputs123a.isLocallyOTwoBalancedWrtP_congr eJI).2 ?_
    by_cases hα1 : chevAut p (GLBConj g K) ⟨a, haL⟩ = 1
    · have hfix : fixSubgroup (chevAut p (GLBConj g K) ⟨a, haL⟩) = ⊤ := by
        rw [hα1]
        ext x
        simp [mem_fixSubgroup]
      rw [hfix] at hI
      obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv hp hSna hI
      exact (Inputs123a.isLocallyOTwoBalancedWrtP_congr (e1.trans eS)).2 hO2K
    · rcases hDown _ hSs hSna s ⟨eS.trans e⟩ hKs p hp hp2 _
          (CFSG.LocalAnalysis.GLTheoremA.chevAut_pow_eq_one p _ haL hap3) hα1 _ hI with hbal | ⟨hrk, h3⟩
      · exact hbal
      · exfalso
        have hrk' : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))) ≤ 2 := by
          rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr eS)]
          exact hrk
        have hcS : Nat.card (PSimple p (GLBConj g K)) = Nat.card (↥K ⧸ Subgroup.center ↥K) :=
          Nat.card_congr eS.toEquiv
        refine Inputs273.spor_false_of_rank hOut hSpM hp hq hOK e hrk' (fun hp5 => ?_) hA2'
        rcases h3 with h3 | h3
        · omega
        · rwa [← hcS]
  · obtain ⟨e'⟩ :=
      Inputs273.nonempty_pSimple_equiv_of_not_mem_normalizer hp hp2 hO hK hA'.2.1 ha ha1 haN hJ
    exact (Inputs123a.isLocallyOTwoBalancedWrtP_congr e').2 hO2K

end Spor4K

section RowsK

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges SporadicOnePair OffPair)

theorem isKGroup_carrier_of (hBr : SporadicBridges) {s : TauCeti.SporadicName}
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group) :
    CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier s) :=
  hK.of_surjective (hBr s).some.symm.toMonoidHom (hBr s).some.symm.surjective

theorem input27_4SporDown_of_rowsK (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hcard : ∀ s, Nat.card (CFSG.Blueprint.NativeSporadic.Carrier s) = CFSG.AGLEmbedding.sporOrd s)
    (hOff : ∀ s, OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hrows : ∀ name p, SporadicOnePair name p ∨ Inputs273c.CubeRow name p →
      CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic name).Group → Inputs273c.DownRow name p) :
    Input27_4SporDownK := by
  intro S _ _ hS hnab s he hK p hp hp2 α hα hα1 I hI
  haveI := hS
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer S) ≤ 2 := hOut S hS hnab s he
  obtain ⟨e⟩ := he
  have e' : S ≃* CFSG.Blueprint.NativeSporadic.Carrier s := e.trans (hBr s).some.symm
  have hcS : Nat.card S = CFSG.AGLEmbedding.sporOrd s := (Nat.card_congr e'.toEquiv).trans (hcard s)
  by_cases hrow : SporadicOnePair s p ∨ Inputs273c.CubeRow s p
  · left
    have hcop : Nat.Coprime p (Nat.card (Outer S)) := coprime_of_le_two hp hp2 Nat.card_pos.ne' hout
    have hαp : IsPGroup p (Subgroup.zpowers α) := by
      haveI : Fact p.Prime := ⟨hp⟩
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hα hα1, pow_one])
    obtain ⟨x, rfl⟩ := le_inner_of_isPGroup hcop hαp (Subgroup.mem_zpowers α)
    have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := conj_injective_of_center_eq_bot hcen
    have hxo : orderOf x = p := by
      haveI : Fact p.Prime := ⟨hp⟩
      rw [← orderOf_injective _ hinj x]
      exact orderOf_eq_prime hα hα1
    rw [Inputs1415.fixSubgroup_conj] at hI
    exact hrows s p hrow hK S ⟨e⟩ x hxo I hI
  · right
    push Not at hrow
    obtain ⟨hnotOne, hnotCube⟩ := hrow
    rcases hOff s p hp hp2 hnotOne with h3 | ⟨h4, hpair⟩
    · rw [← (Nat.card_congr e'.toEquiv)] at h3
      exact ⟨Inputs273.pRank_le_two_of_noCube hp (noElemAbelianCubeAut_of_not_dvd hp hp2 hcen hout h3),
        Or.inr h3⟩
    · rw [← (Nat.card_congr e'.toEquiv)] at h4
      have hpairS : CFSG.RankThree.PartOne.StrongP.HasNoncommPair p S :=
        CFSG.RankThree.PartOne.StrongP.HasNoncommPair.map e'.symm.toMonoidHom e'.symm.injective hpair
      refine ⟨Inputs273.pRank_le_two_of_noCube hp
        (noElemAbelianCubeAut_of_noncomm hp hp2 hcen hout h4 hpairS), ?_⟩
      by_cases hp3 : p = 3
      · exact Or.inl hp3
      · right
        intro h3
        have hp5 : 5 ≤ p := by
          have := hp.two_le
          rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
          · exact absurd h hp2
          · exact absurd h hp3
          · exact absurd (h ▸ hp) (by norm_num)
          · exact h
        rw [hcS] at h3 h4
        exact hnotCube (Inputs273c.cubeRow_of s hp hp5 h3 h4)

end RowsK

section CoreK

set_option linter.unusedSectionVars false

theorem input27_4Spor_of_downK
    (hCube : Inputs273.SporOneBalanceCube) (hDown : Input27_4SporDownK) :
    Inputs273.Input27_4Spor :=
  input27_4Spor_ofK Inputs273b.sporadicLocalOneData_holds hCube
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds Inputs273b.sporadicMultipliers_holds hDown

theorem input27_4Core_of_residualsK
    (hCube : Inputs273.SporOneBalanceCube) (hDown : Input27_4SporDownK)
    (hQ : Inputs273.Input27_4ChevQ) : Inputs27.Input27_4Core :=
  Inputs273.input27_4Core_of_cases Inputs273.input27_4Alt_holds Inputs273b.input27_4ChevP_holds
    (input27_4Spor_of_downK hCube hDown) hQ

end CoreK

section Holds

set_option linter.unusedSectionVars false

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges SporadicOnePair OffPair)
open CFSG.HardMathSupport.Dickson.I271

theorem downRow_B_threeK
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group) :
    Inputs273c.DownRow .B 3 :=
  Inputs273c.downRow_B_three_of_census CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOnePairHolds_Fi22_three
    (CFSG.HardMathSupport.Dickson.BMRows.census_B_three
      (isKGroup_carrier_of CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group hK))

theorem downRow_M_threeK
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    Inputs273c.DownRow .M 3 :=
  Inputs273c.downRow_M_three_of_census CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOnePairHolds_Fi24_three
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOnePairHolds_Th_three
    (CFSG.HardMathSupport.Dickson.BMRows.census_M_three
      (isKGroup_carrier_of CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group hK))

theorem downRow_B_fiveK
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group) :
    Inputs273c.DownRow .B 5 :=
  Inputs273c.downRow_B_five_of_census CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    Inputs273c.cubePairHolds_HS_five
    (CFSG.HardMathSupport.Dickson.BMRows.census_B_five
      (isKGroup_carrier_of CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group hK))

theorem downRow_M_fiveK
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    Inputs273c.DownRow .M 5 :=
  Inputs273c.downRow_M_five_of_census CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOnePairHolds_HN_five
    (CFSG.HardMathSupport.Dickson.BMRows.census_M_five
      (isKGroup_carrier_of CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group hK))

theorem downRows_of_restK
    :
    ∀ name p, SporadicOnePair name p ∨ Inputs273c.CubeRow name p →
      CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic name).Group → Inputs273c.DownRow name p := by
  have hBr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOut : SporadicOuterLeTwo := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hIn : DefCharInnerCoreFree := CFSG.HardMathSupport.Solomon.Coordinator.defCharInnerCoreFree_holds
  have hOutC : CFSG.HardMathSupport.Dickson.I271.DefCharOuterCoreFree := Inputs273b.defCharOuterCoreFree_holds
  have h3 : Nat.Prime 3 := Nat.prime_three
  have h5 : Nat.Prime 5 := Nat.prime_five
  intro name p h hK
  rcases h with h | h
  · simp only [SporadicOnePair, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl⟩
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .J3 (by decide)
        exact Inputs273c.downRow_of_split hIn hOutC hBr h3 (by norm_num) centShapeSplit_J3
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .McL (by decide)
        refine Inputs273c.downRow_of_noComp hBr h3 (Inputs273c.centTypes_of_constrained h3 fun k hk => ?_)
        refine mcl_constrainedShape_three CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_McL k
          (fun h1 => ?_) (by rw [← hk]; exact pow_orderOf_eq_one k)
        rw [h1, orderOf_one] at hk
        norm_num at hk
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Suz (by decide)
        exact Inputs273c.downRow_of_split hIn hOutC hBr h3 (by norm_num) centShapeSplit_Suz
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .ONan (by decide)
        exact Inputs273c.downRow_of_centTypes h3 (hBr .ONan).some
          (SporTables.centTypes_of_centShapeRk h3 onThree_centShapeRk)
          fun _ _ _ _ _ ⟨_, ⟨e⟩⟩ =>
            Inputs273c.balanced_of_alt (m := 6) h3 (by norm_num) (by norm_num) (by norm_num) e
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Co3 (by decide)
        exact Inputs273c.downRow_of_leafShape hIn hOutC hBr h3 (by norm_num) leafShape_Co3
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Co2 (by decide)
        exact Inputs273c.downRow_of_leafShape hIn hOutC hBr h3 (by norm_num) leafShape_Co2
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Co1 (by decide)
        refine Inputs273c.downRow_of_goodSpor hIn hOutC hBr h3 (by norm_num) (names := [.Suz]) (fun S hS => ?_)
          (SporTables.centTypes_of_centShapeRk h3
            (TabCo1.centShapeRk_Co1_three hBr (TabCo1.co1ThreeAShape_holds hOut hBr)))
        rw [List.mem_singleton] at hS
        subst hS
        exact Inputs273c.sporOneAt_of_onePair h3 (by norm_num) hOut hBr
          CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOnePairHolds_Suz_three
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Fi22 (by decide)
        exact Inputs273c.downRow_of_leafShape hIn hOutC hBr h3 (by norm_num) leafShape_Fi22
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Fi23 (by decide)
        exact Inputs273c.downRow_of_leafShape hIn hOutC hBr h3 (by norm_num)
            (TabFi23.leafShape_Fi23_of TabFi23.pConstrained_t3_two)
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Fi24Prime (by decide)
        exact Inputs273c.downRow_of_leafShape hIn hOutC hBr h3 (by norm_num) leafShape_Fi24_three
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .HN (by decide)
        exact Inputs273c.downRow_of_leafShape hIn hOutC hBr h3 (by norm_num) leafShape_HN
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Ly (by decide)
        refine Inputs273c.downRow_of_goodSpor hIn hOutC hBr h3 (by norm_num) (names := [.McL]) (fun S hS => ?_)
          (SporTables.centTypes_of_centShapeRk h3 (tabLy_centShapeRk hOut hBr))
        rw [List.mem_singleton] at hS
        subst hS
        exact Inputs273c.sporOneAt_of_onePair h3 (by norm_num) hOut hBr
          CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOnePairHolds_McL
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Th (by decide)
        exact Inputs273c.downRow_of_leafShape hIn hOutC hBr h3 (by norm_num) leafShape_Th
      · exact downRow_B_threeK hK
      · exact downRow_M_threeK hK
    · rcases h with rfl | rfl | rfl | rfl | rfl
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Co1 (by decide)
        refine Inputs273c.downRow_of_goodSpor hIn hOutC hBr h5 (by norm_num) (names := [.J2]) (fun S hS => ?_)
          (SporTables.centTypes_of_centShapeMulti h5 (TabCo1.centShapeMulti_Co1_five hOut))
        rw [List.mem_singleton] at hS
        subst hS
        exact Inputs273c.sporOneAt_J2_five
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .HN (by decide)
        exact Inputs273c.downRow_of_goodSpor hIn hOutC hBr h5 (by norm_num) (names := [])
          (fun S hS => (List.not_mem_nil hS).elim)
          (SporTables.centTypes_of_centShapeRk' h5 (hn5_centShapeRk'_HN hnFiveMoved_holds))
      · haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Ly (by decide)
        exact Inputs273c.downRow_of_noComp hBr h5 (Inputs273c.centTypes_of_constrained h5 fun k hk =>
          pConstrainedShape_Ly_five _ ⟨MulEquiv.refl _⟩ hk)
      · exact downRow_B_fiveK hK
      · exact downRow_M_fiveK hK
    · exact Inputs273c.downRow_M_seven_of_census hBr (Inputs273c.cubePairHolds_He_seven hOut hBr)
        CFSG.HardMathSupport.Dickson.BMRows.census_M_seven
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Inputs273c.downRow_HS_five hBr
    · exact Inputs273c.downRow_McL_five hBr
    · exact Inputs273c.downRow_Co2_five hBr
    · exact Inputs273c.downRow_Co3_five hBr
    · exact Inputs273c.downRow_Ru_five hBr
    · exact Inputs273c.downRow_Th_five hBr
    · exact Inputs273c.downRow_He_seven hIn hOutC hBr
    · exact Inputs273c.downRow_ON_seven hBr
    · exact Inputs273c.downRow_Fi24_seven hBr
    · exact Inputs273c.downRow_J4_eleven hBr
    · exact Inputs273c.downRow_M_thirteen hBr

theorem input27_4SporDownK_holds
    : Input27_4SporDownK :=
  input27_4SporDown_of_rowsK CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    (CFSG.AGLEmbedding.card_carrier_eq_sporOrd CFSG.Open.Open.monster_y443_derived_card)
    (CFSG.HardMathSupport.Timmesfeld.Tables.Census.offPair_carrier
      CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicBMData_holds)
    downRows_of_restK

end Holds

@[expose] def Input27_34ChevQ : Prop :=
  Inputs273.Input27_3ChevQ ∧ Inputs273.Input27_4ChevQ

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporK3

end
