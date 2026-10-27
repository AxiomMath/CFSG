module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalExclA
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.CoxeterFi24
public import CFSG.LocalAnalysis.SectionRank.QTK.Spor
public import CFSG.RankThree.PartOne.TCB.BabyRoute
public import CFSG.Sporadic.Bridge.Fi24Surj
public import CFSG.Sporadic.Bridge.Y322Central
public import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.YGroups.Y443.Native.EdgeNoncomm
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open Subgroup

theorem nonab_of_simple_not_prime {G : Type} [Group G] [IsSimpleGroup G]
    (hp : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  push Not at h
  letI : CommGroup G := { ‹Group G› with mul_comm := fun a b => h a b }
  exact hp (CommGroup.is_simple_iff_prime_card.mp ‹IsSimpleGroup G›)

theorem false_of_Fi22
    {A : Type} [Group A] [Finite A]
    (L : Subgroup A)
    (hL : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group))
    (hloc : ∀ U : Subgroup A, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank 3 (normalizer (U : Set A) ⊓ L) ≤ 3) : False := by
  obtain ⟨e⟩ := hL
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have hg : ↥L ≃* CFSG.Blueprint.NativeSporadic.Fi22 := e.trans f.symm
  haveI : Finite CFSG.Blueprint.NativeSporadic.Fi22 := Finite.of_equiv ↥L hg.toEquiv
  have hT : CFSG.Assembly.RankThreeEven.localRank 3 ↥L =
      CFSG.Assembly.RankThreeEven.localRank 3 CFSG.Blueprint.NativeSporadic.Fi22 :=
    @CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv ↥L CFSG.Blueprint.NativeSporadic.Fi22
      (inferInstance) (inferInstance) (inferInstance) (inferInstance) hg 3 Nat.prime_three
  have h4c : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 CFSG.Blueprint.NativeSporadic.Fi22 :=
    CFSG.RankThree.PartTwo.Census.four_le_localRank_three_Fi22
  have h4 : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 ↥L := by
    rw [hT]
    exact h4c
  exact false_of_localRank_four L h4 hloc

theorem false_of_Fi23
    {A : Type} [Group A] [Finite A]
    (L : Subgroup A)
    (hL : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .Fi23).Group))
    (hloc : ∀ U : Subgroup A, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank 3 (normalizer (U : Set A) ⊓ L) ≤ 3) : False := by
  obtain ⟨e⟩ := hL
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
  have hg : ↥L ≃* CFSG.Blueprint.NativeSporadic.Fi23 := e.trans f.symm
  haveI : Finite CFSG.Blueprint.NativeSporadic.Fi23 := Finite.of_equiv ↥L hg.toEquiv
  have hT : CFSG.Assembly.RankThreeEven.localRank 3 ↥L =
      CFSG.Assembly.RankThreeEven.localRank 3 CFSG.Blueprint.NativeSporadic.Fi23 :=
    @CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv ↥L CFSG.Blueprint.NativeSporadic.Fi23
      (inferInstance) (inferInstance) (inferInstance) (inferInstance) hg 3 Nat.prime_three
  have h4c : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 CFSG.Blueprint.NativeSporadic.Fi23 :=
    CFSG.RankThree.PartTwo.Census.four_le_localRank_three_Fi23
  have h4 : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 ↥L := by
    rw [hT]
    exact h4c
  exact false_of_localRank_four L h4 hloc

open CFSG.QuasithinUnique.SQTK TauCeti.Sporadic in
theorem false_of_Fi24Prime
    {A : Type} [Group A] [Finite A] (L : Subgroup A)
    (hL : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group))
    (hloc : ∀ U : Subgroup A, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank 3 (normalizer (U : Set A) ⊓ L) ≤ 3) : False := by
  obtain ⟨e⟩ := hL
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have hg : ↥L ≃* CFSG.Blueprint.NativeSporadic.Fi24prime := e.trans f.symm
  haveI : Finite CFSG.Blueprint.NativeSporadic.Fi24prime := Finite.of_equiv ↥L hg.toEquiv
  have hsimple : IsSimpleGroup ↥L :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime hg
  have hcard : Nat.card ↥L = 1255205709190661721292800 := by
    rw [Nat.card_congr hg.toEquiv]
    exact CFSG.Sporadic.Fi24.card_Fi24prime
  have hnp : ¬ (Nat.card ↥L).Prime := by
    rw [hcard]
    intro hp
    have h2 := hp.eq_one_or_self_of_dvd 2 (by norm_num)
    norm_num at h2
  have hnonab : ∃ a b : ↥L, a * b ≠ b * a := nonab_of_simple_not_prime hnp
  have h4 : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 ↥L := by
    refine CFSG.RankThree.PartTwo.Census.four_le_localRank_three_of_coxeter fi24CoxeterEdges
      fi24AutomorphismCoxeterMatrix (fun i j => ?_)
      (Coxeter.edgeGraph_connected 11 (by decide +kernel) (by decide +kernel))
      (Coxeter.edgeGraph_cliqueFree_three (by decide +kernel)) PresentedGroup.of
      (PresentedGroup.closure_range_of _) fi24AutomorphismGroup_of_mul_of_pow
      (K := commutator Fi24AutomorphismGroup) le_rfl (e.trans fi24PrimeGroupMulEquivCommutator)
      hnonab ![5, 11, 1, 7] ![6, 10, 2, 8] (by decide +kernel) (by decide +kernel) 9 4
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
    rw [fi24AutomorphismCoxeterMatrix_apply, fi24AutomorphismEdges_def]
    rfl
  exact false_of_localRank_four L h4 hloc

theorem false_of_B
    {A : Type} [Group A] [Finite A] (L : Subgroup A)
    (hL : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .B).Group))
    (hloc : ∀ U : Subgroup A, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank 3 (normalizer (U : Set A) ⊓ L) ≤ 3) : False := by
  obtain ⟨e⟩ := hL
  obtain ⟨f⟩ := CFSG.RankThree.PartOne.TCB.nonempty_mulEquiv_B
  have hg : ↥L ≃* CFSG.Blueprint.NativeSporadic.B := e.trans f.symm
  haveI : Finite CFSG.Blueprint.NativeSporadic.B := Finite.of_equiv ↥L hg.toEquiv
  have hT : CFSG.Assembly.RankThreeEven.localRank 3 ↥L =
      CFSG.Assembly.RankThreeEven.localRank 3 CFSG.Blueprint.NativeSporadic.B :=
    @CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv ↥L CFSG.Blueprint.NativeSporadic.B
      (inferInstance) (inferInstance) (inferInstance) (inferInstance) hg 3 Nat.prime_three
  have h4c : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 CFSG.Blueprint.NativeSporadic.B :=
    CFSG.RankThree.PartTwo.Census.four_le_localRank_three_B
  have h4 : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 ↥L := by
    rw [hT]
    exact h4c
  exact false_of_localRank_four L h4 hloc

theorem false_of_M
    {A : Type} [Group A] [Finite A] (L : Subgroup A)
    (hL : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .M).Group))
    (hloc : ∀ U : Subgroup A, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank 3 (normalizer (U : Set A) ⊓ L) ≤ 3) : False := by
  obtain ⟨e⟩ := hL
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
  have hg : ↥L ≃* CFSG.Blueprint.NativeSporadic.M := e.trans f.symm
  haveI : Finite CFSG.Blueprint.NativeSporadic.M := Finite.of_equiv ↥L hg.toEquiv
  have hD : ∃ a b : CFSG.Open.MonsterY443Derived, a * b ≠ b * a := by
    refine ⟨CFSG.YGroups.y443C, CFSG.YGroups.y443X * CFSG.YGroups.y443C * CFSG.YGroups.y443X,
      fun h => CFSG.YGroups.Y443.fM_C_X_noncomm ?_⟩
    have h' := congrArg CFSG.YGroups.Y443.fM h
    simpa only [map_mul] using h'
  obtain ⟨a, b, hab⟩ := hD
  have φ : ↥L ≃* CFSG.Open.MonsterY443Derived :=
    hg.trans CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv
  have hnonab : ∃ g h : ↥L, g * h ≠ h * g :=
    ⟨φ.symm a, φ.symm b, fun h => hab (by
      have h' := congrArg φ h
      simpa only [map_mul, MulEquiv.apply_symm_apply] using h')⟩
  have h4 : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 ↥L :=
    CFSG.SectionRank.QTK.four_le_localRank_three_of_mulEquiv_nativeM hg hnonab
  exact false_of_localRank_four L h4 hloc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
