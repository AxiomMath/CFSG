module

public import CFSG.ClassicalInvolution.Q3.Q3DBChain
public import CFSG.ClassicalInvolution.Uniform.UBranchExit

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3DB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Uniform


theorem deltaConnected_of_oddCentralizerFree {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G}
    (hz : IsClassicalMemberU (.sl2 3 1) K z) (hBelow : CITBelowT (.sl2 3 1) (Nat.card G))
    (hW : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥)
    (hD : DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z))) :
    CFSG.ClassicalInvolution.DeltaConnected K := by
  rw [satU_three_eq_of_oddCentralizerFree hW] at hD
  exact deltaConnected_of_dConnected_of_oddCentralizerFree hnab (hz.toQ3 (by norm_num)) hW
    ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hBelow) hD

@[expose] def BootTripleD3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMemberU (.sl2 3 1) K z →
      CITBelowT (.sl2 3 1) (Nat.card G) → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) →
      IndepTriple3 (conjClass3 (satU (.sl2 3 1) K z)) →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥

@[expose] def BootNoTripleD3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMemberU (.sl2 3 1) K z →
      CITBelowT (.sl2 3 1) (Nat.card G) → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) →
      BootData3 (conjClass3 (satU (.sl2 3 1) K z)) →
      ¬ IndepTriple3 (conjClass3 (satU (.sl2 3 1) K z)) →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥

@[expose] def NoDataD3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMemberU (.sl2 3 1) K z →
      CITBelowT (.sl2 3 1) (Nat.card G) → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) →
      ¬ BootData3 (conjClass3 (satU (.sl2 3 1) K z)) →
      CFSG.ClassicalInvolution.DeltaConnected K

theorem dBridgeU_three_of_split (h1 : BootTripleD3) (h2 : BootNoTripleD3) (h3 : NoDataD3) :
    DBridgeU 3 1 := by
  intro G _ _ _ hnab _ _ hBelow K z hz hr hlarge hD
  by_cases hT : IndepTriple3 (conjClass3 (satU (.sl2 3 1) K z))
  · exact deltaConnected_of_oddCentralizerFree hnab hz hBelow
      (h1 G hnab K z hz hBelow hr hlarge hD hT) hD
  · by_cases hdata : BootData3 (conjClass3 (satU (.sl2 3 1) K z))
    · exact deltaConnected_of_oddCentralizerFree hnab hz hBelow
        (h2 G hnab K z hz hBelow hr hlarge hD hdata hT) hD
    · exact h3 G hnab K z hz hBelow hr hlarge hD hdata

@[expose] def BootTriple3ED : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G → DConnected (conjClass3 K) →
      IndepTriple3 (conjClass3 K) →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K → ExactMembers3 (conjClass3 K)

@[expose] def BootNoTriple3ED : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G → DConnected (conjClass3 K) →
      BootData3 (conjClass3 K) → ¬ IndepTriple3 (conjClass3 K) →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K → ExactMembers3 (conjClass3 K)

theorem oddCentralizerFree_of_exact_sat {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (hz : IsClassicalMemberU (.sl2 3 1) K z)
    (hex : ExactMembers3 (conjClass3 (satU (.sl2 3 1) K z))) :
    Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥ :=
  oddCentralizerFree_of_exact_intrinsic ((hz.satU_member).toQ3 (by norm_num))
    (oddCoreIn_le_satU (MemberType.isSolvableType_sl2.mpr (by norm_num)))
    (hex _ ⟨1, conjSub_one _⟩)

theorem bootTripleD3_of_bootTriple3ED (h : BootTriple3ED) : BootTripleD3 :=
  fun G _ _ _ hnab K z hz hBelowT hr hlarge hD hT =>
    oddCentralizerFree_of_exact_sat hz
      (h G hnab _ z ((hz.satU_member).toQ3 (by norm_num))
        ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hBelowT) hr hlarge hD hT
        (oddCoreIn_le_satU (MemberType.isSolvableType_sl2.mpr (by norm_num))))

theorem bootNoTripleD3_of_bootNoTriple3ED (h : BootNoTriple3ED) : BootNoTripleD3 :=
  fun G _ _ _ hnab K z hz hBelowT hr hlarge hD hdata hT =>
    oddCentralizerFree_of_exact_sat hz
      (h G hnab _ z ((hz.satU_member).toQ3 (by norm_num))
        ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hBelowT) hr hlarge hD hdata hT
        (oddCoreIn_le_satU (MemberType.isSolvableType_sl2.mpr (by norm_num))))

theorem dBridgeU_three_of_ED (h1 : BootTriple3ED) (h2 : BootNoTriple3ED) (h3 : NoDataD3) :
    DBridgeU 3 1 :=
  dBridgeU_three_of_split (bootTripleD3_of_bootTriple3ED h1)
    (bootNoTripleD3_of_bootNoTriple3ED h2) h3

@[expose] def OddCoreFreeD3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMemberU (.sl2 3 1) K z →
      CITBelowT (.sl2 3 1) (Nat.card G) → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥

theorem bootTripleD3_of_oddCoreFreeD3 (h : OddCoreFreeD3) : BootTripleD3 :=
  fun G _ _ _ hnab K z hz hBelow hr hlarge hD _ => h G hnab K z hz hBelow hr hlarge hD

theorem bootNoTripleD3_of_oddCoreFreeD3 (h : OddCoreFreeD3) : BootNoTripleD3 :=
  fun G _ _ _ hnab K z hz hBelow hr hlarge hD _ _ => h G hnab K z hz hBelow hr hlarge hD

theorem noDataD3_of_oddCoreFreeD3 (h : OddCoreFreeD3) : NoDataD3 :=
  fun G _ _ _ hnab K z hz hBelow hr hlarge hD _ =>
    deltaConnected_of_oddCentralizerFree hnab hz hBelow (h G hnab K z hz hBelow hr hlarge hD) hD

theorem dBridgeU_three_of_oddCoreFreeD3 (h : OddCoreFreeD3) : DBridgeU 3 1 :=
  dBridgeU_three_of_split (bootTripleD3_of_oddCoreFreeD3 h) (bootNoTripleD3_of_oddCoreFreeD3 h)
    (noDataD3_of_oddCoreFreeD3 h)

end CFSG.ClassicalInvolution.Q3.Q3DB
