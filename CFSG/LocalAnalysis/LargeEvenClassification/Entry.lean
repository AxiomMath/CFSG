module

public import CFSG.LocalAnalysis.LargeEvenClassification.LocalRank
public import CFSG.LocalAnalysis.LargeEvenClassification.ProperSections
public import CFSG.LocalAnalysis.LargeEvenClassification.CharacteristicAction
public import CFSG.LocalAnalysis.LargeEvenClassification.ElementaryLinear
public import CFSG.LocalAnalysis.LargeEvenClassification.BinaryRank

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem large_even_entry (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient]
    [IsSimpleGroup Ambient]
    (hnonab : ∃ first second : Ambient, first * second ≠ second * first)
    (hchar : IsCharTwoType Ambient) (hrank : 4 ≤ evenRank Ambient) :
    ∃ (prime : ℕ) (Local Elementary : Subgroup Ambient),
      prime ∈ oddLocalPrimes 4 Ambient ∧ IsTwoLocal Local ∧ Local ≠ ⊤ ∧
        Elementary ≤ Local ∧ IsElemAbelian prime Elementary ∧
        Nat.card Elementary = prime ^ evenRank Ambient ∧ pCoreOf 2 Local ≠ ⊥ ∧
        IsPGroup 2 (pCoreOf 2 Local) ∧
        ∃ action : Elementary →* MulAut ((pCoreOf 2 Local).subgroupOf Local),
          Function.Injective action := by
  obtain ⟨prime, Local, hprime, hodd, hlocal, hlocalRank⟩ :=
    evenRank_witness Ambient (by omega)
  obtain ⟨Elementary, hle, helementary, hcard⟩ := pRank_witness hprime.one_lt Local
  have hlocalPositive : 0 < pRank prime Local := hlocalRank ▸ (by omega)
  have hstratum : prime ∈ oddLocalPrimes 4 Ambient :=
    ⟨hprime, hodd, pRank_pos_prime_dvd hprime Local hlocalPositive,
      (hlocalRank ▸ hrank).trans (pRank_le_twoLocalPRank hprime.one_lt Local hlocal)⟩
  refine ⟨prime, Local, Elementary, hstratum, hlocal,
    twoLocal_ne_top Ambient hnonab Local hlocal, hle, helementary,
    hlocalRank ▸ hcard, twoLocal_core_ne_bot Local hlocal, pCoreOf_isPGroup 2 Local, ?_⟩
  exact charTwo_odd_core_action_injective hprime hodd hchar Elementary Local hle
    (IsPGroup.of_card hcard) hlocal

theorem large_even_entry_with_K (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient]
    [IsSimpleGroup Ambient]
    (hnonab : ∃ first second : Ambient, first * second ≠ second * first)
    (hK : IsKProperByOrder Ambient) (hchar : IsCharTwoType Ambient)
    (hrank : 4 ≤ evenRank Ambient) :
    ∃ (prime : ℕ) (Local Elementary : Subgroup Ambient),
      prime ∈ oddLocalPrimes 4 Ambient ∧ IsTwoLocal Local ∧ Local ≠ ⊤ ∧
        IsKProperByOrder Local ∧ Elementary ≤ Local ∧ IsElemAbelian prime Elementary ∧
        Nat.card Elementary = prime ^ evenRank Ambient ∧ pCoreOf 2 Local ≠ ⊥ ∧
        IsPGroup 2 (pCoreOf 2 Local) ∧
        ∃ action : Elementary →* MulAut ((pCoreOf 2 Local).subgroupOf Local),
          Function.Injective action := by
  obtain ⟨prime, Local, Elementary, hprime, hlocal, hproper, hle, helementary, hcard,
    hcoreNontrivial, hcorePGroup, haction⟩ := large_even_entry Ambient hnonab hchar hrank
  exact ⟨prime, Local, Elementary, hprime, hlocal, hproper, isKProper_subgroup hK Local,
    hle, helementary, hcard, hcoreNontrivial, hcorePGroup, haction⟩

theorem large_even_local_frattini_dimension (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] [IsSimpleGroup Ambient]
    (hnonab : ∃ first second : Ambient, first * second ≠ second * first)
    (hK : IsKProperByOrder Ambient) (hchar : IsCharTwoType Ambient)
    (hrank : 4 ≤ evenRank Ambient) :
    ∃ (prime : ℕ) (Local Elementary : Subgroup Ambient),
      prime ∈ oddLocalPrimes 4 Ambient ∧ IsTwoLocal Local ∧ Local ≠ ⊤ ∧
        IsKProperByOrder Local ∧ Elementary ≤ Local ∧ IsElemAbelian prime Elementary ∧
        Nat.card Elementary = prime ^ evenRank Ambient ∧ pCoreOf 2 Local ≠ ⊥ ∧
        let _ : CommGroup ((pCore 2 Local) ⧸ frattini (pCore 2 Local)) :=
          pGroupFrattiniCommGroup Nat.prime_two (pCore_isPGroup Local 2)
        ∃ module : Module (ZMod 2) (Additive ((pCore 2 Local) ⧸ frattini (pCore 2 Local))),
          let _ := module
          5 ≤ Module.finrank (ZMod 2) (Additive ((pCore 2 Local) ⧸ frattini (pCore 2 Local))) := by
  obtain ⟨prime, Local, Elementary, hprime, hlocal, hproper, hlocalK, hle,
    helementary, hcard, hcoreNontrivial, _, _⟩ :=
    large_even_entry_with_K Ambient hnonab hK hchar hrank
  refine ⟨prime, Local, Elementary, hprime, hlocal, hproper, hlocalK, hle,
    helementary, hcard, hcoreNontrivial, ?_⟩
  dsimp only
  let : CommGroup ((pCore 2 Local) ⧸ frattini (pCore 2 Local)) :=
    pGroupFrattiniCommGroup Nat.prime_two (pCore_isPGroup Local 2)
  let module : Module (ZMod 2) (Additive ((pCore 2 Local) ⧸ frattini (pCore 2 Local))) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two (pCore_isPGroup Local 2))
  refine ⟨module, ?_⟩
  have hcoreKernel := charTwo_local_coreFrattiniAction_ker hchar Local hlocal
  let : (pCore 2 Local).Normal := pCore_normal Local 2
  have helementaryCore : Disjoint Elementary (pCoreOf 2 Local) :=
    charTwo_odd_subgroup_disjoint_core hprime.1 hprime.2.1 Elementary Local (IsPGroup.of_card hcard)
  let groupAction := (coreFrattiniAction Local 2).comp (Subgroup.inclusion hle)
  have hgroupInjective : Function.Injective groupAction := by
    apply (MonoidHom.ker_eq_bot_iff groupAction).mp
    apply le_antisymm _ bot_le
    intro element helement
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    change (element : Ambient) = 1
    apply Subgroup.disjoint_def.mp helementaryCore element.property
    have hlocalCore : Subgroup.inclusion hle element ∈ pCore 2 Local :=
      hcoreKernel ▸ helement
    exact ⟨Subgroup.inclusion hle element, hlocalCore, rfl⟩
  let linearAction := (elementaryAutLinear 2).comp groupAction
  exact faithful_odd_rank_three_binary_dimension hprime.1 hprime.2.1 (by omega) hcard
    linearAction ((elementaryAutLinear_injective 2).comp hgroupInjective)

end CFSG.LargeEvenClassification.Helpers
