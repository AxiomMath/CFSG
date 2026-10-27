module

public import CFSG.LocalAnalysis.LargeEvenClassification.Entry
public import CFSG.LocalAnalysis.LargeEvenClassification.SemisimpleRank

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem charTwo_local_elementary_frattini_rank {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime rank : ℕ} (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType Ambient) (Local Elementary : Subgroup Ambient)
    (hlocal : IsTwoLocal Local) (hle : Elementary ≤ Local)
    (helementary : IsElemAbelian prime Elementary) (hcard : Nat.card Elementary = prime ^ rank) :
    let _ : CommGroup ((pCore 2 Local) ⧸ frattini (pCore 2 Local)) :=
      pGroupFrattiniCommGroup Nat.prime_two (pCore_isPGroup Local 2)
    ∃ module : Module (ZMod 2) (Additive ((pCore 2 Local) ⧸ frattini (pCore 2 Local))),
      let _ := module
      2 * rank ≤ Module.finrank (ZMod 2) (Additive ((pCore 2 Local) ⧸ frattini (pCore 2 Local))) := by
  dsimp only
  let : CommGroup ((pCore 2 Local) ⧸ frattini (pCore 2 Local)) :=
    pGroupFrattiniCommGroup Nat.prime_two (pCore_isPGroup Local 2)
  let module : Module (ZMod 2) (Additive ((pCore 2 Local) ⧸ frattini (pCore 2 Local))) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two (pCore_isPGroup Local 2))
  refine ⟨module, ?_⟩
  let : CommGroup Elementary :=
    { (inferInstance : Group Elementary) with mul_comm := @mul_comm' Elementary _ helementary.1 }
  let : (pCore 2 Local).Normal := pCore_normal Local 2
  have hcoreKernel := charTwo_local_coreFrattiniAction_ker hchar Local hlocal
  have helementaryCore : Disjoint Elementary (pCoreOf 2 Local) :=
    charTwo_odd_subgroup_disjoint_core hprime hodd Elementary Local (IsPGroup.of_card hcard)
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
  have hexponent : ∀ element : Elementary, element ^ prime = 1 := by
    intro element
    apply Subtype.ext
    exact helementary.2 element element.property
  exact faithful_elementary_binary_dimension hprime hodd hexponent hcard linearAction
    ((elementaryAutLinear_injective 2).comp hgroupInjective)

theorem large_even_local_frattini_rank (Ambient : Type groupUniverse) [Group Ambient]
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
          2 * evenRank Ambient ≤
            Module.finrank (ZMod 2) (Additive ((pCore 2 Local) ⧸ frattini (pCore 2 Local))) := by
  obtain ⟨prime, Local, Elementary, hprime, hlocal, hproper, hlocalK, hle,
    helementary, hcard, hcoreNontrivial, _, _⟩ :=
    large_even_entry_with_K Ambient hnonab hK hchar hrank
  exact ⟨prime, Local, Elementary, hprime, hlocal, hproper, hlocalK, hle, helementary,
    hcard, hcoreNontrivial, charTwo_local_elementary_frattini_rank hprime.1 hprime.2.1
      hchar Local Elementary hlocal hle helementary hcard⟩

end CFSG.LargeEvenClassification.Helpers
