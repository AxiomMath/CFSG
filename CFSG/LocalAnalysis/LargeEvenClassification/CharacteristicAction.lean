module

public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniKernel
public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniElementary

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

@[expose] def coreFrattiniAction (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient]
    (prime : ℕ) : Ambient →* MulAut ((pCore prime Ambient) ⧸ frattini (pCore prime Ambient)) := by
  let : (pCore prime Ambient).Normal := pCore_normal Ambient prime
  exact (frattiniAutAction (pCore prime Ambient)).comp MulAut.conjNormal

theorem conjNormal_ker_le_core {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hselfCentralizing : Subgroup.centralizer (pCore prime Ambient : Set Ambient) ≤
      pCore prime Ambient) :
    let _ : (pCore prime Ambient).Normal := pCore_normal Ambient prime
    (MulAut.conjNormal (H := pCore prime Ambient)).ker ≤ pCore prime Ambient := by
  dsimp only
  let : (pCore prime Ambient).Normal := pCore_normal Ambient prime
  intro element helement
  apply hselfCentralizing
  apply Subgroup.mem_centralizer_iff.mpr
  intro coreElement hcoreElement
  have hfixed := congrArg (fun automorphism : MulAut (pCore prime Ambient) =>
    automorphism ⟨coreElement, hcoreElement⟩) helement
  have hambient := congrArg (fun fixedElement : pCore prime Ambient => (fixedElement : Ambient)) hfixed
  change element * coreElement * element⁻¹ = coreElement at hambient
  exact (mul_inv_eq_iff_eq_mul.mp hambient).symm

theorem coreFrattiniAction_ker_isPGroup {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime)
    (hselfCentralizing : Subgroup.centralizer (pCore prime Ambient : Set Ambient) ≤
      pCore prime Ambient) : IsPGroup prime (coreFrattiniAction Ambient prime).ker := by
  let : (pCore prime Ambient).Normal := pCore_normal Ambient prime
  let conjugation : Ambient →* MulAut (pCore prime Ambient) := MulAut.conjNormal
  have hconjugationKernel : IsPGroup prime conjugation.ker :=
    (pCore_isPGroup Ambient prime).to_le (conjNormal_ker_le_core hselfCentralizing)
  have hfrattiniKernel := frattiniAutAction_isPGroup_ker (pCore prime Ambient) hprime
    (pCore_isPGroup Ambient prime)
  exact hfrattiniKernel.comap_of_ker_isPGroup conjugation hconjugationKernel

theorem core_le_coreFrattiniAction_ker {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) :
    pCore prime Ambient ≤ (coreFrattiniAction Ambient prime).ker := by
  let : (pCore prime Ambient).Normal := pCore_normal Ambient prime
  intro element helement
  let coreElement : pCore prime Ambient := ⟨element, helement⟩
  change (frattiniAutAction (pCore prime Ambient)) (MulAut.conjNormal element) = 1
  change (frattiniAutAction (pCore prime Ambient)) (MulAut.conjNormal (coreElement : Ambient)) = 1
  rw [MulAut.conjNormal_val]
  apply MulEquiv.ext
  intro coset
  induction coset using QuotientGroup.induction_on with
  | H representative =>
    change ((MulAut.conj coreElement) representative :
      (pCore prime Ambient) ⧸ frattini (pCore prime Ambient)) =
        (representative : (pCore prime Ambient) ⧸ frattini (pCore prime Ambient))
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [MulAut.conj_apply, div_eq_mul_inv] using
      pGroup_commutator_mem_frattini hprime (pCore_isPGroup Ambient prime)
        coreElement representative

theorem coreFrattiniAction_ker_eq_core {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime)
    (hselfCentralizing : Subgroup.centralizer (pCore prime Ambient : Set Ambient) ≤
      pCore prime Ambient) : (coreFrattiniAction Ambient prime).ker = pCore prime Ambient := by
  apply le_antisymm
  · exact normal_pSubgroup_le_pCore _ inferInstance
      (coreFrattiniAction_ker_isPGroup hprime hselfCentralizing)
  · exact core_le_coreFrattiniAction_ker hprime

theorem core_quotient_embeds_frattini_aut {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime)
    (hselfCentralizing : Subgroup.centralizer (pCore prime Ambient : Set Ambient) ≤
      pCore prime Ambient) :
    let _ : (pCore prime Ambient).Normal := pCore_normal Ambient prime
    ∃ embedding : (Ambient ⧸ pCore prime Ambient) →*
        MulAut ((pCore prime Ambient) ⧸ frattini (pCore prime Ambient)),
      Function.Injective embedding := by
  dsimp only
  let : (pCore prime Ambient).Normal := pCore_normal Ambient prime
  let action := coreFrattiniAction Ambient prime
  have hkernel : action.ker = pCore prime Ambient :=
    coreFrattiniAction_ker_eq_core hprime hselfCentralizing
  let equivalence := QuotientGroup.quotientMulEquivOfEq hkernel.symm
  exact ⟨(QuotientGroup.kerLift action).comp equivalence.toMonoidHom,
    (QuotientGroup.kerLift_injective action).comp equivalence.injective⟩

theorem charTwo_local_core_selfCentralizing {Ambient : Type groupUniverse} [Group Ambient]
    (hchar : IsCharTwoType Ambient) (Local : Subgroup Ambient) (hlocal : IsTwoLocal Local) :
    Subgroup.centralizer (pCore 2 Local : Set Local) ≤ pCore 2 Local := by
  intro element helement
  have hambient : (element : Ambient) ∈ Subgroup.centralizer (pCoreOf 2 Local : Set Ambient) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro coreElement hcoreElement
    obtain ⟨corePreimage, hcorePreimage, hpreimage⟩ := hcoreElement
    rw [← hpreimage]
    exact congrArg (fun localElement : Local => (localElement : Ambient))
      (Subgroup.mem_centralizer_iff.mp helement corePreimage hcorePreimage)
  have hcoreOf : (element : Ambient) ∈ pCoreOf 2 Local :=
    hchar Local hlocal ⟨element.property, hambient⟩
  have hcomap : element ∈ (pCoreOf 2 Local).subgroupOf Local := hcoreOf
  have hidentity : (pCoreOf 2 Local).subgroupOf Local = pCore 2 Local :=
    Subgroup.comap_map_eq_self_of_injective Local.subtype_injective _
  exact hidentity ▸ hcomap

theorem charTwo_local_coreFrattiniAction_ker {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hchar : IsCharTwoType Ambient) (Local : Subgroup Ambient)
    (hlocal : IsTwoLocal Local) : (coreFrattiniAction Local 2).ker = pCore 2 Local := by
  exact coreFrattiniAction_ker_eq_core Nat.prime_two
    (charTwo_local_core_selfCentralizing hchar Local hlocal)

theorem charTwo_local_quotient_embeds_frattini_aut {Ambient : Type groupUniverse}
    [Group Ambient] [Finite Ambient] (hchar : IsCharTwoType Ambient)
    (Local : Subgroup Ambient) (hlocal : IsTwoLocal Local) :
    let _ : (pCore 2 Local).Normal := pCore_normal Local 2
    ∃ embedding : (Local ⧸ pCore 2 Local) →*
        MulAut ((pCore 2 Local) ⧸ frattini (pCore 2 Local)),
      Function.Injective embedding := by
  exact core_quotient_embeds_frattini_aut Nat.prime_two
    (charTwo_local_core_selfCentralizing hchar Local hlocal)

end CFSG.LargeEvenClassification.Helpers
