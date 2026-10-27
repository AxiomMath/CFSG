module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Descent
public import CFSG.HardMathSupport.Solomon.Proving.LBLemma27
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInnDiag
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop51Proof
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

theorem upD42Statement_of_core (h : UpD42Core) : UpD42Statement := by
  intro G _ _ X K hX hK b hbX hbN hb3 hbd J hJ hJ42
  have hKX : K ≤ X := hK.1
  have hqs : CFSG.Open.IsQuasisimple (barOf 3 K) :=
    isQuasisimple_quotient_of_glaPComponent Nat.prime_three hK
  have hcore0 : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
  have hKK : CFSG.IsKGroup ↥K :=
    CFSG.IsKGroup.of_mulEquiv (hX.subgroup (K.subgroupOf X))
      (Subgroup.subgroupOfEquivOfLe hKX).symm
  have hKb : CFSG.Open.IsKGroup (barOf 3 K) :=
    CFSG.HardMathSupport.Solomon.Proving.isKGroup_open_of_catalog (CFSG.IsKGroup.quotient hKK _)
  have hβ3 := Lemma510Ns.barAut_pow_three hbN hb3
  have hβ1 : barAut 3 K ⟨b, hbN⟩ ≠ 1 := fun h1 =>
    hbd ((Lemma54Ns.mem_centralizerQuot_iff_barAut' 3 (J := K) ⟨b, hbN⟩).2 h1)
  obtain ⟨J₁, hJ₁, rfl⟩ := Lemma510Ns.exists_comp_subgroupOf
    (inf_le_left : K ⊓ Subgroup.centralizer ({b} : Set G) ≤ K) hJ
  have hJ₂ := Lemma510Ns.comp_map_fixSub hbN hb3 hJ₁
  have hT := IsCatalogLieIso.of_mulEquiv (Lemma510Ns.liftEquiv J₁) hJ42
  exact h _ hqs hKb hcore0 (barAut 3 K ⟨b, hbN⟩) ⟨hβ3, hβ1, _, hJ₂, hT⟩

end CFSG.HardMathSupport.Dickson.Sec6

end
