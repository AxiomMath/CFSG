module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcCent
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionPerfect
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.EntryLemma
public import CFSG.Adapters.CatalogueFieldBridges.Exceptional
public import CFSG.LieType.Chevalley.OppositeNoncommutativity
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionB
public import CFSG.Quasithin.H13.J4Order
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KLR.Final
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate17002
public import Certificates.Certificate17951

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.GLTheoremA.T173X
  CFSG.HardMathSupport.Solomon.Coordinator

variable {τ : Tag} {F : Type} [Field F]

theorem perfectInLayer_conj_of_bridge
    [Finite F] {c : TauCeti.PrimePower → TauCeti.LieTypeIndex} {q : TauCeti.PrimePower}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (hv : (c q).Valid)
    (hq : Nat.card F = q.card) (hchar : (c q).characteristic = 2)
    (hs : IsSimpleGroup ↥(adjointGroup τ F))
    (hnc : ∃ x y : ↥(adjointGroup τ F), x * y ≠ y * x)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : ↥(adjointGroup τ F)} (hd1 : d ≠ 1) (hdp : d ^ p = 1) :
    PerfectInLayer (MulAut.conj d) := by
  obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_adjointGroup_catEquiv
    (τ := τ) (c := c) hB hv hq
  refine CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
    ↥(adjointGroup τ F) hs hnc ⟨c q, hv⟩ ⟨e⟩ p hp hp2 ?_ (MulAut.conj d) ?_ ?_
  · rw [hchar]; exact hp2
  · rw [← MonoidHom.map_pow, hdp, MonoidHom.map_one]
  · intro hconj
    have hcen : d ∈ Subgroup.center ↥(adjointGroup τ F) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 : MulAut.conj d x = x := by rw [hconj]; rfl
      rw [MulAut.conj_apply] at h1
      rw [show d * x = (d * x * d⁻¹) * d from by group, h1]
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hcen
    exact hd1 hcen

theorem perfectInLayer_conj_exc
    [Finite F] [CharP F 2] {n p : ℕ} (hn : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {d : ↥(adjointGroup τ F)} (hd1 : d ≠ 1) (hdp : d ^ p = 1)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    PerfectInLayer (MulAut.conj d) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, pow_zero] at hn
      have hF2 : 1 < Nat.card F := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      omega
    · exact h
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, hnpos⟩
  have hqcard : Nat.card F = q.card := by rw [hn]; simp [q, TauCeti.PrimePower.card_def]
  have hnc : ∃ x y : ↥(adjointGroup τ F), x * y ≠ y * x :=
    (CFSG.LieType.Chevalley.opposite_simple_root_noncommutativity τ F).2.2.1
  have key : ∀ (c : TauCeti.PrimePower → TauCeti.LieTypeIndex),
      CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c → (c q).Valid →
      (c q).characteristic = 2 → IsSimpleGroup ↥(adjointGroup τ F) →
      PerfectInLayer (MulAut.conj d) :=
    fun c hB hv hchar hs => perfectInLayer_conj_of_bridge hB hv hqcard hchar hs hnc hp hp2
      hd1 hdp
  rcases hτ with rfl | rfl | rfl | rfl
  · exact key _ CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 (by simp) (by simp [q])
      (CFSG.LieType.SeitzGeneration.ExcOuterLeOne.isSimpleGroup_adjointGroup_of_type (by simp))
  · exact key _ CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 (by simp) (by simp [q])
      (CFSG.LieType.SeitzGeneration.ExcOuterLeOne.isSimpleGroup_adjointGroup_of_type (by simp))
  · exact key _ CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 (by simp) (by simp [q])
      (CFSG.LieType.SeitzGeneration.ExcOuterLeOne.isSimpleGroup_adjointGroup_of_type (by simp))
  · exact key _ CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 (by simp) (by simp [q])
      (CFSG.LieType.SeitzGeneration.ExcOuterLeOne.isSimpleGroup_adjointGroup_of_type (by simp))

theorem rootSubgroup_le_stdLayer_of_perfectInLayer
    [Finite F] [CharP F 2] (hq4 : 4 ≤ Nat.card F)
    {a : Fin τ.rank → Fˣ} {d : ↥(adjointGroup τ F)}
    (hd : (d : ModGL τ F) = rootDiagUnit τ a)
    (hPI : PerfectInLayer (MulAut.conj d))
    {α : Fin τ.rank → ℤ} (hα : α ∈ rootCharKernel a) :
    (rootSubgroup τ F α).subgroupOf (adjointGroup τ F) ≤ stdLayer d := by
  classical
  have hαroot : IsRoot τ α := hα.1
  have hneg : -α ∈ rootCharKernel a := by
    refine ⟨IsRoot.neg hαroot, ?_⟩
    rw [show -α = (-1 : ℤ) • α from (neg_one_smul ℤ α).symm, rootChar_zsmul, zpow_neg_one,
      hα.2, inv_one]
  have hQle : rootSubgroup τ F α ⊔ rootSubgroup τ F (-α) ≤ toralCentralizer τ F a :=
    sup_le ((le_iSup₂_of_le α hα le_rfl).trans (rootSpan_rootCharKernel_le_toralCentralizer a))
      ((le_iSup₂_of_le (-α) hneg le_rfl).trans (rootSpan_rootCharKernel_le_toralCentralizer a))
  have hQadj : rootSubgroup τ F α ⊔ rootSubgroup τ F (-α) ≤ adjointGroup τ F :=
    hQle.trans inf_le_left
  have hQfix : ((rootSubgroup τ F α ⊔ rootSubgroup τ F (-α)).subgroupOf (adjointGroup τ F))
      ≤ fixSubgroup (MulAut.conj d) := by
    intro q hq
    rw [mem_fixSubgroup]
    have hqX : (q : ModGL τ F) ∈ toralCentralizer τ F a :=
      hQle (Subgroup.mem_subgroupOf.1 hq)
    have hconj := (mem_toralCentralizer.1 hqX).2
    refine Subtype.ext ?_
    show ((MulAut.conj d q : ↥(adjointGroup τ F)) : ModGL τ F) = (q : ModGL τ F)
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hd, hconj]
  have hQperf : ⁅(rootSubgroup τ F α ⊔ rootSubgroup τ F (-α)).subgroupOf (adjointGroup τ F),
      (rootSubgroup τ F α ⊔ rootSubgroup τ F (-α)).subgroupOf (adjointGroup τ F)⁆ =
      (rootSubgroup τ F α ⊔ rootSubgroup τ F (-α)).subgroupOf (adjointGroup τ F) := by
    have hperf := CFSG.SeitzReduction.E8Pilot.commutator_rootSubgroup_sup_neg
      (τ := τ) (K := F) hq4 hαroot
    have hmap1 : Subgroup.map (adjointGroup τ F).subtype
        ⁅(rootSubgroup τ F α ⊔ rootSubgroup τ F (-α)).subgroupOf (adjointGroup τ F),
          (rootSubgroup τ F α ⊔ rootSubgroup τ F (-α)).subgroupOf (adjointGroup τ F)⁆ =
        Subgroup.map (adjointGroup τ F).subtype
          ((rootSubgroup τ F α ⊔ rootSubgroup τ F (-α)).subgroupOf (adjointGroup τ F)) := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.2 hQadj, hperf]
    exact Subgroup.map_injective (adjointGroup τ F).subtype_injective hmap1
  have hQleLayer : ((rootSubgroup τ F α ⊔ rootSubgroup τ F (-α)).subgroupOf
      (adjointGroup τ F)) ≤ GLALayer (fixSubgroup (MulAut.conj d)) := hPI _ hQfix hQperf
  have hfix : fixSubgroup (MulAut.conj d) =
      Subgroup.centralizer ({d} : Set ↥(adjointGroup τ F)) := b3Lie_fixSubgroup_conj d
  rw [hfix] at hQleLayer
  exact (Subgroup.subgroupOf_mono (adjointGroup τ F) le_sup_left).trans hQleLayer

theorem rootSubgroup_le_stdLayer
    [Finite F] [CharP F 2] {n p : ℕ} (hn : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) {a : Fin τ.rank → Fˣ}
    {d : ↥(adjointGroup τ F)} (hd : (d : ModGL τ F) = rootDiagUnit τ a)
    (hstd : IsStdElt p (TableBExc.torusPow τ F p) d)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α : Fin τ.rank → ℤ} (hα : α ∈ rootCharKernel a) :
    (rootSubgroup τ F α).subgroupOf (adjointGroup τ F) ≤ stdLayer d := by
  haveI : Fintype F := Fintype.ofFinite F
  have hn_ge2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · rw [pow_zero] at hn
        have hF2 : 1 < Nat.card F := by
          rw [Nat.card_eq_fintype_card]
          exact Fintype.one_lt_card
        omega
      · rw [pow_one] at hpq
        have hp1 := Nat.le_of_dvd (by norm_num) hpq
        have := hp.two_le
        omega
    · exact h
  have hq4 : 4 ≤ Nat.card F := by
    rw [hn]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn_ge2
  exact rootSubgroup_le_stdLayer_of_perfectInLayer hq4 hd
    (perfectInLayer_conj_exc hn hp hp2 hstd.2.1 hstd.2.2.1 hτ) hα

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
