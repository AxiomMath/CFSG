module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Spor
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporNoComp
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431Z

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.I271 (CentShape CentShapeRk)

@[expose] def NoU42Comp (p : ℕ) {Q : Type} [Group Q] (k : Q) : Prop :=
  ∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I →
    Nat.card (PSimple p I) ≠ 25920

theorem card_eq_of_u4two {T : Type} [Group T] (hU : catalogIs T S9.isU4two) :
    Nat.card T = 25920 := by
  obtain ⟨f⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_u4two hU
  rw [Nat.card_congr f.toEquiv]
  exact CFSG.LieType.Multipliers.U42.card_PSp43

theorem noU42Comp_of_mulEquiv {p : ℕ} (hp : p.Prime) {Q Q' : Type} [Group Q] [Group Q'] [Finite Q']
    (σ : Q ≃* Q') {k : Q} (h : NoU42Comp p k) : NoU42Comp p (σ k) := by
  intro I hI hc
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ.symm hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv,
    MulEquiv.symm_apply_apply] at hI'
  have e := CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
    (I.equivMapOfInjective σ.symm.toMonoidHom σ.symm.injective)
  exact h _ hI' ((Nat.card_congr e.toEquiv).symm.trans hc)

theorem row_of_model {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (h : ∀ k : Q, orderOf k = 3 → NoU42Comp 3 k) : I1431SporRow s := by
  intro S _ _ ⟨e⟩ β hβ hβ1 J hJ hU
  let φ : S ≃* Q := e.trans b.symm
  haveI : IsSimpleGroup S := (MulEquiv.isSimpleGroup_congr φ).2 inferInstance
  have hncS : ∃ a c : S, a * c ≠ c * a := by
    obtain ⟨a, c, hac⟩ := hnc
    refine ⟨φ.symm a, φ.symm c, fun h' => hac ?_⟩
    have := congrArg φ h'
    simpa using this
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h' | h'
    · exact h'
    · obtain ⟨a, c, hac⟩ := hncS
      exact absurd ((Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top c)) a) hac
  have hout := hOut S inferInstance hncS s ⟨e⟩
  obtain ⟨x, rfl, hxp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow Nat.prime_three (by norm_num) hcen hout β hβ
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hβ1 (map_one MulAut.conj)
  have hxo : orderOf x = 3 := orderOf_eq_prime hxp hx1
  rw [KDSpor.fixSubgroup_conj_eq] at hJ
  have hk : orderOf (φ x) = 3 := by rw [MulEquiv.orderOf_eq, hxo]
  have := noU42Comp_of_mulEquiv Nat.prime_three φ.symm (h _ hk)
  rw [MulEquiv.symm_apply_apply] at this
  exact this J hJ (card_eq_of_u4two hU)

theorem row_of_centShape {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    {Good : ∀ (T : Type) [Group T], Prop} (h : CentShape 3 Good Q)
    (hG : ∀ (T : Type) [Group T], Good T → Nat.card T ≠ 25920) : I1431SporRow s := by
  refine row_of_model hOut b hnc fun k hk => ?_
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; norm_num at hk
  intro I hI
  rcases h k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k) with hc | ⟨J, -, huniq, hg⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained Nat.prime_three hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

theorem row_of_centShapeRk {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    {Good : ∀ (T : Type) [Group T], Prop} {Rk : ∀ (T : Type) [Group T], Prop}
    (hC : CFSG.HardMathSupport.Dickson.I271.CentShapeRk 3 Good Rk Q)
    (hG : ∀ (T : Type) [Group T], Good T → Nat.card T ≠ 25920) : I1431SporRow s :=
  row_of_centShape hOut b hnc (CentShape.of_centShapeRk hC) hG

theorem card_alt_six_eq : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have hperm : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h : 2 * Nat.card (alternatingGroup (Fin 6)) = 720 := by
    rw [two_mul_nat_card_alternatingGroup, hperm]
  omega

end CFSG.LocalAnalysis.GLTheoremA.I1431Z

end
