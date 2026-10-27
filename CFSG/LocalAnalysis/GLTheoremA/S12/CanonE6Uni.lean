module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6UniComp
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Facts
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Assembly.OpenBridges
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonInn

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
open CFSG.StandardType (GGLabelRigidInput GGLabelIso ggLabelRigidInput_holds)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem canonLabel_of_quot_heldSU (hRig : GGLabelRigidInput) {J : Type} [Group J] [Finite J]
    {labJ : GLALabel} {a m : ℕ} {E : Type} [Field E] [Finite E] (τ' : E ≃+* E)
    (hτ' : ∀ x, τ' (τ' x) = x) (ha : 2 ≤ a) (hτ'm : ∀ x, τ' x = x ^ (2 ^ m))
    (hE : Nat.card E = (2 ^ m) ^ 2) (hJ : HasLabel J (fun l : GLALabel => l = labJ))
    (hφ : Nonempty (J ⧸ Subgroup.center J ≃* heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ'))) :
    canonLabel labJ = ⟨.A, 1, m⟩ ∨ canonLabel labJ = ⟨.twA, a - 1, m⟩ := by
  obtain ⟨φ⟩ := hφ
  obtain ⟨hlab, hs, hhas⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hJ
  haveI := hs
  have hm : 1 ≤ m := by
    by_contra hm0
    have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
    rw [hE, show m = 0 by omega] at h2
    norm_num at h2
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · obtain rfl : a = 2 := by omega
    obtain ⟨k, _, _, hk, ⟨ψ⟩⟩ := exists_quot_heldSU_two_equiv_psl τ' hτ' hτ'm hE
    exact Or.inl (Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig J labJ 2 m k le_rfl hk hJ
      ⟨φ.trans ψ⟩)
  · by_cases h31 : a = 3 ∧ m = 1
    · obtain ⟨rfl, rfl⟩ := h31
      exfalso
      haveI := isSolvable_quot_heldSU_three_two τ' hτ' (fun x => by simpa using hτ'm x)
        (by simpa using hE)
      exact not_isSolvable_quot_center
        (solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
    · have ham : (a, 2 ^ m) ≠ (3, 2) := by
        intro h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact h31 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
      obtain ⟨ψ⟩ := nonempty_quot_heldSU_equiv_statedProj uniScalar_holds τ' hτ' hτ'm hE ha3 ham
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have hiso : GGLabelIso labJ ⟨.twA, b, m⟩ :=
        hRig labJ ⟨.twA, b, m⟩ (J ⧸ Subgroup.center J) hlab
          (largeEvenInLambda2_twA hm (by omega) fun hb => by omega) hhas
          (ggHasLabel_twA hE (φ.trans ψ))
      refine Or.inr ?_
      rw [Y10GInnLin.canonLabel_eq_of_ggLabelIso hiso, Nat.add_sub_cancel]
      rfl

theorem canonLabel_of_component_unitary (hRig : GGLabelRigidInput) {Γ : Type} [Group Γ] [Finite Γ]
    {L K : Subgroup Γ} {y : Γ} {labL : GLALabel} (hy : y ∈ Subgroup.normalizer (L : Set Γ))
    (hy5 : y ^ 5 = 1) (htag : labL.tag = .twA) (hn : labL.n = 2) (hM : MarkedInnDiag L y labL)
    (hK : IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set Γ))) {lab : GLALabel}
    (hlab : LabelOf K lab) :
    (∃ m, canonLabel lab = ⟨.A, 1, m⟩) ∨ (∃ r m, canonLabel lab = ⟨.twA, r, m⟩) ∨
      (∃ r e, canonLabel lab = ⟨.A, r, 4 * e⟩) := by
  obtain ⟨hcen, hin, hpow, hKb, hlb⟩ :=
    marked_bridge hy hy5 hM hK ((labelOf_iff_hasLabel K lab).1 hlab)
  obtain ⟨F, hF, hFf, d, τ, hτ, hτq, hcard, hd3, hd3n, A, u, e, hA, hαu, hgraph⟩ :=
    innDiag_unitary_data hcen (Or.inl htag) hin
  have h2 : (2 : F) = 0 := two_eq_zero_of_card hcard
  have hMEq : MulAut.congr e (centerQuotAut ↥L (conjAut L y hy)) = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpowu : u ^ 5 = 1 := by
    rw [← hMEq, ← map_pow, hpow, map_one]
  set Kb := (K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))
  have hJ' : IsComponentOf (Kb.map e.toMonoidHom) (fixSubgroup u) := by
    rw [← hMEq, ← fixSubgroup_map_congr]
    refine CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map _ (fun g hg => ?_) hKb
    rw [show g = 1 from e.injective (by rw [MulEquiv.coe_toMonoidHom] at hg; rw [hg, map_one])]
    exact one_mem _
  have hlabJ' : HasLabel ↥(Kb.map e.toMonoidHom) (fun l : GLALabel => l = lab) :=
    hasLabel_transport e hlb
  have hdQ : (d, 2 ^ labL.n) ≠ (3, 2) := by
    intro h
    obtain ⟨hd, hQ⟩ := Prod.mk.inj h
    have h2n : 2 ≤ labL.n := hd3n hd
    have : 2 ^ 2 ≤ 2 ^ labL.n := Nat.pow_le_pow_right (by norm_num) h2n
    omega
  rcases component_psu_fixed uniScalar_holds hτ hτq hcard h2 (by omega) hdQ A hA Nat.prime_five
      (by norm_num) u hgraph hpowu _ hJ' with
    ⟨a, dd, E, hE, hEf, τ', hτ', ha2, hτ'Q, hcardE, ⟨φ⟩⟩ |
    ⟨b, ee, E, hE, hEf, hb2, hcardE, ⟨φ⟩⟩
  · have hτ'm : ∀ x : E, τ' x = x ^ 2 ^ (labL.n * dd) := by
      intro x
      rw [pow_mul]
      exact hτ'Q x
    have hcardm : Nat.card E = (2 ^ (labL.n * dd)) ^ 2 := by
      rw [pow_mul]
      exact hcardE
    rcases canonLabel_of_quot_heldSU hRig τ' hτ' ha2 hτ'm hcardm hlabJ' ⟨φ⟩ with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr (Or.inl ⟨_, _, h⟩)
  · have hcardm : Nat.card E = 2 ^ (labL.n * (2 * ee)) := by
      rw [pow_mul]
      exact hcardE
    have hcanon := Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig _ lab b (labL.n * (2 * ee)) E
      hb2 hcardm hlabJ' ⟨φ⟩
    refine Or.inr (Or.inr ⟨b - 1, ee, ?_⟩)
    rw [hcanon, hn]
    congr 1
    ring

theorem unitaryNo5_of_ggLabelRigidInput (hRig : GGLabelRigidInput) : UnitaryNo5 := by
  intro Γ _ _ L K y labL hy hy5 _ htag hn hM hK
  constructor
  · intro h
    rcases canonLabel_of_component_unitary hRig hy hy5 htag hn hM hK h with
      ⟨m, hm⟩ | ⟨r, m, hm⟩ | ⟨r, e, hm⟩ <;> simp [canonLabel] at hm
  · intro h
    rcases canonLabel_of_component_unitary hRig hy hy5 htag hn hM hK h with
      ⟨m, hm⟩ | ⟨r, m, hm⟩ | ⟨r, e, hm⟩
    · simp [canonLabel] at hm
    · simp [canonLabel] at hm
    · have hm' := congrArg (fun l : GLALabel => l.n) hm
      simp only [canonLabel] at hm'
      omega

section Certificates


theorem unitaryNo5_holds : UnitaryNo5 :=
  unitaryNo5_of_ggLabelRigidInput ggLabelRigidInput_holds

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.CanonInn

end
