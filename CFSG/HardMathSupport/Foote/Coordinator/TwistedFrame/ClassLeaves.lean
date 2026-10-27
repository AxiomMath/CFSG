module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Closing
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Assembly
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.LangLevi
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCard
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCyclic
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Normalizer
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ThirdLine
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8Ten

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
open scoped Matrix

set_option linter.unusedSectionVars false


theorem TwClass.w_theta (c : TwClass) : c.w • highRoot c.tag = highRoot c.tag := by
  cases c
  · change (coxeterSystem Tag.F4).wordProd TwClass.wordF4 • highRoot Tag.F4 = highRoot Tag.F4
    rw [wordProd_smul_eq_wordMat_mulVec]
    decide +kernel
  · change (coxeterSystem Tag.E6).wordProd TwClass.wordE6 • highRoot Tag.E6 = highRoot Tag.E6
    rw [wordProd_smul_eq_wordMat_mulVec]
    decide +kernel
  · change (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • highRoot Tag.E8 = highRoot Tag.E8
    rw [wordProd_smul_eq_wordMat_mulVec]
    decide +kernel
  · change (coxeterSystem Tag.E8).wordProd TwClass.wordE8Twelve • highRoot Tag.E8 =
      highRoot Tag.E8
    rw [wordProd_smul_eq_wordMat_mulVec]
    decide +kernel


structure TwClassLeaves (c : TwClass) : Prop where
  lang : ∀ (K : Type) [Field K] [Finite K], Nonempty (LangLevi c.tag K c.w)
  basic : ∀ (K : Type) [Field K] [Finite K], c.minQ ≤ Nat.card K →
    ∀ D : LangLevi c.tag K c.w, TwBasic (c.X₁ D) (c.X₂ D)
  closing : ∀ (K : Type) [Field K] [Finite K], c.minQ ≤ Nat.card K →
    ∀ D : LangLevi c.tag K c.w, TwFrameClosing c.tag K (c.X₁ D ⊔ c.X₂ D)
  normalizer : ∀ (K : Type) [Field K] [Finite K], c.minQ ≤ Nat.card K →
    ∀ D : LangLevi c.tag K c.w, TwFrameNormalizerSolvable c.tag K (c.X₁ D ⊔ c.X₂ D)
  planeData : ∀ (K : Type) [Field K] [Finite K], c.minQ ≤ Nat.card K →
    ∀ D : LangLevi c.tag K c.w, ∀ p : ℕ, p.Prime → 5 ≤ p →
      orderOf ((Nat.card K : ℕ) : ZMod p) = c.e → TwFramePlaneData c.tag K (c.X₁ D) (c.X₂ D) p
  third : ∀ (K : Type) [Field K] [Finite K], c.minQ ≤ Nat.card K →
    ∀ p : ℕ, p.Prime → 5 ≤ p → orderOf ((Nat.card K : ℕ) : ZMod p) = c.e →
      TwThirdLine c.tag K p

theorem twClassLeaves_of (c : TwClass)
    (hclosing : ∀ (K : Type) [Field K] [Finite K], c.minQ ≤ Nat.card K →
      ∀ D : LangLevi c.tag K c.w, TwFrameClosing c.tag K (c.X₁ D ⊔ c.X₂ D))
    (hnorm : ∀ (K : Type) [Field K] [Finite K], c.minQ ≤ Nat.card K →
      ∀ D : LangLevi c.tag K c.w, TwFrameNormalizerSolvable c.tag K (c.X₁ D ⊔ c.X₂ D))
    (hcyc : ∀ (K : Type) [Field K] [Finite K], c.minQ ≤ Nat.card K →
      ∀ D : LangLevi c.tag K c.w, ∀ {p : ℕ}, p.Prime → 5 ≤ p →
      orderOf ((Nat.card K : ℕ) : ZMod p) = c.e →
      (∀ g : ↥(c.X₁ D), orderOf g = p →
        IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(c.X₁ D)))) ∧
      (∀ g : ↥(c.X₂ D), orderOf g = p →
        IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(c.X₂ D))))) :
    TwClassLeaves c where
  lang K _ _ := exists_langLevi c.tag K c.w (TwClass.w_theta c)
  basic K _ _ hK D := twBasic c K hK D
  closing := hclosing
  normalizer := hnorm
  planeData := by
    intro K _ _ hK D p hp hp5 hord
    have h1 := twPlaneCard c K hK D hp hp5 hord
    have h2 := hcyc K hK D hp hp5 hord
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  third K _ _ hK p hp hp5 hord := twThirdLine c K hK hp hp5 hord

theorem twClassLeaves_f4Six : TwClassLeaves TwClass.f4Six :=
  twClassLeaves_of TwClass.f4Six (fun K _ _ hK D => twClosing_f4Six K hK D)
    (fun K _ _ hK D => twNormalizer_f4Six K hK D)
    (fun K _ _ hK D _ hp hp5 hord => twPlaneCyclic_f4Six K hK D hp hp5 hord)

section E6Sc


theorem twClassLeaves_e6Six : TwClassLeaves TwClass.e6Six :=
  twClassLeaves_of TwClass.e6Six (fun K _ _ hK D => twClosing_e6Six K hK D)
    (fun K _ _ hK D => twNormalizer_e6Six K hK D)
    (fun K _ _ hK D _ hp hp5 hord => twPlaneCyclic_e6Six K hK D hp hp5 hord)

end E6Sc

section E8Ten


theorem twClassLeaves_e8Ten : TwClassLeaves TwClass.e8Ten :=
  twClassLeaves_of TwClass.e8Ten (fun K _ _ _ D => twClosing_e8Ten K D)
    (fun K _ _ hK D => twNormalizer_e8Ten K hK D)
    (fun K _ _ hK D _ hp hp5 hord => twPlaneCyclic_e8Ten K hK D hp hp5 hord)

end E8Ten

theorem twClassLeaves_e8Twelve : TwClassLeaves TwClass.e8Twelve :=
  twClassLeaves_of TwClass.e8Twelve (fun K _ _ _ D => twClosing_e8Twelve K D)
    (fun K _ _ hK D => twNormalizer_e8Twelve K hK D)
    (fun K _ _ hK D _ hp hp5 hord => twPlaneCyclic_e8Twelve K hK D hp hp5 hord)

section Generic


theorem twClassLeaves (c : TwClass) : TwClassLeaves c := by
  cases c
  · exact twClassLeaves_f4Six
  · exact twClassLeaves_e6Six
  · exact twClassLeaves_e8Ten
  · exact twClassLeaves_e8Twelve

end Generic

theorem closure_centralizers_eq_top_of_class (c : TwClass) (h : TwClassLeaves c) (K : Type)
    [Field K] [Finite K] (hK : c.minQ ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = c.e) (E : Subgroup ↥(adjointGroup c.tag K))
    (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : ↥(adjointGroup c.tag K) | ∃ x ∈ E, x ≠ 1 ∧ Commute k x} = ⊤ := by
  obtain ⟨D⟩ := h.lang K
  have hb := h.basic K hK D
  haveI : Fact p.Prime := ⟨hp⟩
  exact closure_centralizers_eq_top_of_subgroups hb.le₁ hb.le₂ hb.comm (h.closing K hK D)
    (h.normalizer K hK D) (h.planeData K hK D p hp hp5 hord) (h.third K hK p hp hp5 hord) E hEp hEc

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
