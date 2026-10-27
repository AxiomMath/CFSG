module

public import CFSG.RankThree.PartOne.KS.AllInner
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimEquiv
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.Solomon78

@[irreducible] noncomputable def JT : Subgroup ↥J := ⊤

theorem JT_eq_top : JT = ⊤ := by unfold JT; rfl

theorem mem_JT (g : ↥J) : g ∈ JT := by
  rw [JT_eq_top]; exact Subgroup.mem_top g

noncomputable def eJT : ↥J ≃* ↥JT where
  toFun g := ⟨g, mem_JT g⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

noncomputable def thJTEquiv :
    CFSG.Blueprint.NativeSporadic.Th ≃* ↥JT :=
  @MulEquiv.trans CFSG.Blueprint.NativeSporadic.Th ↥J ↥JT _ _ _ thEquivJ eJT

section


theorem th_finite : Finite J := Nat.finite_of_card_ne_zero
  (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)

theorem th_card_JT : Nat.card ↥JT = Nat.card ↥J := by
  rw [JT_eq_top, Subgroup.card_top]

theorem th_allInner :
    AllInner ↥J := by
  intro α
  have h : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J := by
    rw [CFSG.Sporadic.ThSchreier.inner_J]; exact Subgroup.mem_top α
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg.symm⟩

theorem th_center_J (hnab : ∃ a b : ↥J, a * b ≠ b * a) : Subgroup.center ↥J = ⊥ := by
  have : Finite ↥J := th_finite
  have hs : IsSimpleGroup ↥J :=
    CFSG.Sporadic.Th.Kernel.isSimpleGroup_J CFSG.Sporadic.Th.th_kernel_facts
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥J (Subgroup.toGroup J) hs
    (Subgroup.center ↥J) inferInstance with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center ↥J := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem th_center_JT (hnab : ∃ a b : ↥J, a * b ≠ b * a) : Subgroup.center ↥JT = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have : z.1 ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, mem_JT g⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h
  rw [th_center_J hnab, Subgroup.mem_bot] at this
  exact Subtype.ext this

theorem th_autModel_JT
    (hnab : ∃ a b : ↥J, a * b ≠ b * a) : AutModel JT JT :=
  CFSG.RankThree.PartOne.autModel_self_of_allInner (th_center_JT hnab)
    (@AllInner.of_mulEquiv ↥J ↥JT (Subgroup.toGroup J) (Subgroup.toGroup JT) eJT th_allInner)

end

end CFSG.HardMathSupport.Dickson.I271
