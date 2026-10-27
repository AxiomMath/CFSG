module

public import CFSG.ClassicalInvolution.Asc77.ModOApi

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def s26ConjOn (X : Subgroup G) (b : G) (hb : conjSub b X = X) : ↥X ≃* ↥X :=
  ((MulAut.conj b).subgroupMap X).trans (MulEquiv.subgroupCongr hb)

theorem coe_s26ConjOn (X : Subgroup G) (b : G) (hb : conjSub b X = X) (x : ↥X) :
    ((s26ConjOn X b hb x : ↥X) : G) = b * x * b⁻¹ := rfl

@[expose] noncomputable def s26Ind (X : Subgroup G) (b : G) (hb : conjSub b X = X) :
    MulAut (↥X ⧸ classicalInvolutionOddCore ↥X) :=
  QuotientGroup.congr (classicalInvolutionOddCore ↥X) (classicalInvolutionOddCore ↥X)
    (s26ConjOn X b hb) (CFSG.ComponentClassification.OddCore.equiv_invariant (s26ConjOn X b hb))

theorem s26Ind_mk (X : Subgroup G) (b : G) (hb : conjSub b X = X) (x : ↥X) :
    s26Ind X b hb (x : ↥X ⧸ classicalInvolutionOddCore ↥X) =
      ((s26ConjOn X b hb x : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) :=
  QuotientGroup.congr_mk _ _ _ _ x

@[expose] noncomputable def s26Act (X : Subgroup G) :
    ↥(Subgroup.normalizer (X : Set G)) →* MulAut (↥X ⧸ classicalInvolutionOddCore ↥X) where
  toFun b := s26Ind X b.1 (conjSub_eq_of_mem_normalizer b.2)
  map_one' := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H x =>
      rw [s26Ind_mk]
      show ((s26ConjOn X 1 _ x : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) = _
      congr 1
      apply Subtype.ext
      simp [coe_s26ConjOn]
  map_mul' b c := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H x =>
      show s26Ind X (b.1 * c.1) _ (x : ↥X ⧸ classicalInvolutionOddCore ↥X) =
        s26Ind X b.1 _ (s26Ind X c.1 _ (x : ↥X ⧸ classicalInvolutionOddCore ↥X))
      rw [s26Ind_mk, s26Ind_mk, s26Ind_mk]
      congr 1
      apply Subtype.ext
      simp only [coe_s26ConjOn]
      group

theorem s26Act_mk (X : Subgroup G) (b : ↥(Subgroup.normalizer (X : Set G))) (x x' : ↥X)
    (h : (x' : G) = b * x * (b : G)⁻¹) :
    s26Act X b (x : ↥X ⧸ classicalInvolutionOddCore ↥X) =
      (x' : ↥X ⧸ classicalInvolutionOddCore ↥X) := by
  show s26Ind X b.1 _ (x : ↥X ⧸ classicalInvolutionOddCore ↥X) = _
  rw [s26Ind_mk]
  congr 1
  apply Subtype.ext
  rw [coe_s26ConjOn, h]

theorem s26Act_eq_conj (X : Subgroup G) (z : ↥X) :
    s26Act X ⟨(z : G), Subgroup.le_normalizer z.2⟩ =
      MulAut.conj (z : ↥X ⧸ classicalInvolutionOddCore ↥X) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H x =>
    rw [s26Act_mk X _ x (z * x * z⁻¹) (by simp)]
    simp [MulAut.conj_apply]

theorem s26_comm_mem_oddCore_of_act_eq_one (X : Subgroup G)
    (b : ↥(Subgroup.normalizer (X : Set G))) (h : s26Act X b = 1) {x : G} (hx : x ∈ X) :
    ⁅(b : G), x⁆ ∈ oddCoreOf X := by
  have hxX : ((b : G) * x * (b : G)⁻¹) ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp b.2 x).mp hx
    exact this
  have h1 := s26Act_mk X b ⟨x, hx⟩ ⟨(b : G) * x * (b : G)⁻¹, hxX⟩ rfl
  rw [h, MulAut.one_apply] at h1
  have h2 : (⟨(b : G) * x * (b : G)⁻¹, hxX⟩ : ↥X) / ⟨x, hx⟩ ∈ classicalInvolutionOddCore ↥X :=
    (QuotientGroup.eq_iff_div_mem).mp h1.symm
  refine mem_oddCoreOf_iff.mpr ⟨?_, ?_⟩
  · exact X.mul_mem hxX (X.inv_mem hx)
  · convert h2 using 1
    apply Subtype.ext
    simp [commutatorElement_def, div_eq_mul_inv]

end CFSG.ClassicalInvolution.Asc77
