module

public import CFSG.ClassicalInvolution.Q3.Q3AMLYTri
public import CFSG.ClassicalInvolution.Q3.Q3AMBadShape
public import CFSG.ClassicalInvolution.Q3.Q3AMLYEdge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups commutatorElement

section Plain

variable {G : Type} [Group G] [Finite G]

theorem isUniqueInvolution_modOddIn {Y L M : Subgroup G} {w : G} (hLM : L ≤ M)
    (hw : IsUniqueInvolution M w) (hwL : w ∈ L) (hwY : w ∈ Y) :
    IsUniqueInvolution (modOddIn Y L)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hwY⟩) := by
  have hz : IsUniqueInvolution (L.subgroupOf Y) ⟨w, hwY⟩ := by
    refine ⟨Subgroup.mem_subgroupOf.mpr hwL, fun h => hw.ne_one (congrArg Subtype.val h),
      Subtype.ext hw.sq, ?_⟩
    intro y hy hy2
    rcases hw.unique (y : G) (hLM (Subgroup.mem_subgroupOf.mp hy)) (congrArg Subtype.val hy2)
      with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  exact isUniqueInvolution_map_mk_of_odd
    (odd_natCard_inf (CFSG.ComponentClassification.OddCore.odd_card ↥Y) _) hz

end Plain

section Main


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J K' : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem PspSetting.exists_layerPair [IsSimpleGroup G]
    (h : PspSetting Ω K J S R T W z t K') :
    ∃ hz : z ∈ nbrLayer Ω K z,
      ∃ J₁ J₂ : Subgroup (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)),
        J₁ ∈ layerFam Ω K z ∧ J₂ ∈ layerFam Ω K z ∧ J₁ ≠ J₂ ∧
          (∀ x ∈ J₁, ∀ y ∈ J₂, x * y = y * x) ∧
          ∃ a b, IsUniqueInvolution J₁ a ∧ IsUniqueInvolution J₂ b ∧
            a * b = QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hz⟩ ∧
            QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hz⟩ ≠ 1 ∧
            ∀ y, y * QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hz⟩ =
              QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hz⟩ * y := by
  classical
  have hbad := h.bad
  have hstd := hbad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hint := h.intrinsic
  have hJ : J ∈ omegaNbr Ω K := hstd.hJ
  have hz : IsUniqueInvolution K z := hstd.hz
  have ht : IsUniqueInvolution J t := hstd.ht
  have huK' : IsUniqueInvolution K' (z * t) := h.uniq_K'
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hJ ht
  have htE : t ∈ exactCore3 z J :=
    ⟨ht.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  have hztE : z * t ∈ exactCore3 z K' :=
    ⟨huK'.mem, Subgroup.mem_centralizer_singleton_iff.mpr (by rw [mul_assoc, ← hzt])⟩
  have htY : t ∈ nbrLayer Ω K z := exactCore3_le_nbrLayer hJ htE
  have hztY : z * t ∈ nbrLayer Ω K z := exactCore3_le_nbrLayer h.nbrK hztE
  have hzs : t * (z * t) = z := by
    calc t * (z * t) = (t * z) * t := (mul_assoc _ _ _).symm
      _ = (z * t) * t := by rw [← hzt]
      _ = z * (t * t) := mul_assoc _ _ _
      _ = z := by rw [ht.sq, mul_one]
  have hzY : z ∈ nbrLayer Ω K z := by
    have := (nbrLayer Ω K z).mul_mem htY hztY
    rwa [hzs] at this
  have hne : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hzY⟩ ≠ 1 :=
    Q3Y.mk_ne_one_of_involution (nbrLayer Ω K z) hzY hz.sq hz.ne_one
  have ha : IsUniqueInvolution (modOddIn (nbrLayer Ω K z) (exactCore3 z J))
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩) :=
    isUniqueInvolution_modOddIn (exactCore3_le_left z J) ht htE htY
  have hb : IsUniqueInvolution (modOddIn (nbrLayer Ω K z) (exactCore3 z K'))
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z * t, hztY⟩) :=
    isUniqueInvolution_modOddIn (exactCore3_le_left z K') huK' hztE hztY
  have hab : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩ *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z * t, hztY⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hzY⟩ := by
    rw [← map_mul]
    exact congrArg _ (Subtype.ext hzs)
  refine ⟨hzY, modOddIn (nbrLayer Ω K z) (exactCore3 z J),
    modOddIn (nbrLayer Ω K z) (exactCore3 z K'), modOddIn_mem_layerFam hJ,
    modOddIn_mem_layerFam h.nbrK, ?_,
    commutes_modOddIn_exactCore3_of_triangle hbad hint h.nbrK h.nbrJ, _, _, ha, hb, hab, hne, ?_⟩
  · intro hEq
    rw [← hEq] at hb
    rcases ha.unique _ hb.mem hb.sq with h1 | h1
    · exact hb.ne_one h1
    · apply hne
      rw [← hab, h1]
      exact ha.sq
  · intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hc := commutator_mem_oddCoreOf_nbrLayer' hbad hint hstd.stand.mem hz hz.mem g.2
    exact ((mk_comm_eq_iff hzY g.2).mpr (by rwa [commutatorElement_def] at hc)).symm

end Main

end CFSG.ClassicalInvolution.Q3.Q3AM
