module

public import CFSG.ClassicalInvolution.Q3.Q3ExcAdj
public import CFSG.ClassicalInvolution.Q3.Q3ExcAmalgam
public import CFSG.LieType.HighestRoot.CentG2Main
public import CFSG.ClassicalInvolution.Q3.Q3PlanTags

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.HighestRoot CFSG.ClassicalInvolution.ModelFacts
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem exc3_exists_conj_rootGroup_of_member_G2
    {L : Subgroup ↥(adjointGroup .G2 (GaloisField 3 1))}
    {z : ↥(adjointGroup .G2 (GaloisField 3 1))} (h : IsClassicalMember3 L z)
    (hO : classicalInvolutionOddCore L = ⊥) :
    ∃ (g : ↥(adjointGroup .G2 (GaloisField 3 1))) (γ : Fin Tag.G2.rank → ℤ), IsRoot .G2 γ ∧
      L = (rootGroup (rootOperatorFamily .G2) (GaloisField 3 1) γ ⊔
          rootGroup (rootOperatorFamily .G2) (GaloisField 3 1) (-γ)).map
          (MulAut.conj g⁻¹).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 := exc3_natCard_galoisField_three
  have hK : ringChar (GaloisField 3 1) ≠ 2 := ringChar_ne_two_of_card_eq_three hK3
  have : Finite (ModGL .G2 (GaloisField 3 1)) := finite_modGL
  obtain ⟨g, hg⟩ := isConj_iff.mp (g2_isConj_g2z hK h.orderOf_eq_two)
  set a := signTuple .G2 (GaloisField 3 1) g2l with ha_def
  have ha : ∀ i, a i = 1 ∨ a i = -1 := signTuple_eq_one_or_eq_neg_one g2l
  have hgz : ((g * z * g⁻¹ : ↥(adjointGroup .G2 (GaloisField 3 1))) : ModGL .G2 (GaloisField 3 1)) =
      rootDiagUnit .G2 a := by rw [hg]; rfl
  have hL' : IsClassicalMember3 (conjSub g L) (g * z * g⁻¹) := h.conj g
  have hO' : classicalInvolutionOddCore (conjSub g L) = ⊥ :=
    oddCore_eq_bot_of_equiv ((L.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm) hO
  have hCz := centralizer_eq_subgroupOf_toralCentralizer a (g * z * g⁻¹) hgz
  have hXC := toralCentralizer_le_adjointGroup (K := GaloisField 3 1) (τ := .G2) a
  have hL'C : conjSub g L ≤ Subgroup.centralizer
      ({g * z * g⁻¹} : Set ↥(adjointGroup .G2 (GaloisField 3 1))) :=
    isSubnormal_le hL'.subnormal
  obtain ⟨e⟩ := hL'.nonempty_equiv_sl2 hO'
  let eL : SL(2, ZMod 3) ≃* ↥((conjSub g L).map (adjointGroup .G2 (GaloisField 3 1)).subtype) :=
    e.symm.trans ((conjSub g L).equivMapOfInjective (adjointGroup .G2 (GaloisField 3 1)).subtype
      (adjointGroup .G2 (GaloisField 3 1)).subtype_injective)
  have hLX : (conjSub g L).map (adjointGroup .G2 (GaloisField 3 1)).subtype ≤
      toralCentralizer .G2 (GaloisField 3 1) a := by
    rintro _ ⟨x, hx, rfl⟩
    have := hCz ▸ hL'C hx
    exact Subgroup.mem_subgroupOf.1 this
  have hsubX : IsSubnormal ((conjSub g L).map (adjointGroup .G2 (GaloisField 3 1)).subtype)
      (toralCentralizer .G2 (GaloisField 3 1) a) := by
    have h1 := CFSG.ComponentClassification.Components.chain_map
      (adjointGroup .G2 (GaloisField 3 1)).subtype hL'.subnormal
    rwa [hCz, Subgroup.map_subgroupOf_eq_of_le hXC] at h1
  set J := rootSubgroup .G2 (GaloisField 3 1) g2e0 ⊔
    rootSubgroup .G2 (GaloisField 3 1) (-g2e0) with hJ
  set L₀ := rootSubgroup .G2 (GaloisField 3 1) g2δ ⊔
    rootSubgroup .G2 (GaloisField 3 1) (-g2δ) with hL₀
  have hS : rootSpan .G2 (GaloisField 3 1) (rootCharKernel a) = J ⊔ L₀ := g2_rootSpan_kernel hK
  have hSX : rootSpan .G2 (GaloisField 3 1) (rootCharKernel a) ≤
      toralCentralizer .G2 (GaloisField 3 1) a := rootSpan_rootCharKernel_le_toralCentralizer a
  have eLK : ↥((conjSub g L).map (adjointGroup .G2 (GaloisField 3 1)).subtype) ≃*
      SL2 (GaloisField 3 1) := eL.symm.trans (slEquivSL23 hK3).symm
  have hgen := closure_orderOf_three_eq_top_of_mulEquiv hK3 eLK
  have hLS : (conjSub g L).map (adjointGroup .G2 (GaloisField 3 1)).subtype ≤ J ⊔ L₀ := by
    rw [← hS]
    exact le_rootSpan_of_closure_eq_top hK3 hK ha hLX hgen
  have hsubS : IsSubnormal ((conjSub g L).map (adjointGroup .G2 (GaloisField 3 1)).subtype)
      (J ⊔ L₀) := by
    have h1 := isSubnormal_inf hsubX (J ⊔ L₀)
    rwa [inf_eq_left.mpr hLS, inf_eq_right.mpr (hS ▸ hSX)] at h1
  obtain ⟨-, ⟨eJ⟩, -, -⟩ := odd_arbitrary_root_pair_SL2_p_components .G2 (GaloisField 3 1) hK
    (isRoot_single .G2 g2l)
  obtain ⟨-, ⟨eL₀⟩, -, -⟩ := odd_arbitrary_root_pair_SL2_p_components .G2 (GaloisField 3 1) hK
    isRoot_g2δ
  obtain ⟨eJ3⟩ := exc3_nonempty_equiv_sl2Three hK3 eJ
  obtain ⟨eL₀3⟩ := exc3_nonempty_equiv_sl2Three hK3 eL₀
  have hcomm : ∀ x ∈ J, ∀ y ∈ L₀, x * y = y * x := fun x hx y hy => (g2_commute hK hx hy).eq
  obtain ⟨hzJ, hz2⟩ := g2_rootDiagUnit_mem_long (K := GaloisField 3 1) hK
  have hzL₀ := g2_rootDiagUnit_mem_short (K := GaloisField 3 1) hK
  have hεL : rootDiagUnit .G2 a ∈ (conjSub g L).map (adjointGroup .G2 (GaloisField 3 1)).subtype :=
    ⟨g * z * g⁻¹, hL'.mem, hgz⟩
  have hint : ∀ x ∈ J ⊓ L₀, x = 1 ∨ x = rootDiagUnit .G2 a := by
    intro x hx
    have hxZ : (⟨x, hx.1⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g'
      exact Subtype.ext (hcomm _ g'.2 _ hx.2)
    exact coe_eq_one_or_eq_of_mem_center hK eJ.symm hzJ hz2 hxZ
  have hres := exc3_eq_or_eq_of_isSubnormal_sup eJ3 eL₀3 eL hcomm hz2 hzL₀ hεL hint hLS hsubS
  have finish : ∀ γ : Fin Tag.G2.rank → ℤ, IsRoot .G2 γ →
      (conjSub g L).map (adjointGroup .G2 (GaloisField 3 1)).subtype =
        rootSubgroup .G2 (GaloisField 3 1) γ ⊔ rootSubgroup .G2 (GaloisField 3 1) (-γ) →
      ∃ (g : ↥(adjointGroup .G2 (GaloisField 3 1))) (γ : Fin Tag.G2.rank → ℤ), IsRoot .G2 γ ∧
        L = (rootGroup (rootOperatorFamily .G2) (GaloisField 3 1) γ ⊔
            rootGroup (rootOperatorFamily .G2) (GaloisField 3 1) (-γ)).map
            (MulAut.conj g⁻¹).toMonoidHom := by
    intro γ hγ hLγ
    refine ⟨g, γ, hγ, ?_⟩
    have hL'eq := eq_rootGroup_sup_of_map_eq (rootOperatorFamily .G2) hγ hLγ
    have hLL : L = (conjSub g L).map (MulAut.conj g⁻¹).toMonoidHom := by
      ext x
      simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · intro hx
        exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, by group⟩
      · rintro ⟨y, ⟨x', hx', rfl⟩, rfl⟩
        convert hx' using 1
        group
    rw [hLL, hL'eq]
  rcases hres with hJres | hL₀res
  · exact finish g2e0 (isRoot_single .G2 g2l) hJres
  · exact finish g2δ isRoot_g2δ hL₀res

theorem classicalMembersFundamental3Tag_G2 : ClassicalMembersFundamental3Tag .G2 := by
  intro n hp hFT hadm L z hL hO
  obtain ⟨g, γ, hγ, hLeq⟩ := exc3_exists_conj_rootGroup_of_member_G2 hL hO
  exact ⟨g⁻¹, γ, Or.inr (Or.inl ⟨rfl, mem_adjDatum_roots.2 hγ⟩), hLeq⟩

theorem simpleOddCentralizerFreeTag_G2 : SimpleOddCentralizerFreeTag .G2 := by
  intro n hp hadm s hs
  exact exc3_involutionOddCore_adjoint_eq_bot (τ := .G2) (Or.inl rfl) s hs

theorem oddCentralizerFreeTag_G2 : OddCentralizerFreeTag .G2 :=
  oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_G2

end CFSG.ClassicalInvolution.Q3
