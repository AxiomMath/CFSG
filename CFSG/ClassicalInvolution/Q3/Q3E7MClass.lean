module

public import CFSG.ClassicalInvolution.Q3.Q3E7MStd
public import CFSG.ClassicalInvolution.Q3.Q3ExcE7
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthAdj
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelAdjoint

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LieType.HighestRoot
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false

local notation "M₇" => E7sc 3 1
local notation "D₇" => e7Datum (GaloisField 3 1)

section Adjoint

theorem isClassicalMember3_rootRankOneAd {θ : Fin (Tag.rank .E7) → ℤ} (hθ : IsLongRoot .E7 θ) :
    IsClassicalMember3 (rootRankOneAd .E7 (GaloisField 3 1) θ)
        (rootTorusAd .E7 (GaloisField 3 1) θ (-1)) ∧
      classicalInvolutionOddCore (rootRankOneAd .E7 (GaloisField 3 1) θ) = ⊥ := by
  have hK : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  obtain ⟨a, ha, hd, -⟩ := exists_signTuple_of_isRoot (K := GaloisField 3 1) hθ.1
  have hle : rootRankOneGroup .E7 (GaloisField 3 1) θ ≤ adjointGroup .E7 (GaloisField 3 1) :=
    (exceptional_Lang_root_rank_one_data .E7 (GaloisField 3 1) θ).2.2.2.2.2.1
  obtain ⟨-, e, -⟩ := (exceptional_Lang_root_rank_one_data .E7 (GaloisField 3 1) θ).2.2.2.2.2.2.2.1
    hK
  let eL : rootRankOneAd .E7 (GaloisField 3 1) θ ≃* SL(2, GaloisField 3 1) :=
    (Subgroup.subgroupOfEquivOfLe hle).trans e.symm
  obtain ⟨ε⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three (F := GaloisField 3 1) card_gf3
  let e' : rootRankOneAd .E7 (GaloisField 3 1) θ ≃* SL(2, ZMod 3) := eL.trans ε
  have hO : classicalInvolutionOddCore (rootRankOneAd .E7 (GaloisField 3 1) θ) = ⊥ := by
    have h1 : (classicalInvolutionOddCore (rootRankOneAd .E7 (GaloisField 3 1) θ)).map
        e'.toMonoidHom = classicalInvolutionOddCore SL(2, ZMod 3) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e'
    rw [show classicalInvolutionOddCore SL(2, ZMod 3) = ⊥ from componentOddCore_sl2Three] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).mp h1
  refine ⟨⟨?_, ?_, ?_, ⟨?_⟩⟩, hO⟩
  · refine orderOf_eq_prime ?_ ?_
    · refine Subtype.ext ?_
      simp only [rootTorusAd, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
      exact rootTorusSL2_neg_one_mul_self θ
    · exact fun h => rootTorusSL2_neg_one_ne_one hK θ (congrArg Subtype.val h)
  · exact Subgroup.mem_subgroupOf.2 ⟨HSL (-1), rfl⟩
  · have hCz := centralizer_eq_subgroupOf_toralCentralizer (τ := .E7) a
      (rootTorusAd .E7 (GaloisField 3 1) θ (-1)) hd
    rw [hCz]
    exact isSubnormal_comap (adjointGroup .E7 (GaloisField 3 1)).subtype
      (isSubnormal_rootRankOneGroup_toralCentralizer hK hθ ha hd)
  · exact ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e'

theorem exists_eq_rankOne_of_isClassicalMember3_toral (b : Fin Tag.E7.rank → (GaloisField 3 1)ˣ)
    (hb : ∀ i, b i = 1 ∨ b i = -1) {L : Subgroup ↥(adjointGroup .E7 (GaloisField 3 1))}
    {z : ↥(adjointGroup .E7 (GaloisField 3 1))}
    (hz : (z : ModGL .E7 (GaloisField 3 1)) = rootDiagUnit .E7 b) (h : IsClassicalMember3 L z)
    (hO : classicalInvolutionOddCore L = ⊥) :
    ∃ (γ : Fin Tag.E7.rank → ℤ) (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      L.map (adjointGroup .E7 (GaloisField 3 1)).subtype =
          componentRootSpan (GaloisField 3 1) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ ∧
        componentRootSpan (GaloisField 3 1) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
          rootSubgroup .E7 (GaloisField 3 1) γ ⊔ rootSubgroup .E7 (GaloisField 3 1) (-γ) := by
  have hK3 := exc3_natCard_galoisField_three
  have hK : ringChar (GaloisField 3 1) ≠ 2 := ringChar_ne_two_of_card_eq_three hK3
  have : Finite (ModGL .E7 (GaloisField 3 1)) := finite_modGL
  have hCz := centralizer_eq_subgroupOf_toralCentralizer b z hz
  have hXC := toralCentralizer_le_adjointGroup (K := GaloisField 3 1) (τ := .E7) b
  have hLC : L ≤ Subgroup.centralizer ({z} : Set ↥(adjointGroup .E7 (GaloisField 3 1))) :=
    isSubnormal_le h.subnormal
  obtain ⟨e⟩ := h.nonempty_equiv_sl2 hO
  let eL : SL(2, ZMod 3) ≃* ↥(L.map (adjointGroup .E7 (GaloisField 3 1)).subtype) :=
    e.symm.trans (L.equivMapOfInjective (adjointGroup .E7 (GaloisField 3 1)).subtype
      (adjointGroup .E7 (GaloisField 3 1)).subtype_injective)
  have hLX : L.map (adjointGroup .E7 (GaloisField 3 1)).subtype ≤
      toralCentralizer .E7 (GaloisField 3 1) b := by
    rintro _ ⟨x, hx, rfl⟩
    have := hCz ▸ hLC hx
    exact Subgroup.mem_subgroupOf.1 this
  have hsub : IsSubnormal (L.map (adjointGroup .E7 (GaloisField 3 1)).subtype)
      (toralCentralizer .E7 (GaloisField 3 1) b) := by
    have h1 := CFSG.ComponentClassification.Components.chain_map
      (adjointGroup .E7 (GaloisField 3 1)).subtype h.subnormal
    rwa [hCz, Subgroup.map_subgroupOf_eq_of_le hXC] at h1
  have hU' := fun i j (hi : ¬ 2 < (componentRoots (maskChar (signTupleBits b)) i).ncard)
      (hj : ¬ 2 < (componentRoots (maskChar (signTupleBits b)) j).ncard) =>
    exc3_small_unique hK (uniqIsolated_E7 (maskChar (signTupleBits b))) i j hi hj
  exact exc3_exists_rankOne_of_member hK3 hb hU' eL hLX hsub

theorem exists_rootRankOneGroup_of_conj_toral3 {θ : Fin Tag.E7.rank → ℤ} (hθ : IsLongRoot .E7 θ)
    {u : ModGL .E7 (GaloisField 3 1)} (hu : u ∈ adjointGroup .E7 (GaloisField 3 1))
    {b : Fin Tag.E7.rank → (GaloisField 3 1)ˣ} (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hz : u * rootTorusSL2 .E7 (GaloisField 3 1) θ (-1) * u⁻¹ = rootDiagUnit .E7 b) :
    ∃ (γ : Fin Tag.E7.rank → ℤ) (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      (rootRankOneGroup .E7 (GaloisField 3 1) θ).map (MulAut.conj u).toMonoidHom =
          rootRankOneGroup .E7 (GaloisField 3 1) γ ∧
        componentRootSpan (GaloisField 3 1) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
          rootRankOneGroup .E7 (GaloisField 3 1) γ ∧
        u * rootTorusSL2 .E7 (GaloisField 3 1) θ (-1) * u⁻¹ =
          rootTorusSL2 .E7 (GaloisField 3 1) γ (-1) := by
  have hK : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hle : rootRankOneGroup .E7 (GaloisField 3 1) θ ≤ adjointGroup .E7 (GaloisField 3 1) :=
    (exceptional_Lang_root_rank_one_data .E7 (GaloisField 3 1) θ).2.2.2.2.2.1
  obtain ⟨hA, hAO⟩ := isClassicalMember3_rootRankOneAd hθ
  have hc := hA.conj ⟨u, hu⟩
  have hcO : classicalInvolutionOddCore (conjSub (⟨u, hu⟩ : ↥(adjointGroup .E7 (GaloisField 3 1)))
      (rootRankOneAd .E7 (GaloisField 3 1) θ)) = ⊥ :=
    oddCore_eq_bot_of_equiv ((rootRankOneAd .E7 (GaloisField 3 1) θ).equivMapOfInjective
      (MulAut.conj (⟨u, hu⟩ : ↥(adjointGroup .E7 (GaloisField 3 1)))).toMonoidHom
      (MulAut.conj _).injective).symm hAO
  obtain ⟨γ, hγ, h1, h2⟩ := exists_eq_rankOne_of_isClassicalMember3_toral b hb
    (z := ⟨u, hu⟩ * rootTorusAd .E7 (GaloisField 3 1) θ (-1) * ⟨u, hu⟩⁻¹) hz hc hcO
  have hmap : (conjSub (⟨u, hu⟩ : ↥(adjointGroup .E7 (GaloisField 3 1)))
      (rootRankOneAd .E7 (GaloisField 3 1) θ)).map (adjointGroup .E7 (GaloisField 3 1)).subtype =
        (rootRankOneGroup .E7 (GaloisField 3 1) θ).map (MulAut.conj u).toMonoidHom := by
    unfold Generic.conjSub
    rw [Subgroup.map_map]
    have : (adjointGroup .E7 (GaloisField 3 1)).subtype.comp
        (MulAut.conj (⟨u, hu⟩ : ↥(adjointGroup .E7 (GaloisField 3 1)))).toMonoidHom =
        (MulAut.conj u).toMonoidHom.comp (adjointGroup .E7 (GaloisField 3 1)).subtype := by
      ext x
      rfl
    rw [this, ← Subgroup.map_map, rootRankOneAd, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hle]
  have hLγ : componentRootSpan (GaloisField 3 1) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
      rootRankOneGroup .E7 (GaloisField 3 1) γ := h2.trans (rootRankOneGroup_eq_sup hγ.1).symm
  have himg : (rootRankOneGroup .E7 (GaloisField 3 1) θ).map (MulAut.conj u).toMonoidHom =
      rootRankOneGroup .E7 (GaloisField 3 1) γ := hmap.symm.trans (h1.trans hLγ)
  refine ⟨γ, hγ, himg, hLγ, ?_⟩
  have hzmem : u * rootTorusSL2 .E7 (GaloisField 3 1) θ (-1) * u⁻¹ ∈
      rootRankOneGroup .E7 (GaloisField 3 1) γ := by
    rw [← himg]
    exact ⟨_, ⟨HSL (-1), rfl⟩, rfl⟩
  have hsq : (u * rootTorusSL2 .E7 (GaloisField 3 1) θ (-1) * u⁻¹) *
      (u * rootTorusSL2 .E7 (GaloisField 3 1) θ (-1) * u⁻¹) = 1 := by
    calc _ = u * (rootTorusSL2 .E7 (GaloisField 3 1) θ (-1) *
          rootTorusSL2 .E7 (GaloisField 3 1) θ (-1)) * u⁻¹ := by group
      _ = 1 := by rw [rootTorusSL2_neg_one_mul_self]; group
  have hne : u * rootTorusSL2 .E7 (GaloisField 3 1) θ (-1) * u⁻¹ ≠ 1 := fun h => by
    refine rootTorusSL2_neg_one_ne_one hK θ ?_
    have : rootTorusSL2 .E7 (GaloisField 3 1) θ (-1) = u⁻¹ * 1 * u := by
      rw [← h]
      group
    rw [this]
    group
  exact eq_rootTorusSL2_neg_one_of_mul_self_eq_one hK odd_gf3 hzmem hsq hne

end Adjoint

section Fund

theorem eq_of_map_εm_eq3 {R R' : Subgroup M₇} (hR : R ∈ Generic.fundamentalSubgroups .E7 D₇)
    (hR' : R' ∈ Generic.fundamentalSubgroups .E7 D₇)
    (h : R.map (εm (GaloisField 3 1)) = R'.map (εm (GaloisField 3 1))) : R = R' :=
  eq_of_map_eq_of_pow3 (εm (GaloisField 3 1)) εm_ker_le_center cop_ker3 (pow3_fund3 hR)
    (pow3_fund3 hR') h

theorem e7_fund_class3 :
    Generic.FundamentalSingleClass .E7 D₇ ∧
      stdRankOne D₇ thetaE7 ∈ Generic.fundamentalSubgroups .E7 D₇ :=
  ⟨yData3_E7'.sc, std_mem_fund3 isRoot_thetaE7⟩

theorem εm_involution_of_mem_fund3 {h r : M₇}
    (hr : r ∈ conjSub h (stdRankOne D₇ thetaE7)) (h2 : orderOf r = 2) :
    εm (GaloisField 3 1) r = εm (GaloisField 3 1) h *
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) *
        (εm (GaloisField 3 1) h)⁻¹ := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hRθF := (e7_fund_class3).2
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hr
  have hs2 : orderOf s = 2 := by
    rw [← h2]
    exact (orderOf_injective _ (MulAut.conj h).injective s).symm
  have hss : s * s = 1 := by rw [← sq]; exact hs2 ▸ pow_orderOf_eq_one s
  have hεs : εm (GaloisField 3 1) s ∈ rootRankOneGroup .E7 (GaloisField 3 1) thetaE7 := by
    rw [← map_stdRankOne_εm isRoot_thetaE7]
    exact Subgroup.mem_map_of_mem _ hs
  have hz2 : εm (GaloisField 3 1) s * εm (GaloisField 3 1) s = 1 := by
    rw [← map_mul, hss, map_one]
  have hz1 : εm (GaloisField 3 1) s ≠ 1 := by
    intro h1
    have := no_central_fund3 hRθF hs (εm_ker_le_center (MonoidHom.mem_ker.2 h1))
    rw [this, orderOf_one] at hs2
    omega
  have := eq_rootTorusSL2_neg_one_of_mul_self_eq_one hF odd_gf3 hεs hz2 hz1
  rw [rootTorusSL2_thetaE7] at this
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, this]

theorem eq_of_orderOf_two_fund3 {R : Subgroup M₇} (hR : R ∈ Generic.fundamentalSubgroups .E7 D₇)
    {r r' : M₇} (hr : r ∈ R) (hr' : r' ∈ R) (h2 : orderOf r = 2) (h2' : orderOf r' = 2) :
    r = r' := by
  obtain ⟨hsingle, hRθF⟩ := e7_fund_class3
  obtain ⟨g, hg⟩ := hsingle _ hRθF R hR
  rw [hg] at hr hr'
  have e1 := εm_involution_of_mem_fund3 hr h2
  have e2 := εm_involution_of_mem_fund3 hr' h2'
  have hker : r⁻¹ * r' ∈ (εm (GaloisField 3 1)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, e1, e2]
    group
  have hmem : r⁻¹ * r' ∈ R := R.mul_mem (R.inv_mem (by rw [hg]; exact hr)) (by rw [hg]; exact hr')
  have := no_central_fund3 hR hmem (εm_ker_le_center hker)
  exact (inv_mul_eq_one.1 this)

theorem exists_involution_fund3 {X : Subgroup M₇} (hX : X ∈ Generic.fundamentalSubgroups .E7 D₇) :
    ∃ r ∈ X, orderOf r = 2 := by
  obtain ⟨hsingle, hRθF⟩ := e7_fund_class3
  obtain ⟨g, hg⟩ := hsingle _ hRθF X hX
  obtain ⟨r, hr, hr2⟩ := exists_involution_std3 isRoot_thetaE7
  refine ⟨g * r * g⁻¹, ?_, ?_⟩
  · rw [hg]
    exact conj_mem_conjSub hr
  · rw [← hr2]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective r

end Fund

end CFSG.ClassicalInvolution.Q3.Q3W
