module

public import CFSG.GH74.GLS.Stage2.Local.Prop28Kinds
public import CFSG.GH74.GLS.Stage2.Local.Prop28G2
public import CFSG.GH74.GLS.Stage2.Local.Prop28Two
public import CFSG.GH74.GLS.Stage2.Local.Prop28Good
public import CFSG.GH74.GLS.Stage2.Local.Prop28Layer

public section

namespace CFSG.GH74.GLS.Stage2.Local.Prop28

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12

section Weak

variable {G : Type} [Group G] [Finite G]

@[expose] def Prop27Y (z y : G) : Prop :=
  y ∈ Cen z ∧ IsNonCentralInvolution y ∧
    (Ixz z y ≠ ⊥ ∨ ∀ x' ∈ Cen z, IsNonCentralInvolution x' → Ixz z x' = ⊥)

theorem compsGood_of_hat_isL2
    {y : G} {r : ℕ} (hr : Odd r) (hr3 : 3 < r)
    (hL2 : IVK.IsL2 (↥(Jx y) ⧸ pPrimeCore 2 ↥(Jx y)) (fun s => s = r)) : CompsGood y := by
  intro K hK
  have hJ : IsSimpleGroup (↥(Jx y) ⧸ pPrimeCore 2 ↥(Jx y)) := isSimpleGroup_of_isL2 hr3 hL2
  obtain ⟨e⟩ := component_equiv_hat_of_simple hJ hK
  obtain ⟨F, hF, hfin, hq, ⟨e'⟩⟩ := hL2
  exact good_of_isL2 hK.1 hr hr3 ⟨F, hF, hfin, hq, ⟨e.trans e'⟩⟩

theorem compsGood_of_hat_A7 {y : G}
    (hA7 : Nonempty ((↥(Jx y) ⧸ pPrimeCore 2 ↥(Jx y)) ≃* alternatingGroup (Fin 7))) :
    CompsGood y := by
  intro K hK
  obtain ⟨eA⟩ := hA7
  have hJ : IsSimpleGroup (↥(Jx y) ⧸ pPrimeCore 2 ↥(Jx y)) := isSimpleGroup_of_A7 ⟨eA⟩
  obtain ⟨e⟩ := component_equiv_hat_of_simple hJ hK
  exact good_of_A7 hK.1 ⟨e.trans eA⟩

omit [Finite G] in
theorem isConj_second_class {z x y : G} (hz : IsCentralInvolution z)
    (hcl : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x u) (hy : IsNonCentralInvolution y) :
    IsConj x y := by
  rcases hcl y hy.1 with h | h
  · exact absurd (isCentralInvolution_of_isConj' hz h) hy.2
  · exact h

theorem compsGood_second_class_of_comps {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {x : G} (hz : IsCentralInvolution z)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) (hx : TwoClassData G z S L₁ L₂ q x)
    (hP : ∀ y : G, Prop27Y z y → CompsGood y) : CompsGood x := by
  have hxC : x ∈ Cen z := hS.le hx.x_mem
  have hxnc : IsNonCentralInvolution x := ⟨hx.x_inv, hx.x_nonCentral⟩
  obtain ⟨y, hyC, hync, hyI⟩ := exists_prop27_y ⟨x, hxC, hxnc⟩
  exact compsGood_of_isConj (isConj_second_class hz hx.classes hync).symm (hP y ⟨hyC, hync, hyI⟩)

theorem not_l2Meets_inG2_of_stage1Data_comps {z : G} {S : Subgroup G} {k : Kind}
    (hk : k ≠ Kind.m12) (hz : IsCentralInvolution z)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) (hd : Stage1Data G z S k)
    (hP : ∀ y : G, Prop27Y z y → CompsGood y) : ¬ L2Meets G InG2 := by
  have hz2 : orderOf z = 2 := hz.1
  cases hd with
  | g2 h => exact not_l2Meets_inG2_of_g2 h hz2
  | m12 h => exact absurd rfl hk
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    obtain ⟨x, hx⟩ := h.two
    exact not_l2Meets_inG2_of_reps (compsGood_of_pair h.pair)
      (compsGood_second_class_of_comps hz hS hx hP) hx.classes
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    rcases h.fusion with ⟨-, hone⟩ | ⟨-, x, hx, -⟩
    · exact not_l2Meets_inG2_of_pair_oneClass h.pair hz2 hone
    · exact not_l2Meets_inG2_of_reps (compsGood_of_pair h.pair)
        (compsGood_second_class_of_comps hz hS hx hP) hx.classes
  | mcl h =>
    obtain ⟨n, hn, h⟩ := h
    exact not_l2Meets_inG2_of_sporadic h ⟨by omega, by omega⟩ hz2
  | ly h =>
    obtain ⟨n, hn, h⟩ := h
    exact not_l2Meets_inG2_of_sporadic h ⟨by omega, by omega⟩ hz2

end Weak

end CFSG.GH74.GLS.Stage2.Local.Prop28
