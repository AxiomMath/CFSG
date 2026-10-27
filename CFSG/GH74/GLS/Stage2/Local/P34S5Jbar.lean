module

public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GH74.GLS.Stage12.Interface
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
open CFSG.GorensteinWalter (PSL2 IsOddPrimePower HasDihedralSylowTwo)
open scoped MatrixGroups

@[expose] def DihJ (X : Type) [Group X] : Prop :=
  IVK.IsL2 X Odd ∨ Nonempty (X ≃* alternatingGroup (Fin 7))

theorem psl2_solvable_of_card_le_three {F : Type} [Field F] [Finite F] (hF : Nat.card F ≤ 3) :
    Group.IsSolvable (PSL2 F) := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable F
      (by omega)
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
  infer_instance

theorem DihJ.isSimple {X : Type} [Group X] [Finite X] (h : DihJ X) (hns : ¬ Group.IsSolvable X) :
    IsSimpleGroup X := by
  rcases h with ⟨F, iF, fF, hodd, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · by_cases h4 : 3 < Nat.card F
    · have : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
      exact (IVK.toPSL e).isSimpleGroup
    · exfalso
      apply hns
      have : Group.IsSolvable (PSL2 F) := psl2_solvable_of_card_le_three (by omega)
      exact Group.isSolvable_of_isSolvable_injective (f := (IVK.toPSL e).toMonoidHom) (IVK.toPSL e).injective
  · have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup

theorem DihJ.nonabelian {X : Type} [Group X] [Finite X] (h : DihJ X) (hns : ¬ Group.IsSolvable X) :
    ∃ a b : X, a * b ≠ b * a := by
  have := h.isSimple hns
  by_contra hno
  push Not at hno
  exact hns (IsSimpleGroup.comm_iff_isSolvable.1 hno)

theorem DihJ.hasDihedralSylowTwo {X : Type} [Group X] [Finite X] (h : DihJ X) : HasDihedralSylowTwo X := by
  rcases h with ⟨F, iF, fF, hodd, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv (IVK.toPSL e)
      (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
        (CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hodd))
  · exact CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
      CFSG.GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven

section A7

open Equiv.Perm in
theorem a7_cycleType_of_orderOf_two (c : alternatingGroup (Fin 7)) (hc : orderOf c = 2) :
    (c : Equiv.Perm (Fin 7)).cycleType = Multiset.replicate 2 2 := by
  set σ : Equiv.Perm (Fin 7) := (c : Equiv.Perm (Fin 7)) with hσ
  have hσ2 : orderOf σ = 2 := by rw [hσ, Subgroup.orderOf_coe]; exact hc
  have hlcm := Equiv.Perm.lcm_cycleType σ
  rw [hσ2] at hlcm
  have hmem : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have h1 : n ∣ 2 := hlcm ▸ Multiset.dvd_lcm hn
    have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h1) h2
  have hrep := Multiset.eq_replicate_card.2 hmem
  have hsum : σ.cycleType.sum = σ.support.card := Equiv.Perm.sum_cycleType σ
  have hle : σ.support.card ≤ 7 := by
    have := σ.support.card_le_univ
    simpa using this
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hm3 : Multiset.card σ.cycleType ≤ 3 := by omega
  have hsign : Equiv.Perm.sign σ = 1 := by
    have := c.2
    rwa [mem_alternatingGroup] at this
  rw [Equiv.Perm.sign_of_cycleType, hrep, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hsign
  have heven : Even (Multiset.card σ.cycleType * 2 + Multiset.card σ.cycleType) :=
    (neg_one_pow_eq_one_iff_even (by decide)).1 hsign
  have hm0 : Multiset.card σ.cycleType ≠ 0 := by
    intro h0
    have h1 : σ = 1 := Equiv.Perm.card_cycleType_eq_zero.1 h0
    rw [h1, orderOf_one] at hσ2
    omega
  have hm : Multiset.card σ.cycleType = 2 := by
    obtain ⟨r, hr⟩ := heven
    omega
  rw [hrep, hm]

end A7

theorem a7_involutions_conj {a b : alternatingGroup (Fin 7)} (ha : orderOf a = 2) (hb : orderOf b = 2) :
    IsConj a b := by
  refine alternatingGroup.isConj_of (Equiv.Perm.isConj_iff_cycleType_eq.2 ?_) ?_
  · rw [a7_cycleType_of_orderOf_two a ha, a7_cycleType_of_orderOf_two b hb]
  · rw [← Equiv.Perm.sum_cycleType, a7_cycleType_of_orderOf_two a ha]
    simp

theorem DihJ.involutions_conj {X : Type} [Group X] [Finite X] (h : DihJ X) {a b : X}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  rcases h with ⟨F, iF, fF, hodd, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hinv : ∀ {c : X}, orderOf c = 2 → CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (IVK.toPSL e c) := by
      intro c hc
      refine ⟨?_, ?_⟩
      · intro h1
        have : c = 1 := (IVK.toPSL e).injective (by rw [h1, map_one])
        rw [this, orderOf_one] at hc
        omega
      · have h2 := pow_orderOf_eq_one c
        rw [hc] at h2
        rw [← map_pow, h2, map_one]
    obtain ⟨g, hg⟩ := CFSG.GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power F
      (CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hodd) _ _ (hinv ha) (hinv hb)
    refine isConj_iff.2 ⟨(IVK.toPSL e).symm g, (IVK.toPSL e).injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hg
  · have hord : ∀ {c : X}, orderOf c = 2 → orderOf (e c) = 2 := fun {c} hc => by
      rw [MulEquiv.orderOf_eq]; exact hc
    have := a7_involutions_conj (hord ha) (hord hb)
    obtain ⟨g, hg⟩ := isConj_iff.1 this
    refine isConj_iff.2 ⟨e.symm g, e.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hg

end CFSG.GH74.GLS.Stage2.Local.P34
