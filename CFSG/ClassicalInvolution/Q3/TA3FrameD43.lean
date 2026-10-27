module

public import CFSG.ClassicalInvolution.Q3.TA3FrameLayer
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcSRD4
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Exc

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS
open CFSG.ComponentClassification.Foote5.OddLieCore (oddFixed)

theorem isComponentOf_of_oddFixed {S : Type} [Group S] {x : S} {X : Subgroup S}
    (h : GorensteinWalter.IsComponentOf X (oddFixed (MulAut.conj x))) :
    IsComponentOf X (Subgroup.centralizer ({x} : Set S)) := by
  obtain ⟨hXo, hsub, hq⟩ := h
  have hfix : ∀ s : S, MulAut.conj x s = s → s ∈ Subgroup.centralizer ({x} : Set S) := by
    intro s hs
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr hs.symm
  have hoC : oddFixed (MulAut.conj x) ≤ Subgroup.centralizer ({x} : Set S) := by
    rw [oddFixed, Subgroup.closure_le]
    rintro s ⟨hs, -⟩
    exact hfix s hs
  have hon : ((oddFixed (MulAut.conj x)).subgroupOf
      (Subgroup.centralizer ({x} : Set S))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hoC]
    intro n g hn hg
    have hle : (oddFixed (MulAut.conj x)).map (MulAut.conj g).toMonoidHom ≤
        oddFixed (MulAut.conj x) := by
      rw [oddFixed, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨s, ⟨hs, hso⟩, rfl⟩
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · have hsC := hfix s hs
        have hgs : g * s * g⁻¹ ∈ Subgroup.centralizer ({x} : Set S) :=
          mul_mem (mul_mem hg hsC) (inv_mem hg)
        have e := Subgroup.mem_centralizer_singleton_iff.mp hgs
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← e, mul_inv_cancel_right]
      · rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
        exact hso
    exact hle ⟨n, hn, rfl⟩
  refine ⟨hXo.trans hoC, ?_, hq.2⟩
  have h1 : IsSubnormal X (oddFixed (MulAut.conj x)) :=
    (ComponentClassification.LBalance.subnormal_subgroupOf_iff hXo).mp
      (ComponentClassification.Components.chain_of_mathlib_subnormal hsub)
  exact isSubnormal_trans h1 (IsSubnormal.step hoC hon (IsSubnormal.refl _))

variable {Y : Type} [Group Y] [Finite Y] {z : Y} {L T : Subgroup Y}

theorem false_of_d43 [T.Normal] (hL : IsClassicalMember3 L z) (hTL : T ⊔ L = ⊤)
    (h3 : memberIndex L T = 3) (hC : Subgroup.centralizer (T : Set Y) = ⊥)
    (hT : Blueprint.LieModel ↥T .trialityD4 0 3 1) : False := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_graphFixedRootGroup_D4
      (CFSG.GH74.GLS.IVK.chevalleyExceptionalModel_of_lieModel_D4 hT)
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.sigma_cube hK hσ
  set zT : T := ⟨z, mem_of_member hL hTL h3⟩ with hzT
  have hx : orderOf (e zT) = 2 := by
    rw [MulEquiv.orderOf_eq, hzT, Subgroup.orderOf_mk]
    exact hL.orderOf_eq_two
  obtain ⟨c, ψ, -, hψ, hcomp⟩ :=
    CFSG.ComponentClassification.HarrisLit.L33.SR.E1.triality_slB_component Nat.prime_three
      (by norm_num) le_rfl hK σ hσ hσ3 hx
  have hK1 := isComponentOf_map e (t := zT) (isComponentOf_of_oddFixed hcomp)
  set K' := ψ.range.map e.symm.toMonoidHom with hK'
  have hK2 : IsComponentOf (K'.map T.subtype) (T ⊓ Subgroup.centralizer ({z} : Set Y)) := by
    refine ⟨?_, ?_, ComponentClassification.Components.quasisimple_of_equiv
      (K'.equivMapOfInjective _ T.subtype_injective).symm hK1.2.2⟩
    · rw [← map_centralizer_subtype (z' := zT)]
      exact Subgroup.map_mono hK1.1
    · rw [← map_centralizer_subtype (z' := zT)]
      exact ComponentClassification.Components.chain_map _ hK1.2.1
  obtain ⟨y, hyL, hyT, -⟩ := exists_three_element hL h3
  have hyc := commute_of_isComponentOf hL hK2 y hyL
  set α : MulAut T := MulAut.conjNormal y with hα
  have hαx : ∀ x : T, (α x : Y) = y * x * y⁻¹ := fun x => MulAut.conjNormal_apply y x
  obtain ⟨h, hh⟩ := CFSG.ComponentClassification.Foote5.OddLieCore.Exc.mem_range_conj_of_fix_slB
    Nat.prime_three (by norm_num) le_rfl hK σ hσ hσ3 c (r := MulAut.congr e α) fun C y' hy' => by
      have hy'ψ : y' = ψ C := Subtype.ext (by rw [hy', hψ C])
      rw [hy'ψ]
      change e (α (e.symm (ψ C))) = ψ C
      have hmem : ((e.symm (ψ C) : T) : Y) ∈ K'.map T.subtype :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ ⟨C, rfl⟩)
      have hα1 : α (e.symm (ψ C)) = e.symm (ψ C) :=
        Subtype.ext (by rw [hαx, hyc _ hmem, mul_inv_cancel_right])
      rw [hα1, MulEquiv.apply_symm_apply]
  have key : ∀ t : T, y * (t : Y) * y⁻¹ = (e.symm h : Y) * t * (e.symm h : Y)⁻¹ := by
    intro t
    have h1 := congrArg (fun φ => φ (e t)) hh
    change h * e t * h⁻¹ = e (α (e.symm (e t))) at h1
    rw [MulEquiv.symm_apply_apply] at h1
    have h2 : α t = e.symm h * t * (e.symm h)⁻¹ := by
      apply e.injective
      rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [← hαx, h2]
    simp
  have hyC : (e.symm h : Y)⁻¹ * y ∈ Subgroup.centralizer (T : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 := key ⟨t, ht⟩
    calc t * ((e.symm h : Y)⁻¹ * y) =
        (e.symm h : Y)⁻¹ * ((e.symm h : Y) * t * (e.symm h : Y)⁻¹) * y := by group
      _ = (e.symm h : Y)⁻¹ * (y * t * y⁻¹) * y := by rw [← h1]
      _ = (e.symm h : Y)⁻¹ * y * t := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hyC
  exact hyT (hyC ▸ (e.symm h).2)

end CFSG.ClassicalInvolution.Q3.TA3.Frame
