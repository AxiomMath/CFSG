module

public import CFSG.LargeExtraspecial.S8KT
public import CFSG.CGT.Timmesfeld75.Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup CorBHyp IsWC IsTI SimpleCaseStmt
  Lemma215Stmt isWC_of_corBHyp timmesfeldTransitivity_of_inputs)

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem eq_bot_of_normal_isPGroup_Mbar (N : Subgroup S.Mbar) (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  have hle : N ≤ CFSG.pCore 2 S.Mbar := le_sSup ⟨hN, h2⟩
  rw [S.pCore_Mbar_eq_bot] at hle
  exact le_bot_iff.mp hle

namespace Bad4

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad4 D τ)
include B

theorem corBHyp :
    CorBHyp ((closure (insert τ (N1bar S g t τ : Set S.O))).subgroupOf S.Mbar) := by
  set E := closure (insert τ (N1bar S g t τ : Set S.O)) with hEdef
  have hEM := B.E_le_Mbar
  have hcomm := B.E_comm
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩, fun gg => ?_, fun gg => ?_⟩
  · exact (hcomm _ (mem_ET.mp a.2) _ (mem_ET.mp b.2)).1
  · apply Subtype.ext
    rw [pow_two]
    exact (hcomm _ (mem_ET.mp hx) _ (mem_ET.mp hx)).2
  ·
    by_cases h : ∃ e ∈ E.subgroupOf S.Mbar ⊓ conjSubgroup gg (E.subgroupOf S.Mbar), e ≠ 1
    · right
      obtain ⟨e, he, he1⟩ := h
      have he1' : (e : S.O) ≠ 1 := fun h0 => he1 (Subtype.ext h0)
      have hY := B.map_eq_of_mem gg.2 (mem_ET.mp he.1) he1'
        (mem_conjSubgroup_ET.mp he.2)
      rw [B.conjSubgroup_eq hY, inf_idem]
    · left
      push Not at h
      exact eq_bot_iff.mpr fun x hx => (mem_bot).mpr (h x hx)
  ·
    constructor
    · intro hc
      have htE : t ∈ E := subset_closure (Set.mem_insert_of_mem _ t_mem_N1bar)
      have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
      have h1 : (⟨t, htM⟩ : S.Mbar) ∈ E.subgroupOf S.Mbar := mem_ET.mpr htE
      have h2 : gg * ⟨t, htM⟩ * gg⁻¹ ∈ conjSubgroup gg (E.subgroupOf S.Mbar) := by
        rw [mem_conjSubgroup]
        simpa [mul_assoc] using h1
      have h3 := congrArg Subtype.val (hc _ h1 _ h2).eq
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      have hC := conj_mem_conjCentM ht gg.2 h3.symm
      exact B.conjSubgroup_eq (B.map_eq_of_commSpace_le gg.2 (B.commSpace_le hC))
    · intro h x hx y hy
      rw [h] at hy
      exact Subtype.ext (hcomm _ (mem_ET.mp hx) _ (mem_ET.mp hy)).1

theorem false (hS : SimpleCaseStmt) (h215 : Lemma215Stmt) : False := by
  set E := closure (insert τ (N1bar S g t τ : Set S.O)) with hEdef
  have hEM := B.E_le_Mbar
  have hWC := isWC_of_corBHyp B.corBHyp
  have htE : t ∈ E := subset_closure (Set.mem_insert_of_mem _ t_mem_N1bar)
  have hτE : τ ∈ E := subset_closure (Set.mem_insert τ _)
  have htτE : t * τ ∈ E := mul_mem htE hτE
  have htN := self_mem_Nbar H ht
  have htτ1 : t * τ ≠ 1 := fun h => B.not_mem (by
    have e : τ = t⁻¹ * (t * τ) := by group
    rw [e, h, mul_one]
    exact inv_mem htN)
  obtain ⟨k, -, hk⟩ := timmesfeldTransitivity_of_inputs hS h215 S.Mbar (E.subgroupOf S.Mbar) hWC
    eq_bot_of_normal_isPGroup_Mbar ⟨t, hEM htE⟩ (mem_ET.mpr htE)
    (fun h => ht1 (congrArg Subtype.val h)) ⟨t * τ, hEM htτE⟩ (mem_ET.mpr htτE)
    (fun h => htτ1 (congrArg Subtype.val h))
  have hk' := congrArg Subtype.val hk
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hk'
  have R := B.red
  have h6 := R.six_le
  obtain ⟨-, hτt, x, hxM, hxτ⟩ := B.mem
  apply conj_ne_mul_of_not_mem_Nbar D (by rw [R.hm4]; norm_num) R.hfus R.hsub hxM hxτ
    (R.fix_Vt B.mem) B.not_mem ((k : S.O) * x⁻¹)
  rw [← hk', hxτ]
  group

end Bad4

universe u

theorem timmesfeld83PlusGlobal4_of (hS : SimpleCaseStmt) (h215 : Lemma215Stmt) :
    Timmesfeld83PlusGlobal4.{0} := by
  intro G _ _ S g hCE _ H hNo C t ht ht1 hVQ hΩ D hm4 _ hA7 hn hsub x hxM hxt
  by_contra hN
  have hτM : x * t * x⁻¹ ∈ S.Mbar :=
    mul_mem (mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  exact Bad4.false (D := D) ⟨⟨hCE, hNo, hΩ, hm4, hA7, hn, hsub⟩, ⟨hτM, hxt, x, hxM, rfl⟩, hN⟩
    hS h215

end CFSG.LargeExtraspecial.S8
