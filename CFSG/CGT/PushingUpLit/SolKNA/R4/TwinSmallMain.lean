module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallFam
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallShape
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3M11
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3M12
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3L33
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3U33
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3PSp43

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG.GH74.KGroups CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover
open CFSG.ComponentClassification.CatFactsSmall CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4


@[expose] def TwinLeafR (r n : ℕ) (P : ∀ (F : Type) [Group F], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t → TwoSubgroupsFourGenerated ↥(genFittingFStar Y) →
      P ↥(genFittingFStar Y) → False

theorem twinLeafR_of_noQ16 {r n : ℕ} (hr : 4 ≤ r) {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → ∃ (A : Type) (_ : Group A), EmbedsAut F A ∧ NoQ16 A) :
    TwinLeafR r n P := by
  intro Y _ _ R S t hP _ hPF
  exfalso
  haveI := genFittingFStar_normal Y
  haveI := hP.core.simple
  obtain ⟨A, _, hE, hA⟩ := h _ hPF
  obtain ⟨f, hf⟩ := hE Y (genFittingFStar Y) ⟨MulEquiv.refl _⟩
    (Nobq.centralizer_genFittingFStar_eq_bot hP.core.nonab)
  obtain ⟨e⟩ := hP.core.quat
  let ι : QuaternionGroup (2 ^ (r - 2)) →* Y :=
    R.subtype.comp ((S : Subgroup R).subtype.comp e.symm.toMonoidHom)
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (Subtype.val_injective.comp e.symm.injective)
  obtain ⟨x, y, hxy⟩ := exists_q16Pair_of_injective hr ι hι
  exact hA (f x) (f y) (hxy.map f hf)

theorem twinLeafR_m11 {r n : ℕ}
    (hr : 4 ≤ r) : TwinLeafR r n SmallM11 :=
  twinLeafR_of_noQ16 hr fun F _ hF => by
    obtain ⟨M, -, hA⟩ := M11.autModel hF
    exact ⟨↥M.A, inferInstance, embedsAut_of_autModel M, by rw [hA]; exact m11_noQ16⟩

theorem twinLeafR_m12
    {r n : ℕ} (hr : 4 ≤ r) : TwinLeafR r n SmallM12 :=
  twinLeafR_of_noQ16 hr fun F _ hF => by
    obtain ⟨e⟩ := hF
    exact ⟨↥autModel, inferInstance,
      embedsAut_of_exactModel GH74.Generic.S45.EvSpor.m12_smallAutModel (e.trans m12EquivD),
      m12_noQ16⟩

theorem twinLeafR_l33 {r n : ℕ}
    (hr : 4 ≤ r) : TwinLeafR r n fun F _ => LieModel F .PSL 3 3 1 :=
  twinLeafR_of_noQ16 hr fun F _ hF => by
    obtain ⟨e⟩ := L33.equiv_of_lieModel hF
    obtain ⟨M, -, hA⟩ := L33.autModel e
    exact ⟨↥M.A, inferInstance, embedsAut_of_autModel M, by rw [hA]; exact l33_noQ16⟩

theorem twinLeafR_u33
    {r n : ℕ} (hr : 4 ≤ r) :
    TwinLeafR r n fun F _ => LieModel F .PSU 3 3 1 :=
  twinLeafR_of_noQ16 hr fun F _ hF => by
    obtain ⟨e⟩ := U33.equiv_of_lieModel hF
    obtain ⟨M, -, hA⟩ := U33.autModel e
    exact ⟨↥M.A, inferInstance, embedsAut_of_autModel M, by rw [hA]; exact u33_noQ16⟩

theorem twinLeafR_psp43 {r n : ℕ}
    (hr : 4 ≤ r) : TwinLeafR r n fun F _ => LieModel F .PSp 2 3 1 :=
  twinLeafR_of_noQ16 hr fun F _ hF => by
    obtain ⟨e⟩ := PSp43.equiv_of_lieModel hF
    obtain ⟨M, -, hA⟩ := PSp43.exists_model e
    exact ⟨↥M.A, inferInstance, embedsAut_of_autModel M, by rw [hA]; exact psp43_noQ16⟩

theorem twinLeafR_l2 {r n : ℕ} (hr : 4 ≤ r) : TwinLeafR r n SmallL2 :=
  fun _ _ _ _ _ _ hP _ hF => false_of_l2 hr hP hF

theorem twinLeafR_l3Ne3 {r n : ℕ} (hr : 4 ≤ r) : TwinLeafR r n SmallL3Ne3 :=
  fun _ _ _ _ _ _ hP _ hF => false_of_l3 hr hP hF

theorem twinLeafR_u3Ne3 {r n : ℕ} (hr : 4 ≤ r) : TwinLeafR r n SmallU3Ne3 :=
  fun _ _ _ _ _ _ hP _ hF => false_of_u3 hr hP hF

theorem twinLeafR_g2Ne3
    {r n : ℕ} (hr : 4 ≤ r) : TwinLeafR r n SmallG2Ne3 :=
  fun _ _ _ _ _ _ hP hsmall hF => false_of_g2Ne3 hr hP hsmall hF

theorem twinLeafR_d4Ne3
    {r n : ℕ} (hr : 4 ≤ r) : TwinLeafR r n SmallD4Ne3 :=
  fun _ _ _ _ _ _ hP hsmall hF => false_of_d4Ne3 hr hP hsmall hF

theorem TwinLeafR.of_split {r n : ℕ} {P Q₃ Q : ∀ (F : Type) [Group F], Prop}
    (hsplit : ∀ (F : Type) [Group F], P F → Q₃ F ∨ Q F) (h₃ : TwinLeafR r n Q₃)
    (h : TwinLeafR r n Q) : TwinLeafR r n P :=
  fun Y _ _ R S t hP hsmall hPF =>
    (hsplit _ hPF).elim (fun h3 => h₃ Y R S t hP hsmall h3) (fun h4 => h Y R S t hP hsmall h4)

theorem twinLeafR_l3 {r n : ℕ}
    (hr : 4 ≤ r) : TwinLeafR r n SmallL3 := by
  refine TwinLeafR.of_split (fun F _ hF => ?_) (twinLeafR_l33 hr) (twinLeafR_l3Ne3 hr)
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl (Or.inl ⟨by decide, hm⟩)
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem twinLeafR_u3
    {r n : ℕ} (hr : 4 ≤ r) :
    TwinLeafR r n SmallU3 := by
  refine TwinLeafR.of_split (fun F _ hF => ?_) (twinLeafR_u33 hr) (twinLeafR_u3Ne3 hr)
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl (Or.inl ⟨by decide, hm⟩)
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem twinLeafR_psp4 {r n : ℕ}
    (hr : 4 ≤ r) (h : TwinLeafR r n SmallPSp4Ne3) : TwinLeafR r n SmallPSp4 := by
  refine TwinLeafR.of_split (fun F _ hF => ?_) (twinLeafR_psp43 hr) h
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem twinLeafR_g2
    {r n : ℕ} (hr : 4 ≤ r)
    (h₃ : TwinLeafR r n fun F _ => LieModel F .G2 0 3 1) : TwinLeafR r n SmallG2 := by
  refine TwinLeafR.of_split (fun F _ hF => ?_) h₃ (twinLeafR_g2Ne3 hr)
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem twinLeafR_d4
    {r n : ℕ} (hr : 4 ≤ r)
    (h₃ : TwinLeafR r n fun F _ => LieModel F .trialityD4 0 3 1) : TwinLeafR r n SmallD4 := by
  refine TwinLeafR.of_split (fun F _ hF => ?_) h₃ (twinLeafR_d4Ne3 hr)
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
