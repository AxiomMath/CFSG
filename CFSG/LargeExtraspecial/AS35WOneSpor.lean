module

public import CFSG.LargeExtraspecial.AS35WOneUse
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3
public import CFSG.Sporadic.Recognition.McLASInvolutions
public import CFSG.Walter.J1Props.Facts
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovLy

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Blueprint

namespace AS35W

theorem oneClass_M22
    {X : Type} [Group X]
    (hX : NativeSporadic.IsSporadic X .M22) : OneClass X := by
  obtain ⟨e⟩ := hX
  have e' : X ≃* ↥CFSG.Sporadic.Schreier.m22Certificate.originalSubgroup :=
    e.trans (MulEquiv.subgroupCongr CFSG.Sporadic.Schreier.m22Certificate_originalSubgroup.symm)
  obtain ⟨hcov, -⟩ := CFSG.ClassicalInvolution.m22_cover_and_centralizers
  intro u v hu hv
  refine CFSG.Sporadic.Recognition.McLAS.isConj_involutions_of_equiv e'
    (t₀ := CFSG.Sporadic.Schreier.m22Rep1) (fun τ hτ ho => ?_) u v hu hv
  obtain ⟨d, hd, c, hc, h⟩ := hcov τ (by simpa using hτ) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact ⟨c, hc, h⟩

theorem oneClass_M23
    {X : Type} [Group X]
    (hX : NativeSporadic.IsSporadic X .M23) : OneClass X := by
  obtain ⟨e⟩ := hX
  have e' : X ≃* ↥CFSG.Sporadic.Schreier.m23Certificate.originalSubgroup :=
    e.trans (MulEquiv.subgroupCongr CFSG.Sporadic.Schreier.m23Certificate_originalSubgroup.symm)
  obtain ⟨hcov, -⟩ := CFSG.ClassicalInvolution.m23_cover_and_centralizers
  intro u v hu hv
  refine CFSG.Sporadic.Recognition.McLAS.isConj_involutions_of_equiv e'
    (t₀ := CFSG.Sporadic.Schreier.m23Rep1) (fun τ hτ ho => ?_) u v hu hv
  obtain ⟨d, hd, c, hc, h⟩ := hcov τ (by simpa using hτ) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact ⟨c, hc, h⟩

theorem oneClass_J1 {X : Type} [Group X]
    (hX : NativeSporadic.IsSporadic X .J1) : OneClass X := by
  obtain ⟨e⟩ := hX
  exact OneClass.of_mulEquiv (e.trans CFSG.Walter.walterJ1EquivNative.symm)
    (fun x y hx hy => CFSG.Walter.J1Props.J1_isConj_involutions hx hy)

theorem oneClass_J3 {X : Type}
    [Group X] (hX : NativeSporadic.IsSporadic X .J3) : OneClass X := by
  obtain ⟨e⟩ := hX
  have hP := CFSG.ClassicalInvolution.J3Proof.card_P3
  have hS2 : IsPGroup 2 CFSG.ClassicalInvolution.J3Proof.sChain.originalSubgroup :=
    IsPGroup.of_card (n := 7) (by rw [CFSG.ClassicalInvolution.J3Proof.card_sChain]; norm_num)
  have hidx : ¬ 2 ∣ (CFSG.ClassicalInvolution.J3Proof.sChain.originalSubgroup.subgroupOf
      CFSG.ClassicalInvolution.J3Proof.P3).index := by
    have h := (CFSG.ClassicalInvolution.J3Proof.sChain.originalSubgroup.subgroupOf
      CFSG.ClassicalInvolution.J3Proof.P3).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe CFSG.ClassicalInvolution.J3Proof.sChain_le_P3).toEquiv,
      CFSG.ClassicalInvolution.J3Proof.card_sChain, hP] at h
    omega
  intro u v hu hv
  exact CFSG.Sporadic.Recognition.McLAS.isConj_involutions_of_equiv
    (e.trans CFSG.ClassicalInvolution.J3Proof.nativeEquivP3)
    (CFSG.ClassicalInvolution.cover_of_sylow _ _ hS2 hidx _
      CFSG.ClassicalInvolution.J3Proof.cover_S) u v hu hv

theorem oneClass_McL
    {X : Type} [Group X] (hX : NativeSporadic.IsSporadic X .McL) : OneClass X := by
  obtain ⟨e⟩ := hX
  exact OneClass.of_mulEquiv e
    (fun x y hx hy => CFSG.Sporadic.Recognition.McLAS.mcl_involutions_conj x y hx hy)

theorem oneClass_Ly {X : Type}
    [Group X] [Finite X] (hX : NativeSporadic.IsSporadic X .Ly) : OneClass X :=
  fun u v hu hv => CFSG.GH74.GLS.IVK.Proofs2.ivk93cov_ly_oneClass hX u v hu hv

end AS35W

end CFSG.LargeExtraspecial
