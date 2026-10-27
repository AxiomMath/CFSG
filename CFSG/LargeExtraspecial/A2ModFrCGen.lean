module

public import CFSG.LargeExtraspecial.A2ModFrCRel
public import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne
public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LieType.TitsSimplicity
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrC

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
open TauCeti.GLSymplecticFin (RootSubgroupIndex)

variable {k : ℕ} {F : Type} [Field F]

theorem eq_zero_or_eq_one_of_card (hF : Nat.card F = 2) (c : F) : c = 0 ∨ c = 1 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F
  rcases eq_or_ne c 0 with h | h
  · exact .inl h
  · right
    have h1 := FiniteField.pow_card_sub_one_eq_one c h
    rwa [← Nat.card_eq_fintype_card, hF, show 2 - 1 = 1 from rfl, pow_one] at h1

theorem eq_one_or_eq_elt (hF : Nat.card F = 2) {γ : Fin k → ℤ} {r : RootSubgroupIndex k}
    (hr : stdVec r = toStd k γ) {x : StatedSp k F} (hx : x ∈ rootGroup k F γ) :
    x = 1 ∨ x = SpExtras.elt r 1 := by
  obtain ⟨c, rfl⟩ := (SpExtras.mem_rootGroup_iff hr).mp hx
  rcases eq_zero_or_eq_one_of_card hF c with rfl | rfl
  · exact .inl (SpExtras.elt_zero r)
  · exact .inr rfl

theorem single_inl_inl (i j : Fin k) (c : F) :
    single (Sum.inl i : Fin k ⊕ Fin k) (Sum.inl j : Fin k ⊕ Fin k) c =
      fromBlocks (single i j c) 0 0 0 := by
  ext (a | a) (b | b) <;> simp [single_apply]

theorem single_inl_inr (i j : Fin k) (c : F) :
    single (Sum.inl i : Fin k ⊕ Fin k) (Sum.inr j : Fin k ⊕ Fin k) c =
      fromBlocks 0 (single i j c) 0 0 := by
  ext (a | a) (b | b) <;> simp [single_apply]

theorem single_inr_inl (i j : Fin k) (c : F) :
    single (Sum.inr i : Fin k ⊕ Fin k) (Sum.inl j : Fin k ⊕ Fin k) c =
      fromBlocks 0 0 (single i j c) 0 := by
  ext (a | a) (b | b) <;> simp [single_apply]

theorem single_inr_inr (i j : Fin k) (c : F) :
    single (Sum.inr i : Fin k ⊕ Fin k) (Sum.inr j : Fin k ⊕ Fin k) c =
      fromBlocks 0 0 0 (single i j c) := by
  ext (a | a) (b | b) <;> simp [single_apply]

theorem elt_positiveLong (i : Fin k) :
    SpExtras.elt (.positiveLong i) (1 : F) = longPos i := by
  refine ext_mat ?_
  rw [SpExtras.mat_elt, one_smul, mat_longPos]
  simp only [SpExtras.E, single_inl_inr]
  rw [← fromBlocks_one, fromBlocks_add]
  simp

theorem elt_negativeLong (i : Fin k) :
    SpExtras.elt (.negativeLong i) (1 : F) = longNeg i := by
  refine ext_mat ?_
  rw [SpExtras.mat_elt, one_smul, mat_longNeg]
  simp only [SpExtras.E, single_inr_inl]
  rw [← fromBlocks_one, fromBlocks_add]
  simp

theorem elt_difference [CharP F 2] {i j : Fin k} (hij : i ≠ j) :
    SpExtras.elt (.difference i j hij) (1 : F) = levZ (elemTv i j) := by
  refine ext_mat ?_
  rw [SpExtras.mat_elt, one_smul, mat_levZ_elemTv hij]
  simp only [SpExtras.E, single_inl_inl, single_inr_inr, sub_eq_add_neg, fromBlocks_neg,
    fromBlocks_add, neg_zero, add_zero, single_neg, CharTwo.neg_eq]
  rw [← fromBlocks_one, fromBlocks_add]
  simp

section CharTwo

variable [CharP F 2]

theorem rootGroup_sup_le_of_levZ_le (hF : Nat.card F = 2) {H : Subgroup (StatedSp k F)}
    (hL : (levZ : SpecialLinearGroup (Fin k) (ZMod 2) →* StatedSp k F).range ≤ H)
    {m : Fin k} (hm : m.val + 1 = k) (hp : longPos m ∈ H) (hn : longNeg m ∈ H) (i : Fin k) :
    rootGroup k F (Pi.single i 1) ⊔ rootGroup k F (-Pi.single i 1) ≤ H := by
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · by_cases hi : i.val + 1 < k
    · have hij : i ≠ ⟨i.val + 1, hi⟩ := SpExtras.ne_succ' hi
      have hr : stdVec (.difference i ⟨i.val + 1, hi⟩ hij) = toStd k (Pi.single i 1) :=
        (SpExtras.toStd_single_of_lt' hi).symm
      rcases eq_one_or_eq_elt hF hr hx with rfl | rfl
      · exact H.one_mem
      · rw [elt_difference]
        exact hL ⟨_, rfl⟩
    · obtain rfl : i = m := Fin.ext (by omega)
      have hr : stdVec (.positiveLong i) = toStd k (Pi.single i 1) :=
        (SpExtras.toStd_single_of_not_lt' hi).symm
      rcases eq_one_or_eq_elt hF hr hx with rfl | rfl
      · exact H.one_mem
      · rwa [elt_positiveLong]
  · by_cases hi : i.val + 1 < k
    · have hij : (⟨i.val + 1, hi⟩ : Fin k) ≠ i := (SpExtras.ne_succ' hi).symm
      have hr : stdVec (.difference ⟨i.val + 1, hi⟩ i hij) = toStd k (-Pi.single i 1) := by
        rw [SpExtras.toStd_neg', SpExtras.toStd_single_of_lt' hi, neg_sub]
        rfl
      rcases eq_one_or_eq_elt hF hr hx with rfl | rfl
      · exact H.one_mem
      · rw [elt_difference]
        exact hL ⟨_, rfl⟩
    · obtain rfl : i = m := Fin.ext (by omega)
      have hr : stdVec (.negativeLong i) = toStd k (-Pi.single i 1) := by
        rw [SpExtras.toStd_neg', SpExtras.toStd_single_of_not_lt' hi]
        rfl
      rcases eq_one_or_eq_elt hF hr hx with rfl | rfl
      · exact H.one_mem
      · rwa [elt_negativeLong]

theorem eq_top_of_levZ_le (hF : Nat.card F = 2) {H : Subgroup (StatedSp k F)}
    (hL : (levZ : SpecialLinearGroup (Fin k) (ZMod 2) →* StatedSp k F).range ≤ H)
    {m : Fin k} (hm : m.val + 1 = k) (hp : longPos m ∈ H) (hn : longNeg m ∈ H) : H = ⊤ := by
  rw [eq_top_iff, ← CFSG.ClassicalInvolution.WeakCT.iSup_rankOne_eq_top_of_ct
    (D := rootDatum k F) (isCTGroupDatum k F) rfl]
  exact iSup_le fun i => rootGroup_sup_le_of_levZ_le hF hL hm hp hn i

@[expose] noncomputable def dZero (p m : Fin k) : StatedSp k F :=
  longPos m * levZ (elemTv p m) * (longPos m)⁻¹

theorem sup_zpowers_dZero_eq_top (hF : Nat.card F = 2) {p m : Fin k} (hpm : p ≠ m)
    (hm : m.val + 1 = k) :
    (levZ : SpecialLinearGroup (Fin k) (ZMod 2) →* StatedSp k F).range ⊔
        Subgroup.zpowers (sumPos p m) ⊔ Subgroup.zpowers (sumNeg p m) ⊔
        Subgroup.zpowers (dZero p m) = ⊤ := by
  set H := (levZ : SpecialLinearGroup (Fin k) (ZMod 2) →* StatedSp k F).range ⊔
    Subgroup.zpowers (sumPos p m) ⊔ Subgroup.zpowers (sumNeg p m) ⊔
    Subgroup.zpowers (dZero p m) with hH
  have hL : (levZ : SpecialLinearGroup (Fin k) (ZMod 2) →* StatedSp k F).range ≤ H :=
    le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hlev : ∀ g, (levZ g : StatedSp k F) ∈ H := fun g => hL ⟨g, rfl⟩
  have ha : (sumPos p m : StatedSp k F) ∈ H := Subgroup.mem_sup_left
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have hb : (sumNeg p m : StatedSp k F) ∈ H :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hd : (dZero p m : StatedSp k F) ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have htp : (longPos p : StatedSp k F) ∈ H := by
    have e : (longPos p : StatedSp k F) = (levZ (elemTv p m) * sumPos p m)⁻¹ * dZero p m := by
      rw [dZero, longPos_conj_levZ hpm]
      group
    rw [e]
    exact H.mul_mem (H.inv_mem (H.mul_mem (hlev _) ha)) hd
  have htm : (longPos m : StatedSp k F) ∈ H := by
    have e : (longPos m : StatedSp k F) = (levZ (elemTv m p) * sumPos p m)⁻¹ *
        (longPos p * levZ (elemTv m p) * (longPos p)⁻¹) := by
      rw [longPos_conj_levZ hpm.symm, sumPos_comm p m]
      group
    rw [e]
    exact H.mul_mem (H.inv_mem (H.mul_mem (hlev _) ha))
      (H.mul_mem (H.mul_mem htp (hlev _)) (H.inv_mem htp))
  have hnm : (longNeg m : StatedSp k F) ∈ H := by
    have e : (longNeg m : StatedSp k F) = (levZ (elemTv p m) * sumNeg p m)⁻¹ *
        (longPos p * sumNeg p m * (longPos p)⁻¹) := by
      rw [sumNeg_comm p m, longPos_conj_sumNeg hpm.symm]
      group
    rw [e]
    exact H.mul_mem (H.inv_mem (H.mul_mem (hlev _) hb))
      (H.mul_mem (H.mul_mem htp hb) (H.inv_mem htp))
  exact eq_top_of_levZ_le hF hL hm htm hnm

end CharTwo

end CFSG.LargeExtraspecial.A2Mod.FrC
