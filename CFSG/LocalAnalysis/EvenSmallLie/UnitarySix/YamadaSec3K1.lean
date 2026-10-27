module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Levi
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Link
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsSigma

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open Matrix CFSG.Fischer CFSG.ClassicalInvolution.WeakCT CFSG.EvenSmallLie.UnitarySix.YamadaEnd
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

@[expose] noncomputable def lowerU4 : Subgroup SL(4, F4) :=
  (unitriangular 4 F4).comap
    (conjSL (antiDiagN F4 4) (antiDiagN F4 4) (antiDiagN_mul_self F4 4)).toMonoidHom

theorem isPGroup_lowerU4 : IsPGroup 2 lowerU4 := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := F4) 2 (n := 4) (by norm_num)
  intro g
  set c := (conjSL (antiDiagN F4 4) (antiDiagN F4 4) (antiDiagN_mul_self F4 4)).toMonoidHom
  have hg : c (g : SL(4, F4)) ∈ (P : Subgroup SL(4, F4)) := by
    rw [hP]
    exact g.2
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨_, hg⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 := congrArg Subtype.val hk
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
  rw [← MonoidHom.map_pow] at h1
  have hinj : Function.Injective c :=
    (conjSL (antiDiagN F4 4) (antiDiagN F4 4) (antiDiagN_mul_self F4 4)).injective
  simpa using hinj (h1.trans (map_one c).symm)

theorem transvection_mem_unitriangular {n : ℕ} {i j : Fin n} (hij : i < j) (c : F4) :
    SpecialLinearGroup.transvection hij.ne c ∈ unitriangular n F4 := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    have h1 : a ≠ b := ne_of_gt hba
    have h2 : ¬ (i = a ∧ j = b) := fun h => by
      rw [← h.1, ← h.2] at hba
      exact absurd hba (not_lt.2 hij.le)
    simp [h1, h2]
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.single_apply]
    have h2 : ¬ (i = a ∧ j = a) := fun h => hij.ne (h.1.trans h.2.symm)
    simp [h2]

theorem pstd_le_lowerU4 : pstd F4 ≤ lowerU4 := by
  rw [pstd, Subgroup.closure_le]
  rintro _ ⟨i, j, h, c, hji, rfl⟩
  show conjSL (antiDiagN F4 4) (antiDiagN F4 4) (antiDiagN_mul_self F4 4)
    (SpecialLinearGroup.transvection h c) ∈ unitriangular 4 F4
  rw [conjSL_antiDiagN_transvection]
  exact transvection_mem_unitriangular (Fin.rev_lt_rev.2 hji) c

@[expose] noncomputable def psiChi :
    msigma F4 →* Equiv.Perm (Fin 693) :=
  psi0.comp chi0


theorem psiChi_eq {m : msigma F4} {k : ℕ} (hk : k < 18) (h : chi0 m = yamGen k) :
    psiChi m = wP [k] := by
  rw [psiChi, MonoidHom.comp_apply, h, psi0_yamGen hk, wP_single]

theorem chK1_le_range : chK1.grp ≤ psiChi.range := grp_le fun w hw => by
  simp only [chK1, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, psiChi_eq (by norm_num) chi0_mx2_one⟩
  · exact ⟨_, psiChi_eq (by norm_num) chi0_mx2_ω⟩
  · exact ⟨_, psiChi_eq (by norm_num) chi0_mx3⟩
  · exact ⟨_, psiChi_eq (by norm_num) chi0_sY02⟩
  · exact ⟨_, psiChi_eq (by norm_num) chi0_sY1⟩

theorem card_msigmaF4 : Nat.card (msigma F4) = 25920 :=
  YamadaInputs.card_msigma (by rw [Nat.card_eq_fintype_card, F4.card])

theorem range_psiChi : psiChi.range = chK1.grp := by
  refine (Subgroup.eq_of_le_of_card_ge chK1_le_range ?_).symm
  rw [card_chK1, ← card_msigmaF4]
  exact Nat.le_of_dvd (Nat.card_pos) (Subgroup.card_range_dvd psiChi)

theorem psiChi_injective : Function.Injective psiChi := by
  have hcard : Nat.card psiChi.range = Nat.card (msigma F4) := by
    rw [range_psiChi, card_chK1, card_msigmaF4]
  have hbij := Function.Surjective.bijective_of_nat_card_le psiChi.rangeRestrict_surjective
    hcard.ge
  intro a b hab
  exact hbij.1 (Subtype.ext hab)

@[expose] noncomputable def mPstd : Subgroup (msigma F4) := (pstd F4).comap (msigma F4).subtype

theorem isPGroup_mPstd : IsPGroup 2 mPstd := by
  intro g
  obtain ⟨k, hk⟩ := isPGroup_lowerU4 ⟨_, pstd_le_lowerU4 g.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun x : lowerU4 => (x : SL(4, F4))) hk
  simpa using this

theorem lower_mem_pstd {i j : Fin 4} (h : i ≠ j) (hji : j < i) (c : F4) :
    SpecialLinearGroup.transvection h c ∈ pstd F4 :=
  Subgroup.subset_closure ⟨i, j, h, c, hji, rfl⟩

theorem chT1_le_map : chT1.grp ≤ mPstd.map psiChi := grp_le fun w hw => by
  simp only [chT1, List.mem_cons, List.not_mem_nil, or_false] at hw
  have h2 : ∀ a : F4, mx2 a ∈ mPstd := fun a => by
    show SpecialLinearGroup.transvection (by decide : (1 : Fin 4) ≠ 0) a *
        SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 2) (a ^ 2) ∈ pstd F4
    exact mul_mem (lower_mem_pstd _ (by decide) a) (lower_mem_pstd _ (by decide) _)
  have h5 : ∀ a : F4, mx5 a ∈ mPstd := fun a => by
    show SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 0) a *
        SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 1) (a ^ 2) ∈ pstd F4
    exact mul_mem (lower_mem_pstd _ (by decide) a) (lower_mem_pstd _ (by decide) _)
  have h3 : mx3 ∈ mPstd := by
    show SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 1) 1 ∈ pstd F4
    exact lower_mem_pstd _ (by decide) _
  have h7 : mx7 ∈ mPstd := by
    show SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 0) 1 ∈ pstd F4
    exact lower_mem_pstd _ (by decide) _
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, h2 1, psiChi_eq (by norm_num) chi0_mx2_one⟩
  · exact ⟨_, h2 F4.ω, psiChi_eq (by norm_num) chi0_mx2_ω⟩
  · exact ⟨_, h3, psiChi_eq (by norm_num) chi0_mx3⟩
  · exact ⟨_, h5 1, psiChi_eq (by norm_num) chi0_mx5_one⟩
  · exact ⟨_, h5 F4.ω, psiChi_eq (by norm_num) chi0_mx5_ω⟩
  · exact ⟨_, h7, psiChi_eq (by norm_num) chi0_mx7⟩

theorem map_mPstd : mPstd.map psiChi = chT1.grp := by
  symm
  refine Subgroup.eq_of_le_of_card_ge chT1_le_map ?_
  rw [card_chT1]
  have hP : IsPGroup 2 (mPstd.map psiChi) := isPGroup_mPstd.map psiChi
  have hle : mPstd.map psiChi ≤ chK1.grp := by
    rw [← range_psiChi]
    exact Subgroup.map_le_range psiChi mPstd
  have hdvd : Nat.card (mPstd.map psiChi) ∣ 25920 := by
    rw [← card_chK1]
    exact Subgroup.card_dvd_of_le hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card.1 hP)
  rw [hm] at hdvd ⊢
  by_contra hcon
  have h7 : 7 ≤ m := by
    by_contra h
    have h6 : 2 ^ m ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact hcon (h6.trans (by norm_num))
  have : 2 ^ 7 ∣ 25920 := (Nat.pow_dvd_pow 2 h7).trans hdvd
  norm_num at this

theorem psiChi_mem_T1 {A : msigma F4} (hA : (A : SL(4, F4)) ∈ pstd F4) :
    psiChi A ∈ chT1.grp := by
  rw [← map_mPstd]
  exact ⟨A, hA, rfl⟩

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
