
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43ModelBase

public import Certificates.Certificate26010
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.LieType.Multipliers.U43 CFSG.Sporadic.SmallOddCore
open scoped Pointwise

section Tables

theorem checks : permCheck = true ∧ normCheck = true ∧ relCheck = true ∧ cosetCheck = true ∧
    multCheck = true ∧ repCheck = true := Certificates.certificate26010

theorem isInvA_of_mem {t : Array ℕ} (ht : t ∈ deltaArr :: phiArr :: reps) :
    isInvA 820 t (invCand 820 t) = true := by
  have h := checks.1
  simp only [permCheck, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 t ht

theorem isInvA_tArr {k : ℕ} (hk : k < 8) :
    isInvA 820 (tArr k) (invCand 820 (tArr k)) = true := by
  have h := checks.1
  simp only [permCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.2 k hk

theorem rep_dP : Rep 820 deltaArr dP :=
  (rep_permOfArr (isInvA_of_mem (by simp))).1

theorem rep_dP_inv : Rep 820 (invCand 820 deltaArr) dP⁻¹ :=
  (rep_permOfArr (isInvA_of_mem (by simp))).2

theorem rep_fP : Rep 820 phiArr fP :=
  (rep_permOfArr (isInvA_of_mem (by simp))).1

theorem rep_fP_inv : Rep 820 (invCand 820 phiArr) fP⁻¹ :=
  (rep_permOfArr (isInvA_of_mem (by simp))).2

theorem rep_tArr (k : ℕ) : Rep 820 (tArr k) (tP k) :=
  rep_compA (rep_powA rep_fP _) (rep_powA rep_dP _)

theorem rep_tArr_inv {k : ℕ} (hk : k < 8) : Rep 820 (invCand 820 (tArr k)) (tP k)⁻¹ :=
  rep_inv_of_isInvA (rep_tArr k) (isInvA_tArr hk)

theorem rep_rP {j : ℕ} (hj : j < 9) : Rep 820 reps[j]! (rP j) := by
  have hmem : reps[j]! ∈ deltaArr :: phiArr :: reps :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [reps] using hj)]
      exact List.getElem_mem _))
  exact (rep_permOfArr (isInvA_of_mem hmem)).1

theorem normCheck_spec {u : Array ℕ} {U : Equiv.Perm (Fin 820)}
    (hu : u ∈ [deltaArr, phiArr]) (hU : Rep 820 u U) (hUi : Rep 820 (invCand 820 u) U⁻¹) :
    U * psi xElt * U⁻¹ ∈ P ∧ U * psi yElt * U⁻¹ ∈ P := by
  have h := checks.2.1
  simp only [normCheck, List.all_eq_true] at h
  have h1 := h u hu
  simp only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false] at h1
  exact ⟨(inP_iff (rep_compA hU (rep_compA rep_tabA hUi))).1 h1.1,
    (inP_iff (rep_compA hU (rep_compA rep_tabB hUi))).1 h1.2⟩

theorem dP_mem_normalizer :
    dP ∈ normalizer (P : Set (Equiv.Perm (Fin 820))) := by
  obtain ⟨h1, h2⟩ := normCheck_spec (u := deltaArr) (by simp) rep_dP rep_dP_inv
  exact mem_normalizer_P_of_gens h1 h2

theorem fP_mem_normalizer :
    fP ∈ normalizer (P : Set (Equiv.Perm (Fin 820))) := by
  obtain ⟨h1, h2⟩ := normCheck_spec (u := phiArr) (by simp) rep_fP rep_fP_inv
  exact mem_normalizer_P_of_gens h1 h2

theorem tP_mem_normalizer (k : ℕ) :
    tP k ∈ normalizer (P : Set (Equiv.Perm (Fin 820))) :=
  mul_mem (pow_mem fP_mem_normalizer _) (pow_mem dP_mem_normalizer _)

theorem tP_mul {k k' : ℕ} (hk : k < 8) (hk' : k' < 8) : ∃ k'' < 8, tP k * tP k' = tP k'' := by
  have h := checks.2.2.2.2.1
  simp only [multCheck, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨k'', hk'', he⟩ := h k hk k' hk'
  exact ⟨k'', hk'', (eqA_iff (rep_compA (rep_tArr k) (rep_tArr k')) (rep_tArr k'')).1 he⟩

theorem tP_pow {k : ℕ} (hk : k < 8) (n : ℕ) : ∃ k' < 8, tP k ^ n = tP k' := by
  induction n with
  | zero => exact ⟨0, by norm_num, by simp [tP_zero]⟩
  | succ n ih =>
    obtain ⟨k', hk', h⟩ := ih
    obtain ⟨k'', hk'', h'⟩ := tP_mul hk' hk
    exact ⟨k'', hk'', by rw [pow_succ, h, h']⟩

theorem tP_inv {k : ℕ} (hk : k < 8) : ∃ k' < 8, (tP k)⁻¹ = tP k' := by
  obtain ⟨k', hk', h⟩ := tP_pow hk (orderOf (tP k) - 1)
  refine ⟨k', hk', ?_⟩
  rw [← h]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos _), pow_orderOf_eq_one]

theorem tP_mul_inv_not_mem {k k' : ℕ} (hk : k < 8)
    (hk' : k' < 8) (hne : k ≠ k') : tP k * (tP k')⁻¹ ∉ P := by
  have h := checks.2.2.2.1
  simp only [cosetCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at h
  intro hmem
  have h1 := (inP_iff (rep_compA (rep_tArr k) (rep_tArr_inv hk'))).2 hmem
  rcases h k hk k' hk' with h2 | h2
  · exact hne h2
  · rw [h1] at h2
    exact Bool.noConfusion h2

@[expose] noncomputable def Dgrp : Subgroup (Equiv.Perm (Fin 820)) where
  carrier := {x | ∃ k < 8, x = tP k}
  one_mem' := ⟨0, by norm_num, tP_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩
    obtain ⟨k'', hk'', h⟩ := tP_mul hk hk'
    exact ⟨k'', hk'', h⟩
  inv_mem' := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨k', hk', h⟩ := tP_inv hk
    exact ⟨k', hk', h⟩

theorem Dgrp_le_normalizer :
    Dgrp ≤ normalizer (P : Set (Equiv.Perm (Fin 820))) := by
  rintro _ ⟨k, -, rfl⟩
  exact tP_mem_normalizer k

@[expose] noncomputable def R : Subgroup (Equiv.Perm (Fin 820)) := P ⊔ Dgrp

theorem mem_R_iff {x : Equiv.Perm (Fin 820)} :
    x ∈ R ↔ ∃ g ∈ P, ∃ k < 8, x = g * tP k := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left P Dgrp Dgrp_le_normalizer
  have h2 : x ∈ (↑(P ⊔ Dgrp) : Set (Equiv.Perm (Fin 820))) ↔
      x ∈ (P : Set (Equiv.Perm (Fin 820))) * (Dgrp : Set (Equiv.Perm (Fin 820))) := by rw [h]
  rw [R]
  refine (h2.trans Set.mem_mul).trans ?_
  constructor
  · rintro ⟨g, hg, t, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨g, hg, k, hk, rfl⟩
  · rintro ⟨g, hg, k, hk, rfl⟩
    exact ⟨g, hg, tP k, ⟨k, hk, rfl⟩, rfl⟩

theorem P_le_R : P ≤ R := le_sup_left

theorem tP_mem_R {k : ℕ} (hk : k < 8) : tP k ∈ R :=
  mem_R_iff.2 ⟨1, P.one_mem, k, hk, by simp⟩

theorem disjoint_P_Dgrp : Disjoint P Dgrp := by
  rw [Subgroup.disjoint_def]
  rintro x hxP ⟨k, hk, rfl⟩
  by_cases h0 : k = 0
  · rw [h0, tP_zero]
  · exfalso
    have := tP_mul_inv_not_mem hk (by norm_num : 0 < 8) h0
    rw [tP_zero, inv_one, mul_one] at this
    exact this hxP

theorem card_Dgrp : Nat.card Dgrp = 8 := by
  have e : Fin 8 ≃ Dgrp := Equiv.ofBijective (fun k => ⟨tP k, k, k.2, rfl⟩) ⟨fun k k' h => ?_, ?_⟩
  · rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
  · by_contra hne
    have h1 : tP k = tP k' := congrArg Subtype.val h
    exact tP_mul_inv_not_mem k.2 k'.2 (fun h => hne (Fin.ext h))
      (by rw [h1, mul_inv_cancel]; exact P.one_mem)
  · rintro ⟨_, k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem card_R : Nat.card R = 8 * Nat.card P := by
  rw [R, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P Dgrp
    Dgrp_le_normalizer disjoint_P_Dgrp, card_Dgrp, mul_comm]

theorem conj_mem_P {x : Equiv.Perm (Fin 820)} (hx : x ∈ R)
    {p : Equiv.Perm (Fin 820)} (hp : p ∈ P) : x * p * x⁻¹ ∈ P := by
  obtain ⟨g, hg, k, hk, rfl⟩ := mem_R_iff.1 hx
  have h1 := (mem_normalizer_iff.1 (tP_mem_normalizer k) p).1 hp
  have h2 := P.mul_mem (P.mul_mem hg h1) (P.inv_mem hg)
  simpa [mul_assoc] using h2

end Tables

end CFSG.EvenSporadicStandard.M24Std.CU43
