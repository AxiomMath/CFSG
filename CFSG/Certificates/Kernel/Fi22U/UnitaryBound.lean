
module

public import CFSG.RankThree.Native.Fi22UActionBase
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPairOrbits

public noncomputable section

namespace CFSG.RankThree.Native.Fi22U.Bound

open CFSG.Monster.B.Fischer CFSG.Fischer CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.LinearGroups Matrix
open scoped Pointwise

theorem find_smul {c : F4} (hc : c ≠ 0) (v : Fin 6 → F4) :
    (List.finRange 6).find? (fun i => decide ((c • v) i ≠ 0)) =
      (List.finRange 6).find? (fun i => decide (v i ≠ 0)) := by
  congr 1
  funext i
  simp [Pi.smul_apply, smul_eq_mul, hc]

theorem normalize_zero : fi22Normalize 0 = 0 := by
  unfold fi22Normalize
  split
  · simp
  · rfl

theorem normalize_smul (c : F4) (v : Fin 6 → F4) (hc : c ≠ 0) :
    fi22Normalize (c • v) = fi22Normalize v := by
  unfold fi22Normalize
  rw [find_smul hc]
  split
  · funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_inv]
    calc c⁻¹ * (v _)⁻¹ * (c * v j) = (c⁻¹ * c) * ((v _)⁻¹ * v j) := by ring
      _ = (v _)⁻¹ * v j := by rw [inv_mul_cancel₀ hc, one_mul]
  · rename_i h
    have hv : v = 0 := by
      funext i
      have := List.find?_eq_none.1 h i (List.mem_finRange i)
      simpa using this
    rw [hv, smul_zero]

theorem normalize_normalize (v : Fin 6 → F4) : fi22Normalize (fi22Normalize v) = fi22Normalize v := by
  by_cases hv : v = 0
  · rw [hv, normalize_zero, normalize_zero]
  · obtain ⟨c, hc, he⟩ := fi22Normalize_eq_smul hv
    rw [he, normalize_smul c v hc, he]

@[expose] def UFacts : Prop :=
  (∀ k < 693, fi22UnitaryPoint k ≠ 0 ∧
      fi22Herm (fi22UnitaryPoint k) (fi22UnitaryPoint k) = 0 ∧
      fi22Normalize (fi22UnitaryPoint k) = fi22UnitaryPoint k) ∧
    (∀ j < 693, ∀ k < 693, j < k → fi22LexLt (fi22UnitaryPoint j) (fi22UnitaryPoint k)) ∧
    (Finset.univ.filter fun v : Fin 6 → F4 =>
      v ≠ 0 ∧ fi22Herm v v = 0 ∧ fi22Normalize v = v).card = 693 ∧
    (∀ v : Fin 6 → F4, fi22Normalize (fi22Normalize v) = fi22Normalize v) ∧
    (∀ (c : F4) (v : Fin 6 → F4), c ≠ 0 → fi22Normalize (c • v) = fi22Normalize v) ∧
    (∀ k < 46, fi22Herm (fi22TransvectionVector k) (fi22TransvectionVector k) = 0) ∧
    (∀ k < 46, ∀ j < 693, fi22UnitaryPoint ((fi22OuterArr693 (15 + k))[j]!) =
      fi22Normalize (fi22Tv (fi22TransvectionVector k) (fi22UnitaryPoint j)))

variable (h : UFacts)
include h

theorem B_ne_zero (k : Fin 693) : fi22UnitaryPoint k ≠ 0 := (h.1 k k.2).1

theorem B_iso (k : Fin 693) : fi22Herm (fi22UnitaryPoint k) (fi22UnitaryPoint k) = 0 :=
  (h.1 k k.2).2.1

theorem B_norm (k : Fin 693) : fi22Normalize (fi22UnitaryPoint k) = fi22UnitaryPoint k :=
  (h.1 k k.2).2.2

theorem B_injective : Function.Injective fun k : Fin 693 => fi22UnitaryPoint k := by
  intro j k hjk
  simp only at hjk
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hl | hl
  · have := h.2.1 j j.2 k k.2 hl
    rw [hjk] at this
    exact fi22LexLt_irrefl _ this
  · have := h.2.1 k k.2 j j.2 hl
    rw [hjk] at this
    exact fi22LexLt_irrefl _ this

theorem image_B : Finset.univ.image (fun k : Fin 693 => fi22UnitaryPoint k) = fi22NormIso := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨B_ne_zero h k, B_iso h k, B_norm h k⟩
  · rw [Finset.card_image_of_injective _ (B_injective h), Finset.card_univ, Fintype.card_fin]
    exact h.2.2.1.le

theorem exists_B_eq {v : Fin 6 → F4} (hv : v ≠ 0) (hiso : fi22Herm v v = 0) :
    ∃ k : Fin 693, fi22UnitaryPoint k = fi22Normalize v := by
  obtain ⟨c, hc, he⟩ := fi22Normalize_eq_smul hv
  have hmem : fi22Normalize v ∈ fi22NormIso := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, h.2.2.2.1 v⟩
    · rw [he]
      exact smul_ne_zero hc hv
    · rw [he, fi22Herm_smul, hiso, mul_zero]
  rw [← image_B h] at hmem
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hmem
  exact ⟨k, hk⟩

theorem span_B_mem (k : Fin 693) :
    Submodule.span F4 {fi22UnitaryPoint k} ∈ isotropicLines fi22U_fieldData 6 :=
  span_singleton_mem_isotropicLines fi22U_fieldData (B_ne_zero h k)
    (by rw [stdHermForm_eq_fi22Herm]; exact B_iso h k)

@[expose] def lineOf (k : Fin 693) : isotropicLines fi22U_fieldData 6 := ⟨_, span_B_mem h k⟩

theorem lineOf_injective : Function.Injective (lineOf h) := by
  intro j k hjk
  have hspan : Submodule.span F4 {fi22UnitaryPoint j} = Submodule.span F4 {fi22UnitaryPoint k} :=
    congrArg Subtype.val hjk
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (hspan ▸ Submodule.mem_span_singleton_self (fi22UnitaryPoint j))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact B_ne_zero h j hc.symm
  apply B_injective h
  simp only
  rw [← B_norm h j, ← hc, h.2.2.2.2.1 c _ hc0, B_norm h k]

theorem lineOf_surjective : Function.Surjective (lineOf h) := by
  rintro ⟨L, hL⟩
  obtain ⟨a, ha0, ha, rfl⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_eq_span_of_mem_isotropicLines hL
  rw [stdHermForm_eq_fi22Herm] at ha
  obtain ⟨k, hk⟩ := exists_B_eq h ha0 ha
  refine ⟨k, Subtype.ext ?_⟩
  change Submodule.span F4 {fi22UnitaryPoint k} = Submodule.span F4 {a}
  rw [hk, span_fi22Normalize ha0]

@[expose] def lineEquiv : Fin 693 ≃ isotropicLines fi22U_fieldData 6 :=
  Equiv.ofBijective (lineOf h) ⟨lineOf_injective h, lineOf_surjective h⟩

theorem lineEquiv_apply (k : Fin 693) :
    (lineEquiv h k : Submodule F4 (Fin 6 → F4)) = Submodule.span F4 {fi22UnitaryPoint k} := rfl

@[expose] def rho : StatedSU 6 (2 ^ 1) F4 →* Equiv.Perm (Fin 693) :=
  ((lineEquiv h).symm.permCongrHom).toMonoidHom.comp
    (MulAction.toPermHom (StatedSU 6 (2 ^ 1) F4) (isotropicLines fi22U_fieldData 6))

theorem lineEquiv_rho (g : StatedSU 6 (2 ^ 1) F4) (k : Fin 693) :
    lineEquiv h (rho h g k) = g • lineEquiv h k := by
  simp [rho, Equiv.permCongrHom_coe, Equiv.permCongr_apply]

theorem rho_spec (g : StatedSU 6 (2 ^ 1) F4) (k : Fin 693) :
    fi22UnitaryPoint (rho h g k) =
      fi22Normalize (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ fi22UnitaryPoint k) := by
  set w := ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ fi22UnitaryPoint k with hw
  have hw0 : w ≠ 0 := mulVec_ne_zero' _ (B_ne_zero h k)
  have hwiso : fi22Herm w w = 0 := by rw [hw, fi22Herm_smul_smul, B_iso h]
  obtain ⟨m, hm⟩ := exists_B_eq h hw0 hwiso
  have : rho h g k = m := by
    apply (lineEquiv h).injective
    apply Subtype.ext
    rw [lineEquiv_rho, SubMulAction.val_smul, lineEquiv_apply, lineEquiv_apply, smul_span, hm,
      span_fi22Normalize hw0]
  rw [this, hm]

theorem rho_eq_iff (g : StatedSU 6 (2 ^ 1) F4) (k m : Fin 693) :
    rho h g k = m ↔ fi22UnitaryPoint m =
      fi22Normalize (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ fi22UnitaryPoint k) := by
  rw [← rho_spec h]
  exact ⟨fun e => by rw [e], fun e => (B_injective h e).symm⟩

theorem ker_rho :
    (rho h).ker = (StatedScalars (Fin 6) F4).subgroupOf (StatedSU 6 (2 ^ 1) F4) := by
  refine (MonoidHom.ker_mulEquiv_comp
    (MulAction.toPermHom (StatedSU 6 (2 ^ 1) F4) (isotropicLines fi22U_fieldData 6))
    (lineEquiv h).symm.permCongrHom).trans ?_
  rw [unitary_isotropic_kernel fi22U_fieldData (by norm_num),
    unitaryScalars_eq fi22U_fieldData (by norm_num)]

theorem card_range_rho : Nat.card (rho h).range = 9196830720 := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (rho h)).toEquiv,
    ← card_statedProj_fi22S]
  exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq (ker_rho h)).toEquiv

theorem rho_eq_seed {k : ℕ} (hk : k < 46)
    {g : StatedSU 6 (2 ^ 1) F4}
    (hg : ∀ x, ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ x =
      fi22Tv (fi22TransvectionVector k) x) :
    rho h g = fi22OuterPerm693 (15 + k) := by
  ext j
  have hj := rep_fi22OuterPerm693 (L := 15 + k) (by omega) j
  have hlt : (fi22OuterArr693 (15 + k))[(j : ℕ)]! < 693 := hj ▸ (fi22OuterPerm693 (15 + k) j).2
  have key : rho h g j = ⟨(fi22OuterArr693 (15 + k))[(j : ℕ)]!, hlt⟩ := by
    rw [rho_eq_iff, hg]
    exact h.2.2.2.2.2.2 k hk j j.2
  rw [key]
  exact hj

theorem card_closure_le :
    Nat.card (Subgroup.closure (Set.range fun j : Fin 46 =>
      permOfArr 693 (fi22OuterStrong693 2)[j.val]!)) ≤ 9196830720 := by
  have hle : Subgroup.closure (Set.range fun j : Fin 46 =>
      permOfArr 693 (fi22OuterStrong693 2)[j.val]!) ≤ (rho h).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨t, ht⟩ := exists_mem_fi22S_tv (h.2.2.2.2.2.1 i i.2)
    refine ⟨t, ?_⟩
    rw [rho_eq_seed h i.2 ht, fi22OuterPerm693]
    change _ = permOfArr 693 (fi22OuterStrong693 2)[(i : ℕ)]!
    rw [fi22OuterStrong693_two_get (by omega)]
  rw [← card_range_rho h]
  exact Subgroup.card_le_of_le hle

end CFSG.RankThree.Native.Fi22U.Bound

end
