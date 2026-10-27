module

public import CFSG.LargeExtraspecial.SMod20AutGen
import all CFSG.Fischer.F4

public section

namespace CFSG.LargeExtraspecial.SMod20.Aut

open CFSG.Fischer CFSG.F4.Native CFSG.SmithE Matrix Module

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

theorem diagonal_const_mulVec (c : F4) (x : W) : (diagonal fun _ : Fin 6 => c) *ᵥ x = c • x := by
  funext k
  rw [mulVec_diagonal]
  rfl

theorem isIsom_scalar (c : F4) (hc : c ≠ 0) :
    IsIsom ((Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 c hc) : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4) := by
  intro x y
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_apply, diagonal_const_mulVec,
    diagonal_const_mulVec, herm_eq_std, herm_eq_std]
  rw [hermStd_smul_left, hermStd_smul_right, ← mul_assoc]
  have h := cube_eq_one c hc
  rw [show c * c ^ 2 = c * c * c by ring, h, one_mul]

@[expose] noncomputable def scalGU (c : F4) (hc : c ≠ 0) : GU0 :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 c hc), isIsom_scalar c hc⟩

theorem scalGU_mulVec (c : F4) (hc : c ≠ 0) (x : W) :
    (((scalGU c hc : GU0) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ x = c • x := by
  change ((Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 c hc) : GL (Fin 6) F4) :
    Matrix (Fin 6) (Fin 6) F4) *ᵥ x = c • x
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_apply, diagonal_const_mulVec]

theorem piGU_scalGU (c : F4) (hc : c ≠ 0) :
    piGU (scalGU c hc) = 1 := by
  ext p
  rw [Equiv.Perm.one_apply]
  change ((scalGU c hc) • p).val = p.val
  rw [smul_val, scalGU_mulVec, ptIdx_smul hc, ptIdx_uVec ptsFacts p.2]

theorem F4_cases : ∀ x : F4, x = 0 ∨ x = 1 ∨ x = F4.ω ∨ x = F4.ω + 1 := by decide

theorem eq_self_of_omega (φ : F4 ≃+* F4) (h : φ F4.ω = F4.ω) (x : F4) : φ x = x := by
  rcases F4_cases x with rfl | rfl | rfl | rfl
  · exact map_zero φ
  · exact map_one φ
  · exact h
  · rw [map_add, h, map_one]

theorem semiVec_zero (A : GU0) (φ : F4 ≃+* F4) : semiVec A φ 0 = 0 := by
  rw [semiVec, fvec_zero, mulVec_zero]

theorem semi_fix_plane {i : ℕ} (hi : i < 891) (A : GU0)
    (φ : F4 ≃+* F4) (h : ∀ w ∈ planeSub i, ∃ c : F4, semiVec A φ w = c • w) :
    (∀ x : F4, φ x = x) ∧ ∃ c : F4, c ≠ 0 ∧
      ∀ w ∈ planeSub i, ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ w = c • w := by
  set v := planeVec i with hv
  have hli := planeVec_linearIndependent hi
  have hp : ∀ s t u : F4, s • v 0 + t • v 1 + u • v 2 = 0 → s = 0 ∧ t = 0 ∧ u = 0 := by
    intro s t u hstu
    have := Fintype.linearIndependent_iff.1 hli ![s, t, u] (by
      rw [Fin.sum_univ_three]
      exact hstu)
    exact ⟨this 0, this 1, this 2⟩
  have hvS : ∀ a, v a ∈ planeSub i := planeVec_mem i
  obtain ⟨c0, hc0⟩ := h _ (hvS 0)
  obtain ⟨c1, hc1⟩ := h _ (hvS 1)
  obtain ⟨c2, hc2⟩ := h _ (hvS 2)
  obtain ⟨d1, hd1⟩ := h _ ((planeSub i).add_mem (hvS 0) (hvS 1))
  obtain ⟨d2, hd2⟩ := h _ ((planeSub i).add_mem (hvS 0) (hvS 2))
  obtain ⟨e, he⟩ := h _ ((planeSub i).add_mem ((planeSub i).smul_mem F4.ω (hvS 0)) (hvS 1))
  have hc0ne : c0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc0
    exact semiVec_ne_zero A φ (hli.ne_zero 0) hc0
  have e1 : c0 = c1 := by
    rw [semiVec_add, hc0, hc1, smul_add] at hd1
    have := hp (c0 - d1) (c1 - d1) 0 (by
      calc (c0 - d1) • v 0 + (c1 - d1) • v 1 + (0 : F4) • v 2 =
          (c0 • v 0 + c1 • v 1) - (d1 • v 0 + d1 • v 1) := by
            rw [zero_smul, add_zero, sub_smul, sub_smul]
            abel
        _ = 0 := by rw [hd1, sub_self])
    rw [sub_eq_zero.1 this.1, sub_eq_zero.1 this.2.1]
  have e2 : c0 = c2 := by
    rw [semiVec_add, hc0, hc2, smul_add] at hd2
    have := hp (c0 - d2) 0 (c2 - d2) (by
      calc (c0 - d2) • v 0 + (0 : F4) • v 1 + (c2 - d2) • v 2 =
          (c0 • v 0 + c2 • v 2) - (d2 • v 0 + d2 • v 2) := by
            rw [zero_smul, add_zero, sub_smul, sub_smul]
            abel
        _ = 0 := by rw [hd2, sub_self])
    rw [sub_eq_zero.1 this.1, sub_eq_zero.1 this.2.2]
  have hω : φ F4.ω = F4.ω := by
    rw [semiVec_add, semiVec_smul, hc0, hc1, smul_add, smul_smul, smul_smul] at he
    have := hp (φ F4.ω * c0 - e * F4.ω) (c1 - e) 0 (by
      calc (φ F4.ω * c0 - e * F4.ω) • v 0 + (c1 - e) • v 1 + (0 : F4) • v 2 =
          ((φ F4.ω * c0) • v 0 + c1 • v 1) - ((e * F4.ω) • v 0 + e • v 1) := by
            rw [zero_smul, add_zero, sub_smul, sub_smul]
            abel
        _ = 0 := by rw [he, sub_self])
    have h1 : φ F4.ω * c0 = e * F4.ω := sub_eq_zero.1 this.1
    have h2 : c1 = e := sub_eq_zero.1 this.2.1
    rw [← h2, ← e1, mul_comm c0] at h1
    exact mul_right_cancel₀ hc0ne h1
  have hφ := eq_self_of_omega φ hω
  have hfv : ∀ x : W, fvec φ x = x := fun x => funext fun k => hφ (x k)
  refine ⟨hφ, c0, hc0ne, fun w hw => ?_⟩
  obtain ⟨a, rfl⟩ := (mem_planeSub_iff i w).1 hw
  have hA : ∀ k, ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v k = c0 • v k := by
    intro k
    have hk : ∀ c : F4, semiVec A φ (v k) = c • v k →
        ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v k = c • v k := by
      intro c hc
      rw [← hc, semiVec, hfv]
    fin_cases k
    · exact hk c0 hc0
    · exact e1 ▸ hk c1 hc1
    · exact e2 ▸ hk c2 hc2
  rw [Fin.sum_univ_three, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, hA, hA,
    hA, smul_add, smul_add, smul_comm c0 (a 0), smul_comm c0 (a 1), smul_comm c0 (a 2)]

section Cent

theorem center_T46_eq_bot : Subgroup.center T46 = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have h1 : MulAut.conj z = 1 := by
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.1 hz g).symm,
      mul_inv_cancel_right]
  have h2 := autPerm_conj z
  rw [h1, map_one] at h2
  exact Subtype.ext h2.symm

end Cent

end CFSG.LargeExtraspecial.SMod20.Aut

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.Fischer CFSG.F4.Native CFSG.SmithE Matrix Module Aut

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

section Cent

theorem centralizer_UA_aut {i : ℕ} (hi : i < 891) (α : MulAut T46) :
    (∀ u : T46, (u : Equiv.Perm (Fin 693)) ∈ UAloc i → α u = u) ↔
      ∃ u : T46, (u : Equiv.Perm (Fin 693)) ∈ UAloc i ∧ α = MulAut.conj u := by
  constructor
  · intro hα
    have hfix : ∀ p ∈ planePoints i, autPerm α p = p := by
      intro p hp
      have h1 := congrArg Subtype.val (hα ⟨tvP p, tvP_mem p⟩ (tvP_mem_UAloc hp))
      rw [autPerm_tvP] at h1
      exact tvP_injective h1
    obtain ⟨A, φ, hAφ⟩ := exists_autPerm_eq_semiPerm α
    have hsc : ∀ w ∈ planeSub i, ∃ c : F4, semiVec A φ w = c • w := by
      intro w hw
      by_cases hw0 : w = 0
      · exact ⟨0, by rw [hw0, semiVec_zero, smul_zero]⟩
      have hwi := hermStd_planeSub hi hw hw
      have hpw : ptOf w hw0 hwi ∈ planePoints i := by
        rw [mem_planePoints]
        obtain ⟨c, hc, hcw⟩ := uVec_ptOf w hw0 hwi
        rw [hcw]
        exact (planeSub i).smul_mem c hw
      have h1 := hfix _ hpw
      rw [hAφ, semiPerm_ptOf] at h1
      obtain ⟨c, -, hc⟩ := (ptOf_eq_ptOf_iff hw0 hwi _ _).1 h1.symm
      exact ⟨c, hc⟩
    obtain ⟨hφ, c, hc, hAc⟩ := semi_fix_plane hi A φ hsc
    set A' : GU0 := scalGU c⁻¹ (inv_ne_zero hc) * A with hA'
    have hA'fix : ∀ w ∈ planeSub i,
        ((A' : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ w = w := by
      intro w hw
      rw [hA', Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hAc w hw, scalGU_mulVec,
        smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hmem := piGU_mem_UAloc_of_fix hi hA'fix
    have hφr : φ = RingEquiv.refl F4 := RingEquiv.ext hφ
    have hπ : autPerm α = piGU A' := by
      rw [hAφ, semiPerm, hφr, fieldPerm_refl, mul_one, hA', map_mul, piGU_scalGU, one_mul]
    have hmem' : autPerm α ∈ UAloc i := by
      rw [hπ]
      exact hmem
    refine ⟨⟨autPerm α, UAloc_le_T46 i hmem'⟩, hmem', ?_⟩
    apply autPerm_injective
    rw [autPerm_conj]
  · rintro ⟨u, hu, rfl⟩ v hv
    apply Subtype.ext
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      UAloc_commute hi hu hv, mul_inv_cancel_right]

end Cent

end CFSG.LargeExtraspecial.SMod20
