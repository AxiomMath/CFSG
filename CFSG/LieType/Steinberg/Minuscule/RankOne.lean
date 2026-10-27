module

public import CFSG.LieType.Steinberg.Minuscule.Group
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley

namespace MinData

namespace Valid

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]
include hV

theorem exists_wt_eq_one (i : Fin τ.rank) : ∃ a : Fin D.d, D.wt a i = 1 := by
  by_contra hne
  simp only [not_exists] at hne
  apply hV.simpleE_ne_zero i
  rw [simpleE, ofDigits_eq_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [ite_eq_right fun h => hne (hV.sRefl i a) (by rw [hV.wt_sRefl_self, h]; rfl), zero_mul]

@[expose] def blockOp (i : Fin τ.rank) (M : Matrix (Fin 2) (Fin 2) k) :
    Module.End k (Fin D.d →₀ k) :=
  Finsupp.linearCombination k fun a =>
    if D.wt a i = 1 then M 0 0 • Finsupp.single a 1 + M 1 0 • Finsupp.single (hV.sRefl i a) 1
    else if D.wt a i = -1 then
      M 0 1 • Finsupp.single (hV.sRefl i a) 1 + M 1 1 • Finsupp.single a 1
    else Finsupp.single a 1

theorem blockOp_single_of_eq_one {i : Fin τ.rank} {a : Fin D.d} (h : D.wt a i = 1)
    (M : Matrix (Fin 2) (Fin 2) k) :
    hV.blockOp k i M (Finsupp.single a 1) =
      M 0 0 • Finsupp.single a 1 + M 1 0 • Finsupp.single (hV.sRefl i a) 1 := by
  simp [blockOp, h]

theorem blockOp_single_of_eq_neg_one {i : Fin τ.rank} {a : Fin D.d} (h : D.wt a i = -1)
    (M : Matrix (Fin 2) (Fin 2) k) :
    hV.blockOp k i M (Finsupp.single a 1) =
      M 0 1 • Finsupp.single (hV.sRefl i a) 1 + M 1 1 • Finsupp.single a 1 := by
  simp [blockOp, h]

theorem blockOp_single_of_eq_zero {i : Fin τ.rank} {a : Fin D.d} (h : D.wt a i = 0)
    (M : Matrix (Fin 2) (Fin 2) k) :
    hV.blockOp k i M (Finsupp.single a 1) = Finsupp.single a 1 := by
  simp [blockOp, h]

theorem blockOp_one (i : Fin τ.rank) : hV.blockOp k i 1 = 1 :=
  ext_single fun a => by
    rcases hV.wt_mem a i with h | h | h
    · rw [hV.blockOp_single_of_eq_neg_one k h]
      simp
    · rw [hV.blockOp_single_of_eq_zero k h, Module.End.one_apply]
    · rw [hV.blockOp_single_of_eq_one k h]
      simp

theorem blockOp_mul (i : Fin τ.rank) (M N : Matrix (Fin 2) (Fin 2) k) :
    hV.blockOp k i (M * N) = hV.blockOp k i M * hV.blockOp k i N :=
  ext_single fun a => by
    have hs := hV.wt_sRefl_self i a
    have hss := hV.sRefl_sRefl i a
    rw [Module.End.mul_apply]
    rcases hV.wt_mem a i with h | h | h
    · rw [hV.blockOp_single_of_eq_neg_one k h, hV.blockOp_single_of_eq_neg_one k h, map_add,
        map_smul, map_smul, hV.blockOp_single_of_eq_one k (by rw [hs, h]; rfl),
        hV.blockOp_single_of_eq_neg_one k h, hss]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, smul_add, smul_smul, add_smul]
      module
    · rw [hV.blockOp_single_of_eq_zero k h, hV.blockOp_single_of_eq_zero k h,
        hV.blockOp_single_of_eq_zero k h]
    · rw [hV.blockOp_single_of_eq_one k h, hV.blockOp_single_of_eq_one k h, map_add,
        map_smul, map_smul, hV.blockOp_single_of_eq_one k h,
        hV.blockOp_single_of_eq_neg_one k (by rw [hs, h]), hss]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, smul_add, smul_smul, add_smul]
      module

@[expose] def blockHom (i : Fin τ.rank) :
    Matrix (Fin 2) (Fin 2) k →* Module.End k (Fin D.d →₀ k) where
  toFun := hV.blockOp k i
  map_one' := hV.blockOp_one k i
  map_mul' := hV.blockOp_mul k i

theorem blockOp_injective (i : Fin τ.rank) : Function.Injective (hV.blockOp k i) := by
  intro M N hMN
  obtain ⟨a, ha⟩ := hV.exists_wt_eq_one i
  have hs : D.wt (hV.sRefl i a) i = -1 := by rw [hV.wt_sRefl_self, ha]
  have hne : hV.sRefl i a ≠ a := hV.sRefl_ne_self (by omega)
  have h1 := congrArg (fun φ => φ (Finsupp.single a 1)) hMN
  have h2 := congrArg (fun φ => φ (Finsupp.single (hV.sRefl i a) 1)) hMN
  simp only [hV.blockOp_single_of_eq_one k ha, hV.blockOp_single_of_eq_neg_one k hs,
    hV.sRefl_sRefl] at h1 h2
  have e1 := congrArg (fun v => v a) h1
  have e2 := congrArg (fun v => v (hV.sRefl i a)) h1
  have e3 := congrArg (fun v => v a) h2
  have e4 := congrArg (fun v => v (hV.sRefl i a)) h2
  simp [hne, hne.symm] at e1 e2 e3 e4
  ext x y
  fin_cases x <;> fin_cases y
  · exact e1
  · exact e3
  · exact e2
  · exact e4

theorem blockOp_upper (i : Fin τ.rank) (c : k) :
    hV.blockOp k i !![1, c; 0, 1] = 1 + c • D.rootOp k (Pi.single i 1) :=
  ext_single fun a => by
    have hs := hV.wt_sRefl_self i a
    rw [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
      hV.rootOp_single_apply]
    rcases hV.wt_mem a i with h | h | h
    · rw [hV.blockOp_single_of_eq_neg_one k h, ite_eq_left h]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, one_smul]
      abel
    · rw [hV.blockOp_single_of_eq_zero k h, ite_eq_right (by omega), smul_zero, add_zero]
    · rw [hV.blockOp_single_of_eq_one k h, ite_eq_right (by omega), smul_zero, add_zero]
      simp

theorem blockOp_lower (i : Fin τ.rank) (c : k) :
    hV.blockOp k i !![1, 0; c, 1] = 1 + c • D.rootOp k (-Pi.single i 1) :=
  ext_single fun a => by
    rw [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
      hV.rootOp_neg_single_apply]
    rcases hV.wt_mem a i with h | h | h
    · rw [hV.blockOp_single_of_eq_neg_one k h, ite_eq_right (by omega), smul_zero, add_zero]
      simp
    · rw [hV.blockOp_single_of_eq_zero k h, ite_eq_right (by omega), smul_zero, add_zero]
    · rw [hV.blockOp_single_of_eq_one k h, ite_eq_left h]
      simp

theorem blockOp_weyl (i : Fin τ.rank) : hV.blockOp k i !![0, 1; -1, 0] = D.nOp k i :=
  ext_single fun a => by
    rcases hV.wt_mem a i with h | h | h
    · rw [hV.blockOp_single_of_eq_neg_one k h, hV.nOp_single_of_eq_neg_one h]
      simp
    · rw [hV.blockOp_single_of_eq_zero k h, hV.nOp_single_of_eq_zero h]
    · rw [hV.blockOp_single_of_eq_one k h, hV.nOp_single_of_eq_one h]
      simp

theorem blockOp_diag (i : Fin τ.rank) (t : kˣ) :
    hV.blockOp k i !![(t : k), 0; 0, ((t⁻¹ : kˣ) : k)] = D.hDiag k i t :=
  ext_single fun a => by
    rw [hDiag_single]
    rcases hV.wt_mem a i with h | h | h
    · rw [hV.blockOp_single_of_eq_neg_one k h, h]
      simp
    · rw [hV.blockOp_single_of_eq_zero k h, h, zpow_zero, Units.val_one, one_smul]
    · rw [hV.blockOp_single_of_eq_one k h, h]
      simp

@[expose] def slHom (i : Fin τ.rank) :
    Matrix.SpecialLinearGroup (Fin 2) k →* (Module.End k (Fin D.d →₀ k))ˣ :=
  (Units.map (hV.blockHom k i)).comp Matrix.SpecialLinearGroup.toGL

theorem slHom_val (i : Fin τ.rank) (M : Matrix.SpecialLinearGroup (Fin 2) k) :
    ((hV.slHom k i M : (Module.End k (Fin D.d →₀ k))ˣ) : Module.End k (Fin D.d →₀ k)) =
      hV.blockOp k i M :=
  rfl

@[expose] def slUpper (c : k) : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def slLower (c : k) : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

omit hV in
theorem slUpper_val (c : k) :
    ((slUpper k c : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, c; 0, 1] := rfl

omit hV in
theorem slLower_val (c : k) :
    ((slLower k c : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, 0; c, 1] := rfl

theorem exists_of_mem_rankOne (i : Fin τ.rank) {g : hV.minGroup k}
    (hg : g ∈ hV.rootGroup k (Pi.single i 1) ⊔ hV.rootGroup k (-Pi.single i 1)) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, hV.endo k g = hV.blockOp k i M := by
  let S : Subgroup (hV.minGroup k) := (hV.slHom k i).range.comap (hV.minGroup k).subtype
  have hS : hV.rootGroup k (Pi.single i 1) ⊔ hV.rootGroup k (-Pi.single i 1) ≤ S := by
    refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩
      refine ⟨slUpper k c.toAdd, Units.ext ?_⟩
      rw [slHom_val, slUpper_val, hV.blockOp_upper]
      rfl
    · rintro _ ⟨c, rfl⟩
      refine ⟨slLower k c.toAdd, Units.ext ?_⟩
      rw [slHom_val, slLower_val, hV.blockOp_lower]
      rfl
  obtain ⟨M, hM⟩ := hS hg
  exact ⟨M, by rw [← slHom_val, hM]; rfl⟩

omit hV in
theorem sl_eq_of_lower_eq_zero (M : Matrix.SpecialLinearGroup (Fin 2) k)
    (h : (M : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    ∃ t : kˣ, ∃ c : k, (M : Matrix (Fin 2) (Fin 2) k) =
      !![(t : k), 0; 0, ((t⁻¹ : kˣ) : k)] * !![1, c; 0, 1] := by
  have hdet := M.det_coe
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  have h0 : (M : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have h11 : (M : Matrix (Fin 2) (Fin 2) k) 1 1 = ((M : Matrix (Fin 2) (Fin 2) k) 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  refine ⟨Units.mk0 _ h0, (M : Matrix (Fin 2) (Fin 2) k) 0 1 / (M : Matrix (Fin 2) (Fin 2) k) 0 0,
    ?_⟩
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h, h11, mul_div_cancel₀ _ h0]

omit hV in
theorem sl_eq_of_lower_ne_zero (M : Matrix.SpecialLinearGroup (Fin 2) k)
    (h : (M : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0) :
    ∃ u : k, ∃ t : kˣ, ∃ v : k, (M : Matrix (Fin 2) (Fin 2) k) =
      !![1, u; 0, 1] * !![0, 1; -1, 0] * !![(t : k), 0; 0, ((t⁻¹ : kˣ) : k)] *
        !![1, v; 0, 1] := by
  have hdet := M.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hγ : -(M : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := neg_ne_zero.2 h
  refine ⟨(M : Matrix (Fin 2) (Fin 2) k) 0 0 / (M : Matrix (Fin 2) (Fin 2) k) 1 0,
    Units.mk0 _ hγ, (M : Matrix (Fin 2) (Fin 2) k) 1 1 / (M : Matrix (Fin 2) (Fin 2) k) 1 0, ?_⟩
  ext x y
  fin_cases x <;> fin_cases y <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
  · field_simp
    linear_combination -hdet
  · field_simp

theorem bruhat (i : Fin τ.rank) {g : hV.minGroup k}
    (hg : g ∈ hV.rootGroup k (Pi.single i 1) ⊔ hV.rootGroup k (-Pi.single i 1)) :
    (∃ h ∈ hV.torus k i, ∃ u ∈ hV.rootGroup k (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ hV.rootGroup k (Pi.single i 1), ∃ h ∈ hV.torus k i,
        ∃ v ∈ hV.rootGroup k (Pi.single i 1), g = u * hV.nm k i * h * v := by
  obtain ⟨M, hM⟩ := hV.exists_of_mem_rankOne k i hg
  by_cases h0 : (M : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · obtain ⟨t, c, hc⟩ := sl_eq_of_lower_eq_zero k M h0
    refine Or.inl ⟨_, hV.hm_mem_torus k i t, _, hV.xm_mem_rootGroup k _ c,
      hV.endo_injective k ?_⟩
    rw [hM, hc, hV.blockOp_mul, hV.blockOp_diag, hV.blockOp_upper, endo_mul, endo_hm, endo_xm]
  · obtain ⟨u, t, v, hc⟩ := sl_eq_of_lower_ne_zero k M h0
    refine Or.inr ⟨_, hV.xm_mem_rootGroup k _ u, _, hV.hm_mem_torus k i t, _,
      hV.xm_mem_rootGroup k _ v, hV.endo_injective k ?_⟩
    rw [hM, hc, hV.blockOp_mul, hV.blockOp_mul, hV.blockOp_mul, hV.blockOp_diag,
      hV.blockOp_upper, hV.blockOp_upper, hV.blockOp_weyl, endo_mul, endo_mul, endo_mul, endo_hm,
      endo_xm, endo_xm, endo_nm]

theorem eq_one_of_mem_normalizer (i : Fin τ.rank) {u : hV.minGroup k}
    (hu : u ∈ hV.rootGroup k (Pi.single i 1))
    (hn : u ∈ Subgroup.normalizer (hV.rootGroup k (-Pi.single i 1) : Set (hV.minGroup k))) :
    u = 1 := by
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hu
  have hmem := (hn (hV.xm k (-Pi.single i 1) 1)).1 (hV.xm_mem_rootGroup k _ 1)
  obtain ⟨s, hs⟩ := (hV.mem_rootGroup k).1 hmem
  have he := congrArg (hV.endo k) hs
  simp only [endo_mul, xm_neg, endo_xm] at he
  rw [← hV.blockOp_lower, ← hV.blockOp_upper, ← hV.blockOp_upper, ← hV.blockOp_lower,
    ← hV.blockOp_mul, ← hV.blockOp_mul] at he
  have he' := congrFun (congrFun (hV.blockOp_injective k i he) 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at he'
  rw [he', xm_zero]

end Valid

end MinData

end CFSG.LieType.Steinberg.Minuscule
