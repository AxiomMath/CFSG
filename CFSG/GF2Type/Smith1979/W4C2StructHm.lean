module

public import CFSG.GF2Type.Smith1979.W4C2Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C2

namespace LocalTest

open Module QuadraticMap CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

local notation "mat" => rowsMatrix 4
local notation "vec" => toVecD 4

theorem exists_vecMul (T : V4 →ₗ[ZMod 2] V4) : ∃ A : Mat4, ∀ x, T x = x ᵥ* A := by
  refine ⟨Matrix.of fun i => T fun j => if i = j then 1 else 0, fun x => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ T x]
  funext j
  simp [Matrix.vecMul, dotProduct]

theorem valid_of_dot {G H : Mat4} (h : ∀ x y : V4, (x ᵥ* G) ⬝ᵥ (y ᵥ* H) = x ⬝ᵥ y) :
    G * Hᵀ = 1 := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [Matrix.single_one_vecMul, Matrix.single_one_vecMul] at this
  simpa [Matrix.mul_apply, Matrix.one_apply, dotProduct, Pi.single_apply, eq_comm] using this

theorem exists_act_of_mem_Hm {f : Vm ≃ₗ[ZMod 2] Vm} (hf : f ∈ Hm) :
    ∃ (G H : Mat4) (s : Bool), G * Hᵀ = 1 ∧ ∀ v, f v = act G H s v := by
  obtain ⟨hq, hN⟩ := mem_Hm_iff.mp hf
  have hmem : ∀ (S : Submodule (ZMod 2) Vm) (u : Vm), u ∈ S →
      f u ∈ S.map (f : Vm →ₗ[ZMod 2] Vm) := fun S u hu => Submodule.mem_map_of_mem hu
  have hsplit : ∀ v : Vm, f v = f (v.1, 0) + f (0, v.2) := fun v => by
    rw [← map_add]; simp
  rcases hN with ⟨hN1, hN2⟩ | ⟨hN1, hN2⟩
  · have h2 : ∀ x : V4, (f (x, 0)).2 = 0 := fun x => by
      have := hmem Nsub (x, 0) (mem_Nsub.mpr rfl)
      rw [hN1] at this
      exact mem_Nsub.mp this
    have h1 : ∀ y : V4, (f (0, y)).1 = 0 := fun y => by
      have := hmem Nssub (0, y) (mem_Nssub.mpr rfl)
      rw [hN2] at this
      exact mem_Nssub.mp this
    obtain ⟨G, hG⟩ := exists_vecMul (LinearMap.fst (ZMod 2) V4 V4 ∘ₗ (f : Vm →ₗ[ZMod 2] Vm) ∘ₗ
      LinearMap.inl (ZMod 2) V4 V4)
    obtain ⟨H, hH⟩ := exists_vecMul (LinearMap.snd (ZMod 2) V4 V4 ∘ₗ (f : Vm →ₗ[ZMod 2] Vm) ∘ₗ
      LinearMap.inr (ZMod 2) V4 V4)
    have hG' : ∀ x : V4, (f (x, 0)).1 = x ᵥ* G := fun x => by simpa using hG x
    have hH' : ∀ y : V4, (f (0, y)).2 = y ᵥ* H := fun y => by simpa using hH y
    have hf' : ∀ v, f v = act G H false v := fun v => by
      rw [hsplit v]
      simp [act, Prod.ext_iff, hG', hH', h1, h2]
    refine ⟨G, H, false, valid_of_dot fun x y => ?_, hf'⟩
    have := hq (x, y)
    rw [q0_apply, q0_apply, hf' (x, y)] at this
    simpa [act] using this
  · have h2 : ∀ x : V4, (f (x, 0)).1 = 0 := fun x => by
      have := hmem Nsub (x, 0) (mem_Nsub.mpr rfl)
      rw [hN1] at this
      exact mem_Nssub.mp this
    have h1 : ∀ y : V4, (f (0, y)).2 = 0 := fun y => by
      have := hmem Nssub (0, y) (mem_Nssub.mpr rfl)
      rw [hN2] at this
      exact mem_Nsub.mp this
    obtain ⟨H, hH⟩ := exists_vecMul (LinearMap.snd (ZMod 2) V4 V4 ∘ₗ (f : Vm →ₗ[ZMod 2] Vm) ∘ₗ
      LinearMap.inl (ZMod 2) V4 V4)
    obtain ⟨G, hG⟩ := exists_vecMul (LinearMap.fst (ZMod 2) V4 V4 ∘ₗ (f : Vm →ₗ[ZMod 2] Vm) ∘ₗ
      LinearMap.inr (ZMod 2) V4 V4)
    have hH' : ∀ x : V4, (f (x, 0)).2 = x ᵥ* H := fun x => by simpa using hH x
    have hG' : ∀ y : V4, (f (0, y)).1 = y ᵥ* G := fun y => by simpa using hG y
    have hf' : ∀ v, f v = act G H true v := fun v => by
      rw [hsplit v]
      simp [act, Prod.ext_iff, hG', hH', h1, h2]
    have hd : H * Gᵀ = 1 := by
      refine valid_of_dot fun x y => ?_
      have := hq (x, y)
      rw [q0_apply, q0_apply, hf' (x, y)] at this
      simp only [act, ↓reduceIte] at this
      rw [dotProduct_comm] at this
      exact this
    refine ⟨G, H, true, ?_, hf'⟩
    simpa using congrArg Matrix.transpose hd

theorem exists_rows (M : Mat4) : ∃ R ∈ allRows, mat R = M := by
  have h0 := codeV_lt (M 0)
  have h1 := codeV_lt (M 1)
  have h2 := codeV_lt (M 2)
  have h3 := codeV_lt (M 3)
  set n := codeV (M 0) + 16 * codeV (M 1) + 256 * codeV (M 2) + 4096 * codeV (M 3) with hn
  have e0 : n % 16 = codeV (M 0) := by omega
  have e1 : n / 16 % 16 = codeV (M 1) := by omega
  have e2 : n / 256 % 16 = codeV (M 2) := by omega
  have e3 : n / 4096 = codeV (M 3) := by omega
  refine ⟨#[n % 16, n / 16 % 16, n / 256 % 16, n / 4096], ?_, ?_⟩
  · simp only [allRows, List.mem_map, List.mem_range]
    exact ⟨n, by omega, rfl⟩
  · ext i j
    rw [rowsMatrix_apply]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      show toVecD 4 (n % 16) j = M 0 j
      rw [e0]; exact congrFun (vec_codeV (M 0)) j
    · show toVecD 4 (n / 16 % 16) j = M 1 j
      rw [e1]; exact congrFun (vec_codeV (M 1)) j
    · show toVecD 4 (n / 256 % 16) j = M 2 j
      rw [e2]; exact congrFun (vec_codeV (M 2)) j
    · show toVecD 4 (n / 4096) j = M 3 j
      rw [e3]; exact congrFun (vec_codeV (M 3)) j

theorem injRows_of_valid {G H : Mat4} (h : G * Hᵀ = 1) {R : Array Nat} (hR : mat R = G) :
    injRows R = true := by
  simp only [injRows, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]
  intro i hi hzero
  have h1 : vec (vecMulN 4 R (i + 1)) = vec 0 := (vec_eq_iff _ _).mpr (by simpa using hzero)
  rw [toVecD_vecMulN, hR, toVecD_zero] at h1
  have h2 : vec (i + 1) = 0 := by
    have := congrArg (fun w => w ᵥ* Hᵀ) h1
    simpa [Matrix.vecMul_vecMul, h] using this
  have h3 : (i + 1) % 16 = 0 % 16 := (vec_eq_iff _ 0).mp (by rw [h2, toVecD_zero])
  omega

theorem exists_hlist_of_valid (hv : (Hlist ()).all validE = true) {G H : Mat4} (s : Bool)
    (h : G * Hᵀ = 1) : ∃ E ∈ Hlist (), mat E.G = G ∧ mat E.H = H ∧ E.s = s := by
  obtain ⟨R, hRmem, hR⟩ := exists_rows G
  have hinj := injRows_of_valid h hR
  have hEmem : (⟨R, dualRows R, s⟩ : El) ∈ Hlist () := by
    simp only [Hlist, List.mem_flatMap, List.mem_filter]
    refine ⟨R, ⟨hRmem, hinj⟩, ?_⟩
    cases s <;> simp
  have hval : mat R * (mat (dualRows R))ᵀ = 1 := by
    have := List.all_eq_true.mp hv _ hEmem
    rwa [validE, eqR_iff, rowsMatrix_mulRows, rowsMatrix_transposeRows,
      rowsMatrix_idRows] at this
  refine ⟨⟨R, dualRows R, s⟩, hEmem, hR, ?_, rfl⟩
  have hGH : G * (mat (dualRows R))ᵀ = 1 := by rw [← hR]; exact hval
  have h2 : Hᵀ * G = 1 := mul_eq_one_comm.mp h
  have h4 : (mat (dualRows R))ᵀ = Hᵀ := by
    calc (mat (dualRows R))ᵀ = (Hᵀ * G) * (mat (dualRows R))ᵀ := by rw [h2, Matrix.one_mul]
      _ = Hᵀ * (G * (mat (dualRows R))ᵀ) := by rw [Matrix.mul_assoc]
      _ = Hᵀ := by rw [hGH, Matrix.mul_one]
  simpa using congrArg Matrix.transpose h4

theorem valid_of_mem_Hlist (hv : (Hlist ()).all validE = true) {E : El} (hE : E ∈ Hlist ()) :
    Valid E := by
  have := List.all_eq_true.mp hv _ hE
  unfold Valid
  rwa [validE, eqR_iff, rowsMatrix_mulRows, rowsMatrix_transposeRows,
    rowsMatrix_idRows] at this

theorem exists_hlist_of_mem_Hm (hv : (Hlist ()).all validE = true) {f : Vm ≃ₗ[ZMod 2] Vm}
    (hf : f ∈ Hm) : ∃ E ∈ Hlist (), Valid E ∧ f = dec E := by
  obtain ⟨G, H, s, hGH, hf'⟩ := exists_act_of_mem_Hm hf
  obtain ⟨E, hE, h1, h2, h3⟩ := exists_hlist_of_valid hv s hGH
  have hval : Valid E := valid_of_mem_Hlist hv hE
  refine ⟨E, hE, hval, LinearEquiv.ext fun v => ?_⟩
  rw [dec_apply hval, hf' v]
  unfold semE
  rw [h1, h2, h3]

theorem chk_parts (h : chk = true) :
    (Hlist ()).all validE = true ∧ orbOK (Hlist ()) = true ∧ chkN (Hlist ()) = true ∧
      chkM (Hlist ()) = true := by
  simp only [chk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem vecE_zero : vecE (0, 0) = 0 := by
  simp [vecE, toVecD_zero]

theorem exists_conj_rep (hv : (Hlist ()).all validE = true) (ho : orbOK (Hlist ()) = true)
    {b : Vm} (hb0 : b ≠ 0) (hbq : q0 b = 0) :
    ∃ E : El, Valid E ∧
      (((b ∈ Nsub ∨ b ∈ Nssub) ∧ dec E (vecE bN) = b) ∨
        (¬ (b ∈ Nsub ∨ b ∈ Nssub) ∧ dec E (vecE bM) = b)) := by
  have hxl := codeV_lt b.1
  have hyl := codeV_lt b.2
  set x := codeV b.1 with hx
  set y := codeV b.2 with hy
  have hb : vecE (x, y) = b := by
    refine Prod.ext ?_ ?_
    · exact vec_codeV b.1
    · exact vec_codeV b.2
  have hn0 : x + 16 * y ≠ 0 := by
    intro h0
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    apply hb0
    rw [← hb, hx0, hy0]
    exact vecE_zero
  have hsing : dot4 x y = false := by
    have := q0_vecE (x, y)
    rw [hb, hbq] at this
    cases h : dot4 x y
    · rfl
    · simp [h] at this
  have e1 : (x + 16 * y) % 16 = x := by omega
  have e2 : (x + 16 * y) / 16 = y := by omega
  have key := List.all_eq_true.mp ho (x + 16 * y) (List.mem_range.mpr (by omega))
  simp only [e1, e2, hsing, Bool.or_false, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at key
  rcases key with hz | ⟨E, hE, hEq⟩
  · exact absurd hz hn0
  · have hval := valid_of_mem_Hlist hv hE
    have hEb : dec E (vecE (if x = 0 ∨ y = 0 then bN else bM)) = b := by
      rw [dec_apply hval, ← vecE_appE, ← hb]
      exact eqV_iff.mp hEq
    have hx0 : (x = 0 ∨ y = 0) ↔ (b ∈ Nsub ∨ b ∈ Nssub) := by
      rw [mem_Nsub, mem_Nssub]
      have hb1 : b.1 = vec x := (congrArg Prod.fst hb).symm
      have hb2 : b.2 = vec y := (congrArg Prod.snd hb).symm
      rw [hb1, hb2]
      have z1 : vec x = 0 ↔ x = 0 := by
        rw [← toVecD_zero 4, vec_eq_iff]; omega
      have z2 : vec y = 0 ↔ y = 0 := by
        rw [← toVecD_zero 4, vec_eq_iff]; omega
      rw [z1, z2, or_comm]
    refine ⟨E, hval, ?_⟩
    by_cases hc : x = 0 ∨ y = 0
    · left
      rw [if_pos hc] at hEb
      exact ⟨hx0.mp hc, hEb⟩
    · right
      rw [if_neg hc] at hEb
      exact ⟨fun h => hc (hx0.mpr h), hEb⟩

end LocalTest

end CFSG.GF2Type.Smith1979.W4C2
