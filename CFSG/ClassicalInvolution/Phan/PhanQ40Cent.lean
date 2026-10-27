module

public import CFSG.ClassicalInvolution.Phan.PhanQ39Chain

public section

namespace CFSG.ClassicalInvolution.PhanQ


open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section Cent

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem coe_blockEmb2_torusTwo (k : Fin 3) (u : normOne (unitaryInvolution K p f)) :
    (((blockEmb2 K p f 3 k (torusTwo (unitaryInvolution K p f) u) : Su K p f 4) :
        GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal fun a => if a.val = k.val then (u : Kˣ).val else
        if a.val = k.val + 1 then ((u : Kˣ)⁻¹).val else 1 := by
  rw [← coe_torusEquiv_mulSingle, coe_torusEquiv, coe_coe_diagSU]
  congr 1
  funext a
  rw [ratio_mulSingle]
  split_ifs <;> simp

theorem eq_zero_aux1 {K : Type} [Field K] {Y c : K} (hc : c ≠ 1) (e : Y = c * Y) : Y = 0 := by
  have : (1 - c) * Y = 0 := by linear_combination e
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h).symm hc
  · exact h

theorem eq_zero_aux2 {K : Type} [Field K] {Y c : K} (hc : c ≠ 1) (e : Y * c = Y) : Y = 0 :=
  eq_zero_aux1 hc (by linear_combination -e)

theorem eq_zero_aux3 {K : Type} [Field K] {Y c₁ c₂ : K} (hc : c₁ ≠ c₂) (e : Y * c₂ = c₁ * Y) :
    Y = 0 := by
  have : (c₂ - c₁) * Y = 0 := by linear_combination e
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h).symm hc
  · exact h

theorem mem_torus_of_comm_blocks {x : normOne (unitaryInvolution K p f)} (hx : x * x ≠ 1)
    {y : Su K p f 4}
    (h0 : y * blockEmb2 K p f 3 0 (torusTwo (unitaryInvolution K p f) x) =
      blockEmb2 K p f 3 0 (torusTwo (unitaryInvolution K p f) x) * y)
    (h2 : y * blockEmb2 K p f 3 2 (torusTwo (unitaryInvolution K p f) x) =
      blockEmb2 K p f 3 2 (torusTwo (unitaryInvolution K p f) x) * y) :
    y ∈ torus (unitaryInvolution K p f) 4 := by
  rw [mem_torus_iff]
  intro a b hab
  have e0 := congrArg (fun g : Su K p f 4 => (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) a b)
    h0
  have e2 := congrArg (fun g : Su K p f 4 => (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) a b)
    h2
  simp only [Subgroup.coe_mul, Units.val_mul, coe_blockEmb2_torusTwo, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at e0 e2
  have hxx : (x : Kˣ) * (x : Kˣ) ≠ 1 := fun h => hx (Subtype.ext h)
  set u : Kˣ := (x : Kˣ) with hu
  have hu1 : (u : K) ≠ 1 := by
    intro h
    apply hxx
    have : u = 1 := Units.ext h
    rw [this, one_mul]
  have hu2 : (u : K)⁻¹ ≠ 1 := by
    intro h
    apply hu1
    rw [inv_eq_one] at h
    exact h
  have hu3 : (u : K) ≠ (u : K)⁻¹ := by
    intro h
    apply hxx
    have h' : (u : K) * (u : K) = 1 := by
      have hu0 : (u : K) ≠ 0 := u.ne_zero
      field_simp at h
      linear_combination h
    exact Units.ext h'
  fin_cases a <;> fin_cases b <;> simp at hab e0 e2 ⊢
  all_goals first
    | exact eq_zero_aux1 hu1 e0 | exact eq_zero_aux1 hu1 e2
    | exact eq_zero_aux1 hu2 e0 | exact eq_zero_aux1 hu2 e2
    | exact eq_zero_aux2 hu1 e0 | exact eq_zero_aux2 hu1 e2
    | exact eq_zero_aux2 hu2 e0 | exact eq_zero_aux2 hu2 e2
    | exact eq_zero_aux3 hu3 e0 | exact eq_zero_aux3 hu3 e2
    | exact eq_zero_aux3 hu3.symm e0 | exact eq_zero_aux3 hu3.symm e2

end Cent

section Out

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {S : PhanFamilyD4 K p f G} {e' : Fin 3 → Fin 4} {ψ : Su K p f 4 →* G}

theorem ChainCtx.eq_of_adj_out (C : ChainCtx S e' ψ) {k : Fin 4}
    (hcov : ∀ i : Fin 4, i = k ∨ ∃ j, e' j = i)
    (hc0 : ∀ A B, S.ι k A * S.ι (e' 0) B = S.ι (e' 0) B * S.ι k A)
    (hc2 : ∀ A B, S.ι k A * S.ι (e' 2) B = S.ι (e' 2) B * S.ι k A)
    {c c' : Frame (unitaryInvolution K p f) 4}
    (h : (phanSystem S).adj k (C.Phi c) (C.Phi c')) : c = c' := by
  obtain ⟨g, rfl⟩ := exists_smul_stdFrame C.hσ c
  obtain ⟨g', rfl⟩ := exists_smul_stdFrame C.hσ c'
  rw [C.Phi_smul, C.Phi_smul, phanSystem_adj_mk, ← map_inv, ← map_mul] at h
  obtain ⟨x, hx⟩ : ∃ x : Su K p f 4, x = g⁻¹ * g' := ⟨_, rfl⟩
  rw [← hx] at h
  obtain ⟨r, hr, t, ht, hrt⟩ := exists_mul_of_mem_parab C.hK k h
  obtain ⟨u, rfl⟩ := ht
  have hu : u = Function.update u k 1 * Pi.mulSingle k (u k) := by
    ext i
    by_cases hi : i = k
    · subst hi
      simp
    · simp [hi]
  have hmT : mTor S u = mTor S (Function.update u k 1) * tor S k (u k) := by
    conv_lhs => rw [hu]
    rw [map_mul, mTor_mulSingle]
  set t' := mTor S (Function.update u k 1) with ht'
  have ht'T : t' ∈ torusSub S := mTor_mem_torusSub S _
  have htkT : tor S k (u k) ∈ torusSub S := tor_mem_torusSub S k _
  have hψ : ∀ i : Fin 4, tor S i (Function.update u k 1 i) ∈ ψ.range := by
    intro i
    rcases hcov i with rfl | ⟨j, rfl⟩
    · simp
    · have hmem : tor S (e' j) (Function.update u k 1 (e' j)) ∈ (tor S (e' j)).range :=
        ⟨_, rfl⟩
      rw [← C.hch.torEq j] at hmem
      obtain ⟨s, hs⟩ := hmem
      exact ⟨blockEmb2 K p f 3 j (torusTwo (unitaryInvolution K p f) s), hs⟩
  have ht'ψ : t' ∈ ψ.range := by
    rw [ht', mTor_apply]
    exact mul_mem (mul_mem (mul_mem (hψ 0) (hψ 1)) (hψ 2)) (hψ 3)
  obtain ⟨τ', hτ'⟩ := ht'ψ
  have hl : ψ (x * τ'⁻¹) = r * tor S k (u k) := by
    rw [map_mul, map_inv, hτ', hrt, hmT, torusSub_comm S ht'T htkT]
    group
  have hlr : r * tor S k (u k) ∈ (S.ι k).range := by
    obtain ⟨A, rfl⟩ := hr
    exact mul_mem ⟨A, rfl⟩ ⟨torusTwo (unitaryInvolution K p f) (u k), rfl⟩
  obtain ⟨A, hA⟩ := hlr
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one C.hK (by have := C.hq; omega)
  have hcomm : ∀ (j : Fin 3) (hj : ∀ A B, S.ι k A * S.ι (e' j) B = S.ι (e' j) B * S.ι k A),
      x * τ'⁻¹ * blockEmb2 K p f 3 j (torusTwo (unitaryInvolution K p f) x₀) =
        blockEmb2 K p f 3 j (torusTwo (unitaryInvolution K p f) x₀) * (x * τ'⁻¹) := by
    intro j hj
    apply C.hch.injective C.hK C.hg C.h2
    obtain ⟨B, hB⟩ := C.hch.le_range j (torusTwo (unitaryInvolution K p f) x₀)
    rw [map_mul ψ (x * τ'⁻¹) _, map_mul ψ _ (x * τ'⁻¹), hl, ← hB, ← hA]
    exact hj A B
  have hy := mem_torus_of_comm_blocks hx₀ (hcomm 0 hc0) (hcomm 2 hc2)
  have hψy := C.hch.psi_mem_torusSub C.hg hy
  have hxT : ψ x ∈ torusSub S := by
    have : ψ x = ψ (x * τ'⁻¹) * t' := by rw [map_mul, map_inv, hτ', inv_mul_cancel_right]
    rw [this]
    exact mul_mem hψy ht'T
  have hxt := C.hch.mem_torus_of_psi_mem C.hK C.hg C.h2 hxT
  have h3 : (g⁻¹ * g') • stdFrame (unitaryInvolution K p f) 4 =
      stdFrame (unitaryInvolution K p f) 4 := (smul_stdFrame_eq_iff _).2 (hx ▸ hxt)
  rw [mul_smul, inv_smul_eq_iff] at h3
  exact h3.symm

end Out

end CFSG.ClassicalInvolution.PhanQ
