module

public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.CharacterTheory.Semidihedral.Conjugacy

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf

section Quat

open QuaternionGroup

theorem two_mul_eq_zero_zmod {N : ℕ} [NeZero N] (β : ZMod (2 * N)) (h : β + β = 0) :
    β = 0 ∨ β = (N : ZMod (2 * N)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hv : β.val < 2 * N := ZMod.val_lt β
  have h1 : ((2 * β.val : ℕ) : ZMod (2 * N)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    calc 2 * β = β + β := by ring
      _ = 0 := h
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨m, hm⟩ := h1
  have hm2 : m = 0 ∨ m = 1 := by
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · omega
    · exfalso
      have : 2 * N * 2 ≤ 2 * N * m := Nat.mul_le_mul_left _ hge
      omega
  rcases hm2 with rfl | rfl
  · left
    have : β.val = 0 := by omega
    rw [← ZMod.natCast_zmod_val β, this]; simp
  · right
    have : β.val = N := by omega
    rw [← ZMod.natCast_zmod_val β, this]

theorem natCast_ne_zero {N : ℕ} [NeZero N] : (N : ZMod (2 * N)) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hN := Nat.pos_of_ne_zero (NeZero.ne N)
  have := Nat.le_of_dvd hN h
  omega

theorem N_add_N {N : ℕ} : (N : ZMod (2 * N)) + N = 0 := by
  have : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := ZMod.natCast_self _
  rw [Nat.cast_mul] at this
  push_cast at this
  calc (N : ZMod (2 * N)) + N = 2 * N := by ring
    _ = 0 := this

theorem quat_invol_unique {N : ℕ} [NeZero N] {x : QuaternionGroup N} (h : x * x = 1)
    (h1 : x ≠ 1) : x = a N := by
  rcases x with i | i
  · rw [a_mul_a, one_def] at h
    rcases two_mul_eq_zero_zmod i (a.inj h) with h0 | hN
    · exact absurd (by rw [h0]; rfl) h1
    · rw [hN]
  · exfalso
    rw [xa_mul_xa, one_def] at h
    have h2 := a.inj h
    apply natCast_ne_zero (N := N)
    simpa using h2

theorem quat_sq_sq {N : ℕ} [NeZero N] {w w' : QuaternionGroup N}
    (h : (w * w) * (w * w) = a N) (h' : (w' * w') * (w' * w') = a N) :
    w' * w' = w * w ∨ w' * w' = (w * w)⁻¹ := by
  have key : ∀ v : QuaternionGroup N, (v * v) * (v * v) = a N →
      ∃ α : ZMod (2 * N), v * v = a α ∧ α + α = N := by
    intro v hv
    rcases v with i | i
    · refine ⟨i + i, by simp, ?_⟩
      rw [a_mul_a, a_mul_a] at hv
      exact a.inj hv
    · exfalso
      rw [xa_mul_xa] at hv
      simp only [add_sub_cancel_right, a_mul_a] at hv
      have := a.inj hv
      rw [N_add_N] at this
      exact natCast_ne_zero this.symm
  obtain ⟨α, hα, hα2⟩ := key w h
  obtain ⟨α', hα', hα2'⟩ := key w' h'
  rw [hα, hα']
  have hβ : (α' - α) + (α' - α) = 0 := by
    calc (α' - α) + (α' - α) = (α' + α') - (α + α) := by ring
      _ = 0 := by rw [hα2, hα2']; ring
  rcases two_mul_eq_zero_zmod _ hβ with h0 | hN
  · left
    have : α' = α := sub_eq_zero.1 h0
    rw [this]
  · right
    have : α' = -α := by
      have e1 : α' = α + N := by rw [← hN]; ring
      rw [e1]
      have e2 : (α + N) + α = (N : ZMod (2 * N)) + N := by
        calc (α + N) + α = (α + α) + N := by ring
          _ = N + N := by rw [hα2]
      have e3 : (α + N) + α = 0 := by rw [e2, N_add_N]
      exact eq_neg_of_add_eq_zero_left e3
    rw [this]; rfl

end Quat

section SD

open CFSG.Semidihedral CFSG.Open Subgroup

theorem sd_core (n : ℕ) (hn : 4 ≤ n) :
    ∃ c y : SemidihedralGroup n, c ∈ dihedralSubgroup n ∧ y ∉ dihedralSubgroup n ∧
      y * c * y⁻¹ = c⁻¹ ∧ y * y = c * c ∧ c * c = z n := by
  have hn3 : 3 ≤ n := by omega
  have hhalf : (half n : ZMod (modulus n)) = ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) +
      ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) := by
    rw [half_eq_two_mul_quarter hn3]; push_cast; ring
  have hcc : element n hn3 ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) 0 *
      element n hn3 ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) 0 = z n := by
    rw [element_rotation_mul, z_eq_element n hn3, hhalf]
  refine ⟨element n hn3 ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) 0, element n hn3 1 1, ?_, ?_, ?_, ?_,
    hcc⟩
  · rw [element_mem_dihedralSubgroup_iff]
    rw [ZMod.val_natCast_of_lt]
    · have : 2 ^ (n - 3) = 2 * 2 ^ (n - 4) := by
        rw [show n - 3 = (n - 4) + 1 by omega, pow_succ]; ring
      omega
    · have hm : modulus n = 4 * 2 ^ (n - 3) := by
        rw [modulus_eq_two_mul_half (by omega), half_eq_two_mul_quarter hn3]; ring
      have : 0 < 2 ^ (n - 3) := pow_pos (by norm_num) _
      omega
  · rw [element_mem_dihedralSubgroup_iff]
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (modulus_two_le (by omega))]
    decide
  · rw [conjugate_rotation_by_reflection, element_rotation_inv]
    apply (element_eq_iff n hn3 _ _ _ _).2
    refine ⟨?_, rfl⟩
    have h0 : (half n : ZMod (modulus n)) * ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) = 0 := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      have : modulus n = 2 ^ (n - 1) := rfl
      have h2 : half n * 2 ^ (n - 3) = 2 ^ ((n - 2) + (n - 3)) := by
        rw [pow_add]; rfl
      rw [this, h2]
      exact Nat.pow_dvd_pow 2 (by omega)
    calc twist n * ((2 ^ (n - 3) : ℕ) : ZMod (modulus n))
        = (half n : ZMod (modulus n)) * ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) -
          ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) := by simp only [twist]; ring
      _ = -((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) := by rw [h0]; ring
  · rw [element_reflection_mul, element_rotation_mul]
    apply (element_eq_iff n hn3 _ _ _ _).2
    refine ⟨?_, by decide⟩
    rw [← hhalf]
    simp only [twist]; ring

theorem sd_rot_invol {n : ℕ} (hn : 4 ≤ n) {g : SemidihedralGroup n} (hg : g ∈ rotationSubgroup n)
    (h2 : g * g = 1) (h1 : g ≠ 1) : g = z n := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [r_zpow_eq_element n hn3] at h2 h1 ⊢
  have ho : orderOf (element n hn3 (k : ZMod (modulus n)) 0) = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using h2) h1
  rw [rotation_involution_iff] at ho
  rw [ho, z_eq_element n hn3]

theorem sd_data {G : Type*} [Group G] {D M : Subgroup G} {n : ℕ} (e : ↥D ≃* SemidihedralGroup n)
    (hn : 4 ≤ n) (hM : M ≤ D) (hidx : M.relIndex D = 2) {a b : G} (ha : a ∈ M) (hb : b ∈ M)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    ∃ c y : G, c ∈ M ∧ y ∈ D ∧ y ∉ M ∧ y * c * y⁻¹ = c⁻¹ ∧ y * y = c * c ∧ c * c ≠ 1 ∧
      (c * c) * (c * c) = 1 ∧ (center ↥D).map D.subtype = zpowers (c * c) ∧
      ∀ x ∈ D, x * x = 1 → x ∈ M := by
  have hn3 : 3 ≤ n := by omega
  set M' : Subgroup ↥D := M.subgroupOf D with hM'
  have hM'idx : M'.index = 2 := hidx
  set M'' : Subgroup (SemidihedralGroup n) := M'.map (e : ↥D →* SemidihedralGroup n) with hM''
  have hM''idx : M''.index = 2 := by
    rw [hM'', Subgroup.index_map_equiv]; exact hM'idx
  have hmem : ∀ x : ↥D, e x ∈ M'' ↔ (x : G) ∈ M := by
    intro x
    rw [hM'']
    have := Subgroup.mem_map_iff_mem (f := (e : ↥D →* SemidihedralGroup n)) e.injective (K := M')
      (x := x)
    rw [show e x = (e : ↥D →* SemidihedralGroup n) x from rfl, this]
    simp [hM', Subgroup.mem_subgroupOf]
  have haD : a ∈ D := hM ha
  have hbD : b ∈ D := hM hb
  have ha' : e ⟨a, haD⟩ ∈ M'' := (hmem _).2 ha
  have hb' : e ⟨b, hbD⟩ ∈ M'' := (hmem _).2 hb
  have haa : e ⟨a, haD⟩ * e ⟨a, haD⟩ = 1 := by
    rw [← map_mul]
    have : (⟨a, haD⟩ : ↥D) * ⟨a, haD⟩ = 1 := Subtype.ext (by simpa using ha2)
    rw [this, map_one]
  have hbb : e ⟨b, hbD⟩ * e ⟨b, hbD⟩ = 1 := by
    rw [← map_mul]
    have : (⟨b, hbD⟩ : ↥D) * ⟨b, hbD⟩ = 1 := Subtype.ext (by simpa using hb2)
    rw [this, map_one]
  have ha1' : e ⟨a, haD⟩ ≠ 1 := by
    intro h
    apply ha1
    have := e.injective (h.trans (map_one e).symm)
    simpa using congrArg Subtype.val this
  have hb1' : e ⟨b, hbD⟩ ≠ 1 := by
    intro h
    apply hb1
    have := e.injective (h.trans (map_one e).symm)
    simpa using congrArg Subtype.val this
  have hne : e ⟨a, haD⟩ ≠ e ⟨b, hbD⟩ := by
    intro h
    apply hab
    have := e.injective h
    simpa using congrArg Subtype.val this
  have hdih : M'' = dihedralSubgroup n := by
    rcases (index_eq_two_iff n hn3 M'').1 hM''idx with h | h | h
    · exfalso
      apply hne
      rw [h] at ha' hb'
      rw [sd_rot_invol hn ha' haa ha1', sd_rot_invol hn hb' hbb hb1']
    · exact h
    · exfalso
      apply hne
      rw [h] at ha' hb'
      have e1 := quaternion_unique_involution n hn3 _ ha'
        (orderOf_eq_prime (by simpa [pow_two] using haa) ha1')
      have e2 := quaternion_unique_involution n hn3 _ hb'
        (orderOf_eq_prime (by simpa [pow_two] using hbb) hb1')
      rw [e1, e2]
  obtain ⟨c₀, y₀, hc₀, hy₀, hcy, hyy, hcc⟩ := sd_core n hn
  have hcM : ((e.symm c₀ : ↥D) : G) ∈ M := by
    rw [← hmem, MulEquiv.apply_symm_apply, hdih]; exact hc₀
  have hyM : ((e.symm y₀ : ↥D) : G) ∉ M := by
    rw [← hmem, MulEquiv.apply_symm_apply, hdih]; exact hy₀
  have h1 : ((e.symm c₀ : ↥D) : G) * ((e.symm c₀ : ↥D) : G) = ((e.symm (z n) : ↥D) : G) := by
    have := congrArg (fun x : SemidihedralGroup n => ((e.symm x : ↥D) : G)) hcc
    simpa using this
  refine ⟨((e.symm c₀ : ↥D) : G), ((e.symm y₀ : ↥D) : G), hcM, (e.symm y₀).2, hyM, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · have := congrArg (fun x : SemidihedralGroup n => ((e.symm x : ↥D) : G)) hcy
    simpa using this
  · have := congrArg (fun x : SemidihedralGroup n => ((e.symm x : ↥D) : G)) hyy
    simpa using this
  · rw [h1]
    intro h
    have h2 : e.symm (z n) = 1 := Subtype.ext (by simpa using h)
    exact z_ne_one n hn3 (by simpa using congrArg e h2)
  · rw [h1]
    have h2 : z n * z n = 1 := by rw [← pow_two]; exact z_sq n hn3
    have := congrArg (fun x : SemidihedralGroup n => ((e.symm x : ↥D) : G)) h2
    simpa using this
  · rw [h1]
    have hc : (center ↥D) = (center (SemidihedralGroup n)).map (e.symm : SemidihedralGroup n →* ↥D) :=
      (Subgroup.map_center_eq e.symm).symm
    rw [hc, center_eq_zpowers n hn, Subgroup.map_map]
    exact MonoidHom.map_zpowers _ _
  · intro x hx hx2
    have hx' : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := by
      rw [← map_mul]
      have : (⟨x, hx⟩ : ↥D) * ⟨x, hx⟩ = 1 := Subtype.ext (by simpa using hx2)
      rw [this, map_one]
    have : e ⟨x, hx⟩ ∈ M'' := by
      rw [hdih]
      by_cases h1 : e ⟨x, hx⟩ = 1
      · rw [h1]; exact one_mem _
      · exact involution_mem_dihedralSubgroup n hn3 _
          (orderOf_eq_prime (by simpa [pow_two] using hx') h1)
    exact (hmem _).1 this

end SD

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf
