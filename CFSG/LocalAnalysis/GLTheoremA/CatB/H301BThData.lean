module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BThAlt
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th.Max3

private def thCycWord (k : ZMod 3) : List ℕ :=
  [[2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2],
    [2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2],
    [2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1]].getD k.val []

private def thCycEnc (k : ZMod 3) : List ℕ :=
  [[222, 231, 171, 84, 66, 242, 181, 48], [50, 231, 251, 84, 181, 97, 18, 184],
    [88, 86, 190, 229, 196, 97, 120, 18]].getD k.val []

private def thPow8 (A : List ℕ) : ℕ → List ℕ
  | 0 => id8
  | k + 1 => mul8 A (thPow8 A k)

private def thIdx (u : ZMod 3 × ZMod 3 × ZMod 3) : ℕ := u.1.val + 3 * u.2.1.val + 9 * u.2.2.val

private def thExpEncTab : List (List ℕ) :=
    [[1, 2, 4, 8, 16, 32, 64, 128], [222, 231, 171, 84, 66, 242, 181, 48],
    [223, 229, 175, 92, 82, 210, 245, 176], [50, 231, 251, 84, 181, 97, 18, 184],
    [87, 229, 88, 92, 245, 153, 165, 212], [101, 2, 163, 8, 64, 248, 183, 108],
    [51, 229, 255, 92, 165, 65, 82, 56], [137, 2, 243, 8, 183, 107, 16, 228],
    [186, 231, 12, 84, 18, 42, 66, 220], [88, 86, 190, 229, 196, 97, 120, 18],
    [163, 187, 152, 2, 46, 153, 81, 165], [251, 237, 38, 231, 234, 248, 41, 183],
    [243, 187, 36, 2, 81, 65, 146, 82], [12, 237, 89, 231, 41, 107, 149, 16],
    [255, 86, 125, 229, 120, 42, 7, 66], [171, 237, 154, 231, 149, 32, 234, 64],
    [175, 86, 193, 229, 7, 242, 196, 181], [4, 187, 91, 2, 146, 210, 46, 245],
    [89, 84, 186, 237, 212, 65, 56, 146], [125, 92, 51, 86, 108, 107, 228, 149],
    [36, 8, 137, 187, 184, 42, 220, 7], [193, 92, 223, 86, 228, 32, 128, 234],
    [91, 8, 1, 187, 220, 242, 48, 196], [154, 84, 222, 237, 56, 210, 176, 46],
    [152, 8, 101, 187, 48, 97, 184, 120], [38, 84, 50, 237, 176, 153, 212, 81],
    [190, 92, 87, 86, 128, 248, 108, 41]]

private def thExpEnc (u : ZMod 3 × ZMod 3 × ZMod 3) : List ℕ := thExpEncTab.getD (thIdx u) []

private def thExpFixTab : List (List ℕ) :=
    [[], [0], [0], [0], [0, 27, 47, 52, 75, 80, 100, 127, 136, 147, 167, 188, 195, 216, 236, 247],
    [0, 2, 8, 10, 84, 86, 92, 94, 177, 179, 185, 187, 229, 231, 237, 239], [0],
    [0, 2, 8, 10, 84, 86, 92, 94, 177, 179, 185, 187, 229, 231, 237, 239],
    [0, 27, 47, 52, 75, 80, 100, 127, 136, 147, 167, 188, 195, 216, 236, 247], [0],
    [0, 21, 34, 55, 75, 94, 105, 124, 134, 147, 164, 177, 205, 216, 239, 250],
    [0, 10, 17, 27, 37, 47, 52, 62, 135, 141, 150, 156, 162, 168, 179, 185],
    [0, 27, 47, 52, 69, 94, 106, 113, 133, 158, 170, 177, 192, 219, 239, 244], [0, 10, 179, 185],
    [0, 75, 147, 216], [0, 10, 32, 42, 65, 75, 97, 107, 147, 153, 179, 185, 210, 216, 242, 248],
    [0, 27, 47, 52], [0, 94, 177, 239], [0],
    [0, 10, 17, 27, 37, 47, 52, 62, 135, 141, 150, 156, 162, 168, 179, 185],
    [0, 21, 34, 55, 75, 94, 105, 124, 134, 147, 164, 177, 205, 216, 239, 250],
    [0, 10, 32, 42, 65, 75, 97, 107, 147, 153, 179, 185, 210, 216, 242, 248], [0, 94, 177, 239],
    [0, 27, 47, 52], [0, 27, 47, 52, 69, 94, 106, 113, 133, 158, 170, 177, 192, 219, 239, 244],
    [0, 75, 147, 216], [0, 10, 179, 185]]

private def thExpFix (u : ZMod 3 × ZMod 3 × ZMod 3) : List ℕ := thExpFixTab.getD (thIdx u) []

private theorem thCycWord_perm : ∀ k : ZMod 3, posWord aPerm bPerm (thCycWord k) = nineCyc k := by
  decide +kernel

private theorem thCycWord_enc : ∀ k : ZMod 3, posWord8 B1enc B2enc (thCycWord k) = thCycEnc k := by
  decide +kernel

private theorem thExpEnc_spec : ∀ u : ZMod 3 × ZMod 3 × ZMod 3,
    thExpEnc u = mul8 (mul8 (thPow8 (thCycEnc 0) u.1.val) (thPow8 (thCycEnc 1) u.2.1.val))
      (thPow8 (thCycEnc 2) u.2.2.val) ∧ ∀ x ∈ thExpEnc u, x < 256 := by
  decide +kernel

private theorem thExpFix_spec : ∀ u : ZMod 3 × ZMod 3 × ZMod 3, u ≠ 0 →
    ∀ n < 256, app8 (thExpEnc u) n = n → n ∈ thExpFix u := by
  decide +kernel

private theorem thExpFix_pair : ∀ u v : ZMod 3 × ZMod 3 × ZMod 3, u ≠ 0 → v ≠ 0 → v ≠ u →
    v ≠ u + u → ((thExpFix u).filter (· ∈ thExpFix v)).length ≤ 4 := by
  decide +kernel

private theorem thExpFix_one : thExpFix (1, 0, 0) = [0] := by decide +kernel

private theorem mat8_thPow8 (A : List ℕ) (k : ℕ) : mat8 (thPow8 A k) = mat8 A ^ k := by
  induction k with
  | zero => exact mat8_id8
  | succ k ih => rw [thPow8, mat8_mul, ih, pow_succ']

private theorem vec8_inj {m n : ℕ} (hm : m < 256) (hn : n < 256) (h : vec8 m = vec8 n) :
    m = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have := congrFun h ⟨i, hi⟩
    simp only [vec8, bitZ] at this
    revert this
    cases m.testBit i <;> cases n.testBit i <;> decide
  · have h256 : (256 : ℕ) ≤ 2 ^ i :=
      (show (256 : ℕ) = 2 ^ 8 by norm_num) ▸ Nat.pow_le_pow_right two_pos (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm h256),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hn h256)]

section Generic

variable {G : Type*} [Group G] (D : CFSG.Sporadic.ThSchreier.AutCore.Data G)

private theorem ρ_eq_thExpEnc {m : G} {u : ZMod 3 × ZMod 3 × ZMod 3}
    (hm : D.κPerm m = nineExp u) : D.ρ m = mat8 (thExpEnc u) := by
  have hκ : ∀ k, D.κPerm (posWord D.x D.y (thCycWord k)) = nineCyc k := fun k => by
    rw [D.κPerm_apply, D.κ_posWord, thCycWord_perm]
  have hρ : ∀ k, D.ρ (posWord D.x D.y (thCycWord k)) = mat8 (thCycEnc k) := fun k => by
    rw [map_posWord, D.ρx, D.ρy, ← mat8_B1enc, ← mat8_B2enc, ← mat8_posWord8, thCycWord_enc]
  have h1 : D.ρ m = D.ρ (posWord D.x D.y (thCycWord 0) ^ u.1.val *
      posWord D.x D.y (thCycWord 1) ^ u.2.1.val * posWord D.x D.y (thCycWord 2) ^ u.2.2.val) := by
    refine D.ρ_eq_of_κ_eq (Subtype.ext ?_)
    rw [← D.κPerm_apply, ← D.κPerm_apply, hm, map_mul, map_mul, map_pow, map_pow, map_pow, hκ,
      hκ, hκ, nineExp]
  rw [h1, map_mul, map_mul, map_pow, map_pow, map_pow, hρ, hρ, hρ, (thExpEnc_spec u).1, mat8_mul,
    mat8_mul, mat8_thPow8, mat8_thPow8, mat8_thPow8]

end Generic

section Fixed

variable {G : Type*} [Group G]
  (D : CFSG.Sporadic.ThSchreier.AutCore.Data G)

private theorem enc8_mem_thExpFix {m : G} {u : ZMod 3 × ZMod 3 × ZMod 3} (hu : u ≠ 0)
    (hm : D.κPerm m = nineExp u) (q : D.Q) (hc : m * q = q * m) :
    enc8 (Multiplicative.toAdd (D.π q)) ∈ thExpFix u := by
  have h1 : D.π ⟨m * q * m⁻¹, D.normal.conj_mem q q.2 m⟩ = D.π q := by
    congr 1
    apply Subtype.ext
    change m * (q : G) * m⁻¹ = q
    rw [hc, mul_inv_cancel_right]
  rw [D.π_conj, ρ_eq_thExpEnc D hm] at h1
  have hv := enc8_facts (Multiplicative.toAdd (D.π q))
  have h2 : (mat8 (thExpEnc u)).mulVec (vec8 (enc8 (Multiplicative.toAdd (D.π q)))) =
      vec8 (enc8 (Multiplicative.toAdd (D.π q))) := by
    rw [hv.1]
    exact congrArg Multiplicative.toAdd h1
  rw [mat8_mulVec] at h2
  exact thExpFix_spec u hu _ hv.2 (vec8_inj (app8_lt _ (thExpEnc_spec u).2 _) hv.2 h2)

theorem π_eq_one_of_comm_cycZero {m : G} (hm : D.κPerm m = nineExp (1, 0, 0)) (q : D.Q)
    (hc : m * q = q * m) : D.π q = 1 := by
  have h := enc8_mem_thExpFix D (by decide) hm q hc
  rw [thExpFix_one, List.mem_singleton] at h
  have hv := (enc8_facts (Multiplicative.toAdd (D.π q))).1
  rw [h] at hv
  exact toAdd_eq_zero.1 (hv.symm.trans (funext fun i => bitZ_zero _))

theorem exists_finset_card_le_four_comm_pair {u₁ u₂ : ZMod 3 × ZMod 3 × ZMod 3} (hu₁ : u₁ ≠ 0)
    (hu₂ : u₂ ≠ 0) (h₂₁ : u₂ ≠ u₁) (h₂₁₁ : u₂ ≠ u₁ + u₁) :
    ∃ S : Finset (Fin 8 → ZMod 2), S.card ≤ 4 ∧ ∀ m₁ m₂ : G, D.κPerm m₁ = nineExp u₁ →
      D.κPerm m₂ = nineExp u₂ → ∀ q : D.Q, m₁ * q = q * m₁ → m₂ * q = q * m₂ →
        Multiplicative.toAdd (D.π q) ∈ S := by
  refine ⟨((thExpFix u₁).filter (· ∈ thExpFix u₂)).toFinset.image vec8,
    Finset.card_image_le.trans ((List.toFinset_card_le _).trans
      (thExpFix_pair u₁ u₂ hu₁ hu₂ h₂₁ h₂₁₁)), fun m₁ m₂ hm₁ hm₂ q hc₁ hc₂ => ?_⟩
  rw [← (enc8_facts (Multiplicative.toAdd (D.π q))).1]
  exact Finset.mem_image_of_mem _ (List.mem_toFinset.2 (List.mem_filter.2
    ⟨enc8_mem_thExpFix D hu₁ hm₁ q hc₁, decide_eq_true (enc8_mem_thExpFix D hu₂ hm₂ q hc₂)⟩))

end Fixed

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
