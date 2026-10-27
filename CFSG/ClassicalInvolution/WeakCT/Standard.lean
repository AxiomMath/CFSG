module

public import CFSG.ClassicalInvolution.WeakCT.Amalgam

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.CurtisTits
open scoped MatrixGroups

section Generation

variable {K : Type} [Field K]

theorem iSup_range_blockSL2 (n : ℕ) : ⨆ i : Fin n, (blockSL2 K n i).range = ⊤ := by
  rw [eq_top_iff, ← iSup_fundamentalRootSubgroup_eq_top (m := n) (F := K)]
  refine iSup_le fun k => iSup_le fun s => ?_
  refine le_trans ?_ (le_iSup _ k)
  rw [← rankOne_eq_range, rankOne_rootGroup]
  cases s
  · exact le_sup_right
  · exact le_sup_left

theorem B12_sup_B23 : B12 K ⊔ B23 K = ⊤ := by
  rw [eq_top_iff, ← iSup_range_blockSL2 (K := K) 2]
  refine iSup_le fun i => ?_
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

theorem map_B12_blockSL3 (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (B12 K).map (blockSL3 K n i h) = (blockSL2 K n i).range := by
  rw [B12, ← MonoidHom.range_comp, blockSL3_comp_left]

theorem map_B23_blockSL3 (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (B23 K).map (blockSL3 K n i h) = (blockSL2 K n ⟨i + 1, h⟩).range := by
  rw [B23, ← MonoidHom.range_comp, blockSL3_comp_right]

theorem range_blockSL3 (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (blockSL3 K n i h).range = (blockSL2 K n i).range ⊔ (blockSL2 K n ⟨i + 1, h⟩).range := by
  rw [MonoidHom.range_eq_map, ← B12_sup_B23, Subgroup.map_sup, map_B12_blockSL3,
    map_B23_blockSL3]

end Generation

section Standard

variable {K : Type} [Field K]

theorem weakCTSystem_standard (n : ℕ) :
    WeakCTSystem K n (fun i => (blockSL2 K n i).range)
      (fun i j => (blockSL2 K n i).range ⊔ (blockSL2 K n j).range) where
  iso i := ⟨MonoidHom.ofInjective (blockSL2_injective n i)⟩
  join _ _ _ := rfl
  comm i j hij := by
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact blockSL2_comm n i j hij A B
  pair i j hj := by
    have h : (i : ℕ) + 1 < n := by have := j.isLt; omega
    obtain rfl : j = ⟨i + 1, h⟩ := Fin.ext hj
    have hc : ∀ H : Subgroup SL(3, K), H.map (MulAut.conj (1 : SL(3, K))⁻¹).toMonoidHom = H :=
      fun H => by ext x; simp
    refine ⟨blockSL3 K n i h, 1, range_blockSL3 n i h, ?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [(MonoidHom.ker_eq_bot_iff _).mpr (blockSL3_injective n i h)]
      exact bot_le
    · rw [hc, map_B12_blockSL3]
    · rw [hc, map_B23_blockSL3]
  gen := iSup_range_blockSL2 n

theorem exists_hom_of_ctFamily {n : ℕ} {Y : Type} [Group Y] (F : CTFamily K Y n) :
    ∃ ψ : SL(n + 1, K) →* Y, (∀ i, ψ.comp (blockSL2 K n i) = F.ι i) ∧
      ∀ (i : Fin n) (h : (i : ℕ) + 1 < n), ψ.comp (blockSL3 K n i h) = F.θ i := by
  obtain ⟨φ, hφc, hφ⟩ := exists_compatible_family F
  obtain ⟨ψ, hψ, -⟩ := isUniversalCompletion_specialLinear.{0} n K Y φ hφc
  have hψ' : ∀ (J : {J : Finset (Fin n) // J.card ≤ 2}) (x : levi (rootGroup n K) J.1),
      ψ x = φ J x := hψ
  have h2 : ∀ (i : Fin n) (A : SL(2, K)), ψ (blockSL2 K n i A) = F.ι i A := fun i A =>
    (hψ' ⟨{i}, by simp⟩ ⟨_, blockSL2_mem_levi (Finset.mem_singleton_self i) A⟩).trans
      (hφ ⟨{i}, by simp⟩ i (Finset.mem_singleton_self i) _ A rfl)
  refine ⟨ψ, fun i => MonoidHom.ext (h2 i), fun i h => ?_⟩
  have hle : B12 K ⊔ B23 K ≤ MonoidHom.eqLocus (ψ.comp (blockSL3 K n i h)) (F.θ i) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨A, rfl⟩
      change ψ (blockSL3 K n i h (blockSL K 3 2 0 (by omega) A)) =
        F.θ i (blockSL K 3 2 0 (by omega) A)
      rw [← MonoidHom.comp_apply (blockSL3 K n i h), blockSL3_comp_left, h2,
        ← F.left i h]
      rfl
    · rintro _ ⟨A, rfl⟩
      change ψ (blockSL3 K n i h (blockSL K 3 2 1 (by omega) A)) =
        F.θ i (blockSL K 3 2 1 (by omega) A)
      rw [← MonoidHom.comp_apply (blockSL3 K n i h), blockSL3_comp_right, h2,
        ← F.right i h]
      rfl
  refine MonoidHom.ext fun x => hle ?_
  rw [B12_sup_B23 (K := K)]
  exact Subgroup.mem_top x

end Standard

end CFSG.ClassicalInvolution.WeakCT
