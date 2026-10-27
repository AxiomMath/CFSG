module

public import CFSG.CGT.T75N.L29Stab

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

@[expose] noncomputable def tauHom (n : ℕ) (F : Type) [Field F] :
    SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F where
  toFun g := ⟨(((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ).submatrix
    (Fin.revPerm : Equiv.Perm (Fin n)) (Fin.revPerm : Equiv.Perm (Fin n)), by
      rw [det_submatrix_equiv_self, det_transpose]
      exact (g⁻¹).2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    show ((((g * h)⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ).submatrix
        (Fin.revPerm : Equiv.Perm (Fin n)) (Fin.revPerm : Equiv.Perm (Fin n)) =
      ((((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ).submatrix
        (Fin.revPerm : Equiv.Perm (Fin n)) (Fin.revPerm : Equiv.Perm (Fin n))) *
      ((((h⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ).submatrix
        (Fin.revPerm : Equiv.Perm (Fin n)) (Fin.revPerm : Equiv.Perm (Fin n)))
    rw [submatrix_mul_equiv, _root_.mul_inv_rev, SpecialLinearGroup.coe_mul, transpose_mul])

theorem tauHom_apply (n : ℕ) (g : SpecialLinearGroup (Fin n) F) (i j : Fin n) :
    ((tauHom n F g : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) (Fin.rev j) (Fin.rev i) :=
  rfl

theorem tauHom_tauHom (n : ℕ) (g : SpecialLinearGroup (Fin n) F) :
    tauHom n F (tauHom n F g) = g := by
  apply Subtype.ext
  ext i j
  rw [tauHom_apply, ← map_inv (tauHom n F), tauHom_apply]
  simp [inv_inv]

theorem tauHom_bijective (n : ℕ) : Function.Bijective (tauHom n F) :=
  Function.bijective_iff_has_inverse.2 ⟨tauHom n F, tauHom_tauHom n, tauHom_tauHom n⟩

theorem tauHom_mem_unitriangular {n : ℕ} {u : SpecialLinearGroup (Fin n) F}
    (hu : u ∈ unitriangular n F) : tauHom n F u ∈ unitriangular n F := by
  have hu' := (unitriangular n F).inv_mem hu
  rw [mem_unitriangular] at hu' ⊢
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [tauHom_apply]
    exact hu'.1 _ _ (Fin.rev_lt_rev.2 hji)
  · rw [tauHom_apply]
    exact hu'.2 _

section P1

variable [Finite F] {m : ℕ}

omit [Finite F] in
theorem mem_P1_of_col {g : SpecialLinearGroup (Fin (m + 2)) F}
    (hg : ∀ i : Fin (m + 2), 1 ≤ (i : ℕ) → (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) i 0 = 0) :
    g ∈ stabilizer (flagSpace (m + 2) F 1) := by
  set a : F := (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) 0 0 with ha
  have hcol : (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single 0 1 : Fin (m + 2) → F) =
      a • (Pi.single 0 1 : Fin (m + 2) → F) := by
    funext k
    by_cases hk : k = 0
    · subst hk; simp [ha]
    · have : 1 ≤ (k : ℕ) := by
        rcases Nat.eq_zero_or_pos (k : ℕ) with h | h
        · exact absurd (Fin.ext h) hk
        · exact h
      simp [hk, hg k this]
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hcol
    have h2 := congrArg (fun x => ((g⁻¹ : SpecialLinearGroup (Fin (m + 2)) F) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ x) hcol
    simp only [mulVec_mulVec, mulVec_zero] at h2
    rw [coe_inv_mul_coe, one_mulVec] at h2
    have := congrFun h2 0
    simp at this
  change (flagSpace (m + 2) F 1).map (mulVecLin (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F)) =
    flagSpace (m + 2) F 1
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    rw [mulVecLin_apply, eq_smul_e0_of_mem_flag hv, mulVec_smul, hcol, smul_smul]
    exact Submodule.smul_mem _ _ e0_mem_flag
  · intro v hv
    refine ⟨(v 0 * a⁻¹) • (Pi.single 0 1 : Fin (m + 2) → F), ?_, ?_⟩
    · exact Submodule.smul_mem _ _ e0_mem_flag
    · rw [mulVecLin_apply, mulVec_smul, hcol, smul_smul, mul_assoc, inv_mul_cancel₀ ha0,
        mul_one]
      exact (eq_smul_e0_of_mem_flag hv).symm

omit [Finite F] in
theorem row_last_zero_of_mem_hyperplane {g : SpecialLinearGroup (Fin (m + 2)) F}
    (hg : g ∈ stabilizer (flagSpace (m + 2) F (m + 1))) (k : Fin (m + 2))
    (hk : k ≠ Fin.last (m + 1)) :
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) (Fin.last (m + 1)) k = 0 := by
  have hek : (Pi.single k 1 : Fin (m + 2) → F) ∈ flagSpace (m + 2) F (m + 1) := by
    rw [mem_flagSpace]
    intro j hj
    have hjl : j = Fin.last (m + 1) := by
      apply Fin.ext
      have := j.isLt
      simp only [Fin.val_last]
      omega
    have : j ≠ k := fun h => hk (h ▸ hjl)
    simp [this.symm]
  have h1 : (flagSpace (m + 2) F (m + 1)).map
      (mulVecLin (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F)) = flagSpace (m + 2) F (m + 1) := hg
  have h2 : (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single k 1 : Fin (m + 2) → F) ∈
      flagSpace (m + 2) F (m + 1) := by
    rw [← h1]
    exact ⟨_, hek, rfl⟩
  have h3 := (mem_flagSpace.1 h2) (Fin.last (m + 1)) (by simp)
  simpa [mulVec_single_one] using h3

omit [Finite F] in
theorem tauHom_mem_P1 {g : SpecialLinearGroup (Fin (m + 2)) F}
    (hg : g ∈ stabilizer (flagSpace (m + 2) F (m + 1))) :
    tauHom (m + 2) F g ∈ stabilizer (flagSpace (m + 2) F 1) := by
  apply mem_P1_of_col
  intro i hi
  rw [tauHom_apply]
  have hne : Fin.rev (0 : Fin (m + 2)) ≠ Fin.rev i := by
    intro h
    have := Fin.rev_injective h
    rw [← this] at hi
    simp at hi
  rw [Fin.rev_zero] at hne
  exact row_last_zero_of_mem_hyperplane ((stabilizer _).inv_mem hg) _ (Ne.symm hne) |>.trans rfl

variable [CharP F 2]

theorem eq_tau_vecStab_of_index (S : Subgroup (SpecialLinearGroup (Fin (m + 2)) F))
    (hU : unitriangular (m + 2) F ≤ S) (hS : S ≤ stabilizer (flagSpace (m + 2) F (m + 1)))
    (hidx : S.index = Nat.card F ^ (m + 2) - 1) :
    S = (vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F)).map (tauHom (m + 2) F) := by
  have hbij := tauHom_bijective (F := F) (m + 2)
  have hU₂ : unitriangular (m + 2) F ≤ S.map (tauHom (m + 2) F) := fun u hu =>
    ⟨tauHom (m + 2) F u, hU (tauHom_mem_unitriangular hu), tauHom_tauHom _ u⟩
  have hS₂ : S.map (tauHom (m + 2) F) ≤ stabilizer (flagSpace (m + 2) F 1) := by
    rintro _ ⟨g, hg, rfl⟩
    exact tauHom_mem_P1 (hS hg)
  have hidx₂ : (S.map (tauHom (m + 2) F)).index = Nat.card F ^ (m + 2) - 1 := by
    rw [Subgroup.index_map_of_bijective hbij]
    exact hidx
  have h := eq_vecStab_of_index _ hU₂ hS₂ hidx₂
  have hS' : S = (S.map (tauHom (m + 2) F)).map (tauHom (m + 2) F) := by
    ext x
    constructor
    · intro hx
      exact ⟨tauHom (m + 2) F x, ⟨x, hx, rfl⟩, tauHom_tauHom _ x⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rw [tauHom_tauHom]
      exact hz
  rw [hS', h]

end P1

end CFSG.CGT.T75N
