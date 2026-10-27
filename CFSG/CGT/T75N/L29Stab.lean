module

public import CFSG.CGT.T75N.L29Overgroup
public import CFSG.CGT.T75N.L29Levi

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Finite F] {n : ℕ}

@[expose] def vecStab (n : ℕ) (v : Fin n → F) : Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) F) *ᵥ v = v}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show ((a * b : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v = v
    rw [SpecialLinearGroup.coe_mul, ← mulVec_mulVec]
    change (a : Matrix (Fin n) (Fin n) F) *ᵥ v = v at ha
    change (b : Matrix (Fin n) (Fin n) F) *ᵥ v = v at hb
    rw [hb, ha]
  inv_mem' := fun {a} ha => by
    change ((a⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v = v
    change (a : Matrix (Fin n) (Fin n) F) *ᵥ v = v at ha
    conv_lhs => rw [← ha]
    rw [mulVec_mulVec, coe_inv_mul_coe, one_mulVec]

omit [Finite F] in
theorem mem_vecStab {v : Fin n → F} {g : SpecialLinearGroup (Fin n) F} :
    g ∈ vecStab n v ↔ (g : Matrix (Fin n) (Fin n) F) *ᵥ v = v := Iff.rfl

section P1

variable {m : ℕ}

omit [Finite F] in
theorem eq_smul_e0_of_mem_flag {v : Fin (m + 2) → F} (hv : v ∈ flagSpace (m + 2) F 1) :
    v = v 0 • (Pi.single 0 1 : Fin (m + 2) → F) := by
  rw [mem_flagSpace] at hv
  funext k
  by_cases hk : k = 0
  · subst hk; simp
  · have : 1 ≤ (k : ℕ) := by
      rcases Nat.eq_zero_or_pos (k : ℕ) with h | h
      · exact absurd (Fin.ext h) hk
      · exact h
    simp [hk, hv k this]

omit [Finite F] in
theorem e0_mem_flag : (Pi.single 0 1 : Fin (m + 2) → F) ∈ flagSpace (m + 2) F 1 := by
  rw [mem_flagSpace]
  intro j hj
  have : j ≠ 0 := fun h => by rw [h] at hj; simp at hj
  simp [this]

omit [Finite F] in
theorem vecStab_le_P1 :
    vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F) ≤ stabilizer (flagSpace (m + 2) F 1) := by
  intro g hg
  rw [mem_vecStab] at hg
  change (flagSpace (m + 2) F 1).map (mulVecLin (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F)) =
    flagSpace (m + 2) F 1
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    rw [mulVecLin_apply, eq_smul_e0_of_mem_flag hv, mulVec_smul, hg]
    exact Submodule.smul_mem _ _ e0_mem_flag
  · intro v hv
    refine ⟨v, hv, ?_⟩
    rw [mulVecLin_apply]
    conv_lhs => rw [eq_smul_e0_of_mem_flag hv]
    rw [mulVec_smul, hg]
    exact (eq_smul_e0_of_mem_flag hv).symm

@[expose] def scal0 (g : SpecialLinearGroup (Fin (m + 2)) F) : F :=
  ((g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single 0 1 : Fin (m + 2) → F)) 0

omit [Finite F] in
theorem mem_P1_imp {g : SpecialLinearGroup (Fin (m + 2)) F}
    (hg : g ∈ stabilizer (flagSpace (m + 2) F 1)) :
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single 0 1 : Fin (m + 2) → F) =
      scal0 g • (Pi.single 0 1 : Fin (m + 2) → F) := by
  have h : (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single 0 1 : Fin (m + 2) → F) ∈
      flagSpace (m + 2) F 1 := by
    have h1 : (flagSpace (m + 2) F 1).map
        (mulVecLin (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F)) = flagSpace (m + 2) F 1 := hg
    rw [← h1]
    exact ⟨_, e0_mem_flag, rfl⟩
  exact eq_smul_e0_of_mem_flag h

omit [Finite F] in
theorem scal0_ne_zero {g : SpecialLinearGroup (Fin (m + 2)) F}
    (hg : g ∈ stabilizer (flagSpace (m + 2) F 1)) : scal0 g ≠ 0 := by
  intro h0
  have h1 := mem_P1_imp hg
  rw [h0, zero_smul] at h1
  have h2 := congrArg (fun x => ((g⁻¹ : SpecialLinearGroup (Fin (m + 2)) F) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ x) h1
  simp only [mulVec_mulVec, mulVec_zero] at h2
  rw [coe_inv_mul_coe, one_mulVec] at h2
  have := congrFun h2 0
  simp at this

omit [Finite F] in
theorem scal0_mul {a b : SpecialLinearGroup (Fin (m + 2)) F}
    (ha : a ∈ stabilizer (flagSpace (m + 2) F 1)) (hb : b ∈ stabilizer (flagSpace (m + 2) F 1)) :
    scal0 (a * b) = scal0 a * scal0 b := by
  have h1 : ((a * b : SpecialLinearGroup (Fin (m + 2)) F) : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ
      (Pi.single 0 1 : Fin (m + 2) → F) = (a : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ
      ((b : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single 0 1 : Fin (m + 2) → F)) := by
    rw [SpecialLinearGroup.coe_mul, mulVec_mulVec]
  have h2 : scal0 (a * b) = (((a * b : SpecialLinearGroup (Fin (m + 2)) F) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single 0 1 : Fin (m + 2) → F)) 0 := rfl
  rw [h2, h1, mem_P1_imp hb, mulVec_smul, mem_P1_imp ha]
  simp [mul_comm]

omit [Finite F] in
theorem scal0_eq_one_iff {g : SpecialLinearGroup (Fin (m + 2)) F}
    (hg : g ∈ stabilizer (flagSpace (m + 2) F 1)) :
    scal0 g = 1 ↔ g ∈ vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F) := by
  rw [mem_vecStab, mem_P1_imp hg]
  constructor
  · intro h
    rw [h, one_smul]
  · intro h
    have := congrFun h 0
    simpa using this

@[expose] noncomputable def lam1 (m : ℕ) (F : Type) [Field F] :
    stabilizer (flagSpace (m + 2) F 1) →* Fˣ where
  toFun g := Units.mk0 (scal0 (g : SpecialLinearGroup (Fin (m + 2)) F)) (scal0_ne_zero g.2)
  map_one' := by
    apply Units.ext
    simp [scal0]
  map_mul' a b := by
    apply Units.ext
    exact scal0_mul a.2 b.2

theorem eq_vecStab_of_index [CharP F 2] (S : Subgroup (SpecialLinearGroup (Fin (m + 2)) F))
    (hU : unitriangular (m + 2) F ≤ S) (hS : S ≤ stabilizer (flagSpace (m + 2) F 1))
    (hidx : S.index = Nat.card F ^ (m + 2) - 1) :
    S = vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F) := by
  have hq : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  set P1 := stabilizer (flagSpace (m + 2) F 1) with hP1
  have h1 : P1.index * (Nat.card F - 1) = Nat.card F ^ (m + 2) - 1 :=
    index_stabilizer_flag_one (K := F) (n := m + 2) (by omega)
  have hP1pos : 0 < P1.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hrel : S.relIndex P1 = Nat.card F - 1 := by
    have h2 := Subgroup.relIndex_mul_index hS
    rw [hidx, ← h1, mul_comm] at h2
    exact Nat.eq_of_mul_eq_mul_left hP1pos h2
  set T := S.comap (epsHom m F) with hT
  have hTU : unitriangular (m + 1) F ≤ T := fun u hu => hU (epsHom_mem_unitriangular hu)
  have hrange : (epsHom m F).range ≤ P1 := by
    rintro _ ⟨A, rfl⟩
    exact vecStab_le_P1 (epsHom_fix_e0 A)
  have hTidx : T.index ≤ Nat.card F - 1 := by
    rw [hT, Subgroup.index_comap]
    calc S.relIndex (epsHom m F).range ≤ S.relIndex P1 :=
          Subgroup.relIndex_le_of_le_right hrange (by rw [hrel]; omega)
      _ = Nat.card F - 1 := hrel
  have hTtop : T = ⊤ := eq_top_of_index_le (m + 1) T hTU hTidx
  have hQS : vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F) ≤ S := by
    intro g hg
    obtain ⟨A, hA⟩ := exists_unitriangular_of_fix g hg
    have hAT : A ∈ T := by rw [hTtop]; trivial
    have hAS : epsHom m F A ∈ S := hAT
    have hr : g * (epsHom m F A)⁻¹ ∈ S := hU hA
    have := S.mul_mem hr hAS
    rwa [inv_mul_cancel_right] at this
  have hQrel : (vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F)).relIndex P1 ≤
      Nat.card F - 1 := by
    have hker : (lam1 m F).ker =
        (vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F)).subgroupOf P1 := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← scal0_eq_one_iff g.2]
      simp [lam1, Units.ext_iff]
    have h := Subgroup.index_ker (lam1 m F)
    rw [hker] at h
    have hle : Nat.card (lam1 m F).range ≤ Nat.card Fˣ :=
      Nat.card_le_card_of_injective (fun x => (x : Fˣ)) Subtype.val_injective
    rw [Nat.card_units] at hle
    change ((vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F)).subgroupOf P1).index ≤ _
    rw [h]
    exact hle
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hQS hS
  rw [hrel] at hmul
  have hpos : 0 < (vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F)).relIndex S :=
    Nat.pos_of_ne_zero (by
      intro h0
      rw [h0, zero_mul] at hmul
      have : (vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F)).relIndex P1 ≠ 0 :=
        Subgroup.index_ne_zero_of_finite
      omega)
  have hone : (vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F)).relIndex S = 1 := by
    by_contra hne
    have h2 : 2 ≤ (vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F)).relIndex S := by omega
    have : 2 * (Nat.card F - 1) ≤
        (vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F)).relIndex S * (Nat.card F - 1) :=
      Nat.mul_le_mul_right _ h2
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hone) hQS

end P1

end CFSG.CGT.T75N
