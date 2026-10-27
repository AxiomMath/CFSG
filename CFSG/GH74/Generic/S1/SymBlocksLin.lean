module

public import CFSG.GH74.Generic.S1.SymBlocksLinDefs
public import CFSG.GH74.Generic.S1.BlkOps
public import CFSG.GH74.L5U5.ModelsPairs

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

theorem exists_two_more : ∀ a b : Fin 4, a ≠ b →
    ∃ c d : Fin 4, a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by decide

theorem exists_one_more : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
    ∃ d : Fin 4, a ≠ d ∧ b ≠ d ∧ c ≠ d := by decide

theorem fin4_cases : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ i : Fin 4, i = a ∨ i = b ∨ i = c ∨ i = d := by decide

theorem exists_perm_four (a b c d : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c ∧ σ 3 = d := by
  have hinj : Function.Injective ![a, b, c, d] := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp at h; tauto)
  exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj), rfl, rfl, rfl, rfl⟩

theorem exists_perm_three (a b c : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c := by
  obtain ⟨d, had, hbd, hcd⟩ := exists_one_more a b c hab hac hbc
  obtain ⟨σ, h0, h1, h2, -⟩ := exists_perm_four a b c d hab hac had hbc hbd hcd
  exact ⟨σ, h0, h1, h2⟩

theorem exists_perm_two (a b : Fin 4) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = a ∧ σ 1 = b := by
  obtain ⟨c, d, hac, had, hbc, hbd, hcd⟩ := exists_two_more a b hab
  obtain ⟨σ, h0, h1, -, -⟩ := exists_perm_four a b c d hab hac had hbc hbd hcd
  exact ⟨σ, h0, h1⟩

open CFSG.ClassicalInvolution.WeakCT

theorem blkLin_zero_one_eq : blkLin (F := F) 0 1 =
    ((blockSL2 F 3 0).range).map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom :=
  blkLin_succ_eq (F := F) 0

theorem blkLin_one_two_eq : blkLin (F := F) 1 2 =
    ((blockSL2 F 3 1).range).map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom :=
  blkLin_succ_eq (F := F) 1

theorem blkLin_zero_one_perfect [Finite F] (h4 : 4 ≤ Nat.card F) :
    ⁅blkLin (F := F) 0 1, blkLin (F := F) 0 1⁆ = blkLin (F := F) 0 1 := by
  have hSL : Group.IsPerfect SL(2, F) := CFSG.ClassicalInvolution.sl2_isPerfect h4
  have hR : ⁅(blockSL2 F 3 0).range, (blockSL2 F 3 0).range⁆ = (blockSL2 F 3 0).range :=
    Subgroup.isPerfect_iff.1 (Group.IsPerfect.range _)
  rw [blkLin_zero_one_eq, ← Subgroup.map_commutator, hR]

theorem blkLin_perfect [Finite F] (h4 : 4 ≤ Nat.card F) (a b : Fin 4) (hab : a ≠ b) :
    ⁅blkLin (F := F) a b, blkLin (F := F) a b⁆ = blkLin (F := F) a b := by
  obtain ⟨σ, h0, h1⟩ := exists_perm_two a b hab
  have hmap : blkLin (F := F) a b = (blkLin (F := F) 0 1).map (permS σ).toMonoidHom := by
    rw [map_permS_blkLin, h0, h1]
  rw [hmap, ← Subgroup.map_commutator, blkLin_zero_one_perfect h4]

theorem blkLin_equiv (a b : Fin 4) (hab : a ≠ b) : Nonempty (SL(2, F) ≃* ↥(blkLin (F := F) a b)) := by
  obtain ⟨σ, h0, h1⟩ := exists_perm_two a b hab
  let H : Subgroup SL(3 + 1, F) := (blockSL2 F 3 0).range
  have e1 : SL(2, F) ≃* H := MonoidHom.ofInjective (blockSL2_injective 3 0)
  have e2 : H ≃* H.map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom :=
    H.equivMapOfInjective _ (specialLinearGroupEquivStatedSL 4 F).injective
  have e3 : (H.map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom) ≃*
      (H.map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom).map (permS σ).toMonoidHom :=
    (H.map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom).equivMapOfInjective _
      (permS σ).injective
  have hH : H.map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom = blkLin (F := F) 0 1 :=
    blkLin_zero_one_eq.symm
  have e4 : ((H.map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom).map
      (permS σ).toMonoidHom) ≃* ↥(blkLin (F := F) a b) :=
    MulEquiv.subgroupCongr (by rw [hH, map_permS_blkLin, h0, h1])
  exact ⟨e1.trans (e2.trans (e3.trans e4))⟩

theorem blkLin_standardPair (a b c : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ W : Subgroup ↥(StatedSL 4 F),
      LinearBlockStandardPair F W (blkLin (F := F) a b) (blkLin b c) := by
  obtain ⟨σ, h0, h1, h2⟩ := exists_perm_three a b c hab hac hbc
  have hstd := (weakCTSystem_standard (K := F) 3).pair 0 1 rfl
  have hm1 := linearBlockStandardPair_map' hstd (specialLinearGroupEquivStatedSL 4 F).toMonoidHom
    (specialLinearGroupEquivStatedSL 4 F).injective
  have hm2 := linearBlockStandardPair_map' hm1 (permS σ).toMonoidHom (permS σ).injective
  have hU0 : (((blockSL2 F 3 0).range).map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom).map
      (permS σ).toMonoidHom = blkLin (F := F) a b := by
    rw [← blkLin_zero_one_eq, map_permS_blkLin, h0, h1]
  have hU1 : (((blockSL2 F 3 1).range).map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom).map
      (permS σ).toMonoidHom = blkLin (F := F) b c := by
    rw [← blkLin_one_two_eq, map_permS_blkLin, h1, h2]
  rw [hU0, hU1] at hm2
  exact ⟨_, hm2⟩

theorem blkLin_chain : ∃ W : Fin 3 → Fin 3 → Subgroup ↥(StatedSL 4 F),
    WeakCTSystem F 3 (fun i : Fin 3 => blkLin (F := F) (Fin.castSucc i) (Fin.succ i)) W := by
  have h := weakCTSystem_map_equiv (weakCTSystem_standard (K := F) 3)
    (specialLinearGroupEquivStatedSL 4 F)
  have hU : (fun i : Fin 3 => blkLin (F := F) (Fin.castSucc i) (Fin.succ i)) =
      fun i => ((blockSL2 F 3 i).range).map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom :=
    funext blkLin_succ_eq
  rw [hU]
  exact ⟨_, h⟩

@[expose] def IsDiagAt (c d : Fin 4) (M : Matrix (Fin 4) (Fin 4) F) : Prop :=
  ∀ i j : Fin 4, i ≠ j → (i = c ∨ i = d ∨ j = c ∨ j = d) → M i j = 0

theorem IsDiagAt.mul {c d : Fin 4} {M N : Matrix (Fin 4) (Fin 4) F} (hM : IsDiagAt c d M)
    (hN : IsDiagAt c d N) : IsDiagAt c d (M * N) := by
  intro i j hij hcd
  rw [Matrix.mul_apply]
  by_cases hi : i = c ∨ i = d
  · rw [Finset.sum_eq_single i]
    · rw [hN i j hij (by tauto), mul_zero]
    · intro k _ hk
      rw [hM i k (Ne.symm hk) (by tauto), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Finset.sum_eq_single j]
    · rw [hM i j hij (by tauto), zero_mul]
    · intro k _ hk
      rw [hN k j hk (by tauto), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h

theorem IsDiagAt.mul_apply_self {c d : Fin 4} {M : Matrix (Fin 4) (Fin 4) F} (hM : IsDiagAt c d M)
    (N : Matrix (Fin 4) (Fin 4) F) {x : Fin 4} (hx : x = c ∨ x = d) :
    (M * N) x x = M x x * N x x := by
  rw [Matrix.mul_apply, Finset.sum_eq_single x]
  · intro k _ hk
    rw [hM x k (Ne.symm hk) (by tauto), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ x) h

theorem isDiagAt_of_comm (h2 : (2 : F) ≠ 0) {c d : Fin 4} {M : Matrix (Fin 4) (Fin 4) F}
    (hc : M * reflDiagMat F c = reflDiagMat F c * M)
    (hd : M * reflDiagMat F d = reflDiagMat F d * M) : IsDiagAt c d M := by
  have key : ∀ e : Fin 4, M * reflDiagMat F e = reflDiagMat F e * M →
      ∀ i j : Fin 4, i ≠ j → (i = e ∨ j = e) → M i j = 0 := by
    intro e he i j hij hij'
    have h := congrFun (congrFun he i) j
    simp only [reflDiagMat, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    rcases hij' with rfl | rfl
    · have e1 : (if j = i then (-1 : F) else 1) = 1 := by simp [Ne.symm hij]
      have e2 : (if i = i then (-1 : F) else 1) = -1 := by simp
      rw [e1, e2] at h
      have h' : (2 : F) * M i j = 0 := by linear_combination h
      exact (mul_eq_zero.1 h').resolve_left h2
    · have e1 : (if j = j then (-1 : F) else 1) = -1 := by simp
      have e2 : (if i = j then (-1 : F) else 1) = 1 := by simp [hij]
      rw [e1, e2] at h
      have h' : (2 : F) * M i j = 0 := by linear_combination (-1 : F) * h
      exact (mul_eq_zero.1 h').resolve_left h2
  intro i j hij hcd
  rcases hcd with h | h | h | h
  · exact key c hc i j hij (Or.inl h)
  · exact key d hd i j hij (Or.inl h)
  · exact key c hc i j hij (Or.inr h)
  · exact key d hd i j hij (Or.inr h)

theorem perfect_le_blkLin (h2 : (2 : F) ≠ 0) (a b c d : Fin 4) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (P : Subgroup ↥(StatedSL 4 F))
    (hP : ∀ g ∈ P, (g : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (g : GL (Fin 4) F) ∧
      (g : GL (Fin 4) F) * reflDiag F d = reflDiag F d * (g : GL (Fin 4) F))
    (hperf : ⁅P, P⁆ = P) : P ≤ blkLin a b := by
  have hall := fin4_cases a b c d hab hac had hbc hbd hcd
  have hdiag : ∀ g ∈ P, IsDiagAt c d ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    intro g hg
    obtain ⟨h1, h3⟩ := hP g hg
    refine isDiagAt_of_comm h2 ?_ ?_
    · have := congrArg Units.val h1
      rw [Units.val_mul, Units.val_mul] at this
      exact this
    · have := congrArg Units.val h3
      rw [Units.val_mul, Units.val_mul] at this
      exact this
  conv_lhs => rw [← hperf]
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hgi : IsDiagAt c d (((g⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) :=
    hdiag _ (P.inv_mem hg)
  have hhi : IsDiagAt c d (((h⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) :=
    hdiag _ (P.inv_mem hh)
  have hgd := hdiag g hg
  have hhd := hdiag h hh
  have hQ : (((⁅g, h⁆ : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (g : GL (Fin 4) F) * (h : GL (Fin 4) F) * ((g⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F) *
        ((h⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F) := by
    rw [commutatorElement_def]
    simp [mul_assoc]
  set G : Matrix (Fin 4) (Fin 4) F := (((g : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hG
  set Hm : Matrix (Fin 4) (Fin 4) F := (((h : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hHm
  set Gi : Matrix (Fin 4) (Fin 4) F := (((g⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hGi
  set Hi : Matrix (Fin 4) (Fin 4) F := (((h⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hHi
  have hGGi : G * Gi = 1 := by
    have h1 : ((g : GL (Fin 4) F) * (g : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) = 1 := mul_inv_cancel _
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, Units.val_one] at h2
    exact h2
  have hHHi : Hm * Hi = 1 := by
    have h1 : ((h : GL (Fin 4) F) * (h : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) = 1 := mul_inv_cancel _
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, Units.val_one] at h2
    exact h2
  have hQd : IsDiagAt c d (G * Hm * Gi * Hi) := ((hgd.mul hhd).mul hgi).mul hhi
  have hdiag1 : ∀ x : Fin 4, (x = c ∨ x = d) → (G * Hm * Gi * Hi) x x = 1 := by
    intro x hx
    have e1 : G x x * Gi x x = 1 := by
      have := hgd.mul_apply_self Gi hx
      rw [hGGi, Matrix.one_apply_eq] at this
      exact this.symm
    have e2 : Hm x x * Hi x x = 1 := by
      have := hhd.mul_apply_self Hi hx
      rw [hHHi, Matrix.one_apply_eq] at this
      exact this.symm
    rw [((hgd.mul hhd).mul hgi).mul_apply_self Hi hx, (hgd.mul hhd).mul_apply_self Gi hx,
      hgd.mul_apply_self Hm hx]
    calc G x x * Hm x x * Gi x x * Hi x x = (G x x * Gi x x) * (Hm x x * Hi x x) := by ring
      _ = 1 := by rw [e1, e2, one_mul]
  rw [mem_blkLin, hQ]
  intro i j hij
  have hout : ∀ x : Fin 4, ¬ (x = a ∨ x = b) → (x = c ∨ x = d) := by
    intro x hx
    rcases hall x with h' | h' | h' | h'
    · exact absurd (Or.inl h') hx
    · exact absurd (Or.inr h') hx
    · exact Or.inl h'
    · exact Or.inr h'
  by_cases hij' : i = j
  · subst hij'
    have hi : ¬ (i = a ∨ i = b) := fun h' => hij ⟨h', h'⟩
    rw [hdiag1 i (hout i hi), Matrix.one_apply_eq]
  · have hcd' : i = c ∨ i = d ∨ j = c ∨ j = d := by
      by_cases hi : i = a ∨ i = b
      · have hj : ¬ (j = a ∨ j = b) := fun hj => hij ⟨hi, hj⟩
        have := hout j hj
        tauto
      · have := hout i hi
        tauto
    rw [hQd i j hij' hcd', Matrix.one_apply_ne hij']

theorem blkLin_commute (a b c d : Fin 4) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∀ g ∈ blkLin (F := F) a b, ∀ h ∈ blkLin (F := F) c d, g * h = h * g := by
  intro g hg h hh
  refine Subtype.ext (Units.ext ?_)
  show (((g : GL (Fin 4) F) * (h : GL (Fin 4) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
    (((h : GL (Fin 4) F) * (g : GL (Fin 4) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  rw [Units.val_mul, Units.val_mul]
  refine IsBlockAt.commute (fun k hk hk' => ?_) hg hh
  rcases hk with rfl | rfl <;> rcases hk' with h' | h'
  · exact hac h'
  · exact had h'
  · exact hbc h'
  · exact hbd h'

theorem blkLin_comm_refl (a b c : Fin 4) (hca : c ≠ a) (hcb : c ≠ b) :
    ∀ g ∈ blkLin (F := F) a b,
      (g : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (g : GL (Fin 4) F) := by
  intro g hg
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact IsBlockAt.comm_reflDiagMat hca hcb hg

@[expose] noncomputable def linBlockOps {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (h4 : 3 < Nat.card F) : BlockOps F (StatedSL 4 F) where
  blk := blkLin
  blk_symm := blkLin_symm
  perfect := fun a b hab => blkLin_perfect (by omega) a b hab
  commute := fun a b c d _ _ hac had hbc hbd => blkLin_commute a b c d hac had hbc hbd
  comm_refl := fun a b c _ hca hcb => blkLin_comm_refl a b c hca hcb
  perfect_le := fun a b c d hab hac had hbc hbd hcd P hP hperf =>
    perfect_le_blkLin (two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))) a b c d hab hac had hbc
      hbd hcd P hP hperf

theorem linBlockOps_blk {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (h4 : 3 < Nat.card F) (a b : Fin 4) : (linBlockOps hF h4).blk a b = blkLin a b := rfl

theorem lin_blk_equiv {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (h4 : 3 < Nat.card F) :
    ∀ a b : Fin 4, a ≠ b → Nonempty (SL(2, F) ≃* ↥((linBlockOps hF h4).blk a b)) :=
  fun a b hab => blkLin_equiv a b hab

theorem lin_std {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3) (h4 : 3 < Nat.card F) :
    ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c → ∃ W : Subgroup ↥(StatedSL 4 F),
      CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair F W
        ((linBlockOps hF h4).blk a b) ((linBlockOps hF h4).blk b c) :=
  fun a b c hab hac hbc => blkLin_standardPair a b c hab hac hbc

theorem lin_chain {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3) (h4 : 3 < Nat.card F) :
    ∃ W : Fin 3 → Fin 3 → Subgroup ↥(StatedSL 4 F),
      CFSG.ClassicalInvolution.WeakCT.WeakCTSystem F 3
        (fun i : Fin 3 => (linBlockOps hF h4).blk (Fin.castSucc i) (Fin.succ i)) W :=
  blkLin_chain

theorem IsBlockAt.comm_diagonal {a b : Fin 4} {M : Matrix (Fin 4) (Fin 4) F} (hM : IsBlockAt a b M)
    (d : Fin 4 → F) (hd : d a = d b) : M * diagonal d = diagonal d * M := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst hij
    exact mul_comm _ _
  · by_cases hin : (i = a ∨ i = b) ∧ (j = a ∨ j = b)
    · have : d i = d j := by
        rcases hin with ⟨h1 | h1, h2 | h2⟩ <;> rw [h1, h2] <;> first | rfl | exact hd | exact hd.symm
      rw [this, mul_comm]
    · rw [hM i j hin, Matrix.one_apply_ne hij, zero_mul, mul_zero]

@[expose] def zDiag (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  Matrix.diagonal ![-1, -1, 1, 1]

theorem zDiag_mul_self : zDiag F * zDiag F = 1 := by
  rw [zDiag, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

theorem det_zDiag : (zDiag F).det = 1 := by
  simp [zDiag, det_diagonal, Fin.prod_univ_four]

theorem isBlockAt_zDiag : IsBlockAt (0 : Fin 4) 1 (zDiag F) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [zDiag] at hij ⊢

theorem lin_blk_center {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (h4 : 3 < Nat.card F) :
    ∃ z ∈ (linBlockOps hF h4).blk 0 1, orderOf z = 2 ∧
      ∀ g ∈ (linBlockOps hF h4).blk 0 1, g * z = z * g := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
  let zS : ↥(StatedSL 4 F) :=
    ⟨⟨zDiag F, zDiag F, zDiag_mul_self, zDiag_mul_self⟩, by
      rw [statedSL_eq_detOne, mem_detOne]
      exact det_zDiag⟩
  have hz1 : zS ≠ 1 := by
    intro h
    have h' := congrArg (fun x : ↥(StatedSL 4 F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0) h
    simp only [zS, zDiag, Matrix.diagonal_apply_eq] at h'
    apply h2
    have h'' : (-1 : F) = 1 := by simpa using h'
    linear_combination -h''
  have hzz : zS ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (Units.ext zDiag_mul_self)
  refine ⟨zS, isBlockAt_zDiag, ?_, fun g hg => ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hzz hz1
  · refine Subtype.ext (Units.ext ?_)
    show (((g : GL (Fin 4) F) * (zS : GL (Fin 4) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (((zS : GL (Fin 4) F) * (g : GL (Fin 4) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [Units.val_mul, Units.val_mul]
    exact IsBlockAt.comm_diagonal hg ![-1, -1, 1, 1] rfl

end CFSG.GH74.Generic.S1
