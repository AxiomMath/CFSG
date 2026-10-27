module

public import CFSG.GH74.Generic.BProg.B2.GenLocU3E8Gen

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.GH74.Generic.BProg.B2.GenLocU3Blk CFSG.GH74.Generic.BProg.B2.GenLocU3Good
  CFSG.GH74.Generic.BProg.B2.GenLocU3Lift CFSG.GH74.Generic.BProg.B2.GenLocU3E8Elem
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.KGroups.L3Eps.Uni
open scoped MatrixGroups

namespace GenLocU3E8Core

theorem adm_closure_pair {A : Type} [Group A] [Finite A] (hA : IsRank23 A) {u v : A} (hu : u ≠ 1)
    (hv : v ≠ 1) (huv : u ≠ v) :
    pRank 2 A - 1 ≤ pRank 2 ↥(Subgroup.closure ({u, v} : Set A)) := by
  classical
  rw [GenLocBasic.adm_iff_index hA.1]
  have hcardA : Nat.card A = 2 ^ pRank 2 A := GenLocBasic.card_eq_two_pow_pRank_type hA.1
  have hle8 : Nat.card A ≤ 8 := by
    rcases hA.2 with h | h <;> rw [hcardA, h] <;> norm_num
  set E : Subgroup A := Subgroup.closure ({u, v} : Set A) with hE
  have hmul := Subgroup.card_mul_index E
  have hsq : ∀ x : A, x * x = 1 := fun x => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 x
  have hinv : ∀ x : A, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have huv1 : u * v ≠ 1 := by
    intro h1
    apply huv
    have : v = u⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, hinv]
  have huvu : u * v ≠ u := by
    intro h1
    exact hv (by simpa using h1)
  have huvv : u * v ≠ v := by
    intro h1
    exact hu (by simpa using h1)
  have e1 : (1 : A) ∉ ({u, v, u * v} : Finset A) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hu, Ne.symm hv, Ne.symm huv1⟩
  have e2 : u ∉ ({v, u * v} : Finset A) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨huv, Ne.symm huvu⟩
  have hc4 : ({1, u, v, u * v} : Finset A).card = 4 := by
    rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
      Finset.card_pair (Ne.symm huvv)]
  have hsub : (↑({1, u, v, u * v} : Finset A) : Set A) ⊆ (E : Set A) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact E.one_mem
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact E.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have h4 : 4 ≤ Nat.card E := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hc4] at this
    rwa [← Nat.card_coe_set_eq] at this
  nlinarith

theorem mem_gammaAct_of_fixed_pair {J : Type} [Group J] {A : Type} [Group A] [Finite A]
    (hA : IsRank23 A) (α : A →* MulAut J) {u v : A} (hu : u ≠ 1) (hv : v ≠ 1) (huv : u ≠ v) {x : J}
    (hxu : α u x = x) (hxv : α v x = x) : x ∈ gammaAct α := by
  refine le_gammaAct α (adm_closure_pair hA hu hv huv) ((GenLocBasic.mem_fixedIn_map α _ x).2 ?_)
  have hle : Subgroup.closure ({u, v} : Set A) ≤
      (MulAction.stabilizer (MulAut J) x).comap α := by
    rw [Subgroup.closure_le]
    intro e he
    rcases he with rfl | he
    · exact (MulAction.mem_stabilizer_iff).2 hxu
    · rw [Set.mem_singleton_iff] at he
      rw [he]
      exact (MulAction.mem_stabilizer_iff).2 hxv
  intro e he
  exact (MulAction.mem_stabilizer_iff).1 (hle he)

variable {p f : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F p]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem diag_comm_of {D M : Matrix (Fin 3) (Fin 3) F} (hD : D.IsDiag)
    (h : ∀ i j, D i i * M i j = M i j * D j j) : D * M = M * D := by
  have hD' := hD.diagonal_diag
  calc D * M = Matrix.diagonal D.diag * M := by rw [hD']
    _ = M * Matrix.diagonal D.diag := by
        ext i j
        rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
        exact h i j
    _ = M * D := by rw [hD']

theorem comm_iota1 {D : Matrix (Fin 3) (Fin 3) F} (hD : D.IsDiag) (he : D 1 1 = D 2 2)
    (y : Su F p f 2) :
    D * (((blockEmb2 F p f 2 1 y : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (((blockEmb2 F p f 2 1 y : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * D := by
  refine diag_comm_of hD fun i j => ?_
  rw [coe_iota1]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Fin.reduceFinMk, Fin.mk_one] <;>
    first | ring1 | (rw [he]; ring1)

theorem comm_iota0 {D : Matrix (Fin 3) (Fin 3) F} (hD : D.IsDiag) (he : D 0 0 = D 1 1)
    (y : Su F p f 2) :
    D * (((blockEmb2 F p f 2 0 y : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (((blockEmb2 F p f 2 0 y : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * D := by
  refine diag_comm_of hD fun i j => ?_
  rw [coe_iota0]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Fin.reduceFinMk, Fin.mk_one] <;>
    first | ring1 | (rw [he]; ring1)

theorem comm_iota0_t {h : UnitaryFieldData p f F} (D : Gauss h) {M : Matrix (Fin 3) (Fin 3) F}
    (hM : M.IsDiag) :
    M * (((blockEmb2 F p f 2 0 D.tSu : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (((blockEmb2 F p f 2 0 D.tSu : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M := by
  refine diag_comm_of hM fun i j => ?_
  rw [coe_iota0, D.ym_tSu]
  fin_cases i <;> fin_cases j <;>
    simp only [Gauss.tMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    ring

theorem comm_iota1_t {h : UnitaryFieldData p f F} (D : Gauss h) {M : Matrix (Fin 3) (Fin 3) F}
    (hM : M.IsDiag) :
    M * (((blockEmb2 F p f 2 1 D.tSu : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (((blockEmb2 F p f 2 1 D.tSu : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M := by
  refine diag_comm_of hM fun i j => ?_
  rw [coe_iota1, D.ym_tSu]
  fin_cases i <;> fin_cases j <;>
    simp only [Gauss.tMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    ring

theorem map_iota0_r {h : UnitaryFieldData p f F} (D : Gauss h) (ψ : F ≃+* F) :
    (((blockEmb2 F p f 2 0 D.rSu : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map ψ =
      (((blockEmb2 F p f 2 0 D.rSu : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have h2 : ψ (2 : F) = 2 := map_ofNat ψ 2
  rw [coe_iota0, D.ym_rSu, rMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, h2]

theorem map_iota1_r {h : UnitaryFieldData p f F} (D : Gauss h) (ψ : F ≃+* F) :
    (((blockEmb2 F p f 2 1 D.rSu : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map ψ =
      (((blockEmb2 F p f 2 1 D.rSu : Su F p f 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have h2 : ψ (2 : F) = 2 := map_ofNat ψ 2
  rw [coe_iota1, D.ym_rSu, rMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, h2]

theorem fixed_of_lift (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} {x : MulAut J} {A' : GL (Fin 3) F} {ψ : F ≃+* F}
    (hl : IsLift θ A' ψ x) (g : Su F p f 3)
    (hg : A' * glAut ψ (g : GL (Fin 3) F) = (g : GL (Fin 3) F) * A') :
    x (θ (suEquiv h 3 g)) = θ (suEquiv h 3 g) := by
  obtain ⟨g', hg1, hg2⟩ := hl (suEquiv h 3 g)
  have : g' = suEquiv h 3 g := by
    apply Subtype.ext
    rw [hg1]
    change A' * glAut ψ (g : GL (Fin 3) F) * A'⁻¹ = (g : GL (Fin 3) F)
    rw [hg]
    group
  rw [← hg2, this]

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem glAut_one_apply' (g : GL (Fin 3) F) : glAut (1 : F ≃+* F) g = g := by
  rw [map_one]; rfl

theorem fixed_of_lift_one (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} {x : MulAut J} {A' : GL (Fin 3) F} (hl : IsLift θ A' 1 x)
    (g : Su F p f 3)
    (hg : (A' : Matrix (Fin 3) (Fin 3) F) * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A' : Matrix (Fin 3) (Fin 3) F)) :
    x (θ (suEquiv h 3 g)) = θ (suEquiv h 3 g) :=
  fixed_of_lift h hl g (by
    rw [glAut_one_apply']
    apply Units.ext
    simpa only [Units.val_mul] using hg)

theorem fixed_of_lift_real (h : UnitaryFieldData p f F) {J : Type} [Group J]
    {θ : ↥(unitarySU p f F 3) →* J} {x : MulAut J} {A' : GL (Fin 3) F} {ψ : F ≃+* F}
    (hl : IsLift θ A' ψ x) (g : Su F p f 3)
    (hreal : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map ψ =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (hg : (A' : Matrix (Fin 3) (Fin 3) F) * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A' : Matrix (Fin 3) (Fin 3) F)) :
    x (θ (suEquiv h 3 g)) = θ (suEquiv h 3 g) :=
  fixed_of_lift h hl g (Units.ext (by
    simpa only [Units.val_mul, coe_glAut, hreal] using hg))

theorem gammaAct_eq_top_core (h : UnitaryFieldData p f F) (hq : p ^ f = 7) (D : Gauss h)
    {J : Type} [Group J] {θ : ↥(unitarySU p f F 3) →* J} (hθ : IsCover h θ)
    {A : Type} [Group A] [Finite A] (hA : IsRank23 A) (α : A →* MulAut J)
    {a₁ a₃ a : A} (h1 : a₁ ≠ 1) (h3 : a₃ ≠ 1) (ha : a ≠ 1) (h13 : a₁ ≠ a₃) (h1a : a₁ ≠ a)
    (h3a : a₃ ≠ a) {Δ₁ Δ₃ Λ : GL (Fin 3) F} {ψ : F ≃+* F}
    (hl₁ : IsLift θ Δ₁ 1 (α a₁)) (hd₁ : ((Δ₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (he₁ : (Δ₁ : Matrix (Fin 3) (Fin 3) F) 1 1 = (Δ₁ : Matrix (Fin 3) (Fin 3) F) 2 2)
    (hl₃ : IsLift θ Δ₃ 1 (α a₃)) (hd₃ : ((Δ₃ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (he₃ : (Δ₃ : Matrix (Fin 3) (Fin 3) F) 0 0 = (Δ₃ : Matrix (Fin 3) (Fin 3) F) 1 1)
    (hl : IsLift θ Λ ψ (α a))
    (hΛ : ∀ M : Matrix (Fin 3) (Fin 3) F,
      (Λ : Matrix (Fin 3) (Fin 3) F) * M = M * (Λ : Matrix (Fin 3) (Fin 3) F)) :
    gammaAct α = ⊤ := by
  set H : Subgroup (Su F p f 3) := (gammaAct α).comap (θ.comp (suEquiv h 3).toMonoidHom) with hH
  have hmem : ∀ g : Su F p f 3, g ∈ H ↔ θ (suEquiv h 3 g) ∈ gammaAct α := fun g => Iff.rfl
  have hT1 : blockEmb2 F p f 2 0 D.tSu ∈ H := by
    rw [hmem]
    exact mem_gammaAct_of_fixed_pair hA α h1 h3 h13
      (fixed_of_lift_one h hl₁ _ (comm_iota0_t D hd₁)) (fixed_of_lift_one h hl₃ _ (comm_iota0_t D hd₃))
  have hT2 : blockEmb2 F p f 2 1 D.tSu ∈ H := by
    rw [hmem]
    exact mem_gammaAct_of_fixed_pair hA α h1 h3 h13
      (fixed_of_lift_one h hl₁ _ (comm_iota1_t D hd₁)) (fixed_of_lift_one h hl₃ _ (comm_iota1_t D hd₃))
  have hR23 : blockEmb2 F p f 2 1 D.rSu ∈ H := by
    rw [hmem]
    exact mem_gammaAct_of_fixed_pair hA α h1 ha h1a
      (fixed_of_lift_one h hl₁ _ (comm_iota1 hd₁ he₁ D.rSu))
      (fixed_of_lift_real h hl _ (map_iota1_r D ψ) (hΛ _))
  have hR12 : blockEmb2 F p f 2 0 D.rSu ∈ H := by
    rw [hmem]
    exact mem_gammaAct_of_fixed_pair hA α h3 ha h3a
      (fixed_of_lift_one h hl₃ _ (comm_iota0 hd₃ he₃ D.rSu))
      (fixed_of_lift_real h hl _ (map_iota0_r D ψ) (hΛ _))
  have htop : H = ⊤ := GenLocU3E8Gen.eq_top_of_generators h hq D H hT1 hT2 hR12 hR23
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨g, rfl⟩ := hθ.surj x
  have hg : (suEquiv h 3).symm g ∈ H := htop ▸ Subgroup.mem_top _
  rw [hmem, MulEquiv.apply_symm_apply] at hg
  exact hg

end GenLocU3E8Core

end CFSG.GH74.Generic.BProg.B2
