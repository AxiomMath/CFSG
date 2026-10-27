module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4OutC
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAProj
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Odd
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvBlock

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups commutatorElement

section Defs

variable (F : Type) [Field F]

@[expose] def kaL4B3Mat : Matrix (Fin 4) (Fin 4) F :=
  Matrix.diagonal fun i : Fin 4 => if (i : ℕ) < 3 then (1 : F) else -1

theorem kaL4B3Mat_mul_self : kaL4B3Mat F * kaL4B3Mat F = 1 := by
  rw [kaL4B3Mat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

@[expose] def kaL4B3GL : GL (Fin 4) F :=
  ⟨kaL4B3Mat F, kaL4B3Mat F, kaL4B3Mat_mul_self F, kaL4B3Mat_mul_self F⟩

theorem coe_kaL4B3GL : ((kaL4B3GL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = kaL4B3Mat F :=
  rfl

theorem kaL4B3GL_mul_self : kaL4B3GL F * kaL4B3GL F = 1 :=
  Units.ext (by rw [Units.val_mul, coe_kaL4B3GL, kaL4B3Mat_mul_self, Units.val_one])

theorem kaL4B3GL_inv : (kaL4B3GL F)⁻¹ = kaL4B3GL F :=
  inv_eq_of_mul_eq_one_right (kaL4B3GL_mul_self F)

@[expose] def kaL4B3E : Fin 4 → F := Pi.single 3 1

theorem kaL4B3E_apply (i : Fin 4) : kaL4B3E F i = if i = 3 then 1 else 0 := by
  simp [kaL4B3E, Pi.single_apply]

@[expose] def kaL4B3Phi : SL(3, F) →* projectiveSL 4 F := (proj 4 F).comp eLastHom

end Defs

section Frame

variable {F : Type} [Field F]

theorem kaL4B3_exists_frame (hK : ringChar F ≠ 2) {B : GL (Fin 4) F} (hB : B * B = 1)
    (h3 : Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 3) :
    ∃ P : GL (Fin 4) F, B = P * kaL4B3GL F * P⁻¹ := by
  have hBm : (B : Matrix (Fin 4) (Fin 4) F) * B = 1 := by
    rw [← Units.val_mul, hB, Units.val_one]
  obtain ⟨b, hb⟩ := exists_eigenbasis hK hBm
  obtain ⟨P, D, hPD, hD⟩ := exists_gl_inv_mul_mul_eq_toMatrix b B
  have hDd : (D : Matrix (Fin 4) (Fin 4) F) = kaL4B3Mat F := by
    rw [hD, kaL4B3Mat]
    ext a c
    rw [LinearMap.toMatrix_apply, toLin'_apply, hb c, h3, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, diagonal_apply]
    by_cases hac : a = c
    · subst hac
      simp
    · simp [hac, Ne.symm hac]
  refine ⟨P, ?_⟩
  have hDe : D = kaL4B3GL F := Units.ext hDd
  rw [← hDe, ← hPD]
  group

end Frame

section Vec

variable {F : Type} [Field F]

@[expose] def kaL4B3Has (M : Matrix (Fin 4) (Fin 4) F) (z : F) : Prop :=
  M *ᵥ kaL4B3E F = z • kaL4B3E F ∧ kaL4B3E F ᵥ* M = z • kaL4B3E F

theorem kaL4B3Has_mul {M N : Matrix (Fin 4) (Fin 4) F} {z w : F} (hM : kaL4B3Has M z)
    (hN : kaL4B3Has N w) : kaL4B3Has (M * N) (z * w) := by
  refine ⟨?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, hN.1, Matrix.mulVec_smul, hM.1, smul_smul, mul_comm]
  · rw [← Matrix.vecMul_vecMul, hM.2, Matrix.smul_vecMul, hN.2, smul_smul]

theorem kaL4B3Has_inv {M N : Matrix (Fin 4) (Fin 4) F} {z : F} (h1 : M * N = 1) (h2 : N * M = 1)
    (hM : kaL4B3Has M z) : z ≠ 0 ∧ kaL4B3Has N z⁻¹ := by
  have hrow : kaL4B3E F = z • (kaL4B3E F ᵥ* N) := by
    calc kaL4B3E F = kaL4B3E F ᵥ* (M * N) := by rw [h1, Matrix.vecMul_one]
      _ = (kaL4B3E F ᵥ* M) ᵥ* N := (Matrix.vecMul_vecMul _ _ _).symm
      _ = z • (kaL4B3E F ᵥ* N) := by rw [hM.2, Matrix.smul_vecMul]
  have hcol : kaL4B3E F = z • (N *ᵥ kaL4B3E F) := by
    calc kaL4B3E F = (N * M) *ᵥ kaL4B3E F := by rw [h2, Matrix.one_mulVec]
      _ = N *ᵥ (M *ᵥ kaL4B3E F) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = z • (N *ᵥ kaL4B3E F) := by rw [hM.1, Matrix.mulVec_smul]
  have hz : z ≠ 0 := by
    rintro rfl
    have := congrFun hrow 3
    simp [kaL4B3E_apply] at this
  refine ⟨hz, ?_, ?_⟩
  · calc N *ᵥ kaL4B3E F = z⁻¹ • (z • (N *ᵥ kaL4B3E F)) := by
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = z⁻¹ • kaL4B3E F := by rw [← hcol]
  · calc kaL4B3E F ᵥ* N = z⁻¹ • (z • (kaL4B3E F ᵥ* N)) := by
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = z⁻¹ • kaL4B3E F := by rw [← hrow]

theorem kaL4B3Has_inv_sl {g : SL(4, F)} {z : F}
    (hg : kaL4B3Has (g : Matrix (Fin 4) (Fin 4) F) z) :
    z ≠ 0 ∧ kaL4B3Has ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) z⁻¹ := by
  refine kaL4B3Has_inv (M := (g : Matrix (Fin 4) (Fin 4) F)) ?_ ?_ hg
  · rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  · rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem kaL4B3_entries (h2 : (2 : F) ≠ 0) {c : Matrix (Fin 4) (Fin 4) F}
    (hc : c * kaL4B3Mat F = kaL4B3Mat F * c) :
    (∀ i : Fin 4, i ≠ 3 → c i 3 = 0) ∧ (∀ j : Fin 4, j ≠ 3 → c 3 j = 0) := by
  have key : ∀ x : F, -x = x → x = 0 := fun x hx => by
    have : (2 : F) * x = 0 := by linear_combination -hx
    exact (mul_eq_zero.1 this).resolve_left h2
  constructor
  · intro i hi
    have h := congrFun (congrFun hc i) 3
    rw [kaL4B3Mat, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    fin_cases i
    · exact key _ (by simpa using h)
    · exact key _ (by simpa using h)
    · exact key _ (by simpa using h)
    · exact absurd rfl hi
  · intro j hj
    have h := congrFun (congrFun hc 3) j
    rw [kaL4B3Mat, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    fin_cases j
    · exact key _ (by simpa using h.symm)
    · exact key _ (by simpa using h.symm)
    · exact key _ (by simpa using h.symm)
    · exact absurd rfl hj

theorem kaL4B3_has_of_comm (h2 : (2 : F) ≠ 0) {c : Matrix (Fin 4) (Fin 4) F}
    (hc : c * kaL4B3Mat F = kaL4B3Mat F * c) : kaL4B3Has c (c 3 3) := by
  obtain ⟨hcol, hrow⟩ := kaL4B3_entries h2 hc
  refine ⟨?_, ?_⟩
  · funext i
    simp only [Matrix.mulVec, dotProduct, kaL4B3E_apply, Pi.smul_apply, smul_eq_mul]
    simp
    by_cases hi : i = 3
    · subst hi
      simp
    · rw [hcol i hi]
      simp [hi]
  · funext j
    simp only [Matrix.vecMul, dotProduct, kaL4B3E_apply, Pi.smul_apply, smul_eq_mul]
    simp
    by_cases hj : j = 3
    · subst hj
      simp
    · rw [hrow j hj]
      simp [hj]

end Vec

section Block

variable {F : Type} [Field F]

theorem kaL4B3_eLast_col (A : Matrix (Fin 3) (Fin 3) F) (i : Fin 4) :
    eLast A i 3 = if i = 3 then 1 else 0 := by
  fin_cases i <;> simp [eLast]

theorem kaL4B3_eLast_row (A : Matrix (Fin 3) (Fin 3) F) (j : Fin 4) :
    eLast A 3 j = if j = 3 then 1 else 0 := by
  fin_cases j <;> simp [eLast]

theorem kaL4B3Has_eLast (A : Matrix (Fin 3) (Fin 3) F) : kaL4B3Has (eLast A) 1 := by
  refine ⟨?_, ?_⟩
  · funext i
    simp [Matrix.mulVec, dotProduct, kaL4B3E_apply, kaL4B3_eLast_col]
  · funext j
    simp [Matrix.vecMul, dotProduct, kaL4B3E_apply, kaL4B3_eLast_row]

theorem kaL4B3_exists_eLast {k : SL(4, F)} (h : kaL4B3Has (k : Matrix (Fin 4) (Fin 4) F) 1) :
    ∃ A : SL(3, F), eLastHom A = k := by
  have hcol : ∀ i : Fin 4, (k : Matrix (Fin 4) (Fin 4) F) i 3 = if i = 3 then 1 else 0 := by
    intro i
    have := congrFun h.1 i
    simpa [Matrix.mulVec, dotProduct, kaL4B3E_apply] using this
  have hrow : ∀ j : Fin 4, (k : Matrix (Fin 4) (Fin 4) F) 3 j = if j = 3 then 1 else 0 := by
    intro j
    have := congrFun h.2 j
    simpa [Matrix.vecMul, dotProduct, kaL4B3E_apply] using this
  set A : Matrix (Fin 3) (Fin 3) F :=
    Matrix.of fun i j => (k : Matrix (Fin 4) (Fin 4) F) i.castSucc j.castSucc with hA
  have hk : (k : Matrix (Fin 4) (Fin 4) F) = eLast A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [eLast, hA, hcol, hrow]
  have hdet : A.det = 1 := by
    rw [← det_eLast, ← hk]
    exact k.2
  exact ⟨(⟨A, hdet⟩ : SL(3, F)), Subtype.ext hk.symm⟩

theorem kaL4B3_eLast_comm (A : Matrix (Fin 3) (Fin 3) F) :
    eLast A * kaL4B3Mat F = kaL4B3Mat F * eLast A := by
  rw [kaL4B3Mat]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [eLast]

end Block

section Struct

variable {F : Type} [Field F]

theorem kaL4B3_mem_cent {g : SL(4, F)} :
    g ∈ kaSlCent (kaL4B3GL F) ↔
      (g : Matrix (Fin 4) (Fin 4) F) * kaL4B3Mat F = kaL4B3Mat F * g := by
  rw [kaSlCent, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have h1 := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F))
      (h (kaL4B3GL F) (Set.mem_singleton _))
    simp only [Units.val_mul, coe_kaL4B3GL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h1
    exact h1.symm
  · intro h x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    apply Units.ext
    simp only [Units.val_mul, coe_kaL4B3GL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact h.symm

theorem kaL4B3_eLast_mem_cent (A : SL(3, F)) : eLastHom A ∈ kaSlCent (kaL4B3GL F) := by
  rw [kaL4B3_mem_cent, coe_eLastHom]
  exact kaL4B3_eLast_comm _

theorem kaL4B3_range_le_map :
    (kaL4B3Phi F).range ≤ (kaSlCent (kaL4B3GL F)).map (proj 4 F) := by
  rintro _ ⟨A, rfl⟩
  exact ⟨eLastHom A, kaL4B3_eLast_mem_cent A, rfl⟩

theorem kaL4B3_map_le_fix {x : projectiveSL 4 F}
    (hx : x ∈ (kaSlCent (kaL4B3GL F)).map (proj 4 F)) : conjAut 4 F (kaL4B3GL F) x = x := by
  obtain ⟨g, hg, rfl⟩ := hx
  have hc := kaL4B3_mem_cent.1 hg
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, kaL4B3GL_inv, coe_kaL4B3GL, ← hc, Matrix.mul_assoc,
    kaL4B3Mat_mul_self, Matrix.mul_one]

theorem kaL4B3_conj_mem_range (h2 : (2 : F) ≠ 0) {c : SL(4, F)} (hc : c ∈ kaSlCent (kaL4B3GL F))
    (A : SL(3, F)) : ∃ A' : SL(3, F), eLastHom A' = c * eLastHom A * c⁻¹ := by
  apply kaL4B3_exists_eLast
  have h1 := kaL4B3_has_of_comm h2 (kaL4B3_mem_cent.1 hc)
  obtain ⟨hz, hinv⟩ := kaL4B3Has_inv_sl h1
  have h3 := kaL4B3Has_mul (kaL4B3Has_mul h1 (kaL4B3Has_eLast (A : Matrix (Fin 3) (Fin 3) F)))
    hinv
  rw [mul_one, mul_inv_cancel₀ hz] at h3
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_eLastHom]
  exact h3

theorem kaL4B3_normalizes (h2 : (2 : F) ≠ 0) :
    ∀ x ∈ (kaSlCent (kaL4B3GL F)).map (proj 4 F),
      x ∈ normalizer ((kaL4B3Phi F).range : Set (projectiveSL 4 F)) := by
  have key : ∀ x ∈ (kaSlCent (kaL4B3GL F)).map (proj 4 F), ∀ l ∈ (kaL4B3Phi F).range,
      x * l * x⁻¹ ∈ (kaL4B3Phi F).range := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨A, rfl⟩
    obtain ⟨A', hA'⟩ := kaL4B3_conj_mem_range h2 hc A
    refine ⟨A', ?_⟩
    change proj 4 F (eLastHom A') = _
    rw [hA', map_mul, map_mul, map_inv]
    rfl
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · exact fun hl => key x hx l hl
  · intro hl
    have := key x⁻¹ (inv_mem hx) _ hl
    simpa [mul_assoc] using this

theorem kaL4B3_perfect : ⁅(kaL4B3Phi F).range, (kaL4B3Phi F).range⁆ = (kaL4B3Phi F).range := by
  have hP : Group.IsPerfect SL(3, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
    Group.isPerfect_def.mp hP]

theorem kaL4B3_quasisimple : CFSG.IsQuasisimple SL(3, F) := by
  have hperf : Group.IsPerfect SL(3, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by omega) (Or.inl le_rfl)
  refine ⟨hperf, hsimple, ?_⟩
  by_contra h
  push Not at h
  have : IsMulCommutative (SL(3, F) ⧸ Subgroup.center SL(3, F)) := ⟨⟨h⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (SL(3, F) ⧸ Subgroup.center SL(3, F)) this

theorem kaL4B3_hLp [Finite F] :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ M : Subgroup (projectiveSL 4 F), M ≤ (kaL4B3Phi F).range →
      IsPGroup p ↥M → (∀ l ∈ (kaL4B3Phi F).range, l ∈ normalizer (M : Set (projectiveSL 4 F))) →
        ∀ m ∈ M, ∀ l ∈ (kaL4B3Phi F).range, m * l = l * m :=
  fun _ hp _ M hML hMp hMn =>
    ka_central_of_quasisimple_image (kaL4B3Phi F) kaL4B3_quasisimple hp M hML hMp hMn

end Struct

section Torus

variable {F : Type} [Field F]

@[expose] noncomputable def kaL4B3Tor (u : Fˣ) : SL(4, F) :=
  ⟨Matrix.diagonal ![(u : F), u, u, ((u ^ 3)⁻¹ : Fˣ)], by
    have hu : (u : F) ≠ 0 := u.ne_zero
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    simp
    field_simp⟩

theorem coe_kaL4B3Tor (u : Fˣ) :
    (kaL4B3Tor u : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![(u : F), u, u, ((u ^ 3)⁻¹ : Fˣ)] :=
  rfl

@[expose] noncomputable def kaL4B3TorHom : Fˣ →* SL(4, F) where
  toFun := kaL4B3Tor
  map_one' := by
    apply Subtype.ext
    rw [coe_kaL4B3Tor, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' u v := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_kaL4B3Tor, coe_kaL4B3Tor, coe_kaL4B3Tor,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_pow, mul_comm]

theorem kaL4B3_comm_of_proj (h2 : (2 : F) ≠ 0) {g : SL(4, F)} (hg : g ∈ kaSlCent (kaL4B3GL F))
    (A : SL(3, F))
    (h : proj 4 F g * proj 4 F (eLastHom A) = proj 4 F (eLastHom A) * proj 4 F g) :
    g * eLastHom A = eLastHom A * g := by
  have h1 : proj 4 F (g * eLastHom A) = proj 4 F (eLastHom A * g) := by
    rw [map_mul, map_mul]
    exact h
  rw [proj_eq_proj_iff] at h1
  obtain ⟨c, -, hc⟩ := h1
  have hg1 := kaL4B3_has_of_comm h2 (kaL4B3_mem_cent.1 hg)
  have hgA : kaL4B3Has ((g * eLastHom A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) (g 3 3 * 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_eLastHom]
    exact kaL4B3Has_mul hg1 (kaL4B3Has_eLast _)
  obtain ⟨hz, hinv⟩ := kaL4B3Has_inv_sl hgA
  have hAg : kaL4B3Has ((eLastHom A * g : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) (1 * g 3 3) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_eLastHom]
    exact kaL4B3Has_mul (kaL4B3Has_eLast _) hg1
  have hs := kaL4B3Has_mul hinv hAg
  rw [← Matrix.SpecialLinearGroup.coe_mul, hc, mul_one, one_mul,
    inv_mul_cancel₀ (by simpa using hz)] at hs
  have hc1 : (c : F) = 1 := by
    have := congrFun hs.1 3
    simpa [kaL4B3E_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal] using this
  have hs1 : (g * eLastHom A)⁻¹ * (eLastHom A * g) = 1 := by
    apply Subtype.ext
    rw [hc, hc1, Matrix.SpecialLinearGroup.coe_one]
    simp
  exact inv_mul_eq_one.1 hs1

theorem kaL4B3_eq_tor (h2 : (2 : F) ≠ 0) {g : SL(4, F)} (hg : g ∈ kaSlCent (kaL4B3GL F))
    (hcomm : ∀ A : SL(3, F),
      (g : Matrix (Fin 4) (Fin 4) F) * eLast (A : Matrix (Fin 3) (Fin 3) F) =
        eLast (A : Matrix (Fin 3) (Fin 3) F) * g) : ∃ u : Fˣ, g = kaL4B3Tor u := by
  obtain ⟨hcol, hrow⟩ := kaL4B3_entries h2 (kaL4B3_mem_cent.1 hg)
  have hsc : (Matrix.of fun i j : Fin 3 => (g : Matrix (Fin 4) (Fin 4) F) i.castSucc j.castSucc) ∈
      Set.range (Matrix.scalar (Fin 3)) := by
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_
    exact (commute_eLast (hcomm (⟨t.toMatrix, t.det⟩ : SL(3, F)))).1.symm
  obtain ⟨l, hl⟩ := hsc
  have hA : ∀ i j : Fin 3, (g : Matrix (Fin 4) (Fin 4) F) i.castSucc j.castSucc =
      if i = j then l else 0 := by
    intro i j
    have := congrFun (congrFun hl i) j
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply] using this.symm
  have h00 := hA 0 0
  have h01 := hA 0 1
  have h02 := hA 0 2
  have h10 := hA 1 0
  have h11 := hA 1 1
  have h12 := hA 1 2
  have h20 := hA 2 0
  have h21 := hA 2 1
  have h22 := hA 2 2
  simp at h00 h01 h02 h10 h11 h12 h20 h21 h22
  have hg4 : (g : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![l, l, l, (g : Matrix (Fin 4) (Fin 4) F) 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h02, h10, h11, h12, h20, h21, h22, hcol, hrow]
  have hdet : l * l * l * (g : Matrix (Fin 4) (Fin 4) F) 3 3 = 1 := by
    have h := g.2
    rw [hg4, Matrix.det_diagonal, Fin.prod_univ_four] at h
    simpa using h
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hdet
  have hz : (g : Matrix (Fin 4) (Fin 4) F) 3 3 = (l ^ 3)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    linear_combination hdet
  refine ⟨Units.mk0 l hl0, Subtype.ext ?_⟩
  rw [coe_kaL4B3Tor, hg4, hz]
  simp

theorem kaL4B3_cyc [Finite F] (hodd : ringChar F ≠ 2) (X : Subgroup (projectiveSL 4 F))
    (hXR : X ≤ (kaSlCent (kaL4B3GL F)).map (proj 4 F))
    (hXc : ∀ x ∈ X, ∀ l ∈ (kaL4B3Phi F).range, x * l = l * x) : IsCyclic ↥X := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  let T : Fˣ →* projectiveSL 4 F := (proj 4 F).comp kaL4B3TorHom
  have hXT : X ≤ T.range := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hXR hx
    have hcomm : ∀ A : SL(3, F), g * eLastHom A = eLastHom A * g := fun A =>
      kaL4B3_comm_of_proj h2 hg A (hXc _ hx _ ⟨A, rfl⟩)
    obtain ⟨u, rfl⟩ := kaL4B3_eq_tor h2 hg fun A => by
      have := congrArg (fun k : SL(4, F) => (k : Matrix (Fin 4) (Fin 4) F)) (hcomm A)
      simpa [Matrix.SpecialLinearGroup.coe_mul, coe_eLastHom] using this
    exact ⟨u, rfl⟩
  have : IsCyclic ↥T.range := isCyclic_of_surjective T.rangeRestrict T.rangeRestrict_surjective
  exact isCyclic_of_injective (Subgroup.inclusion hXT) (Subgroup.inclusion_injective hXT)

end Torus

section Rig

variable {F : Type} [Field F]

@[expose] def kaL4B3N : Matrix (Fin 4) (Fin 4) F :=
  !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

theorem kaL4B3N_ne_zero : (kaL4B3N : Matrix (Fin 4) (Fin 4) F) ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [kaL4B3N] at this

theorem kaL4B3N_sq : (kaL4B3N : Matrix (Fin 4) (Fin 4) F) * kaL4B3N = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kaL4B3N, Matrix.mul_apply, Fin.sum_univ_four]

theorem kaL4B3_root (c : F) : ∃ g : SL(4, F),
    (g : Matrix (Fin 4) (Fin 4) F) = 1 + c • kaL4B3N ∧ proj 4 F g ∈ (kaL4B3Phi F).range := by
  let A : SL(3, F) := ⟨!![1, c, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩
  refine ⟨eLastHom A, ?_, ⟨A, rfl⟩⟩
  rw [coe_eLastHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eLast, kaL4B3N, A]

theorem kaL4B3_rigid [Finite F] (hodd : ringChar F ≠ 2) : KARigid (kaL4B3Phi F).range :=
  ka_rigid_proj (n := 4) (by norm_num) (ka_conjAut_inner_of_odd_pl4 hodd) _ kaL4B3N
    kaL4B3N_ne_zero kaL4B3N_sq kaL4B3_root

end Rig

section Main

variable {F : Type} [Field F]

theorem kaL4B3_main [Finite F] (hodd : ringChar F ≠ 2) : KAAll (conjAut 4 F (kaL4B3GL F)) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have hB : kaL4B3GL F * kaL4B3GL F = GeneralLinearGroup.scalar (Fin 4) (1 : Fˣ) := by
    rw [map_one]
    exact kaL4B3GL_mul_self F
  refine ka_all_of_torus (ka_conj_inj_pl4 hodd) ((kaSlCent (kaL4B3GL F)).map (proj 4 F))
    (kaL4B3Phi F).range ?_ ?_ kaL4B3_range_le_map (kaL4B3_normalizes h2) kaL4B3_perfect
    kaL4B3_hLp ?_ (kaL4B3_rigid hodd) (ka_outCentral_pl4 hodd (kaL4B3GL F) 1 hB)
  · intro y hy
    exact mem_fixSub.2 (kaL4B3_map_le_fix hy)
  · intro c hc ho
    exact ka_odd_mem_map_cent_pl4 (kaL4B3GL F) 1 hB (mem_fixSub.1 hc) ho
  · intro p _ _ X _ hXR hXc
    exact kaL4B3_cyc hodd X hXR hXc

theorem kaL4B3_congr_eq_mul {Y : Type} [Group Y] (e α : MulAut Y) :
    MulAut.congr e α = e * α * e⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

end Main

theorem kaL4B3_thm : KAL4B3 := by
  intro F _ _ hodd B hB h3
  obtain ⟨P, rfl⟩ := kaL4B3_exists_frame hodd hB h3
  have h' := KAAll.of_mulEquiv (conjAut 4 F P : projectiveSL 4 F ≃* projectiveSL 4 F)
    (kaL4B3_main hodd)
  have key : MulAut.congr (conjAut 4 F P : projectiveSL 4 F ≃* projectiveSL 4 F)
      (conjAut 4 F (kaL4B3GL F)) = conjAut 4 F (P * kaL4B3GL F * P⁻¹) := by
    rw [kaL4B3_congr_eq_mul, map_mul, map_mul, map_inv]
  rwa [key] at h'

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
