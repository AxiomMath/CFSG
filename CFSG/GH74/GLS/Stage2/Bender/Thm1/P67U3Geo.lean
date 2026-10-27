module

public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.RankThree.SubgroupLists
open scoped commutatorElement

variable {K : Type} [Field K] {σ : K ≃+* K}

section Plane

@[expose] noncomputable def u3Plane (σ : K ≃+* K) (u0 u1 : K) : Matrix (Fin 3) (Fin 3) K :=
  !![σ u0, σ u1, 0; -u1, u0, 0; 0, 0, 1]

theorem u3Plane_det (u0 u1 : K) (h : σ u0 * u0 + σ u1 * u1 = 1) :
    (u3Plane σ u0 u1).det = 1 := by
  rw [u3Plane, det_fin_three]
  simp
  linear_combination h

theorem u3Plane_unit (hσ : ∀ c, σ (σ c) = c) (u0 u1 : K) (h : σ u0 * u0 + σ u1 * u1 = 1) :
    conjTr σ (u3Plane σ u0 u1) * u3Plane σ u0 u1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, u3Plane, Matrix.mul_apply, Fin.sum_univ_succ, hσ] <;>
    first | ring1 | linear_combination h

@[expose] noncomputable def u3PlaneSU (hσ : ∀ c, σ (σ c) = c) (u0 u1 : K)
    (h : σ u0 * u0 + σ u1 * u1 = 1) : SUid σ 3 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (u3Plane σ u0 u1)
      (by rw [u3Plane_det u0 u1 h]; exact one_ne_zero),
    ⟨u3Plane_det u0 u1 h, u3Plane_unit hσ u0 u1 h⟩⟩

theorem u3PlaneSU_smul (hσ : ∀ c, σ (σ c) = c) (u0 u1 : K) (h : σ u0 * u0 + σ u1 * u1 = 1)
    (v : Fin 3 → K) :
    u3PlaneSU hσ u0 u1 h • v = ![σ u0 * v 0 + σ u1 * v 1, -u1 * v 0 + u0 * v 1, v 2] := by
  show (u3Plane σ u0 u1) *ᵥ v = _
  ext i
  fin_cases i <;> simp [u3Plane, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end Plane

section Generation

theorem u3_eq_top_of_stab (hσ : IsUnitaryInvolution σ) (hq : ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1)
    (H : Subgroup (SUid σ 3))
    (hH : ∀ k : Fin 3, MulAction.stabilizer (SUid σ 3) (Pi.single k (1 : K) : Fin 3 → K) ≤ H) :
    H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hT : T σ 3 = ⊤ := T_eq_top hσ (by norm_num) (fun _ => hq)
  have hgT : g ∈ T σ 3 := hT ▸ Subgroup.mem_top g
  refine (?_ : T σ 3 ≤ H) hgT
  rw [T, Subgroup.closure_le]
  rintro t ⟨a, c, ha, hc, ht⟩
  by_cases h2 : a 2 = 0
  · apply hH 2
    rw [MulAction.mem_stabilizer_iff, ht, herm_single_right]
    simp [h2]
  · have hs : σ (a 0) * a 0 + σ (a 1) * a 1 + σ (a 2) * a 2 = 0 := by
      simpa [herm, Fin.sum_univ_three] using ha
    have h2' : σ (a 2) * a 2 ≠ 0 := mul_ne_zero ((map_ne_zero σ).mpr h2) h2
    have hs0 : σ (a 0) * a 0 + σ (a 1) * a 1 ≠ 0 := by
      intro h0
      apply h2'
      linear_combination hs - h0
    have hsfix : σ (σ (a 0) * a 0 + σ (a 1) * a 1) = σ (a 0) * a 0 + σ (a 1) * a 1 := by
      rw [map_add, hσ.norm_fixed, hσ.norm_fixed]
    obtain ⟨μ, hμ⟩ := hσ.exists_norm hsfix
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hμ
      exact hs0 hμ.symm
    have hσμ0 : σ μ ≠ 0 := (map_ne_zero σ).mpr hμ0
    have hu : σ (a 0 / μ) * (a 0 / μ) + σ (a 1 / μ) * (a 1 / μ) = 1 := by
      rw [map_div₀, map_div₀]
      field_simp
      linear_combination -hμ
    set g0 := u3PlaneSU hσ.invol (a 0 / μ) (a 1 / μ) hu with hg0
    have hg0e : g0 ∈ MulAction.stabilizer (SUid σ 3) (Pi.single 2 (1 : K) : Fin 3 → K) := by
      rw [MulAction.mem_stabilizer_iff, hg0, u3PlaneSU_smul]
      ext i
      fin_cases i <;> simp
    have ha1 : (g0 • a) 1 = 0 := by
      rw [hg0, u3PlaneSU_smul]
      show -(a 1 / μ) * a 0 + (a 0 / μ) * a 1 = 0
      ring
    have ht' : g0 * t * g0⁻¹ ∈
        MulAction.stabilizer (SUid σ 3) (Pi.single 1 (1 : K) : Fin 3 → K) := by
      rw [MulAction.mem_stabilizer_iff, conj_smul_of_tv g0 t ht, herm_single_right, ha1,
        map_zero, zero_mul, mul_zero, zero_smul, add_zero]
    have h1 := hH 1 ht'
    have h2g := hH 2 hg0e
    have : t = g0⁻¹ * (g0 * t * g0⁻¹) * g0 := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem h2g) h1) h2g

@[expose] def u3Stab (σ : K ≃+* K) (k : Fin 3) : Subgroup (GL (Fin 3) K) :=
  SUid σ 3 ⊓ MulAction.stabilizer (GL (Fin 3) K) (Pi.single k (1 : K) : Fin 3 → K)

theorem mem_u3Stab {g : GL (Fin 3) K} {k : Fin 3} :
    g ∈ u3Stab σ k ↔ g ∈ SUid σ 3 ∧
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single k (1 : K) : Fin 3 → K) =
        Pi.single k (1 : K) := by
  unfold u3Stab
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rfl

theorem u3_le_of_stab (hσ : IsUnitaryInvolution σ) (hq : ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1)
    (H : Subgroup (GL (Fin 3) K)) (hH : ∀ k, u3Stab σ k ≤ H) : SUid σ 3 ≤ H := by
  have := u3_eq_top_of_stab hσ hq (H.comap (SUid σ 3).subtype) (fun k g hg =>
    hH k (mem_u3Stab.2 ⟨g.2, hg⟩))
  intro g hg
  have h1 : (⟨g, hg⟩ : SUid σ 3) ∈ H.comap (SUid σ 3).subtype := by
    rw [this]; exact Subgroup.mem_top _
  exact h1

end Generation

section Perfect

theorem u3_leviMat_inj {A B : Matrix (Fin 2) (Fin 2) K} (h : leviMat A = leviMat B) : A = B := by
  have e := fun i j : Fin 3 => congrFun (congrFun h i) j
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [leviMat] using e 0 0
  · simpa [leviMat] using e 0 1
  · simpa [leviMat] using e 1 0
  · simpa [leviMat] using e 1 1

theorem u3_conjTr_leviMat (A : Matrix (Fin 2) (Fin 2) K) :
    conjTr σ (leviMat A) = leviMat (conjTr σ A) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, leviMat]

theorem blockGL3_mem_u3Stab {A : GL (Fin 2) K} (hA : A ∈ SUid σ 2) :
    blockGL3 A ∈ u3Stab σ 2 := by
  rw [mem_u3Stab]
  obtain ⟨hdet, hu⟩ := hA
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [coe_blockGL3, det_leviMat, hdet]
  · rw [coe_blockGL3, u3_conjTr_leviMat, ← leviMat_mul, hu, leviMat_one]
  · rw [coe_blockGL3]
    ext i
    fin_cases i <;> simp [leviMat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem exists_blockGL3_of_mem_u3Stab {g : GL (Fin 3) K} (hg : g ∈ u3Stab σ 2) :
    ∃ A : GL (Fin 2) K, A ∈ SUid σ 2 ∧ blockGL3 A = g := by
  rw [mem_u3Stab] at hg
  obtain ⟨⟨hdet, hu⟩, hcol⟩ := hg
  set M : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K) with hM
  have hc : ∀ i, M i 2 = (Pi.single 2 (1 : K) : Fin 3 → K) i := fun i => by
    have := congrFun hcol i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have h02 : M 0 2 = 0 := by simpa using hc 0
  have h12 : M 1 2 = 0 := by simpa using hc 1
  have h22 : M 2 2 = 1 := by simpa using hc 2
  have hr : ∀ j, (conjTr σ M * M) 2 j = (1 : Matrix (Fin 3) (Fin 3) K) 2 j := fun j => by
    rw [hu]
  have h20 : M 2 0 = 0 := by
    have := hr 0
    simp [conjTr, Matrix.mul_apply, Fin.sum_univ_succ, h02, h12, h22] at this
    exact this
  have h21 : M 2 1 = 0 := by
    have := hr 1
    simp [conjTr, Matrix.mul_apply, Fin.sum_univ_succ, h02, h12, h22] at this
    exact this
  set B0 : Matrix (Fin 2) (Fin 2) K := !![M 0 0, M 0 1; M 1 0, M 1 1] with hB0
  have hMB : M = leviMat B0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [leviMat, hB0, h02, h12, h22, h20, h21]
  have hdet0 : B0.det = 1 := by rw [← det_leviMat, ← hMB]; exact hdet
  have hu0 : conjTr σ B0 * B0 = 1 := by
    apply u3_leviMat_inj
    rw [leviMat_mul, ← u3_conjTr_leviMat, ← hMB, leviMat_one]
    exact hu
  refine ⟨GeneralLinearGroup.mkOfDetNeZero B0 (by rw [hdet0]; exact one_ne_zero),
    ⟨hdet0, hu0⟩, ?_⟩
  apply Units.ext
  rw [coe_blockGL3]
  exact hMB.symm

theorem u3Stab_two_eq_range :
    u3Stab σ 2 = ((blockGL3 : GL (Fin 2) K →* GL (Fin 3) K).comp (SUid σ 2).subtype).range := by
  ext g
  constructor
  · intro hg
    obtain ⟨A, hA, rfl⟩ := exists_blockGL3_of_mem_u3Stab hg
    exact ⟨⟨A, hA⟩, rfl⟩
  · rintro ⟨⟨A, hA⟩, rfl⟩
    exact blockGL3_mem_u3Stab hA

theorem commutator_u3Stab_two (hP : Group.IsPerfect (SUid σ 2)) :
    ⁅u3Stab σ 2, u3Stab σ 2⁆ = u3Stab σ 2 := by
  rw [u3Stab_two_eq_range, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    hP.commutator_eq_top]

theorem u3Stab_le_commutator_of_conj {k : Fin 3} {c : GL (Fin 3) K} (hc : c ∈ SUid σ 3)
    (hck : (c : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 2 (1 : K) : Fin 3 → K) =
      Pi.single k (1 : K))
    (h2 : u3Stab σ 2 ≤ ⁅u3Stab σ 2, u3Stab σ 2⁆) : u3Stab σ k ≤ ⁅u3Stab σ k, u3Stab σ k⁆ := by
  intro g hg
  have hcs : c • (Pi.single 2 (1 : K) : Fin 3 → K) = Pi.single k (1 : K) := hck
  have hcs' : c⁻¹ • (Pi.single k (1 : K) : Fin 3 → K) = Pi.single 2 (1 : K) := by
    rw [inv_smul_eq_iff, hcs]
  obtain ⟨hgU, hgs⟩ := mem_u3Stab.1 hg
  have hgs' : g • (Pi.single k (1 : K) : Fin 3 → K) = Pi.single k (1 : K) := hgs
  have hg' : c⁻¹ * g * c ∈ u3Stab σ 2 := by
    refine mem_u3Stab.2 ⟨mul_mem (mul_mem (inv_mem hc) hgU) hc, ?_⟩
    show (c⁻¹ * g * c) • (Pi.single 2 (1 : K) : Fin 3 → K) = Pi.single 2 (1 : K)
    rw [mul_smul, mul_smul, hcs, hgs', hcs']
  have hle : (u3Stab σ 2).map (MulAut.conj c).toMonoidHom ≤ u3Stab σ k := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxU, hxs⟩ := mem_u3Stab.1 hx
    have hxs' : x • (Pi.single 2 (1 : K) : Fin 3 → K) = Pi.single 2 (1 : K) := hxs
    refine mem_u3Stab.2 ⟨mul_mem (mul_mem hc hxU) (inv_mem hc), ?_⟩
    show (c * x * c⁻¹) • (Pi.single k (1 : K) : Fin 3 → K) = Pi.single k (1 : K)
    rw [mul_smul, mul_smul, hcs', hxs', hcs]
  have h3 : c * (c⁻¹ * g * c) * c⁻¹ ∈
      (⁅u3Stab σ 2, u3Stab σ 2⁆).map (MulAut.conj c).toMonoidHom :=
    ⟨c⁻¹ * g * c, h2 hg', rfl⟩
  rw [Subgroup.map_commutator] at h3
  have h4 := Subgroup.commutator_mono hle hle h3
  have : c * (c⁻¹ * g * c) * c⁻¹ = g := by group
  rwa [this] at h4

@[expose] def u3CycMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem det_u3CycMat : (u3CycMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [u3CycMat, det_fin_three]
  simp

@[expose] noncomputable def u3CycGL : GL (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero u3CycMat (by rw [det_u3CycMat]; exact one_ne_zero)

theorem coe_u3CycGL : ((u3CycGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u3CycMat := rfl

theorem u3CycGL_mem (σ : K ≃+* K) : (u3CycGL : GL (Fin 3) K) ∈ SUid σ 3 := by
  refine ⟨?_, ?_⟩
  · rw [coe_u3CycGL, det_u3CycMat]
  · rw [coe_u3CycGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr, u3CycMat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem u3CycGL_mulVec_two :
    ((u3CycGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 2 (1 : K) : Fin 3 → K) =
      Pi.single 0 (1 : K) := by
  rw [coe_u3CycGL]
  ext i
  fin_cases i <;> simp [u3CycMat, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem u3CycGL_mulVec_zero :
    ((u3CycGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 (1 : K) : Fin 3 → K) =
      Pi.single 1 (1 : K) := by
  rw [coe_u3CycGL]
  ext i
  fin_cases i <;> simp [u3CycMat, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem u3_le_of_derived_stab (hσ : IsUnitaryInvolution σ)
    (hq : ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) (hP : Group.IsPerfect (SUid σ 2))
    (H : Subgroup (GL (Fin 3) K)) (hH : ∀ k, ⁅u3Stab σ k, u3Stab σ k⁆ ≤ H) :
    SUid σ 3 ≤ H := by
  have h2 : u3Stab σ 2 ≤ ⁅u3Stab σ 2, u3Stab σ 2⁆ := (commutator_u3Stab_two hP).ge
  refine u3_le_of_stab hσ hq H fun k => ?_
  refine le_trans ?_ (hH k)
  fin_cases k
  · exact u3Stab_le_commutator_of_conj (u3CycGL_mem σ) u3CycGL_mulVec_two h2
  · refine u3Stab_le_commutator_of_conj (c := u3CycGL * u3CycGL)
      (mul_mem (u3CycGL_mem σ) (u3CycGL_mem σ)) ?_ h2
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, u3CycGL_mulVec_two, u3CycGL_mulVec_zero]
    rfl
  · exact h2

end Perfect

end CFSG.GH74.GLS.Stage2.Bender.Thm1
