module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalSymplecticAutBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration

public section

namespace CFSG.QuasithinUnique.K1

open Matrix Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.ComponentClassification.CatalogueBSymplecticTwo

variable {K : Type} [Field K]

theorem proj_injective_charTwo [CharP K 2] : Function.Injective (proj 2 K) := by
  rw [← MonoidHom.ker_eq_bot_iff, SymplecticHigher.ker_proj]
  exact statedScalars_subgroupOf_eq_bot 2

theorem map_projStabilizer_le [CharP K 2] (β : MulAut (StatedProj (StatedSp 2 K)))
    (hfix : ∀ t : K, β (proj 2 K (tauS t 0 0)) = proj 2 K (tauS t 0 0)) :
    (projStabilizer 2 K (flag 2 K 1)).map β.toMonoidHom ≤ projStabilizer 2 K (flag 2 K 1) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨g', hg'⟩ := SymplecticHigher.proj_surjective (β (proj 2 K g))
  refine ⟨g', ?_, hg'⟩
  obtain ⟨s, hs⟩ := exists_tauS_conj_of_mem_stabilizer hg
  apply mem_stabilizer_of_conj_tauS (s := s)
  apply proj_injective_charTwo
  calc proj 2 K (g' * tauS 1 0 0 * g'⁻¹)
      = proj 2 K g' * proj 2 K (tauS 1 0 0) * (proj 2 K g')⁻¹ := by simp [map_mul, map_inv]
    _ = β (proj 2 K g) * β (proj 2 K (tauS 1 0 0)) * (β (proj 2 K g))⁻¹ := by
        rw [hg', hfix 1]
    _ = β (proj 2 K g * proj 2 K (tauS 1 0 0) * (proj 2 K g)⁻¹) := by simp [map_mul, map_inv]
    _ = β (proj 2 K (g * tauS 1 0 0 * g⁻¹)) := by simp [map_mul, map_inv]
    _ = β (proj 2 K (tauS s 0 0)) := by rw [hs]
    _ = proj 2 K (tauS s 0 0) := hfix s

theorem map_projStabilizer_eq [Finite K] [CharP K 2] (β : MulAut (StatedProj (StatedSp 2 K)))
    (hfix : ∀ t : K, β (proj 2 K (tauS t 0 0)) = proj 2 K (tauS t 0 0)) :
    (projStabilizer 2 K (flag 2 K 1)).map β.toMonoidHom = projStabilizer 2 K (flag 2 K 1) :=
  Subgroup.eq_of_le_of_card_ge (map_projStabilizer_le β hfix)
    (by rw [Subgroup.card_map_of_injective β.injective])

theorem mem_typeKernel_of_fixes [Finite K] [CharP K 2] (β : MulAut (StatedProj (StatedSp 2 K)))
    (hfix : ∀ t : K, β (proj 2 K (tauS t 0 0)) = proj 2 K (tauS t 0 0)) : β ∈ typeKernel K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hdisj, -⟩ := extremal_parabolics (K := K) 2 (rfl : Nat.card K = Nat.card K)
  obtain ⟨Φ, -, hcase⟩ := (type_kernel (K := K) 2).1 β
  rcases hcase with ⟨hX, -⟩ | ⟨hXY, -⟩
  · exact mem_typeKernel.mpr hX
  · exfalso
    have hPX : projStabilizer 2 K (flag 2 K 1) ∈ pointParabolics K :=
      ⟨flag 2 K 1, finrank_flag (by norm_num), rfl⟩
    have hPY : projStabilizer 2 K (flag 2 K 1) ∈ planeParabolics K := by
      rw [← hXY]
      exact ⟨_, hPX, map_projStabilizer_eq β hfix⟩
    exact Set.disjoint_left.mp hdisj hPX hPY

theorem coe_mul_coe_inv_sp (A : GL (Fin 2 ⊕ Fin 2) K) :
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem coe_inv_mul_coe_sp (A : GL (Fin 2 ⊕ Fin 2) K) :
    ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem conj_eq_of_conj_one_add_sp (A : GL (Fin 2 ⊕ Fin 2) K)
    {X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (1 + X) *
      ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 + Y) :
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X *
      ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Y := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, coe_mul_coe_inv_sp] at h
  exact add_left_cancel h

theorem mul_eq_mul_of_conj_eq_sp (A : GL (Fin 2 ⊕ Fin 2) K)
    {E : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * E *
      ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = E) :
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * E =
      E * (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  calc (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * E
      = ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * E *
        ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
          (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
        rw [Matrix.mul_assoc _ _ (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K), coe_inv_mul_coe_sp,
          Matrix.mul_one]
    _ = E * (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by rw [h]

theorem map_one_add_smul_E (σ : K ≃+* K) (t : K) :
    ((1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) +
      t • single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (1 : K)).map σ =
      1 + σ t • single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (1 : K) := by
  ext k l
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, single_apply,
    smul_eq_mul]
  split_ifs <;> simp

theorem entries_of_commute {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : M * single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (1 : K) =
      single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (1 : K) * M) :
    (∀ k : Fin 2 ⊕ Fin 2, k ≠ Sum.inl 0 → M k (Sum.inl 0) = 0) ∧
      M (Sum.inr 0) (Sum.inr 0) = M (Sum.inl 0) (Sum.inl 0) := by
  refine ⟨fun k hk => ?_, ?_⟩
  · have := congrFun₂ h k (Sum.inr 0)
    rw [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hk] at this
    simpa using this
  · have := congrFun₂ h (Sum.inl 0) (Sum.inr 0)
    rw [mul_single_apply_same, single_mul_apply_same] at this
    simpa using this.symm

theorem inner_of_conjAut_mul_fieldAut [CharP K 2] (A : gsp 2 K) (σ : K ≃+* K)
    (hfix : ∀ t : K, (conjAut 2 K A * fieldAut 2 K σ) (proj 2 K (tauS t 0 0)) =
      proj 2 K (tauS t 0 0)) :
    ∃ x : StatedProj (StatedSp 2 K), ∀ y : StatedProj (StatedSp 2 K),
      (conjAut 2 K A * fieldAut 2 K σ) y = x⁻¹ * y * x := by
  have hX : ∀ t : K, conjSp 2 K A (fieldSp 2 K σ (tauS t 0 0)) = tauS t 0 0 := by
    intro t
    have h := hfix t
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h
    exact proj_injective_charTwo h
  have hM : ∀ t : K, ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (1 + σ t • single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (1 : K)) *
        (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      1 + t • single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (1 : K) := by
    intro t
    have h := congrArg spM (hX t)
    have e1 : spM (conjSp 2 K A (fieldSp 2 K σ (tauS t 0 0))) =
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          (spM (tauS t 0 0)).map σ *
          (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      show (((A : GL (Fin 2 ⊕ Fin 2) K) * ((fieldSp 2 K σ (tauS t 0 0) : StatedSp 2 K) :
        GL (Fin 2 ⊕ Fin 2) K) * (A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = _
      rw [Units.val_mul, Units.val_mul]
      rfl
    rw [e1, spM_tauS_first, map_one_add_smul_E] at h
    exact h
  have hE0 : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (1 : K) *
        (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      single (Sum.inl 0 : Fin 2 ⊕ Fin 2) (Sum.inr 0 : Fin 2 ⊕ Fin 2) (1 : K) := by
    have h1 := conj_eq_of_conj_one_add_sp (A : GL (Fin 2 ⊕ Fin 2) K) (hM 1)
    simpa using h1
  have hE1 := mul_eq_mul_of_conj_eq_sp (A : GL (Fin 2 ⊕ Fin 2) K) hE0
  have hσ : ∀ t, σ t = t := by
    intro t
    have h2 := conj_eq_of_conj_one_add_sp (A : GL (Fin 2 ⊕ Fin 2) K) (hM t)
    rw [Matrix.mul_smul, Matrix.smul_mul, hE0] at h2
    have h3 := congrFun₂ h2 (Sum.inl 0) (Sum.inr 0)
    simpa [Matrix.smul_apply, single_apply] using h3
  obtain ⟨hcol, hdiag⟩ := entries_of_commute hE1
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  have hrow := lam_mul_row_matrix
    (M := ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (μ := (μ : K)) hcol hμ (Sum.inr 0)
  set a := ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (Sum.inl 0) (Sum.inl 0) with ha_def
  have ha2 : a * a = (μ : K) := by simpa [hdiag] using hrow
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at ha2
    exact μ.ne_zero ha2.symm
  set s : GL (Fin 2 ⊕ Fin 2) K :=
    Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 a ha) with hs
  set A' : GL (Fin 2 ⊕ Fin 2) K := s⁻¹ * (A : GL (Fin 2 ⊕ Fin 2) K) with hA'
  have hA'mat : (A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      a⁻¹ • ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [hA', Units.val_mul, hs, ← map_inv, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    simp
  have hA'mem : A' ∈ StatedSp 2 K := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff, hA'mat]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hμ, smul_smul]
    have h1 : a⁻¹ * a⁻¹ * (μ : K) = 1 := by
      rw [← ha2]
      field_simp
    rw [h1, one_smul]
  set A'' : StatedSp 2 K := ⟨A', hA'mem⟩ with hA''
  have hAeq : (A : GL (Fin 2 ⊕ Fin 2) K) = s * A' := by
    rw [hA']
    group
  have hscen : s ∈ Subgroup.center (GL (Fin 2 ⊕ Fin 2) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have hcomm := Subgroup.mem_center_iff.mp hscen
  have hconj : ∀ g : StatedSp 2 K, conjSp 2 K A g = A'' * g * A''⁻¹ := by
    intro g
    apply Subtype.ext
    show (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) * (A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ =
      A' * (g : GL (Fin 2 ⊕ Fin 2) K) * A'⁻¹
    rw [hAeq]
    calc s * A' * (g : GL (Fin 2 ⊕ Fin 2) K) * (s * A')⁻¹
        = s * (A' * (g : GL (Fin 2 ⊕ Fin 2) K) * A'⁻¹) * s⁻¹ := by group
      _ = (A' * (g : GL (Fin 2 ⊕ Fin 2) K) * A'⁻¹) * s * s⁻¹ := by
          rw [← hcomm (A' * (g : GL (Fin 2 ⊕ Fin 2) K) * A'⁻¹)]
      _ = A' * (g : GL (Fin 2 ⊕ Fin 2) K) * A'⁻¹ := by group
  have hσ1 : σ = 1 := RingEquiv.ext hσ
  subst hσ1
  have hf1 : fieldSp 2 K (1 : K ≃+* K) = 1 := map_one _
  refine ⟨(proj 2 K A'')⁻¹, fun y => ?_⟩
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective y
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, hf1, MulAut.one_apply, hconj, map_mul,
    map_mul, map_inv, inv_inv]

theorem inner_of_fixes_unipotent [Finite K] [CharP K 2] (β : MulAut (StatedProj (StatedSp 2 K)))
    (hβ : ∀ u ∈ unipotent 2 K, β (proj 2 K u) = proj 2 K u) :
    ∃ x : StatedProj (StatedSp 2 K), ∀ y : StatedProj (StatedSp 2 K), β y = x⁻¹ * y * x := by
  have hfix : ∀ t : K, β (proj 2 K (tauS t 0 0)) = proj 2 K (tauS t 0 0) := fun t =>
    hβ _ (tauS_mem_unipotent t 0 0)
  obtain ⟨A, σ, hAσ⟩ := (kernel_generation (K := K)).2.1 β (mem_typeKernel_of_fixes β hfix)
  subst hAσ
  exact inner_of_conjAut_mul_fieldAut A σ hfix

theorem sylowCentralizingAutInner_statedProj [Finite K] [CharP K 2] :
    SylowCentralizingAutInner (StatedProj (StatedSp 2 K)) := by
  obtain ⟨-, ⟨S, hS⟩, -⟩ := unique_symplectic_four_Sylow_center (K := K) (Nat.card K) rfl
  let T : Sylow 2 (StatedProj (StatedSp 2 K)) :=
    S.mapSurjective (SymplecticHigher.proj_surjective (r := 2) (K := K))
  have hT : IsSylowTwoOf (T : Subgroup (StatedProj (StatedSp 2 K))) ⊤ :=
    isSylowTwoOf_top_iff.mpr ⟨T.isPGroup', T.not_dvd_index⟩
  refine sylowCentralizingAutInner_of_sylow _ hT fun β hβ =>
    inner_of_fixes_unipotent β fun u hu => hβ _ ?_
  rw [Sylow.coe_mapSurjective, hS]
  exact Subgroup.mem_map_of_mem _ hu

end CFSG.QuasithinUnique.K1
