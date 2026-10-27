module

public import CFSG.CGT.Stroth77.Section34T201Act
public import CFSG.CGT.Stroth77.Section34T201Levels
public import CFSG.CGT.Stroth77.Section34T201Ident
public import CFSG.CGT.Stroth77.Section34T201Finite

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth34T201 Stroth34T201Levels Stroth34T201Natural Stroth34T201Ident
open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t201 m)}

theorem compat_eMat (m : ℕ) : Compat (StrothTypeIndex.t201 m).k (eMat m) := by
  refine Compat.of_witness (C := !![1, 0, 0; 0, 1 + 2 ^ (m + 1), 0; 0, 0, 1 + 2 ^ (m + 1)])
    fun i l => ?_
  fin_cases i <;> fin_cases l <;> simp [StrothTypeIndex.k, Type201.k, eMat, ofCols_apply]

theorem matAct_eMat (v : Torus (StrothTypeIndex.t201 m).k) :
    matAct _ (eMat m) (compat_eMat m) v = (1 + 2 ^ (m + 1) : ℤ) • v := by
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec v
  rw [matAct_ofInt, t201_zsmul_vec]
  rw [show (eMat m *ᵥ ![a, b, c]) = ![a, (1 + 2 ^ (m + 1)) * b, (1 + 2 ^ (m + 1)) * c] by
      funext i; fin_cases i <;>
        simp [eMat, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]]
  rw [t201_vec_eq_iff]
  exact ⟨⟨2 * a, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem compat_uvK (m : ℕ) : Compat (StrothTypeIndex.t201 m).k (Type201.uvM m) :=
  Type201.compat_uv m
theorem compat_tK (m : ℕ) : Compat (StrothTypeIndex.t201 m).k (Type201.tM m) :=
  Type201.compat_t m
theorem compat_uK (m : ℕ) : Compat (StrothTypeIndex.t201 m).k (Type201.uM m) :=
  Type201.compat_u m
theorem compat_ρK (m : ℕ) : Compat (StrothTypeIndex.t201 m).k (Type201.ρM m) :=
  Type201.compat_rho m

theorem compat_ρ200K (m : ℕ) : Compat (StrothTypeIndex.t201 m).k Type200.ρM :=
  Type201.compat_rho m
theorem compat_u200K (m : ℕ) : Compat (StrothTypeIndex.t201 m).k Type200.uM :=
  Type201.compat_u m

theorem compat_conjρ {X : IntMat} (hX : Compat (StrothTypeIndex.t201 m).k X) :
    Compat (StrothTypeIndex.t201 m).k (conjρ X) :=
  ((compat_ρ200K m).mul hX).mul ((compat_ρ200K m).mul (compat_ρ200K m))

theorem compat_conjU {X : IntMat} (hX : Compat (StrothTypeIndex.t201 m).k X) :
    Compat (StrothTypeIndex.t201 m).k (conjU X) :=
  ((compat_u200K m).mul hX).mul (compat_u200K m)

theorem matAct_conjρ {X : IntMat} (hX : Compat (StrothTypeIndex.t201 m).k X)
    (v : Torus (StrothTypeIndex.t201 m).k) :
    matAct _ (conjρ X) (compat_conjρ hX) v =
      dD.thetaT dD.ρ_mem (matAct _ X hX (dD.thetaT (inv_mem dD.ρ_mem) v)) := by
  show matAct _ (Type200.ρM * X * (Type200.ρM * Type200.ρM))
    (((compat_ρ200K m).mul hX).mul ((compat_ρ200K m).mul (compat_ρ200K m))) v = _
  rw [dD.thetaT_ρ_inv,
    matAct_mul_apply ((compat_ρ200K m).mul hX) ((compat_ρ200K m).mul (compat_ρ200K m)),
    matAct_mul_apply (compat_ρ200K m) hX, matAct_mul_apply (compat_ρ200K m) (compat_ρ200K m),
    dD.thetaT_ρ]
  rfl

theorem matAct_conjU {X : IntMat} (hX : Compat (StrothTypeIndex.t201 m).k X)
    (v : Torus (StrothTypeIndex.t201 m).k) :
    matAct _ (conjU X) (compat_conjU hX) v =
      dD.thetaT dD.u_mem (matAct _ X hX (dD.thetaT (inv_mem dD.u_mem) v)) := by
  show matAct _ (Type200.uM * X * Type200.uM) (((compat_u200K m).mul hX).mul (compat_u200K m)) v
    = _
  rw [t201_thetaT_u_inv,
    matAct_mul_apply ((compat_u200K m).mul hX) (compat_u200K m),
    matAct_mul_apply (compat_u200K m) hX, dD.thetaT_u]
  rfl

theorem matAct_one_apply (v : Torus (StrothTypeIndex.t201 m).k) :
    matAct (StrothTypeIndex.t201 m).k 1 Compat.one v = v := by
  rw [matAct_one]; rfl

theorem thetaT_ρ_inv_eq (v : Torus (StrothTypeIndex.t201 m).k) :
    dD.thetaT (inv_mem dD.ρ_mem) v = matAct (StrothTypeIndex.t201 m).k
      (Type201.ρM m * Type201.ρM m) ((compat_ρK m).mul (compat_ρK m)) v := by
  rw [dD.thetaT_ρ_inv, matAct_mul_apply]; rfl

theorem thetaT_uv_eq (v : Torus (StrothTypeIndex.t201 m).k) :
    dD.thetaT dD.uv_mem v =
      matAct (StrothTypeIndex.t201 m).k (Type201.uvM m) (compat_uvK m) v :=
  dD.thetaT_uv v

theorem thetaT_t_eq (v : Torus (StrothTypeIndex.t201 m).k) :
    dD.thetaT dD.t_mem v =
      matAct (StrothTypeIndex.t201 m).k (Type201.tM m) (compat_tK m) v :=
  dD.thetaT_t v

theorem thetaT_u_eq (v : Torus (StrothTypeIndex.t201 m).k) :
    dD.thetaT dD.u_mem v =
      matAct (StrothTypeIndex.t201 m).k (Type201.uM m) (compat_uK m) v :=
  dD.thetaT_u v

theorem thetaT_u_inv_eq (v : Torus (StrothTypeIndex.t201 m).k) :
    dD.thetaT (inv_mem dD.u_mem) v =
      matAct (StrothTypeIndex.t201 m).k (Type201.uM m) (compat_uK m) v :=
  t201_thetaT_u_inv v

theorem thetaT_ρ_eq (v : Torus (StrothTypeIndex.t201 m).k) :
    dD.thetaT dD.ρ_mem v =
      matAct (StrothTypeIndex.t201 m).k (Type201.ρM m) (compat_ρK m) v :=
  dD.thetaT_ρ v

theorem compat_omegaMat (m : ℕ) :
    Compat (StrothTypeIndex.t201 m).k (omegaMat (StrothTypeIndex.t201 m).k) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    simp only [omegaMat, Matrix.diagonal_apply_eq]
    exact ⟨2 ^ ((StrothTypeIndex.t201 m).k i - 1), by ring⟩
  · simp [omegaMat, Matrix.diagonal_apply_ne _ hij]

theorem conj_ofTorus_eq {g : G} (hgN : g ∈ Subgroup.normalizer (D : Set G))
    {φ : Torus (StrothTypeIndex.t201 m).k → Torus (StrothTypeIndex.t201 m).k}
    (hφ : ∀ v, dD.thetaT hgN v = φ v) (v : Torus (StrothTypeIndex.t201 m).k) :
    g⁻¹ * dD.ofTorus v * g = dD.ofTorus (φ v) := by
  have hmem : g⁻¹ * dD.ofTorus v * g ∈ D :=
    (Subgroup.mem_normalizer_iff''.mp hgN _).mp (dD.ofT_mem v)
  rw [← hφ, dD.thetaT_apply]
  exact (dD.ofT_crdT hmem).symm

theorem thetaT_inv_of_rel34i {e : G} (he : Rel34i dD e (2 ^ (m + 1)))
    (heN : e ∈ Subgroup.normalizer (D : Set G)) (v : Torus (StrothTypeIndex.t201 m).k) :
    dD.thetaT (inv_mem heN) v = (1 + 2 ^ (m + 1) : ℤ) • v := by
  have h1 := dD.thetaT_thetaT_inv heN v
  rw [t201_thetaT_of_rel34i he heN] at h1
  calc dD.thetaT (inv_mem heN) v
      = ((1 + 2 ^ (m + 1) : ℤ) * (1 + 2 ^ (m + 1))) • dD.thetaT (inv_mem heN) v :=
        (sigma_sq_zsmul _).symm
    _ = (1 + 2 ^ (m + 1) : ℤ) • v := by rw [mul_smul, h1]

theorem mem_R1_of_acts (hS : Local.Setting (F.S : Subgroup G) D) {e : G} (heR : e ∈ hS.R)
    (he : Rel34i dD e (2 ^ (m + 1))) (hR1 : hS.R1 dD.uv dD.t = D ⊔ Subgroup.zpowers e)
    {f : G} (hfR : f ∈ hS.R)
    (hθ : (∀ v, dD.thetaT (hS.R_le_normalizer hfR) v = v) ∨
      ∀ v, dD.thetaT (hS.R_le_normalizer hfR) v = (1 + 2 ^ (m + 1) : ℤ) • v) :
    f ∈ hS.R1 dD.uv dD.t := by
  have hfN := hS.R_le_normalizer hfR
  have heN := hS.R_le_normalizer heR
  have heR1 : e ∈ hS.R1 dD.uv dD.t := by
    rw [hR1]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  rcases hθ with hθ | hθ
  · exact t201_D_le_R1 hS (dD.mem_of_thetaT_id hS (hS.R_le_S hfR) hfN hθ)
  · have hd : f * e⁻¹ ∈ D := by
      refine dD.mem_of_thetaT_id hS (mul_mem (hS.R_le_S hfR) (inv_mem (hS.R_le_S heR)))
        (mul_mem hfN (inv_mem heN)) fun v => ?_
      rw [dD.thetaT_mul hfN (inv_mem heN), hθ, thetaT_inv_of_rel34i he heN, smul_smul,
        sigma_sq_zsmul]
    have := mul_mem (t201_D_le_R1 hS hd) heR1
    simpa using this

theorem exists_twist_one_sigma (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    {e : G} (heR : e ∈ hS.R) (he : Rel34i dD e (2 ^ (m + 1)))
    (hR1 : hS.R1 dD.uv dD.t = D ⊔ Subgroup.zpowers e) (hlt : hS.R1 dD.uv dD.t < hS.R) :
    ∃ f₁, ∃ hf₁ : f₁ ∈ hS.R, dD.Twist dD.uv_mem (hS.R_le_normalizer hf₁) 1 ∧
      dD.Twist dD.t_mem (hS.R_le_normalizer hf₁) (1 + 2 ^ (m + 1)) := by
  have heN := hS.R_le_normalizer heR
  have he2 : e * e ∈ D := by rw [he.e_sq]; exact inv_mem dD.c.2
  have hsc : ∀ f (hf : f ∈ hS.R1 dD.uv dD.t), ∃ y : ℤ,
      ∀ v, dD.thetaT (hS.R_le_normalizer hf.1) v = y • v := by
    intro f hf
    have hfN := hS.R_le_normalizer hf.1
    have hf' := hf
    rw [hR1] at hf'
    rcases mem_or_mul_inv_mem_of_mem_sup heN he2 hf' with hD | hD
    · exact ⟨1, fun v => by rw [dD.thetaT_of_mem hfN hD, one_smul]⟩
    · refine ⟨1 + 2 ^ (m + 1), fun v => ?_⟩
      have hdN : f * e⁻¹ ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hD
      rw [dD.thetaT_congr hfN (mul_mem hdN heN) (by group), dD.thetaT_mul hdN heN,
        dD.thetaT_of_mem hdN hD, t201_thetaT_of_rel34i he heN]
  obtain ⟨f, hfR, hfR1, hcuv, hct⟩ :=
    h.exists_mem_R_conj_mem_R1 hS (t201_R_le_normalizer_R1 hS hsc) hlt
  have sq : ∀ v : Torus (StrothTypeIndex.t201 m).k,
      ((1 + 2 ^ (m + 1) : ℤ) * (1 + 2 ^ (m + 1))) • v = (1 : ℤ) • v := fun v => by
    rw [sigma_sq_zsmul, one_smul]
  rcases twist_cases hS heR he hR1 dD.uv_mem hfR hcuv with t₁ | t₁ <;>
    rcases twist_cases hS heR he hR1 dD.t_mem hfR hct with t₂ | t₂
  ·
    exact absurd (mem_R1_of_acts hS heR he hR1 hfR
      (h.thetaT_eq_of_twist_one hS heR he hR1 hfR t₁ t₂)) hfR1
  · exact ⟨f, hfR, t₁, t₂⟩
  ·
    obtain ⟨t₃, t₄⟩ := twist_proj_rho hS hfR t₁ t₂
    have t₃' := t₃.congr (s' := 1 + 2 ^ (m + 1)) (fun v => by rw [mul_one])
    obtain ⟨t₅, t₆⟩ := twist_proj_rho hS (hS.proj_mem dD.ρ_mem hfR) t₃' t₄
    exact ⟨_, hS.proj_mem dD.ρ_mem (hS.proj_mem dD.ρ_mem hfR), t₅.congr sq, t₆⟩
  ·
    obtain ⟨t₃, t₄⟩ := twist_proj_rho hS hfR t₁ t₂
    exact ⟨_, hS.proj_mem dD.ρ_mem hfR, t₃.congr sq, t₄⟩

section Matrix

variable (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e : G}
  (heR : e ∈ hS.R) (he : Rel34i dD e (2 ^ (m + 1)))
  (hR1 : hS.R1 dD.uv dD.t = D ⊔ Subgroup.zpowers e) {f : G} (hfR : f ∈ hS.R)
  (h₁ : dD.Twist dD.uv_mem (hS.R_le_normalizer hfR) 1)
  (h₂ : dD.Twist dD.t_mem (hS.R_le_normalizer hfR) (1 + 2 ^ (m + 1)))
include h hS heR he hR1 h₁ h₂

theorem matAct_matOf_thetaT (v : Torus (StrothTypeIndex.t201 m).k) :
    matAct _ (matOf (dD.thetaT (hS.R_le_normalizer hfR))) (compat_matOf _) v =
      dD.thetaT (hS.R_le_normalizer hfR) v := by
  rw [matAct_matOf]

omit h heR he hR1 h₂ in
theorem matOf_comm_uv :
    MatEq (StrothTypeIndex.t201 m).k (matOf (dD.thetaT (hS.R_le_normalizer hfR)) * Type201.uvM m)
      (Type201.uvM m * matOf (dD.thetaT (hS.R_le_normalizer hfR))) := by
  refine matEq_of_matAct_eq
    ((compat_matOf (dD.thetaT (hS.R_le_normalizer hfR))).mul (compat_uvK m))
    ((compat_uvK m).mul (compat_matOf (dD.thetaT (hS.R_le_normalizer hfR)))) fun v => ?_
  rw [matAct_mul_apply (compat_matOf _) (compat_uvK m),
    matAct_mul_apply (compat_uvK m) (compat_matOf _), matAct_matOf,
    ← thetaT_uv_eq (dD := dD), h₁, one_smul, ← thetaT_uv_eq (dD := dD)]

omit h heR he hR1 h₁ in
theorem matOf_twist_t :
    MatEq (StrothTypeIndex.t201 m).k (matOf (dD.thetaT (hS.R_le_normalizer hfR)) * Type201.tM m)
      (Type201.tM m * matOf (dD.thetaT (hS.R_le_normalizer hfR)) * eMat m) := by
  refine matEq_of_matAct_eq
    ((compat_matOf (dD.thetaT (hS.R_le_normalizer hfR))).mul (compat_tK m))
    (((compat_tK m).mul (compat_matOf (dD.thetaT (hS.R_le_normalizer hfR)))).mul
      (compat_eMat m)) fun v => ?_
  rw [matAct_mul_apply (compat_matOf _) (compat_tK m),
    matAct_mul_apply ((compat_tK m).mul (compat_matOf _)) (compat_eMat m),
    matAct_mul_apply (compat_tK m) (compat_matOf _), matAct_matOf, matAct_eMat,
    ← thetaT_t_eq (dD := dD), h₂, map_zsmul, map_zsmul, ← thetaT_t_eq (dD := dD)]

omit h heR he hR1 h₁ h₂ in
theorem isAut1_matOf (hm : 1 ≤ m) :
    IsAut1 (StrothTypeIndex.t201 m).k (matOf (dD.thetaT (hS.R_le_normalizer hfR))) := by
  have hfN := hS.R_le_normalizer hfR
  have hfix : ∀ w : Torus (StrothTypeIndex.t201 m).k, w + w = 0 → dD.thetaT hfN w = w := by
    intro w hw
    have hΩ : dD.ofT w ∈ omegaIn 1 D :=
      mem_omegaIn_one_of_mul_self (dD.ofT_mem w) (by rw [← dD.ofT_add, hw, dD.ofT_zero])
    have hc := Subgroup.mem_centralizer_iff.mp (hS.R_le_centralizer_omega hfR) _ hΩ
    rw [dD.thetaT_apply, mul_assoc, hc, inv_mul_cancel_left, dD.crdT_ofT]
  refine matEq_of_matAct_eq ((compat_matOf (dD.thetaT hfN)).mul (compat_omegaMat m))
    (compat_omegaMat m) fun v => ?_
  rw [matAct_mul_apply (compat_matOf (dD.thetaT hfN)) (compat_omegaMat m), matAct_matOf]
  refine hfix _ ?_
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec v
  rw [matAct_ofInt]
  rw [show (omegaMat (StrothTypeIndex.t201 m).k *ᵥ ![a, b, c]) =
      ![2 ^ (m - 1) * a, 2 ^ (m + 1) * b, 2 ^ (m + 1) * c] by
    funext i; fin_cases i <;>
      simp [omegaMat, StrothTypeIndex.k, Type201.k, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Matrix.diagonal_apply]]
  rw [t201_add_vec, t201_vec_eq_zero_iff]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  exact ⟨⟨a, by rw [Nat.add_sub_cancel]; ring⟩, ⟨b, by ring⟩, ⟨c, by ring⟩⟩

theorem matOf_sq :
    MatEq (StrothTypeIndex.t201 m).k
        (matOf (dD.thetaT (hS.R_le_normalizer hfR)) * matOf (dD.thetaT (hS.R_le_normalizer hfR)))
        1 ∨
      MatEq (StrothTypeIndex.t201 m).k
        (matOf (dD.thetaT (hS.R_le_normalizer hfR)) * matOf (dD.thetaT (hS.R_le_normalizer hfR)))
        (eMat m) := by
  have hfN := hS.R_le_normalizer hfR
  have hMc := compat_matOf (dD.thetaT hfN)
  have t₁ := (h₁.mul h₁).congr (s' := 1) (fun v => by rw [mul_one])
  have t₂ := (h₂.mul h₂).congr (s' := 1) (fun v => by rw [sigma_sq_zsmul, one_smul])
  have hact : ∀ v, matAct _ _ (hMc.mul hMc) v = dD.thetaT (mul_mem hfN hfN) v := fun v => by
    rw [matAct_mul_apply hMc hMc, matAct_matOf, dD.thetaT_mul hfN hfN]
  rcases h.thetaT_eq_of_twist_one hS heR he hR1 (mul_mem hfR hfR) t₁ t₂ with hθ | hθ
  · exact Or.inl (matEq_of_matAct_eq (hMc.mul hMc) Compat.one fun v => by
      rw [hact, matAct_one_apply]; exact hθ v)
  · exact Or.inr (matEq_of_matAct_eq (hMc.mul hMc) (compat_eMat m) fun v => by
      rw [hact, matAct_eMat]; exact hθ v)

theorem matOf_conjρ :
    MatEq (StrothTypeIndex.t201 m).k
        (conjρ (conjρ (matOf (dD.thetaT (hS.R_le_normalizer hfR)))) *
          conjρ (matOf (dD.thetaT (hS.R_le_normalizer hfR))) *
          matOf (dD.thetaT (hS.R_le_normalizer hfR))) 1 ∨
      MatEq (StrothTypeIndex.t201 m).k
        (conjρ (conjρ (matOf (dD.thetaT (hS.R_le_normalizer hfR)))) *
          conjρ (matOf (dD.thetaT (hS.R_le_normalizer hfR))) *
          matOf (dD.thetaT (hS.R_le_normalizer hfR))) (eMat m) := by
  have hfN := hS.R_le_normalizer hfR
  have hMc := compat_matOf (dD.thetaT hfN)
  have hf'R := hS.proj_mem dD.ρ_mem hfR
  have hf''R := hS.proj_mem dD.ρ_mem hf'R
  have hf'N := hS.R_le_normalizer hf'R
  have hf''N := hS.R_le_normalizer hf''R
  obtain ⟨a₁, a₂⟩ := twist_proj_rho hS hfR h₁ h₂
  obtain ⟨b₁, b₂⟩ := twist_proj_rho hS hf'R a₁ a₂
  have t₁ := ((h₁.mul a₁).mul b₁).congr (s' := 1)
    (fun v => by rw [one_mul, one_mul, mul_one, sigma_sq_zsmul, one_smul])
  have t₂ := ((h₂.mul a₂).mul b₂).congr (s' := 1)
    (fun v => by rw [mul_one, one_mul, sigma_sq_zsmul, one_smul])
  have e₁ : ∀ w, matAct _ _ (compat_conjρ hMc) w = dD.thetaT hf'N w := fun w => by
    rw [matAct_conjρ (dD := dD) hMc, matAct_matOf, thetaT_proj hS dD.ρ_mem hfR]
  have e₂ : ∀ w, matAct _ _ (compat_conjρ (compat_conjρ hMc)) w = dD.thetaT hf''N w := fun w => by
    rw [matAct_conjρ (dD := dD) (compat_conjρ hMc), e₁, thetaT_proj hS dD.ρ_mem hf'R]
  have hc := ((compat_conjρ (compat_conjρ hMc)).mul (compat_conjρ hMc)).mul hMc
  have hact : ∀ v, matAct _ _ hc v = dD.thetaT (mul_mem (mul_mem hfN hf'N) hf''N) v := fun v => by
    rw [matAct_mul_apply ((compat_conjρ (compat_conjρ hMc)).mul (compat_conjρ hMc)) hMc,
      matAct_mul_apply (compat_conjρ (compat_conjρ hMc)) (compat_conjρ hMc), matAct_matOf, e₁,
      e₂, dD.thetaT_mul (mul_mem hfN hf'N) hf''N, dD.thetaT_mul hfN hf'N]
  rcases h.thetaT_eq_of_twist_one hS heR he hR1 (mul_mem (mul_mem hfR hf'R) hf''R) t₁ t₂ with
    hθ | hθ
  · exact Or.inl (matEq_of_matAct_eq hc Compat.one fun v => by
      rw [hact, matAct_one_apply]; exact hθ v)
  · exact Or.inr (matEq_of_matAct_eq hc (compat_eMat m) fun v => by
      rw [hact, matAct_eMat]; exact hθ v)

theorem matOf_conjU :
    MatEq (StrothTypeIndex.t201 m).k (conjU (matOf (dD.thetaT (hS.R_le_normalizer hfR))))
        (matOf (dD.thetaT (hS.R_le_normalizer hfR))) ∨
      MatEq (StrothTypeIndex.t201 m).k (conjU (matOf (dD.thetaT (hS.R_le_normalizer hfR))))
        (matOf (dD.thetaT (hS.R_le_normalizer hfR)) * eMat m) := by
  have hfN := hS.R_le_normalizer hfR
  have hMc := compat_matOf (dD.thetaT hfN)
  have hgR := h.conj_u_mem_R hS hfR
  have hgN := hS.R_le_normalizer hgR
  have hqR : dD.u⁻¹ * f * dD.u * f⁻¹ ∈ hS.R := mul_mem hgR (inv_mem hfR)
  obtain ⟨a₁, a₂⟩ := twist_conj_u h hS hfR h₁ h₂
  have i₁ := h₁.inv (fun v => by rw [mul_one, one_smul])
  have i₂ := h₂.inv sigma_sq_zsmul
  have t₁ := (a₁.mul i₁).congr (s' := 1) (fun v => by rw [mul_one])
  have t₂ := (a₂.mul i₂).congr (s' := 1) (fun v => by rw [one_mul, sigma_sq_zsmul, one_smul])
  have hq : ∀ v, dD.thetaT hgN v = dD.thetaT hfN (dD.thetaT (hS.R_le_normalizer hqR) v) :=
    fun v => by
      rw [dD.thetaT_mul hgN (inv_mem hfN), dD.thetaT_thetaT_inv]
  have hu : ∀ v, matAct _ _ (compat_conjU hMc) v = dD.thetaT hgN v := fun v => by
    rw [matAct_conjU (dD := dD) hMc, matAct_matOf, dD.thetaT_conj hfN dD.u_mem]
  rcases h.thetaT_eq_of_twist_one hS heR he hR1 hqR t₁ t₂ with hθ | hθ
  · exact Or.inl (matEq_of_matAct_eq (compat_conjU hMc) hMc fun v => by
      rw [hu, hq, hθ, matAct_matOf])
  · exact Or.inr (matEq_of_matAct_eq (compat_conjU hMc) (hMc.mul (compat_eMat m)) fun v => by
      rw [hu, hq, hθ, matAct_mul_apply hMc (compat_eMat m), matAct_eMat, matAct_matOf])

end Matrix

theorem mul_inv_mem_of_thetaT_eq (hS : Local.Setting (F.S : Subgroup G) D) {x y : G}
    (hxS : x ∈ (F.S : Subgroup G)) (hyS : y ∈ (F.S : Subgroup G))
    (hxN : x ∈ Subgroup.normalizer (D : Set G)) (hyN : y ∈ Subgroup.normalizer (D : Set G))
    (hxy : ∀ v, dD.thetaT hxN v = dD.thetaT hyN v) : x * y⁻¹ ∈ D :=
  dD.mem_of_thetaT_id hS (mul_mem hxS (inv_mem hyS)) (mul_mem hxN (inv_mem hyN)) fun v => by
    rw [dD.thetaT_mul hxN (inv_mem hyN), hxy, dD.thetaT_inv_thetaT]

theorem thetaT_proj_mul_e {e : G} (hS : Local.Setting (F.S : Subgroup G) D) (heR : e ∈ hS.R)
    (he : Rel34i dD e (2 ^ (m + 1))) {f : G} (hfR : f ∈ hS.R) {A B : IntMat}
    (hA : Compat (StrothTypeIndex.t201 m).k A) (hB : Compat (StrothTypeIndex.t201 m).k B)
    (hθ : ∀ v, dD.thetaT (hS.R_le_normalizer hfR) v = matAct _ A hA v)
    (hAB : MatEq (StrothTypeIndex.t201 m).k (conjρ A) (B * eMat m))
    (v : Torus (StrothTypeIndex.t201 m).k) :
    dD.thetaT (mul_mem (hS.R_le_normalizer (hS.proj_mem dD.ρ_mem hfR)) (hS.R_le_normalizer heR))
      v = matAct _ B hB v := by
  have heN := hS.R_le_normalizer heR
  have h1 : ∀ w, dD.thetaT (hS.R_le_normalizer (hS.proj_mem dD.ρ_mem hfR)) w =
      matAct _ (conjρ A) (compat_conjρ hA) w := fun w => by
    rw [thetaT_proj hS dD.ρ_mem hfR, matAct_conjρ (dD := dD) hA, hθ]
  rw [dD.thetaT_mul (hS.R_le_normalizer (hS.proj_mem dD.ρ_mem hfR)) heN, h1,
    t201_thetaT_of_rel34i he heN,
    matAct_congr (compat_conjρ hA) (hB.mul (compat_eMat m)) hAB,
    matAct_mul_apply hB (compat_eMat m),
    matAct_eMat, map_zsmul, smul_smul, sigma_sq_zsmul]

theorem false_of_acts_theta₁ (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 2 ≤ m) {e : G} (heR : e ∈ hS.R) (he : Rel34i dD e (2 ^ (m + 1))) {f : G}
    (hfR : f ∈ hS.R)
    (hθ : ∀ v, dD.thetaT (hS.R_le_normalizer hfR) v = matAct _ (theta₁₁ m) (compat_theta₁₁ hm) v) :
    False := by
  have hfN := hS.R_le_normalizer hfR
  have heN := hS.R_le_normalizer heR
  have hfS := hS.R_le_S hfR
  have heS := hS.R_le_S heR
  have huS : dD.u ∈ (F.S : Subgroup G) := h.u_eq ▸ F.u_mem_S
  have hc₁ := compat_theta₁₁ hm
  have hc₂ := compat_theta₁₂ hm
  set f₂ := hS.proj dD.ρ f * e with hf₂def
  have hf₂R : f₂ ∈ hS.R := mul_mem (hS.proj_mem dD.ρ_mem hfR) heR
  have hf₂N := hS.R_le_normalizer hf₂R
  have hθ₂ : ∀ v, dD.thetaT hf₂N v = matAct _ (theta₁₂ m) hc₂ v :=
    thetaT_proj_mul_e hS heR he hfR hc₁ hc₂ hθ (conjρ_theta₁₁ hm)
  have hact : ∀ {A B : IntMat} (hA : Compat (StrothTypeIndex.t201 m).k A)
      (hB : Compat (StrothTypeIndex.t201 m).k B), MatEq (Type201.k m) A B →
      ∀ v, matAct _ A hA v = matAct _ B hB v := fun hA hB hAB v => by
    rw [matAct_congr hA hB hAB]
  refine dD.t201_false_of_theta₁ hm he (conj_ofTorus_eq hfN hθ) (conj_ofTorus_eq hf₂N hθ₂) ?_
    ?_ ?_ ?_ ?_
  ·
    refine dD.mem_of_thetaT_id hS (mul_mem hfS hfS) (mul_mem hfN hfN) fun v => ?_
    rw [dD.thetaT_mul hfN hfN, hθ, hθ, ← matAct_mul_apply hc₁ hc₁,
      hact _ Compat.one (theta₁₁_mul_self hm), matAct_one_apply]
  ·
    exact dD.conj_mem_of_thetaT_comm hS hfS heS hfN heN fun x => by
      rw [t201_thetaT_of_rel34i he heN, t201_thetaT_of_rel34i he heN, map_zsmul]
  ·
    exact dD.conj_mem_of_thetaT_comm hS hfS (hS.R_le_S hf₂R) hfN hf₂N fun x => by
      rw [hθ, hθ₂, hθ, hθ₂, ← matAct_mul_apply hc₁ hc₂, ← matAct_mul_apply hc₂ hc₁,
        hact _ _ (theta₁₁_theta₁₂_comm hm)]
  ·
    have hgR := h.conj_u_mem_R hS hfR
    refine mul_inv_mem_of_thetaT_eq (dD := dD) hS (hS.R_le_S hgR) hfS (hS.R_le_normalizer hgR)
      hfN fun v => ?_
    rw [dD.thetaT_conj hfN dD.u_mem, hθ, ← matAct_conjU (dD := dD) hc₁,
      hact (compat_conjU hc₁) hc₁ (conjU_theta₁₁ hm), ← hθ]
  ·
    have hgR := h.conj_u_mem_R hS hf₂R
    refine mul_inv_mem_of_thetaT_eq (dD := dD) hS (hS.R_le_S hgR) (mul_mem hfS (hS.R_le_S hf₂R))
      (hS.R_le_normalizer hgR) (mul_mem hfN hf₂N) fun v => ?_
    rw [dD.thetaT_conj hf₂N dD.u_mem, hθ₂, ← matAct_conjU (dD := dD) hc₂,
      hact (compat_conjU hc₂) (hc₂.mul hc₁) (conjU_theta₁₂ hm), matAct_mul_apply hc₂ hc₁,
      dD.thetaT_mul hfN hf₂N, hθ, hθ₂]

theorem false_of_acts_theta₂ (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 2 ≤ m) {e : G} (heR : e ∈ hS.R) (he : Rel34i dD e (2 ^ (m + 1))) {f : G}
    (hfR : f ∈ hS.R)
    (hθ : ∀ v, dD.thetaT (hS.R_le_normalizer hfR) v = matAct _ (theta₂₁ m) (compat_theta₂₁ hm) v) :
    False := by
  have hfN := hS.R_le_normalizer hfR
  have heN := hS.R_le_normalizer heR
  have hfS := hS.R_le_S hfR
  have hc₁ := compat_theta₂₁ hm
  have hc₂ := compat_theta₂₂ hm
  set f₂ := hS.proj dD.ρ f * e with hf₂def
  have hf₂R : f₂ ∈ hS.R := mul_mem (hS.proj_mem dD.ρ_mem hfR) heR
  have hf₂N := hS.R_le_normalizer hf₂R
  have hθ₂ : ∀ v, dD.thetaT hf₂N v = matAct _ (theta₂₂ m) hc₂ v :=
    thetaT_proj_mul_e hS heR he hfR hc₁ hc₂ hθ (conjρ_theta₂₁ hm)
  have hact : ∀ {A B : IntMat} (hA : Compat (StrothTypeIndex.t201 m).k A)
      (hB : Compat (StrothTypeIndex.t201 m).k B), MatEq (Type201.k m) A B →
      ∀ v, matAct _ A hA v = matAct _ B hB v := fun hA hB hAB v => by
    rw [matAct_congr hA hB hAB]
  refine dD.t201_false_of_theta₂ hm he (conj_ofTorus_eq hfN hθ) (conj_ofTorus_eq hf₂N hθ₂) ?_
    ?_ ?_
  ·
    refine dD.mem_of_thetaT_id hS (mul_mem hfS hfS) (mul_mem hfN hfN) fun v => ?_
    rw [dD.thetaT_mul hfN hfN, hθ, hθ, ← matAct_mul_apply hc₁ hc₁,
      hact _ Compat.one (theta₂₁_mul_self hm), matAct_one_apply]
  ·
    have hgR := h.conj_u_mem_R hS hfR
    refine mul_inv_mem_of_thetaT_eq (dD := dD) hS (hS.R_le_S hgR) hfS (hS.R_le_normalizer hgR)
      hfN fun v => ?_
    rw [dD.thetaT_conj hfN dD.u_mem, hθ, ← matAct_conjU (dD := dD) hc₁,
      hact (compat_conjU hc₁) hc₁ (conjU_theta₂₁ hm), ← hθ]
  ·
    have hgR := h.conj_u_mem_R hS hf₂R
    have hff₂e : f * f₂ * e ∈ hS.R := mul_mem (mul_mem hfR hf₂R) heR
    refine mul_inv_mem_of_thetaT_eq (dD := dD) hS (hS.R_le_S hgR) (hS.R_le_S hff₂e)
      (hS.R_le_normalizer hgR) (hS.R_le_normalizer hff₂e) fun v => ?_
    rw [dD.thetaT_conj hf₂N dD.u_mem, hθ₂, ← matAct_conjU (dD := dD) hc₂,
      hact (compat_conjU hc₂) ((hc₂.mul hc₁).mul (compat_eMat m)) (conjU_theta₂₂ hm),
      matAct_mul_apply (hc₂.mul hc₁) (compat_eMat m), matAct_mul_apply hc₂ hc₁, matAct_eMat,
      dD.thetaT_mul (mul_mem hfN hf₂N) heN, dD.thetaT_mul hfN hf₂N, t201_thetaT_of_rel34i he heN,
      hθ, hθ₂, map_zsmul, map_zsmul]

theorem eMat_matEq_one {p : ℕ} (hp : p < m) : MatEq (Type200.k p) (eMat m) 1 := by
  refine MatEq.of_dvd (P := !![0, 0, 0; 0, 1, 0; 0, 0, 1]) (2 ^ (m + 1)) (fun i => ?_)
    fun i j => ?_
  · fin_cases i <;> simp only [Type200.k, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Fin.reduceFinMk, Matrix.cons_val] <;>
      exact pow_dvd_pow 2 (by omega)
  · fin_cases i <;> fin_cases j <;> simp [eMat, ofCols_apply]

theorem false_of_R1_lt (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    {e : G} (heR : e ∈ hS.R) (he : Rel34i dD e (2 ^ (m + 1)))
    (hR1 : hS.R1 dD.uv dD.t = D ⊔ Subgroup.zpowers e) (hlt : hS.R1 dD.uv dD.t < hS.R) :
    False := by
  obtain ⟨f, hfR, h₁, h₂⟩ := h.exists_twist_one_sigma hS heR he hR1 hlt
  have hfN := hS.R_le_normalizer hfR
  have heN := hS.R_le_normalizer heR
  set M := matOf (dD.thetaT hfN) with hMdef
  have hMc : Compat (StrothTypeIndex.t201 m).k M := compat_matOf _
  have hAut := isAut1_matOf (dD := dD) hS hfR hm
  have huv0 := matOf_comm_uv (dD := dD) hS hfR h₁
  have ht0 := matOf_twist_t (dD := dD) hS hfR h₂
  have hsq0 := matOf_sq h hS heR he hR1 hfR h₁ h₂
  have hρ0 := matOf_conjρ h hS heR he hR1 hfR h₁ h₂
  have hu0 := matOf_conjU h hS heR he hR1 hfR h₁ h₂
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  ·
    obtain rfl : m = 1 := by omega
    exact false_of_theta_one hMc hAut huv0 ht0 hsq0 hρ0 hu0
  have hkle : ∀ p, p ≤ m → ∀ i, Type200.k p i ≤ (StrothTypeIndex.t201 m).k i := by
    intro p hp i
    fin_cases i <;> simp [Type200.k, StrothTypeIndex.k, Type201.k] <;> omega
  have hcl : ∀ p, p ≤ m → ∀ {X : IntMat}, Compat (StrothTypeIndex.t201 m).k X →
      Compat (Type200.k p) X := by
    intro p hp X hX
    rw [type200_k_eq hp]
    exact Stroth34T201Levels.Compat.shift
      (fun i => by fin_cases i <;> simp [StrothTypeIndex.k, Type201.k] <;> omega) hX
  have hc : ∀ p, 1 ≤ p → p ≤ m - 1 → Compat (Type200.k p) M := fun p _ hp => hcl p (by omega) hMc
  have h1 : IsAut1 (Type200.k 1) M := by
    rw [type200_k_eq (by omega : 1 ≤ m)]
    exact Stroth34T201Levels.IsAut1.shift
      (fun i => by fin_cases i <;> simp [StrothTypeIndex.k, Type201.k] <;> omega) hAut
  have hMone : ∀ p, 1 ≤ p → p ≤ m - 1 → MatEq (Type200.k p) (M * eMat m) M := fun p hp1 hpm => by
    have := Stroth34T201Levels.MatEq.mul_left (hc p hp1 hpm) (eMat_matEq_one (m := m) (p := p)
      (by omega))
    rwa [Matrix.mul_one] at this
  have huv : ∀ p, 1 ≤ p → p ≤ m - 1 →
      MatEq (Type200.k p) (M * Type200.uvM) (Type200.uvM * M) := by
    intro p hp1 hpm
    have hU := uvM_matEq_type200 (m := m) (p := p) (by omega)
    exact Stroth34T201Levels.MatEq.trans
      (Stroth34T201Levels.MatEq.mul_left (hc p hp1 hpm) (Stroth34T201Levels.MatEq.symm' hU))
      (Stroth34T201Levels.MatEq.trans (Stroth34T201Levels.MatEq.mono (hkle p (by omega)) huv0)
        (Stroth34T201Levels.MatEq.mul_right hU M))
  have ht : ∀ p, 1 ≤ p → p ≤ m - 1 →
      MatEq (Type200.k p) (M * Type200.tM) (Type200.tM * M) := by
    intro p hp1 hpm
    have hT := tM_matEq_type200 (m := m) (p := p) (by omega)
    have hTM : Compat (Type200.k p) (Type201.tM m * M) :=
      (hcl p (by omega) (compat_tK m)).mul (hc p hp1 hpm)
    have hE : MatEq (Type200.k p) (Type201.tM m * M * eMat m) (Type201.tM m * M) := by
      have := Stroth34T201Levels.MatEq.mul_left hTM (eMat_matEq_one (m := m) (p := p) (by omega))
      rwa [Matrix.mul_one] at this
    exact Stroth34T201Levels.MatEq.trans
      (Stroth34T201Levels.MatEq.mul_left (hc p hp1 hpm) (Stroth34T201Levels.MatEq.symm' hT))
      (Stroth34T201Levels.MatEq.trans (Stroth34T201Levels.MatEq.mono (hkle p (by omega)) ht0)
        (Stroth34T201Levels.MatEq.trans hE (Stroth34T201Levels.MatEq.mul_right hT M)))
  have hnat : ∀ p, 1 ≤ p → p ≤ m - 1 → NatCond (Type200.k p) M := by
    intro p hp1 hpm
    refine ⟨?_, Or.inl ?_⟩
    · rcases hρ0 with hρ | hρ
      · exact Stroth34T201Levels.MatEq.mono (hkle p (by omega)) hρ
      · exact Stroth34T201Levels.MatEq.trans (Stroth34T201Levels.MatEq.mono (hkle p (by omega)) hρ)
          (eMat_matEq_one (by omega))
    · rcases hu0 with hu | hu
      · exact Stroth34T201Levels.MatEq.mono (hkle p (by omega)) hu
      · exact Stroth34T201Levels.MatEq.trans (Stroth34T201Levels.MatEq.mono (hkle p (by omega)) hu)
          (hMone p hp1 hpm)
  have hsq : ∀ p, 1 ≤ p → p ≤ m - 1 → MatEq (Type200.k p) (M * M) 1 := by
    intro p hp1 hpm
    rcases hsq0 with hs | hs
    · exact Stroth34T201Levels.MatEq.mono (hkle p (by omega)) hs
    · exact Stroth34T201Levels.MatEq.trans (Stroth34T201Levels.MatEq.mono (hkle p (by omega)) hs)
        (eMat_matEq_one (by omega))
  have hN := matEq_one_of_levels hm2 exists_wMat_one exists_wMat_of_two_le hc h1 huv ht hnat hsq
    hsq0
  have hθM : ∀ v, dD.thetaT hfN v = matAct _ M hMc v := fun v => by
    rw [matAct_congr hMc (compat_matOf (dD.thetaT hfN)) (MatEq.of_eq hMdef),
      matAct_matOf]
  have hfe : ∀ v, dD.thetaT (mul_mem hfN heN) v =
      (1 + 2 ^ (m + 1) : ℤ) • matAct _ M hMc v := fun v => by
    rw [dD.thetaT_mul hfN heN, t201_thetaT_of_rel34i he heN, hθM]
  have twist_e : ∀ {A : IntMat} (hA : Compat (StrothTypeIndex.t201 m).k A),
      MatEq (Type201.k m) M (A * eMat m) →
        ∀ v, dD.thetaT (mul_mem hfN heN) v = matAct _ A hA v := fun hA hMA v => by
    rw [hfe, matAct_congr hMc (hA.mul (compat_eMat m)) hMA, matAct_mul_apply hA (compat_eMat m),
      matAct_eMat, map_zsmul, smul_smul, sigma_sq_zsmul]
  rcases theta_classify hm2 hMc hN huv0 ht0 hρ0 hu0 with hθ | hθ | hθ | hθ
  · exact false_of_acts_theta₁ h hS hm2 heR he hfR fun v => by
      rw [hθM, matAct_congr hMc (compat_theta₁₁ hm2) hθ]
  · exact false_of_acts_theta₁ h hS hm2 heR he (mul_mem hfR heR) (twist_e (compat_theta₁₁ hm2) hθ)
  · exact false_of_acts_theta₂ h hS hm2 heR he hfR fun v => by
      rw [hθM, matAct_congr hMc (compat_theta₂₁ hm2) hθ]
  · exact false_of_acts_theta₂ h hS hm2 heR he (mul_mem hfR heR) (twist_e (compat_theta₂₁ hm2) hθ)

theorem eq_sup_zpowers_of_rel34i {G : Type} [Group G] [Finite G]
    {F : StrothFrame G} {D : Subgroup G} {m : ℕ} {dD : StrothWeakTypeData D (.t201 m)}
    (h : F.IsD D dD) (hm : 1 ≤ m)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (hmax : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D)
    (hSN : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    (h11 : 2 ^ 11 ∣ Nat.card G)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u)
    {e : G} (heR : e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (he : Rel34i dD e (2 ^ (m + 1))) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e := by
  have hS := h.setting hns
  have hR1 := h.t201_R1_eq_of_rel34i hS hm hfus heR he
  have hle : hS.R1 dD.uv dD.t ≤ hS.R := fun f hf => hf.1
  have key : hS.R1 dD.uv dD.t = hS.R := by
    by_contra hne
    exact false_of_R1_lt h hS hm heR he hR1 (lt_of_le_of_ne hle hne)
  show hS.R = _
  rw [← key, hR1]

end StrothFrame.IsD

end CFSG.CGT.Stroth77
