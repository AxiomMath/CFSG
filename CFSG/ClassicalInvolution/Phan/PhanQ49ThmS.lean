module

public import CFSG.ClassicalInvolution.Phan.PhanQ48Frames

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section StdFrames

variable {F : Type} [Field F]

@[expose] def v8 (x y : Fin 4 → F) : V8 F := Sum.elim x y

theorem Q8_v8 (x y : Fin 4 → F) : Q8 (v8 x y) = ∑ i, x i * y i := by
  rw [Q8_eq_sum]
  rfl

theorem B8_v8 (x y x' y' : Fin 4 → F) :
    B8 (v8 x y) (v8 x' y') = ∑ i, (x i * y' i + x' i * y i) := by
  rw [B8_eq_sum]
  rfl

variable (ε a c : F)

@[expose] noncomputable def stdNP1 : NPair ε where
  x := v8 ![1, 0, 0, 0] ![1, 0, 0, 0]
  y := v8 ![0, 1, 0, 0] ![0, ε, 0, 0]
  hx := by simp [Q8_v8, Fin.sum_univ_four]
  hy := by simp [Q8_v8, Fin.sum_univ_four]
  hxy := by simp [B8_v8, Fin.sum_univ_four]

@[expose] noncomputable def stdNP2 : NPair ε where
  x := v8 ![0, 0, 1, 0] ![0, 0, 1, 0]
  y := v8 ![0, 0, 0, 1] ![0, 0, 0, ε]
  hx := by simp [Q8_v8, Fin.sum_univ_four]
  hy := by simp [Q8_v8, Fin.sum_univ_four]
  hxy := by simp [B8_v8, Fin.sum_univ_four]

@[expose] noncomputable def stdNP3 (hac : a ^ 2 + ε * c ^ 2 = -1) : NPair ε where
  x := v8 ![a, c, 0, 0] ![-a, -(ε * c), 0, 0]
  y := v8 ![-(ε * c), a, 0, 0] ![ε * c, -(ε * a), 0, 0]
  hx := by
    simp only [Q8_v8, Fin.sum_univ_four]
    simp
    linear_combination -hac
  hy := by
    simp only [Q8_v8, Fin.sum_univ_four]
    simp
    linear_combination -ε * hac
  hxy := by
    simp only [B8_v8, Fin.sum_univ_four]
    simp
    ring

@[expose] noncomputable def stdNP4 (hac : a ^ 2 + ε * c ^ 2 = -1) : NPair ε where
  x := v8 ![0, 0, a, c] ![0, 0, -a, -(ε * c)]
  y := v8 ![0, 0, -(ε * c), a] ![0, 0, ε * c, -(ε * a)]
  hx := by
    simp only [Q8_v8, Fin.sum_univ_four]
    simp
    linear_combination -hac
  hy := by
    simp only [Q8_v8, Fin.sum_univ_four]
    simp
    linear_combination -ε * hac
  hxy := by
    simp only [B8_v8, Fin.sum_univ_four]
    simp
    ring

theorem jG_stdNP1 : jG ε (stdNP1 ε).x = (stdNP1 ε).y := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [stdNP1, jG, v8]

theorem jH_stdNP1 : jH ε (stdNP1 ε).x = (stdNP1 ε).y := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [stdNP1, jH, v8]

theorem jG_stdNP2 : jG ε (stdNP2 ε).x = (stdNP2 ε).y := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [stdNP2, jG, v8]

theorem jH_stdNP2 : jH ε (stdNP2 ε).x = (stdNP2 ε).y := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [stdNP2, jH, v8]

theorem jG_stdNP3 (hac : a ^ 2 + ε * c ^ 2 = -1) :
    jG ε (stdNP3 ε a c hac).x = (stdNP3 ε a c hac).y := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [stdNP3, jG, v8]

theorem jH_stdNP3 (hac : a ^ 2 + ε * c ^ 2 = -1) :
    jH ε (stdNP3 ε a c hac).x = (stdNP3 ε a c hac).y := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [stdNP3, jH, v8]

theorem jG_stdNP4 (hac : a ^ 2 + ε * c ^ 2 = -1) :
    jG ε (stdNP4 ε a c hac).x = (stdNP4 ε a c hac).y := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [stdNP4, jG, v8]

theorem jH_stdNP4 (hac : a ^ 2 + ε * c ^ 2 = -1) :
    jH ε (stdNP4 ε a c hac).x = -(stdNP4 ε a c hac).y := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [stdNP4, jH, v8]

@[expose] noncomputable def stdFrame3 (hac : a ^ 2 + ε * c ^ 2 = -1) : Fin 3 → NPair ε :=
  ![stdNP1 ε, stdNP2 ε, stdNP3 ε a c hac]

theorem stdFrame3_orth (hac : a ^ 2 + ε * c ^ 2 = -1) (i j : Fin 3) (hij : i ≠ j) :
    B8 (stdFrame3 ε a c hac i).x (stdFrame3 ε a c hac j).x = 0 ∧
      B8 (stdFrame3 ε a c hac i).x (stdFrame3 ε a c hac j).y = 0 ∧
      B8 (stdFrame3 ε a c hac i).y (stdFrame3 ε a c hac j).x = 0 ∧
      B8 (stdFrame3 ε a c hac i).y (stdFrame3 ε a c hac j).y = 0 := by
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp [stdFrame3, stdNP1, stdNP2, stdNP3, B8_v8, Fin.sum_univ_four] <;> ring)

end StdFrames

section Ext

variable {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]

@[expose] def extLin (T : V8 F →ₗ[F] V8 F) : V8 K →ₗ[K] V8 K where
  toFun v := ∑ j, v j • extV K (T (Pi.single j 1))
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.smul_sum, smul_smul]

theorem extLin_apply (T : V8 F →ₗ[F] V8 F) (v : V8 K) :
    extLin K T v = ∑ j, v j • extV K (T (Pi.single j 1)) := rfl

theorem extLin_extV (T : V8 F →ₗ[F] V8 F) (x : V8 F) : extLin K T (extV K x) = extV K (T x) := by
  ext i
  rw [extLin_apply]
  have h := congrFun (LinearMap.pi_apply_eq_sum_univ T x) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, extV] at h ⊢
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (Pi.single j (1 : F) : V8 F) = fun j' => if j = j' then 1 else 0 := by
    ext j'
    simp [Pi.single_apply, eq_comm]
  simp [map_mul, e]

theorem single_eq_extV (j : Fin 4 ⊕ Fin 4) :
    (Pi.single j (1 : K) : V8 K) = extV K (Pi.single j (1 : F) : V8 F) := by
  ext i
  by_cases h : i = j
  · subst h
    simp [extV]
  · simp [extV, h]

theorem B8_extLin (T : V8 F →ₗ[F] V8 F) (hT : ∀ x y, B8 (T x) (T y) = B8 x y) (u v : V8 K) :
    B8 (extLin K T u) (extLin K T v) = B8 u v := by
  have hbil : ((quadPlus 4 K).polarBilin).compl₁₂ (extLin K T) (extLin K T) =
      (quadPlus 4 K).polarBilin := by
    refine LinearMap.BilinForm.ext_basis (Pi.basisFun K (Fin 4 ⊕ Fin 4)) fun i j => ?_
    simp only [LinearMap.compl₁₂_apply, Pi.basisFun_apply, QuadraticMap.polarBilin_apply_apply]
    rw [single_eq_extV (F := F) K i, single_eq_extV (F := F) K j, extLin_extV, extLin_extV]
    show B8 _ _ = B8 _ _
    rw [B8_extV, B8_extV, hT]
  have := LinearMap.congr_fun₂ hbil u v
  simpa only [LinearMap.compl₁₂_apply, QuadraticMap.polarBilin_apply_apply] using this

theorem Q8_extLin (T : V8 F →ₗ[F] V8 F) (hT : ∀ x y, B8 (T x) (T y) = B8 x y) (h2 : (2 : K) ≠ 0)
    (v : V8 K) : Q8 (extLin K T v) = Q8 v := by
  have h1 := B8_extLin K T hT v v
  rw [B8_self, B8_self] at h1
  exact (mul_right_injective₀ h2) h1

@[expose] noncomputable def gK (g : spinGroup (quadPlus 4 F)) : V8 K →ₗ[K] V8 K :=
  extLin K (spinAction (quadPlus 4 F) g).toLinearMap

theorem gK_extV (g : spinGroup (quadPlus 4 F)) (x : V8 F) :
    gK K g (extV K x) = extV K (spinAction (quadPlus 4 F) g x) :=
  extLin_extV K _ x

theorem gK_Q (h2 : (2 : K) ≠ 0) (g : spinGroup (quadPlus 4 F)) (v : V8 K) :
    Q8 (gK K g v) = Q8 v :=
  Q8_extLin K _ (fun x y => by
    show B8 (spinAction (quadPlus 4 F) g x) (spinAction (quadPlus 4 F) g y) = B8 x y
    simp only [B8, polar_spinAction]) h2 v

theorem gK_gK_inv (g : spinGroup (quadPlus 4 F)) (v : V8 K) :
    gK K g⁻¹ (gK K g v) = v := by
  have h : (gK K g⁻¹).comp (gK K g) = LinearMap.id := by
    refine (Pi.basisFun K (Fin 4 ⊕ Fin 4)).ext fun i => ?_
    rw [Pi.basisFun_apply, single_eq_extV (F := F) K i]
    simp only [LinearMap.comp_apply, gK_extV, LinearMap.id_apply]
    congr 1
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  exact LinearMap.congr_fun h v

theorem gK_vecK {ε : F} (D : KData F K ε) (g : spinGroup (quadPlus 4 F)) (z : NPair ε) :
    gK K g (vecK D z) = vecK D (g • z) := by
  unfold vecK
  rw [map_add, map_smul, map_smul, gK_extV, gK_extV]
  simp only [one_smul, NPair.smul_x, NPair.smul_y]

end Ext

section ThmS

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem quadPlusForm_Q (v : V8 K) : (quadPlusForm 4 K).Q v = Q8 v := by
  rw [Q8_eq_sum]
  rfl

theorem finrank_V8 : Module.finrank K (V8 K) = 8 := by
  simp [Module.finrank_fintype_fun_eq_card]

theorem PhanSolid.isLagrangian [Finite K] {W : Submodule K (V8 K)} (hW : PhanSolid D W)
    (h2 : (2 : K) ≠ 0) : (quadPlusForm 4 K).IsLagrangian W := by
  refine ⟨fun w hw => ?_, ?_⟩
  · rw [quadPlusForm_Q]
    have h1 := hW.ts w hw w hw
    rw [B8_self] at h1
    exact (mul_eq_zero.1 h1).resolve_left h2
  · rw [hW.finrank_eq h2]
    have : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := finrank_V8
    omega

theorem PhanSolid.exists_conj_std [Finite F] [Finite K] {W : Submodule K (V8 K)}
    (hW : PhanSolid D W) (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = D.τ x) :
    ∃ g : spinGroup (quadPlus 4 F),
      W = (solidOf D (jGK K ε)).map (gK K g) ∨ W = (solidOf D (jHK K ε)).map (gK K g) := by
  have h2F : (2 : F) ≠ 0 := two_ne_zero_of_algebra (F := F) h2
  obtain ⟨s, t, hst⟩ := exists_norm_eq hodd hε (-1)
  have hac : s ^ 2 + ε * (t / ε) ^ 2 = -1 := by
    rw [← hst]
    field_simp
  obtain ⟨z, hindep, hzW, hzorth⟩ := PhanSolid.exists_orthoframe D hW hodd h2 hε hσ
  let z3 : Fin 3 → NPair ε := fun i => z i.castSucc
  obtain ⟨g, hg⟩ := exists_spin_frames (le_refl 3) hodd h2F hε z3 (stdFrame3 ε s (t / ε) hac)
    (fun i j hij => hzorth i.castSucc j.castSucc (fun h => hij (Fin.castSucc_injective _ h)))
    (stdFrame3_orth ε s (t / ε) hac)
  have hQ8 := quadPlusForm_Q (K := K)
  have hWG := (phanJK_jGK D).phanSolid h2 hε
  have hWH := (phanJK_jHK D).phanSolid h2 hε
  have hWL := hW.isLagrangian D h2
  have hindep3 : LinearIndependent K (fun i : Fin 3 => vecK D (z3 i)) :=
    hindep.comp Fin.castSucc (Fin.castSucc_injective 3)
  let I : Submodule K (V8 K) := Submodule.span K (Set.range fun i : Fin 3 => vecK D (z3 i))
  have hIW : I ≤ W := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hzW _)
  have hI_ts : (quadPlusForm 4 K).IsTotallySingular I := fun v hv => hWL.1 v (hIW hv)
  have hI_dim : Module.finrank K I = 3 := by
    rw [finrank_span_eq_card hindep3]
    simp
  obtain ⟨Y, Y', hYY', hY, hY', hIY, hIY', huniq⟩ := QuadForm.exists_isLagrangian_pair
    (Φ := quadPlusForm 4 K) (n := 4) (by rw [finrank_V8]) (isLagrangian_quadPlusForm 4 K) hI_ts
    (by rw [hI_dim])
  have hgQ : ∀ v, (quadPlusForm 4 K).Q (gK K g v) = (quadPlusForm 4 K).Q v := fun v => by
    rw [hQ8, hQ8]
    exact gK_Q K h2 g v
  have hLG : (quadPlusForm 4 K).IsLagrangian ((solidOf D (jGK K ε)).map (gK K g)) :=
    (hWG.isLagrangian D h2).map hgQ
  have hLH : (quadPlusForm 4 K).IsLagrangian ((solidOf D (jHK K ε)).map (gK K g)) :=
    (hWH.isLagrangian D h2).map hgQ
  have hvec : ∀ i : Fin 3, vecK D (z3 i) = gK K g (vecK D (stdFrame3 ε s (t / ε) hac i)) := by
    intro i
    rw [gK_vecK, hg i]
  have hstdG : ∀ i : Fin 3, vecK D (stdFrame3 ε s (t / ε) hac i) ∈ solidOf D (jGK K ε) := by
    intro i
    rw [vecK_mem_solidOf_iff h2 hε (jG ε) (jGK_extV K ε) (jG_jG ε)]
    fin_cases i
    · exact jG_stdNP1 ε
    · exact jG_stdNP2 ε
    · exact jG_stdNP3 ε s (t / ε) hac
  have hstdH : ∀ i : Fin 3, vecK D (stdFrame3 ε s (t / ε) hac i) ∈ solidOf D (jHK K ε) := by
    intro i
    rw [vecK_mem_solidOf_iff h2 hε (jH ε) (jHK_extV K ε) (jH_jH ε)]
    fin_cases i
    · exact jH_stdNP1 ε
    · exact jH_stdNP2 ε
    · exact jH_stdNP3 ε s (t / ε) hac
  have hILG : I ≤ (solidOf D (jGK K ε)).map (gK K g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨vecK D (stdFrame3 ε s (t / ε) hac i), hstdG i, (hvec i).symm⟩
  have hILH : I ≤ (solidOf D (jHK K ε)).map (gK K g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨vecK D (stdFrame3 ε s (t / ε) hac i), hstdH i, (hvec i).symm⟩
  have hne : (solidOf D (jGK K ε)).map (gK K g) ≠ (solidOf D (jHK K ε)).map (gK K g) := by
    intro h
    have h4 : vecK D (stdNP4 ε s (t / ε) hac) ∈ solidOf D (jGK K ε) := by
      rw [vecK_mem_solidOf_iff h2 hε (jG ε) (jGK_extV K ε) (jG_jG ε)]
      exact jG_stdNP4 ε s (t / ε) hac
    have h5 : gK K g (vecK D (stdNP4 ε s (t / ε) hac)) ∈
        (solidOf D (jGK K ε)).map (gK K g) := ⟨_, h4, rfl⟩
    rw [h] at h5
    obtain ⟨w, hw, hw'⟩ := h5
    have hw'' := QuadForm.injective_of_Q hgQ hw'
    rw [hw'', SetLike.mem_coe] at hw
    rw [vecK_mem_solidOf_iff h2 hε (jH ε) (jHK_extV K ε) (jH_jH ε)] at hw
    have h6 := jH_stdNP4 ε s (t / ε) hac
    rw [hw] at h6
    have h7 : (2 : F) • (stdNP4 ε s (t / ε) hac).y = 0 := by
      rw [two_smul]
      exact (add_eq_zero_iff_eq_neg.2 h6)
    have h8 : (stdNP4 ε s (t / ε) hac).y = 0 := (smul_eq_zero.1 h7).resolve_left h2F
    have := (stdNP4 ε s (t / ε) hac).hy
    rw [h8] at this
    simp [Q8_eq_sum] at this
    exact hε this.symm
  refine ⟨g, ?_⟩
  rcases huniq _ hLG hILG with h1 | h1 <;> rcases huniq _ hLH hILH with h3 | h3 <;>
    rcases huniq _ hWL hIW with h4 | h4
  · exact absurd (h1.trans h3.symm) hne
  · exact absurd (h1.trans h3.symm) hne
  · left; exact h4.trans h1.symm
  · right; exact h4.trans h3.symm
  · right; exact h4.trans h3.symm
  · left; exact h4.trans h1.symm
  · exact absurd (h1.trans h3.symm) hne
  · exact absurd (h1.trans h3.symm) hne

theorem vecK_mem_map_gK_iff (g : spinGroup (quadPlus 4 F)) {Wx : Submodule K (V8 K)}
    (z : NPair ε) : vecK D z ∈ Wx.map (gK K g) ↔ vecK D (g⁻¹ • z) ∈ Wx := by
  constructor
  · rintro ⟨w, hw, hwz⟩
    have : gK K g⁻¹ (gK K g w) = gK K g⁻¹ (vecK D z) := by rw [hwz]
    rw [gK_gK_inv, gK_vecK] at this
    rw [← this]
    exact hw
  · intro h
    refine ⟨_, h, ?_⟩
    rw [gK_vecK, NPair.smul_inv_smul']

theorem PhanSolid.exists_conj_std_iff [Finite F] [Finite K] {W : Submodule K (V8 K)}
    (hW : PhanSolid D W) (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = D.τ x) :
    ∃ g : spinGroup (quadPlus 4 F),
      (∀ z : NPair ε, vecK D z ∈ W ↔ vecK D (g⁻¹ • z) ∈ solidOf D (jGK K ε)) ∨
      (∀ z : NPair ε, vecK D z ∈ W ↔ vecK D (g⁻¹ • z) ∈ solidOf D (jHK K ε)) := by
  obtain ⟨g, hg⟩ := hW.exists_conj_std D hodd h2 hε hσ
  refine ⟨g, ?_⟩
  rcases hg with h | h
  · left
    intro z
    rw [h, vecK_mem_map_gK_iff]
  · right
    intro z
    rw [h, vecK_mem_map_gK_iff]

end ThmS

end CFSG.ClassicalInvolution.PhanQ
