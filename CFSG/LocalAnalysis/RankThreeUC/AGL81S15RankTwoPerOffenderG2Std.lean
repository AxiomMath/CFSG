module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderNat
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base11
public import CFSG.Quasithin.Vol2.Ch9KGFFG2Model
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.SecB.K5
  CFSG.Quasithin.Vol2.Ch11.G2Q8 Matrix

private def g2s_toSix {F : Type} (w : Ix3 → F) : Fin 6 → F :=
  fun i => w (e6.symm i)

private def g2s_ofSix {F : Type} (u : Fin 6 → F) : Ix3 → F :=
  fun k => u (e6 k)

private theorem g2s_ofSix_toSix {F : Type} (w : Ix3 → F) :
    g2s_ofSix (g2s_toSix w) = w := by
  funext k
  simp [g2s_ofSix, g2s_toSix]

private theorem g2s_toSix_ofSix {F : Type} (u : Fin 6 → F) :
    g2s_toSix (g2s_ofSix u) = u := by
  funext i
  simp [g2s_ofSix, g2s_toSix]

private theorem g2s_mulVec_g2Six {F : Type} [Field F] [CharP F 2] (g : ↥(cayleyGroup F))
    (w : Ix3 → F) :
    ((g2Six g : Matrix.GeneralLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ
        g2s_toSix w = g2s_toSix (g2Act g w) := by
  have hM : ((g2Six g : Matrix.GeneralLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      ((g2Mat g : Matrix.GeneralLinearGroup Ix3 F) : Matrix Ix3 Ix3 F).submatrix e6.symm
        e6.symm := rfl
  rw [hM, Matrix.submatrix_mulVec_equiv]
  funext i
  have hw : g2s_toSix w ∘ (e6.symm).symm = w := by
    funext k
    simp [g2s_toSix]
  simp only [Function.comp_apply, g2s_toSix]
  rw [hw]
  have := congrFun (g2Mat_mulVec g w) (e6.symm i)
  simpa [g2s_toSix] using this

theorem natSchur_g2Six {F : Type} [Field F] [Finite F] [CharP F 2] :
    NatSchur (g2Six (K := F)) := by
  intro c hc
  let toSixHom : (Ix3 → F) →+ (Fin 6 → F) :=
    { toFun := g2s_toSix
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ofSixHom : (Fin 6 → F) →+ (Ix3 → F) :=
    { toFun := g2s_ofSix
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let T : (Ix3 → F) →+ (Ix3 → F) := ofSixHom.comp (c.comp toSixHom)
  have hofSix : ∀ (g : ↥(cayleyGroup F)) (u : Fin 6 → F),
      g2s_ofSix (((g2Six g : Matrix.GeneralLinearGroup (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) *ᵥ u) = g2Act g (g2s_ofSix u) := by
    intro g u
    have h := g2s_mulVec_g2Six g (g2s_ofSix u)
    rw [g2s_toSix_ofSix] at h
    rw [h, g2s_ofSix_toSix]
  have hT : ∀ (g : ↥(cayleyGroup F)) (x : Ix3 → F), T (g2Act g x) = g2Act g (T x) := by
    intro g x
    change g2s_ofSix (c (g2s_toSix (g2Act g x))) = g2Act g (g2s_ofSix (c (g2s_toSix x)))
    rw [← g2s_mulVec_g2Six, hc, hofSix]
  obtain ⟨c0, hc0⟩ := commutant_cayley T hT
  refine ⟨c0, fun u => ?_⟩
  have h := hc0 (g2s_ofSix u)
  change g2s_ofSix (c (g2s_toSix (g2s_ofSix u))) = c0 • g2s_ofSix u at h
  rw [g2s_toSix_ofSix] at h
  have h2 := congrArg g2s_toSix h
  rw [g2s_toSix_ofSix] at h2
  rw [h2]
  funext i
  simp [g2s_toSix, g2s_ofSix]

open CFSG.Quasithin.H13.Ch9.KGFF.G2M CFSG.Quasithin.B42G2Id
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

private noncomputable def g2no_N3 {F : Type} [Field F] : Matrix Ix3 Ix3 F :=
  fun k l => (if k = Sum.inl (1 : Fin 3) ∧ l = Sum.inl (0 : Fin 3) then (1 : F) else 0) +
    (if k = Sum.inr (0 : Fin 3) ∧ l = Sum.inr (1 : Fin 3) then (1 : F) else 0)

private theorem g2no_mat_root {F : Type} [Field F] [CharP F 2] (c : F) :
    ((g2Mat (zPsi (Pi.single iA 1) c) : GL Ix3 F) : Matrix Ix3 Ix3 F) =
      1 + c • g2no_N3 := by
  rw [zPsi_a]
  ext k l
  rw [g2Mat_apply, g2Act_tv]
  rcases k with k | k <;> fin_cases k <;> rcases l with l | l <;> fin_cases l <;>
    simp [g2no_N3, eu, ev]

private noncomputable def g2no_N6 {F : Type} [Field F] : Matrix (Fin 6) (Fin 6) F :=
  Matrix.reindexAlgEquiv F F e6 (g2no_N3 (F := F))

private theorem g2no_six_root {F : Type} [Field F] [CharP F 2] (c : F) :
    ((g2Six (zPsi (Pi.single iA 1) c) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      1 + c • g2no_N6 := by
  change Matrix.reindexAlgEquiv F F e6
      ((g2Mat (zPsi (Pi.single iA 1) c) : GL Ix3 F) : Matrix Ix3 Ix3 F) =
    1 + c • g2no_N6
  rw [g2no_mat_root, g2no_N6]
  simp only [map_add, map_smul, map_one]

private theorem g2no_N6_entry {F : Type} [Field F] :
    g2no_N6 (F := F) (e6 (Sum.inl (1 : Fin 3))) (e6 (Sum.inl (0 : Fin 3))) = 1 := by
  simp [g2no_N6, g2no_N3, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

private theorem g2no_exists_mulAut {F : Type} [Field F] [CharP F 2]
    (M : GL (Fin 6) F) (hM : M * M = 1)
    (hnorm : ∀ l : ↥(cayleyGroup F), ∃ l' : ↥(cayleyGroup F), g2Six l' = M * g2Six l * M⁻¹) :
    ∃ α : MulAut ↥(cayleyGroup F), ∀ l, g2Six (α l) = M * g2Six l * M⁻¹ := by
  classical
  let G6 : Subgroup (GL (Fin 6) F) := (g2Six (K := F)).range
  let αGL : MulAut (GL (Fin 6) F) := MulAut.conj M
  have hMconj : αGL * αGL = 1 := by
    rw [show αGL * αGL = MulAut.conj (M * M) from by rw [map_mul]]
    rw [hM, map_one]
  have hle : G6.map αGL.toMonoidHom ≤ G6 := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨l, rfl⟩ := hx
    obtain ⟨l', hl'⟩ := hnorm l
    exact ⟨l', by
      change g2Six l' = MulAut.conj M (g2Six l)
      rw [MulAut.conj_apply]
      exact hl'⟩
  have hmap : G6.map αGL.toMonoidHom = G6 := by
    refine le_antisymm hle ?_
    intro y hy
    refine Subgroup.mem_map.mpr ⟨αGL y, hle (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩), ?_⟩
    change αGL (αGL y) = y
    rw [← MulAut.mul_apply, hMconj, MulAut.one_apply]
  let αR : MulAut ↥G6 := mulAutRestrict G6 αGL hmap
  let e : ↥(cayleyGroup F) ≃* ↥G6 := MonoidHom.ofInjective (g2Six_injective (K := F))
  let α : MulAut ↥(cayleyGroup F) := e.trans (αR.trans e.symm)
  refine ⟨α, fun l => ?_⟩
  have hαl : α l = e.symm (αR (e l)) := rfl
  change (e (α l) : GL (Fin 6) F) = M * g2Six l * M⁻¹
  rw [hαl, MulEquiv.apply_symm_apply, coe_mulAutRestrict, MulAut.conj_apply,
    MonoidHom.ofInjective_apply]

theorem natOut_g2Six
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    NatOut (g2Six (K := F)) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_psiEquiv (F := F) hF hn
  intro M hM hnorm
  obtain ⟨α, hαM⟩ := g2no_exists_mulAut M hM hnorm
  let α' : MulAut ↥(adjointGroup .G2 F) :=
    { toFun := fun h => ψ.symm (α (ψ h))
      invFun := fun h => ψ.symm (α.symm (ψ h))
      left_inv := fun h => by simp
      right_inv := fun h => by simp
      map_mul' := fun h k => by simp [map_mul] }
  obtain ⟨⟨g, σ⟩, hg, -⟩ :=
    (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      hn F hF).1 α'
  have hα'eq : ∀ h : ↥(adjointGroup .G2 F),
      α' h = g * entrywiseAdjointAut .G2 σ h * g⁻¹ := by
    intro h
    apply Subtype.ext
    rw [hg h]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_entrywiseAdjointAut]
  have hαz : ∀ c : F, α (zPsi (Pi.single iA 1) c) =
      ψ g * zPsi (Pi.single iA 1) (σ c) * (ψ g)⁻¹ := by
    intro c
    have hγ : IsRoot .G2 (Pi.single iA 1) := CFSG.Blueprint.Chevalley.isRoot_single .G2 iA
    have hx : ψ (xPar (rootOperatorFamily .G2) (Pi.single iA 1) c) =
        zPsi (Pi.single iA 1) c := hψ _ hγ c
    have hxσ : ψ (xPar (rootOperatorFamily .G2) (Pi.single iA 1) (σ c)) =
        zPsi (Pi.single iA 1) (σ c) := hψ _ hγ (σ c)
    calc α (zPsi (Pi.single iA 1) c)
        = ψ (α' (xPar (rootOperatorFamily .G2) (Pi.single iA 1) c)) := by
          rw [← hx]; simp [α']
      _ = ψ (g * entrywiseAdjointAut .G2 σ
              (xPar (rootOperatorFamily .G2) (Pi.single iA 1) c) * g⁻¹) := by
          rw [hα'eq]
      _ = ψ g * ψ (entrywiseAdjointAut .G2 σ
              (xPar (rootOperatorFamily .G2) (Pi.single iA 1) c)) * (ψ g)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = ψ g * ψ (xPar (rootOperatorFamily .G2) (Pi.single iA 1) (σ c)) * (ψ g)⁻¹ := by
          rw [CFSG.StandardType.AutSt.entrywiseAdjointAut_xPar]
      _ = ψ g * zPsi (Pi.single iA 1) (σ c) * (ψ g)⁻¹ := by rw [hxσ]
  let g6 : GL (Fin 6) F := g2Six (ψ g)
  let M' : GL (Fin 6) F := g6⁻¹ * M
  have hσ1 : σ = 1 := by
    have hrel : ∀ c : F, M' * g2Six (zPsi (Pi.single iA 1) c) * M'⁻¹ =
        g2Six (zPsi (Pi.single iA 1) (σ c)) := by
      intro c
      have h1 := hαM (zPsi (Pi.single iA 1) c)
      rw [hαz c, map_mul, map_mul, map_inv] at h1
      have h2 : M' * g2Six (zPsi (Pi.single iA 1) c) * M'⁻¹ =
          g6⁻¹ * (M * g2Six (zPsi (Pi.single iA 1) c) * M⁻¹) * g6 := by
        change (g6⁻¹ * M) * g2Six (zPsi (Pi.single iA 1) c) * (g6⁻¹ * M)⁻¹ = _
        group
      rw [h2, ← h1]
      simp only [g6]
      group
    have hmat : ∀ c : F,
        (M' : Matrix (Fin 6) (Fin 6) F) * (1 + c • g2no_N6) *
            (M' : Matrix (Fin 6) (Fin 6) F)⁻¹ = 1 + σ c • g2no_N6 := by
      intro c
      have h := congrArg (fun z : GL (Fin 6) F => (z : Matrix (Fin 6) (Fin 6) F)) (hrel c)
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv] at h
      rw [g2no_six_root (F := F) c, g2no_six_root (F := F) (σ c)] at h
      exact h
    have hone : (M' : Matrix (Fin 6) (Fin 6) F) * (M' : Matrix (Fin 6) (Fin 6) F)⁻¹ = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.coe_mul,
        mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
    have h4 : ∀ c : F, (M' : Matrix (Fin 6) (Fin 6) F) * (c • g2no_N6) *
        (M' : Matrix (Fin 6) (Fin 6) F)⁻¹ = σ c • g2no_N6 := by
      intro c
      have h := hmat c
      rw [mul_add, add_mul, mul_one] at h
      rw [hone] at h
      exact add_left_cancel h
    have hNfix : (M' : Matrix (Fin 6) (Fin 6) F) * g2no_N6 *
        (M' : Matrix (Fin 6) (Fin 6) F)⁻¹ = g2no_N6 := by
      have h := h4 1
      simpa using h
    have hσeq : ∀ c : F, c = σ c := by
      intro c
      have h := h4 c
      have hL : (M' : Matrix (Fin 6) (Fin 6) F) * (c • g2no_N6) *
          (M' : Matrix (Fin 6) (Fin 6) F)⁻¹ =
          c • ((M' : Matrix (Fin 6) (Fin 6) F) * g2no_N6 *
            (M' : Matrix (Fin 6) (Fin 6) F)⁻¹) := by
        rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      rw [hL, hNfix] at h
      have hentry : c * g2no_N6 (e6 (Sum.inl (1 : Fin 3))) (e6 (Sum.inl (0 : Fin 3))) =
          σ c * g2no_N6 (e6 (Sum.inl (1 : Fin 3))) (e6 (Sum.inl (0 : Fin 3))) := by
        simpa using congrFun (congrFun h (e6 (Sum.inl 1))) (e6 (Sum.inl 0))
      rw [g2no_N6_entry] at hentry
      simpa using hentry
    exact RingEquiv.ext fun c => (hσeq c).symm
  have hα'conj : ∀ h : ↥(adjointGroup .G2 F), α' h = g * h * g⁻¹ := by
    intro h
    apply Subtype.ext
    rw [hα'eq h, hσ1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_entrywiseAdjointAut,
      units_map_entrywiseHom_one_ringEquiv]
  have hαconj : ∀ l : ↥(cayleyGroup F), α l = ψ g * l * (ψ g)⁻¹ := by
    intro l
    have hl : ψ (α' (ψ.symm l)) = α l := by simp [α']
    rw [← hl, hα'conj, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hM'conj : ∀ l : ↥(cayleyGroup F), M' * g2Six l * M'⁻¹ = g2Six l := by
    intro l
    have h1 := hαM l
    rw [hαconj l, map_mul, map_mul, map_inv] at h1
    have h2 : M' * g2Six l * M'⁻¹ = g6⁻¹ * (M * g2Six l * M⁻¹) * g6 := by
      change (g6⁻¹ * M) * g2Six l * (g6⁻¹ * M)⁻¹ = _
      group
    rw [h2, ← h1]
    simp only [g6]
    group
  have hcomm : ∀ l : ↥(cayleyGroup F), M' * g2Six l = g2Six l * M' := by
    intro l
    have h := congrArg (fun z : GL (Fin 6) F => z * M') (hM'conj l)
    simp only [mul_assoc, inv_mul_cancel, mul_one] at h
    exact h
  let toSixHom : (Ix3 → F) →+ (Fin 6 → F) :=
    { toFun := g2s_toSix, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let ofSixHom : (Fin 6 → F) →+ (Ix3 → F) :=
    { toFun := g2s_ofSix, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let mulVecHom : (Fin 6 → F) →+ (Fin 6 → F) :=
    (Matrix.mulVecLin (M' : Matrix (Fin 6) (Fin 6) F)).toAddMonoidHom
  let T : (Ix3 → F) →+ (Ix3 → F) := ofSixHom.comp (mulVecHom.comp toSixHom)
  have hcommm : ∀ l : ↥(cayleyGroup F),
      (M' : Matrix (Fin 6) (Fin 6) F) * (g2Six l : Matrix (Fin 6) (Fin 6) F) =
        (g2Six l : Matrix (Fin 6) (Fin 6) F) * (M' : Matrix (Fin 6) (Fin 6) F) := by
    intro l
    have h := congrArg (fun z : GL (Fin 6) F => (z : Matrix (Fin 6) (Fin 6) F)) (hcomm l)
    simpa using h
  have hT : ∀ (l : ↥(cayleyGroup F)) (x : Ix3 → F), T (g2Act l x) = g2Act l (T x) := by
    intro l x
    change g2s_ofSix ((M' : Matrix (Fin 6) (Fin 6) F) *ᵥ g2s_toSix (g2Act l x)) =
      g2Act l (g2s_ofSix ((M' : Matrix (Fin 6) (Fin 6) F) *ᵥ g2s_toSix x))
    have h1 : g2s_toSix (g2Act l x) =
        (g2Six l : Matrix (Fin 6) (Fin 6) F) *ᵥ g2s_toSix x :=
      (g2s_mulVec_g2Six l x).symm
    have h2 : (M' : Matrix (Fin 6) (Fin 6) F) *ᵥ
          ((g2Six l : Matrix (Fin 6) (Fin 6) F) *ᵥ g2s_toSix x) =
        (g2Six l : Matrix (Fin 6) (Fin 6) F) *ᵥ
          ((M' : Matrix (Fin 6) (Fin 6) F) *ᵥ g2s_toSix x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcommm l]
    rw [h1, h2]
    have h3 := congrArg g2s_ofSix
      (g2s_mulVec_g2Six l (g2s_ofSix ((M' : Matrix (Fin 6) (Fin 6) F) *ᵥ g2s_toSix x)))
    rw [g2s_toSix_ofSix, g2s_ofSix_toSix] at h3
    exact h3
  obtain ⟨c0, hc0⟩ := commutant_cayley T hT
  have hM'vec : ∀ u : Fin 6 → F, (M' : Matrix (Fin 6) (Fin 6) F) *ᵥ u = c0 • u := by
    intro u
    have h := hc0 (g2s_ofSix u)
    change g2s_ofSix ((M' : Matrix (Fin 6) (Fin 6) F) *ᵥ g2s_toSix (g2s_ofSix u)) =
      c0 • g2s_ofSix u at h
    rw [g2s_toSix_ofSix] at h
    have h2 := congrArg g2s_toSix h
    rw [g2s_toSix_ofSix] at h2
    have h3 : g2s_toSix (c0 • g2s_ofSix u) = c0 • u := by
      funext i
      simp [g2s_toSix, g2s_ofSix]
    rw [h3] at h2
    exact h2
  have hM'scalar : (M' : Matrix (Fin 6) (Fin 6) F) = c0 • 1 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [hM'vec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hMM : (M : Matrix (Fin 6) (Fin 6) F) * (M : Matrix (Fin 6) (Fin 6) F) = 1 := by
    have h := congrArg (fun z : GL (Fin 6) F => (z : Matrix (Fin 6) (Fin 6) F)) hM
    simpa using h
  have hMmat : (M : Matrix (Fin 6) (Fin 6) F) = c0 • (g6 : Matrix (Fin 6) (Fin 6) F) := by
    have hgl : M = g6 * M' := by
      change M = g6 * (g6⁻¹ * M)
      group
    have h := congrArg (fun z : GL (Fin 6) F => (z : Matrix (Fin 6) (Fin 6) F)) hgl
    simp only [Matrix.GeneralLinearGroup.coe_mul] at h
    rw [h, hM'scalar, Algebra.mul_smul_comm, mul_one]
  have hA : (g6 : Matrix (Fin 6) (Fin 6) F) * (g6 : Matrix (Fin 6) (Fin 6) F) =
      (c0 ^ 2)⁻¹ • 1 := by
    have h1 : c0 ^ 2 • ((g6 : Matrix (Fin 6) (Fin 6) F) *
        (g6 : Matrix (Fin 6) (Fin 6) F)) = 1 := by
      have h2 : (c0 • (g6 : Matrix (Fin 6) (Fin 6) F)) *
          (c0 • (g6 : Matrix (Fin 6) (Fin 6) F)) = 1 := by
        rw [← hMmat]
        exact hMM
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul] at h2
      simpa [pow_two] using h2
    have hc0sq : c0 ^ 2 ≠ 0 := by
      intro h0
      have h := h1
      rw [h0, zero_smul] at h
      exact zero_ne_one h
    ext i j
    have hentry := congrArg (fun M : Matrix (Fin 6) (Fin 6) F => M i j) h1
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hentry
    by_cases hij : i = j
    · rw [if_pos hij] at hentry
      rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, if_pos hij, mul_one]
      exact eq_inv_of_mul_eq_one_right hentry
    · rw [if_neg hij] at hentry
      rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, if_neg hij, mul_zero]
      exact (mul_eq_zero.mp hentry).resolve_left hc0sq
  have hBscalar : (g2Six ((ψ g) ^ 2) : Matrix (Fin 6) (Fin 6) F) = (c0 ^ 2)⁻¹ • 1 := by
    calc (g2Six ((ψ g) ^ 2) : Matrix (Fin 6) (Fin 6) F)
        = ((g2Six (ψ g) * g2Six (ψ g) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
          rw [pow_two, map_mul]
      _ = (g6 : Matrix (Fin 6) (Fin 6) F) * (g6 : Matrix (Fin 6) (Fin 6) F) := by
          simp [g6]
      _ = (c0 ^ 2)⁻¹ • 1 := hA
  have hcentral : ∀ l : ↥(cayleyGroup F), l * (ψ g) ^ 2 = (ψ g) ^ 2 * l := by
    intro l
    refine g2Six_injective (K := F) ?_
    rw [map_mul, map_mul]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hBscalar]
    simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  obtain ⟨c, hc0', hc1'⟩ := CFSG.Quasithin.B42G2Id.exists_ne_zero_ne_one_of_three_le
    (K := F) (by rw [hF]; exact CFSG.Quasithin.B42G2Id.three_le_two_pow hn)
  have hz : (ψ g) ^ 2 ∈ Subgroup.center ↥(cayleyGroup F) :=
    Subgroup.mem_center_iff.mpr hcentral
  have hz1 : (ψ g) ^ 2 = 1 := by
    have := (CFSG.Quasithin.A318Excl.center_cayleyGroup_eq_bot hc0' hc1').le hz
    simpa using this
  have hB1 : (g2Six ((ψ g) ^ 2) : Matrix (Fin 6) (Fin 6) F) = 1 := by
    rw [hz1, map_one, Matrix.GeneralLinearGroup.coe_one]
  have hc0sq_eq : c0 ^ 2 = 1 := by
    have h := hB1.symm.trans hBscalar
    have hentry : (1 : F) = (c0 ^ 2)⁻¹ := by
      have h00 := congrArg (fun M : Matrix (Fin 6) (Fin 6) F => M (0 : Fin 6) (0 : Fin 6)) h
      simpa [Matrix.one_apply, Matrix.smul_apply, smul_eq_mul] using h00
    exact inv_eq_one.mp hentry.symm
  have hc0_eq : c0 = 1 := by
    have h : c0 ^ 2 = (1 : F) ^ 2 := by simpa using hc0sq_eq
    exact CharTwo.sq_inj.mp h
  refine ⟨ψ g, ?_⟩
  apply Units.ext
  rw [hMmat, hc0_eq, one_smul]

end CFSG.LocalAnalysis.RankThreeUC.S15

end
