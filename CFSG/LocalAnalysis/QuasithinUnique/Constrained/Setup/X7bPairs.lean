module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bInvol

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7

section RankOne

theorem rank_one_vecMulVec {F : Type} [Field F] (N : Matrix (Fin 4) (Fin 4) F) (hN : N.rank = 1) :
    ∃ u ℓ : Fin 4 → F, u ≠ 0 ∧ N = vecMulVec u ℓ := by
  rw [Matrix.rank_eq_finrank_span_cols] at hN
  obtain ⟨j₀, hj₀⟩ : ∃ j, N.col j ≠ 0 := by
    by_contra h
    push Not at h
    have : Submodule.span F (Set.range N.col) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨j, rfl⟩
      exact h j
    rw [this, finrank_bot] at hN
    exact zero_ne_one hN
  set S := Submodule.span F (Set.range N.col) with hS
  have hu : N.col j₀ ∈ S := Submodule.subset_span ⟨j₀, rfl⟩
  have h1 := (finrank_eq_one_iff_of_nonzero' (⟨N.col j₀, hu⟩ : S)
    (fun h => hj₀ (congrArg Subtype.val h))).mp hN
  choose c hc using fun j => h1 ⟨N.col j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨N.col j₀, c, hj₀, ?_⟩
  ext i j
  have := congrArg (fun w : S => (w : Fin 4 → F) i) (hc j)
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at this
  rw [vecMulVec_apply]
  simp [Matrix.col_apply] at this ⊢
  rw [mul_comm]
  exact this.symm

end RankOne

section Transvection

variable {F : Type} [Field F] [CharP F 2]

theorem transv_coeff (u ℓ : Fin 4 → F)
    (h : (1 + vecMulVec u ℓ)ᵀ * minorJ F * (1 + vecMulVec u ℓ) = minorJ F) :
    ∀ i j : Fin 4, ℓ i * u j.rev = u i.rev * ℓ j := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  intro i j
  have hij := congrFun (congrFun h i) j
  have hq : ℓ i * u j.rev + u i.rev * ℓ j + 2 * (ℓ i * ℓ j * (u 0 * u 3 + u 1 * u 2)) = 0 := by
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply, vecMulVec_apply,
        Matrix.one_apply, Matrix.add_apply, Fin.rev] at hij ⊢ <;>
      linear_combination hij
  rw [h2, zero_mul, add_zero] at hq
  exact CharTwo.add_eq_zero.mp hq

theorem transvection_form (u ℓ : Fin 4 → F) (hu : u ≠ 0) (hℓ : ℓ ≠ 0)
    (h : (1 + vecMulVec u ℓ)ᵀ * minorJ F * (1 + vecMulVec u ℓ) = minorJ F) :
    ∃ t : F, t ≠ 0 ∧ ∀ i, ℓ i = t * u i.rev := by
  have hc := transv_coeff u ℓ h
  obtain ⟨m, hm⟩ : ∃ m, u m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu (funext hcon)
  refine ⟨ℓ m.rev / u m, ?_, fun i => ?_⟩
  · intro h0
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · apply hℓ
      funext i
      have := hc i m.rev
      rw [Fin.rev_rev, h0, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hm
    · exact hm h0
  · have := hc i m.rev
    rw [Fin.rev_rev] at this
    field_simp
    linear_combination this

end Transvection

section Conj

open scoped Pointwise

variable {F : Type} [Field F] [CharP F 2] [Fintype F]

omit [Fintype F] in
theorem antiSp_exists_mulVec_eq {u v : Fin 4 → F} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : antiSp F, (glMat (g : GL (Fin 4) F)).mulVec u = v := by
  obtain ⟨g, hg, hgu⟩ := (CFSG.ClassicalGroups.Alternating.alternating_transvection_vector_transitivity
    (minorForm_isAlt (K := F)) minorForm_nondegenerate).2 u v hu hv
  have hmem : (GeneralLinearGroup.toLin (n := Fin 4) (R := F)).symm g ∈ antiSp F := by
    rw [antiSp_eq_closure]
    have := Subgroup.mem_map_of_mem
      (GeneralLinearGroup.toLin (n := Fin 4) (R := F)).symm.toMonoidHom hg
    rw [MonoidHom.map_closure] at this
    have hset : {g' : GL (Fin 4) F | ∃ (v : Fin 4 → F) (t : F), g' =
        GeneralLinearGroup.toLin.symm (CFSG.ClassicalGroups.Alternating.symplecticTransvection
          (minorForm F) minorForm_isAlt v t)} =
        ⇑(GeneralLinearGroup.toLin (n := Fin 4) (R := F)).symm.toMonoidHom ''
          {g | ∃ (a : Fin 4 → F) (c : F), g =
            CFSG.ClassicalGroups.Alternating.symplecticTransvection (minorForm F)
              minorForm_isAlt a c} := by
      ext y
      constructor
      · rintro ⟨a, c, rfl⟩
        exact ⟨_, ⟨a, c, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, c, rfl⟩, rfl⟩
        exact ⟨a, c, rfl⟩
    rw [hset]
    exact this
  refine ⟨⟨_, hmem⟩, ?_⟩
  have h1 : (GeneralLinearGroup.toLin (n := Fin 4) (R := F))
      ((GeneralLinearGroup.toLin (n := Fin 4) (R := F)).symm g) = g := MulEquiv.apply_symm_apply _ _
  have h2 := congrArg (fun x : LinearMap.GeneralLinearGroup F (Fin 4 → F) =>
    (x : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) u) h1
  simp only [GeneralLinearGroup.coe_toLin, mulVecLin_apply] at h2
  rw [← hgu]
  exact h2

omit [CharP F 2] [Fintype F] in
theorem glMat_conj_vecMulVec (g : antiSp F) (e : Fin 4 → F) :
    glMat (g : GL (Fin 4) F) * vecMulVec e (minorJ F *ᵥ e) *
        glMat ((g⁻¹ : antiSp F) : GL (Fin 4) F) =
      vecMulVec (glMat (g : GL (Fin 4) F) *ᵥ e) (minorJ F *ᵥ (glMat (g : GL (Fin 4) F) *ᵥ e)) := by
  have hGG : glMat (g : GL (Fin 4) F) * glMat ((g⁻¹ : antiSp F) : GL (Fin 4) F) = 1 :=
    (g : GL (Fin 4) F).mul_inv
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  rw [← Matrix.mulVec_transpose, glMat_inv_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have : minorJ F * glMat (g : GL (Fin 4) F) * minorJ F * minorJ F =
      minorJ F * glMat (g : GL (Fin 4) F) := by
    rw [Matrix.mul_assoc _ (minorJ F) (minorJ F), minorJ_mul_self, Matrix.mul_one]
  rw [this]

omit [Fintype F] in
theorem glMat_invX : glMat ((invX F : antiSp F) : GL (Fin 4) F) =
    1 + vecMulVec (Pi.single 0 1 : Fin 4 → F) (minorJ F *ᵥ (Pi.single 0 1 : Fin 4 → F)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invX, glMat_uElt, uMat, vecMulVec_apply, minorJ_apply]

@[expose] noncomputable def rk0 (z : antiSp F) : ℕ := (glMat (z : GL (Fin 4) F) - 1).rank

@[expose] noncomputable def rk1 (z : antiSp F) : ℕ := (glMat (minorHom F z : GL (Fin 4) F) - 1).rank

theorem exists_conj_invX {z : antiSp F} (h1 : rk0 z = 1) : ∃ g : antiSp F, g * invX F * g⁻¹ = z := by
  obtain ⟨u, ℓ, hu, hN⟩ := rank_one_vecMulVec _ h1
  have hz1 : glMat (z : GL (Fin 4) F) = 1 + vecMulVec u ℓ := by
    rw [← hN]
    abel
  have hℓ : ℓ ≠ 0 := by
    rintro rfl
    rw [vecMulVec_zero] at hN
    have : (glMat (z : GL (Fin 4) F) - 1).rank = 0 := by rw [hN, Matrix.rank_zero]
    exact zero_ne_one (this.symm.trans h1)
  have hsymp : (1 + vecMulVec u ℓ)ᵀ * minorJ F * (1 + vecMulVec u ℓ) = minorJ F := by
    rw [← hz1]
    exact mem_antiSp.mp z.2
  obtain ⟨t, ht0, hℓt⟩ := transvection_form u ℓ hu hℓ hsymp
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) t
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact ht0 (by rw [hs]; ring)
  have ha : s • u ≠ 0 := smul_ne_zero hs0 hu
  have hza : glMat (z : GL (Fin 4) F) =
      1 + vecMulVec (s • u) (minorJ F *ᵥ (s • u)) := by
    rw [hz1]
    congr 1
    ext i j
    have hJ : (minorJ F *ᵥ (s • u)) j = s * u j.rev := by
      fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, minorJ_apply]
    rw [vecMulVec_apply, vecMulVec_apply, hJ, hℓt j, hs]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have he0 : (Pi.single 0 1 : Fin 4 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨g, hg⟩ := antiSp_exists_mulVec_eq he0 ha
  refine ⟨g, Subtype.ext (Units.ext ?_)⟩
  have hGG : glMat (g : GL (Fin 4) F) * glMat ((g⁻¹ : antiSp F) : GL (Fin 4) F) = 1 :=
    (g : GL (Fin 4) F).mul_inv
  show glMat (g : GL (Fin 4) F) * glMat ((invX F : antiSp F) : GL (Fin 4) F) *
    glMat ((g⁻¹ : antiSp F) : GL (Fin 4) F) = glMat (z : GL (Fin 4) F)
  rw [glMat_invX, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hGG, glMat_conj_vecMulVec, hg, hza]

omit [Fintype F] in
theorem glMat_invX_sub_one : glMat ((invX F : antiSp F) : GL (Fin 4) F) - 1 = mE03 F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [invX, glMat_uElt, uMat, mE03, Matrix.sub_apply]

omit [Fintype F] in
theorem glMat_invY_sub_one : glMat ((invY F : antiSp F) : GL (Fin 4) F) - 1 = mE0213 F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [invY, glMat_uElt, uMat, mE0213, Matrix.sub_apply]

omit [Fintype F] in
theorem rk0_invX : rk0 (invX F) = 1 := by
  rw [rk0, glMat_invX_sub_one, rank_mE03]

omit [Fintype F] in
theorem rk1_invX : rk1 (invX F) = 2 := by
  rw [rk1, minorHom_invX, glMat_invY_sub_one, rank_mE0213]

omit [Fintype F] in
theorem rk_conj (g z : antiSp F) : rk0 (g * z * g⁻¹) = rk0 z ∧ rk1 (g * z * g⁻¹) = rk1 z := by
  have key : ∀ (a b : antiSp F),
      (glMat ((a * b * a⁻¹ : antiSp F) : GL (Fin 4) F) - 1).rank =
        (glMat (b : GL (Fin 4) F) - 1).rank := by
    intro a b
    have h1 : glMat ((a * b * a⁻¹ : antiSp F) : GL (Fin 4) F) - 1 =
        glMat (a : GL (Fin 4) F) * (glMat (b : GL (Fin 4) F) - 1) *
          glMat ((a⁻¹ : antiSp F) : GL (Fin 4) F) := by
      have hGG : glMat (a : GL (Fin 4) F) * glMat ((a⁻¹ : antiSp F) : GL (Fin 4) F) = 1 :=
        (a : GL (Fin 4) F).mul_inv
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hGG]
      rfl
    rw [h1]
    exact rank_conj_eq _ _ _ (a : GL (Fin 4) F).inv_mul
  refine ⟨key g z, ?_⟩
  rw [rk1, rk1, map_mul, map_mul, map_inv]
  exact key (minorHom F g) (minorHom F z)

theorem rk_bounds {z : antiSp F} (hz : z * z = 1) (hz1 : z ≠ 1) :
    1 ≤ rk0 z ∧ rk0 z ≤ 2 ∧ 1 ≤ rk1 z ∧ rk1 z ≤ 2 := by
  have hmul : ∀ w : antiSp F, w * w = 1 →
      glMat (w : GL (Fin 4) F) * glMat (w : GL (Fin 4) F) = 1 := fun w hw => by
    have := congrArg (fun a : antiSp F => glMat (a : GL (Fin 4) F)) hw
    simpa using this
  have hne : ∀ w : antiSp F, w ≠ 1 → glMat (w : GL (Fin 4) F) - 1 ≠ 0 := fun w hw h => by
    apply hw
    have h1 : glMat (w : GL (Fin 4) F) = 1 := sub_eq_zero.mp h
    exact Subtype.ext (Units.ext h1)
  have hm : minorHom F z * minorHom F z = 1 := by rw [← map_mul, hz, map_one]
  have hm1 : minorHom F z ≠ 1 := fun h =>
    hz1 ((minorHom_bijective (K := F)).1 (h.trans (map_one _).symm))
  refine ⟨one_le_rank_of_ne_zero _ (hne z hz1), ?_, one_le_rank_of_ne_zero _ (hne _ hm1), ?_⟩
  · have := two_mul_rank_le (k := F) (κ := Fin 4) _ (hmul z hz)
    simp only [Fintype.card_fin] at this
    unfold rk0
    omega
  · have := two_mul_rank_le (k := F) (κ := Fin 4) _ (hmul _ hm)
    simp only [Fintype.card_fin] at this
    unfold rk1
    omega

theorem involution_rank_pair {z : antiSp F} (hz : z * z = 1) (hz1 : z ≠ 1) :
    (rk0 z = 1 ∧ rk1 z = 2) ∨ (rk0 z = 2 ∧ rk1 z = 1) ∨ (rk0 z = 2 ∧ rk1 z = 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := rk_bounds hz hz1
  by_cases h0 : rk0 z = 1
  · obtain ⟨g, hg⟩ := exists_conj_invX h0
    have := (rk_conj g (invX F)).2
    rw [hg, rk1_invX] at this
    exact Or.inl ⟨h0, this⟩
  · have : rk0 z = 2 := by omega
    rcases (by omega : rk1 z = 1 ∨ rk1 z = 2) with h | h
    · exact Or.inr (Or.inl ⟨this, h⟩)
    · exact Or.inr (Or.inr ⟨this, h⟩)

omit [Fintype F] in
theorem minorMap_uMat_z : minorMap (uMat (0 : F) 1 1 0) = uMat 0 1 1 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three, uMat,
      CharTwo.sub_eq_add]

@[expose] noncomputable def witZ (F : Type) [Field F] [CharP F 2] : antiSp F := uElt 0 1 1 0

omit [Fintype F] in
theorem witZ_mem_radA1 : witZ F ∈ radA1 F := ⟨1, 1, 0, rfl⟩

omit [Fintype F] in
theorem witZ_mem_radA2 : witZ F ∈ radA2 F := ⟨0, 1, 1, rfl⟩

omit [Fintype F] in
theorem minorHom_witZ : minorHom F (witZ F) = witZ F :=
  Subtype.ext (Units.ext (by
    show minorMap (uMat (0 : F) 1 1 0) = uMat 0 1 1 0
    exact minorMap_uMat_z))

omit [Fintype F] in
theorem rank_witZ_sub_one : (glMat ((witZ F : antiSp F) : GL (Fin 4) F) - 1).rank = 2 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let W : Matrix (Fin 4) (Fin 4) F := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]
  have hWW : W * W = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [W, Matrix.mul_apply, Fin.sum_univ_four]
    all_goals linear_combination h2
  have h : glMat ((witZ F : antiSp F) : GL (Fin 4) F) - 1 = mE0213 F * W := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [witZ, glMat_uElt, uMat, mE0213, W, Matrix.mul_apply, Fin.sum_univ_four,
        Matrix.sub_apply]
  rw [h, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hWW),
    rank_mE0213]

omit [Fintype F] in
theorem rk_witZ : rk0 (witZ F) = 2 ∧ rk1 (witZ F) = 2 := by
  refine ⟨rank_witZ_sub_one, ?_⟩
  rw [rk1, minorHom_witZ]
  exact rank_witZ_sub_one

omit [Fintype F] in
theorem witZ_mul_self : witZ F * witZ F = 1 := by
  have h := uElt_mul_self (K := F) 0 1 1 0
  rw [witZ]
  simpa [uElt_zero_eq_one] using h

theorem elementary_le_conj_antiUnipotent (E : Subgroup (antiSp F)) (hE : ∀ x ∈ E, x * x = 1) :
    ∃ g : antiSp F, ∀ x ∈ E, g⁻¹ * x * g ∈ antiUnipotent F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hUp, hUi⟩ := (card_and_isSylowTwoOf_antiUnipotent (K := F)).2
  rw [show ((antiUnipotent F).subgroupOf ⊤).index = (antiUnipotent F).index from
    Subgroup.relIndex_top_right _] at hUi
  let Pu : Sylow 2 (antiSp F) := hUp.toSylow hUi
  have hEp : IsPGroup 2 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hE x x.2⟩
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (antiSp F) Pu P
  refine ⟨g, fun x hx => ?_⟩
  have hxP : x ∈ (MulAut.conj g) • (Pu : Subgroup (antiSp F)) := by
    have h0 : x ∈ (P : Subgroup (antiSp F)) := hEP hx
    rw [← hg, Sylow.coe_subgroup_smul] at h0
    exact h0
  have h1 := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := MulAut.conj g)).mp hxP
  have hmem : g⁻¹ * x * g ∈ (Pu : Subgroup (antiSp F)) := by
    simpa [MulAut.inv_def, MulAut.conj_symm_apply] using h1
  exact hmem

theorem elementary_abelian_card_le {f : ℕ} (hF : Nat.card F = 2 ^ f) (E : Subgroup (antiSp F))
    (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ (3 * f) ∧
      (Nat.card E = 2 ^ (3 * f) → ∃ z ∈ E, rk0 z = 2 ∧ rk1 z = 2) := by
  obtain ⟨g, hg⟩ := elementary_le_conj_antiUnipotent E hE
  let E' : Subgroup (antiSp F) := E.map (MulAut.conj g⁻¹).toMonoidHom
  have hE'U : E' ≤ antiUnipotent F := by
    rintro _ ⟨x, hx, rfl⟩
    have := hg x hx
    show g⁻¹ * x * g⁻¹⁻¹ ∈ antiUnipotent F
    simpa using this
  have hE'sq : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * x * g⁻¹⁻¹) = 1
    calc g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * x * g⁻¹⁻¹) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hE x hx]; group
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  obtain ⟨-, h1, h2, -⟩ := card_radicals (K := F)
  have hq3 : Nat.card F ^ 3 = 2 ^ (3 * f) := by rw [hF, ← pow_mul, mul_comm]
  rcases elementary_le_radA1_or_radA2 hE'U hE'sq with hle | hle
  · refine ⟨?_, fun hEeq => ?_⟩
    · rw [← hcard, ← hq3, ← h1]
      exact Subgroup.card_le_of_le hle
    · have hEq : E' = radA1 F := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hEeq, ← hq3, h1])
      have hz : witZ F ∈ E' := hEq ▸ witZ_mem_radA1
      obtain ⟨y, hy, hyz⟩ := hz
      refine ⟨y, hy, ?_⟩
      have hy' : y = g * witZ F * g⁻¹ := by
        have hyz' : g⁻¹ * y * g⁻¹⁻¹ = witZ F := hyz
        rw [← hyz']; group
      rw [hy', (rk_conj g (witZ F)).1, (rk_conj g (witZ F)).2]
      exact rk_witZ
  · refine ⟨?_, fun hEeq => ?_⟩
    · rw [← hcard, ← hq3, ← h2]
      exact Subgroup.card_le_of_le hle
    · have hEq : E' = radA2 F := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hEeq, ← hq3, h2])
      have hz : witZ F ∈ E' := hEq ▸ witZ_mem_radA2
      obtain ⟨y, hy, hyz⟩ := hz
      refine ⟨y, hy, ?_⟩
      have hy' : y = g * witZ F * g⁻¹ := by
        have hyz' : g⁻¹ * y * g⁻¹⁻¹ = witZ F := hyz
        rw [← hyz']; group
      rw [hy', (rk_conj g (witZ F)).1, (rk_conj g (witZ F)).2]
      exact rk_witZ

theorem involution_rank_pairs_and_maximal_elementary_witness {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    (∀ z : antiSp F, z * z = 1 → z ≠ 1 →
        (rk0 z = 1 ∧ rk1 z = 2) ∨ (rk0 z = 2 ∧ rk1 z = 1) ∨ (rk0 z = 2 ∧ rk1 z = 2)) ∧
      (∀ g z : antiSp F, rk0 (g * z * g⁻¹) = rk0 z ∧ rk1 (g * z * g⁻¹) = rk1 z) ∧
      ∀ E : Subgroup (antiSp F), (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 2 ^ (3 * f) ∧
          (Nat.card E = 2 ^ (3 * f) → ∃ z ∈ E, rk0 z = 2 ∧ rk1 z = 2) :=
  ⟨fun _ hz hz1 => involution_rank_pair hz hz1, rk_conj,
    fun E hE => elementary_abelian_card_le hF E hE⟩

end Conj

end CFSG.QuasithinUnique.Setup.X7b
