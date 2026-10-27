module

public import CFSG.CGT.PushingUpLit.CGT6X.K7aNumber
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearGraphFieldDescent
public import CFSG.RankThree.PartOne.KC.LinearSubfieldFixedPoints
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.K7a

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups CFSG.SL2MinimalFaithful CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCLinearSubfield

section Prime

variable {K : Type} [Field K] [Finite K]

theorem exists_prime_elt {G : Type*} [Group G] [Finite G] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f)
    (Y : Subgroup G) (hY : Nat.card Y = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card K + 1 ∧ ∃ y ∈ Y, orderOf y = p := by
  have hq : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqeven : 2 ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self 2 (by omega)
  have hne : Nat.card K + 1 ≠ 1 := by omega
  set p := (Nat.card K + 1).minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hne
  have hpq : p ∣ Nat.card K + 1 := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpq
    omega
  refine ⟨p, hp, hp2, hpq, ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Y := by
    rw [hY, card_specialLinearGroup_fin_two]
    refine Dvd.dvd.mul_left (hpq.trans ?_) _
    have : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      have : (m + 1) ^ 2 = (m + 1 + 1) * m + 1 := by ring
      omega
    rw [this]
    exact dvd_mul_right _ _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨y.1, y.2, by rw [← hy]; exact (Subgroup.orderOf_coe y)⟩

end Prime

section Counts

theorem card_proj_dvd_prod (k : Type) [Field k] [Finite k] :
    Nat.card (projectiveSL 3 k) ∣
      (Nat.card k ^ 3 - 1) * (Nat.card k ^ 3 - Nat.card k) * (Nat.card k ^ 3 - Nat.card k ^ 2) := by
  have : Fintype k := Fintype.ofFinite k
  have h1 : Nat.card (projectiveSL 3 k) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) k) :=
    Subgroup.card_quotient_dvd_card (scalars 3 k)
  have hinj : Function.Injective
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 3) k →* GL (Fin 3) k) := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun u : GL (Fin 3) k => (u : Matrix (Fin 3) (Fin 3) k)) hab
  have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) k) ∣ Nat.card (GL (Fin 3) k) :=
    Subgroup.card_dvd_of_injective _ hinj
  have h3 := Matrix.card_GL_field (𝔽 := k) 3
  rw [Fin.prod_univ_three, ← Nat.card_eq_fintype_card] at h3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at h3
  rw [h3] at h2
  exact h1.trans h2

end Counts

section Field

variable {K : Type} [Field K] [Finite K]

theorem no_SL2_field {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (A : GL (Fin 3) K)
    (σ : K ≃+* K) (hσ : σ ≠ 1) (hα : (conjAut 3 K A * fieldAut 3 K σ) ^ 2 = 1)
    (Y : Subgroup (projectiveSL 3 K))
    (hY : Nat.card Y = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K))
    (hYt : ∀ y ∈ Y, (conjAut 3 K A * fieldAut 3 K σ) y = y) : False := by
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨hfe, hσpow, H, hH⟩ :=
    even_linear_field_involution_descent hf hK (by norm_num) A σ hσ hα
  obtain ⟨p, hp, hp2, hpq, y, hyY, hy⟩ := exists_prime_elt hf hK Y hY
  obtain ⟨e, he⟩ := hfe
  have hfe2 : f = 2 * e := by omega
  have he1 : 1 ≤ e := by omega
  have hU : UnitaryFieldData 2 e K := ⟨Nat.prime_two, he1, by rw [hK, hfe2]⟩
  have hσbar : ∀ x, σ x = hU.bar x := fun x => by
    rw [hσpow, UnitaryFieldData.bar_apply]
    congr 2
    omega
  have hσ2 : σ ^ 2 = 1 := by
    refine RingEquiv.ext fun x => ?_
    rw [pow_two]
    show σ (σ x) = x
    rw [hσbar, hσbar, hU.bar_bar]
  have hk : ∀ x, x ∈ hU.fixedField ↔ σ x = x := fun x => by rw [hσbar]; exact Iff.rfl
  have hfix := fixed_points_eq_range hk (by norm_num : 0 < 3)
    (root_descent_of_coprime hk hσ2 (by norm_num : Nat.Coprime 3 2))
  set cH : MulAut (projectiveSL 3 K) := conjAut 3 K H with hcH
  have hy'fix : fieldAut 3 K σ ((cH⁻¹ : MulAut (projectiveSL 3 K)) y) =
      (cH⁻¹ : MulAut (projectiveSL 3 K)) y := by
    have h1 := hYt y hyY
    rw [hH] at h1
    have h2 : cH (fieldAut 3 K σ ((cH⁻¹ : MulAut (projectiveSL 3 K)) y)) = y := by
      simpa [hcH, MulAut.mul_apply] using h1
    have h3 := congrArg (cH⁻¹ : MulAut (projectiveSL 3 K)) h2
    simpa using h3
  have hmem : (cH⁻¹ : MulAut (projectiveSL 3 K)) y ∈
      ((linearSubfieldInclusion 3 hU.fixedField).range : Set (projectiveSL 3 K)) := by
    rw [← hfix]
    exact hy'fix
  obtain ⟨z, hz⟩ := hmem
  have hord : orderOf ((cH⁻¹ : MulAut (projectiveSL 3 K)) y) = p := by
    rw [MulEquiv.orderOf_eq]
    exact hy
  have hpz : p ∣ orderOf z := by
    rw [← hord, ← hz]
    exact orderOf_map_dvd _ z
  have hpcard : p ∣ Nat.card (projectiveSL 3 hU.fixedField) := hpz.trans (orderOf_dvd_natCard z)
  have hr : Nat.card hU.fixedField = 2 ^ e := hU.card_fixedField
  have hKr : Nat.card K = (2 ^ e) ^ 2 := by rw [hK, hfe2, ← pow_mul, mul_comm]
  have hpr : p ∣ (2 ^ e) ^ 2 + 1 := by rw [← hKr]; exact hpq
  have h2e : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he1
  exact not_dvd_GL3 hp hp2 h2e hpr (hpcard.trans (by rw [← hr]; exact card_proj_dvd_prod _))

end Field

section GraphField

variable {K : Type} [Field K] {e : ℕ} (h : UnitaryFieldData 2 e K)

@[expose] def gramToSL :
    gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →*
      Matrix.SpecialLinearGroup (Fin 3) K where
  toFun g := ⟨(g.1 : Matrix (Fin 3) (Fin 3) K), g.2.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[expose] noncomputable def toP :
    gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →* projectiveSL 3 K :=
  (proj 3 K).comp (gramToSL h)

theorem scalar_eq_smul_one' (a : K) :
    scalar (Fin 3) a = a • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [Matrix.smul_one_eq_diagonal]
  rfl

theorem graphField_fixed (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) (x : projectiveSL 3 K)
    (hx : (fieldAut 3 K σ * dualAut 3 K) x = x) :
    ∃ g : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), toP h g = x := by
  have hσσ : ∀ a, σ (σ a) = a := fun a => by rw [hσ, hσ, h.bar_bar]
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  rw [MulAut.mul_apply, dualAut_proj, fieldAut_proj] at hx
  have hzN := QuotientGroup.eq.1 hx
  obtain ⟨c, hc3, hc⟩ := id hzN
  set a : Matrix.SpecialLinearGroup (Fin 3) K :=
    Matrix.SpecialLinearGroup.map σ.toRingHom ((g⁻¹).transpose) with ha
  have hgm : (g : Matrix (Fin 3) (Fin 3) K) =
      (a : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) (c : K) := by
    have hgz : g = a * (a⁻¹ * g) := (mul_inv_cancel_left _ _).symm
    conv_lhs => rw [hgz]
    rw [Matrix.SpecialLinearGroup.coe_mul, hc]
  set M : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K) with hM
  set N : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) with hN
  have hNM : N * M = 1 := by
    rw [hN, hM, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hamat : (a : Matrix (Fin 3) (Fin 3) K) = (N.map σ)ᵀ := by
    rw [ha, Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_transpose,
      RingHom.mapMatrix_apply, transpose_map]
    rfl
  have hMt : Mᵀ = (c : K) • N.map σ := by
    have h1 := congrArg Matrix.transpose hgm
    rw [transpose_mul, hamat, transpose_transpose] at h1
    rw [h1, scalar_eq_smul_one', transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul]
  have E1 : Mᵀ * M.map σ = (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [hMt, Matrix.smul_mul, ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have E2 : (M.map σ)ᵀ * M = (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have h1 := congrArg Matrix.transpose E1
    rw [transpose_mul, transpose_transpose, transpose_smul, transpose_one] at h1
    exact h1
  have E3 : (M.map σ)ᵀ * M = σ (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have h1 := congrArg (fun X : Matrix (Fin 3) (Fin 3) K => X.map σ) E1
    simp only [Matrix.map_mul, transpose_map] at h1
    have h2 : (M.map σ).map σ = M := Matrix.ext fun i j => hσσ _
    rw [h2] at h1
    rw [h1]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hcσ : σ (c : K) = c := by
    have h1 : (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) = σ (c : K) • 1 := E2.symm.trans E3
    have h2 := congrFun (congrFun h1 0) 0
    simpa using h2.symm
  have hc3' : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  set gs : Matrix.SpecialLinearGroup (Fin 3) K := scalarElement c hc3 * g with hgs
  have hgsm : (gs : Matrix (Fin 3) (Fin 3) K) = (c : K) • M := by
    rw [hgs, Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, scalar_eq_smul_one',
      Matrix.smul_mul, Matrix.one_mul]
  have hgram : ((gs : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (gs : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [hgsm]
    have hmap : ((c : K) • M).map h.bar = (c : K) • M.map σ := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, ← hσ, hcσ]
    rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, E2, smul_smul]
    have h3 : (c : K) * (c : K) * (c : K) = 1 := by rw [← pow_three', hc3']
    rw [h3, one_smul]
  have hmem : (Matrix.SpecialLinearGroup.toGL gs : GL (Fin 3) K) ∈
      gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [mem_gramSU]
    refine ⟨?_, gs.2⟩
    show ((gs : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (gs : Matrix (Fin 3) (Fin 3) K) =
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [Units.val_one, Matrix.mul_one]
    exact hgram
  refine ⟨⟨_, hmem⟩, ?_⟩
  show proj 3 K gs = proj 3 K g
  have hz : proj 3 K (scalarElement c hc3) = 1 :=
    (MonoidHom.mem_ker).1 (by rw [ker_proj]; exact scalarElement_mem_scalars c hc3)
  rw [hgs, map_mul, hz, one_mul]

theorem card_gramSU_one :
    Nat.card (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      (2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) := by
  have hfin : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  have h1 : ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := Units.val_one
  have hB : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).IsSymm :=
    gramForm_isSymm h (by simp)
  have hBl : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  have hSU := (unitary_full_group_order h hB hBl (Module.finrank_fin_fun K) (by norm_num)).2.1
  rw [h1, card_gramSU]
  have hIcc : Finset.Icc 2 3 = {2, 3} := by decide
  rw [hIcc, Finset.prod_pair (by norm_num)] at hSU
  have hr1 : 1 ≤ (2 ^ e) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have : ((Nat.card (sesqSpecialUnitaryGroup (gramForm h (1 : Matrix (Fin 3) (Fin 3) K))) : ℕ) :
      ℤ) = (((2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) : ℕ) : ℤ) := by
    rw [hSU]
    push_cast [Nat.cast_sub hr1]
    norm_num
    ring
  exact_mod_cast this

theorem no_SL2_graphField {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (A : GL (Fin 3) K)
    (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hα : (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) ^ 2 = 1)
    (Y : Subgroup (projectiveSL 3 K))
    (hY : Nat.card Y = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K))
    (hYt : ∀ y ∈ Y, (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) y = y) : False := by
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨hfe, hσpow, H, hH⟩ :=
    linear_graph_field_involution_descent Nat.prime_two hf hK (by norm_num) A σ hσ hα
  obtain ⟨p, hp, hp2, hpq, y, hyY, hy⟩ := exists_prime_elt hf hK Y hY
  obtain ⟨e, he⟩ := hfe
  have hfe2 : f = 2 * e := by omega
  have he1 : 1 ≤ e := by omega
  have hU : UnitaryFieldData 2 e K := ⟨Nat.prime_two, he1, by rw [hK, hfe2]⟩
  have hσbar : ∀ x, σ x = hU.bar x := fun x => by
    rw [hσpow, UnitaryFieldData.bar_apply]
    congr 2
    omega
  set cH : MulAut (projectiveSL 3 K) := conjAut 3 K H with hcH
  have hy'fix : (fieldAut 3 K σ * dualAut 3 K) ((cH⁻¹ : MulAut (projectiveSL 3 K)) y) =
      (cH⁻¹ : MulAut (projectiveSL 3 K)) y := by
    have h1 := hYt y hyY
    rw [hH] at h1
    have h2 : cH ((fieldAut 3 K σ * dualAut 3 K) ((cH⁻¹ : MulAut (projectiveSL 3 K)) y)) = y := by
      simpa [hcH, MulAut.mul_apply] using h1
    have h3 := congrArg (cH⁻¹ : MulAut (projectiveSL 3 K)) h2
    simpa using h3
  obtain ⟨g, hg⟩ := graphField_fixed hU σ hσbar _ hy'fix
  have hord : orderOf ((cH⁻¹ : MulAut (projectiveSL 3 K)) y) = p := by
    rw [MulEquiv.orderOf_eq]
    exact hy
  have hpg : p ∣ orderOf g := by
    rw [← hord, ← hg]
    exact orderOf_map_dvd _ g
  have hpcard : p ∣ Nat.card (gramSU hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    hpg.trans (orderOf_dvd_natCard g)
  rw [card_gramSU_one hU] at hpcard
  have hKr : Nat.card K = (2 ^ e) ^ 2 := by rw [hK, hfe2, ← pow_mul, mul_comm]
  have hpr : p ∣ (2 ^ e) ^ 2 + 1 := by rw [← hKr]; exact hpq
  have h2e : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he1
  exact not_dvd_SU3 hp hp2 h2e hpr hpcard

end GraphField

end CFSG.CGT.PushingUpLit.CGT6X.K7a
