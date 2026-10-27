module

public import CFSG.LieType.SeitzGeneration.UnitaryPlane
public import CFSG.LieType.SeitzGeneration.UnitaryToralNine
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.Open

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem conjHom_eq_one_iff (h : UnitaryFieldData ℓ f K) (A : primeFormUnitary h (idGram K 3)) :
    primeFormConjHom h (idGram K 3) A = 1 ↔ ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (A : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have := primeFormPsi_eq_one_iff h hC (le_refl 3) ⟨A, RingEquiv.refl K⟩
  rw [primeFormPsi_apply] at this
  have h1 : primeFormFieldHom h hC (RingEquiv.refl K) = 1 := map_one _
  rw [h1, mul_one] at this
  simpa using this

noncomputable def toP (h : UnitaryFieldData ℓ f K) :
    unitarySU ℓ f K 3 →* primeFormP h (idGram K 3) :=
  (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 3)) 3)).comp
    (Subgroup.inclusion (le_of_eq (unitarySU_eq_gramSU h 3)))

theorem toP_surjective (h : UnitaryFieldData ℓ f K) : Function.Surjective (toP h) := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨⟨g.1, (unitarySU_eq_gramSU h 3).symm ▸ g.2⟩, rfl⟩

theorem mul_scalarGL_mul_comm {n : ℕ} (c : Kˣ) (a b : GL (Fin n) K) :
    a * (Matrix.GeneralLinearGroup.scalar (Fin n) c * b) =
      Matrix.GeneralLinearGroup.scalar (Fin n) c * (a * b) := by
  rw [← mul_assoc, ← (commute_scalarGL c a).eq, mul_assoc]

theorem conj_scalar_aux {a b : GL (Fin 3) K} {u : Kˣ}
    (h : b * a = Matrix.GeneralLinearGroup.scalar (Fin 3) u * (a * b)) :
    (a * b * a⁻¹)⁻¹ * b = Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
  have h2 : a⁻¹ * b = Matrix.GeneralLinearGroup.scalar (Fin 3) u * (b * a⁻¹) := by
    calc a⁻¹ * b = a⁻¹ * (b * a) * a⁻¹ := by group
      _ = a⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) u * (a * b)) * a⁻¹ := by rw [h]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) u * (b * a⁻¹) := by
        rw [mul_scalarGL_mul_comm]; group
  calc (a * b * a⁻¹)⁻¹ * b = a * b⁻¹ * (a⁻¹ * b) := by group
    _ = a * b⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) u * (b * a⁻¹)) := by rw [h2]
    _ = Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
      rw [mul_assoc, mul_scalarGL_mul_comm, mul_scalarGL_mul_comm]; group

theorem conjHom_toP_of_mem_FixU (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    {A : primeFormUnitary h (idGram K 3)} {g : unitarySU ℓ f K 3}
    (hg : g ∈ FixU ℓ f K (A : GL (Fin 3) K)) :
    primeFormConjHom h (idGram K 3) A (toP h g) = toP h g := by
  obtain ⟨c, hc⟩ := hg
  have hdA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K)).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  have hc3 : c ^ 3 = 1 := by
    have h1 := congrArg Matrix.det hc
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, ((mem_unitarySU_iff h).1 g.2).1,
      Fintype.card_fin] at h1
    have h2 : (c ^ 3 - 1) * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 0 := by
      linear_combination -h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hdA)
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at hc3
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, (u : K) = c := ⟨Units.mk0 c hc0, rfl⟩
  have hGL : (g : GL (Fin 3) K) * A = Matrix.GeneralLinearGroup.scalar (Fin 3) u *
      ((A : GL (Fin 3) K) * g) := by
    apply Units.ext
    rw [Units.val_mul, coe_scalarGL_mul, hu, Units.val_mul]
    exact hc
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, hc3, Units.val_one])
  have hnorm : h.norm (u : K) = 1 := by
    obtain ⟨m, hm⟩ := hq3
    rw [UnitaryFieldData.norm, h.bar_apply, ← pow_succ', hm, pow_mul, ← Units.val_pow_eq_pow_val,
      hu3, Units.val_one, one_pow]
  have hkey := conj_scalar_aux hGL
  have hgram : (g : GL (Fin 3) K) ∈ gramSU h (idGram K 3) :=
    (le_of_eq (unitarySU_eq_gramSU h 3)) g.2
  show primeFormConjHom h (idGram K 3) A ((⟨(g : GL (Fin 3) K), hgram⟩ : gramSU h (idGram K 3)) :
      primeFormP h (idGram K 3)) = ((⟨(g : GL (Fin 3) K), hgram⟩ : gramSU h (idGram K 3)) :
      primeFormP h (idGram K 3))
  rw [primeFormConjHom_mk, QuotientGroup.eq]
  exact ⟨u, hnorm, hu3, hkey⟩

theorem bar_mul_eq_one_of_scalar (h : UnitaryFieldData ℓ f K) {g : GL (Fin 3) K}
    (hg : g ∈ primeFormUnitary h (idGram K 3)) {c : Kˣ}
    (hc : g = Matrix.GeneralLinearGroup.scalar (Fin 3) c) : h.bar (c : K) * c = 1 := by
  have h1 := mem_primeFormUnitary.1 hg
  simp only [idGram, Units.val_one] at h1
  rw [hc, coe_scalarGL, barTranspose_smul_mul_smul] at h1
  have h2 := congrFun (congrFun h1 0) 0
  simpa using h2

theorem scalar_mem_primeFormUnitary (h : UnitaryFieldData ℓ f K) {c : Kˣ}
    (hc : h.bar (c : K) * c = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ primeFormUnitary h (idGram K 3) := by
  have := smul_mem_primeFormUnitary (n := 3) h (g := 1) (one_mem _) c.ne_zero hc
  simpa using this

theorem planeGen_of_unitaryDiagAut (hcoreI : UnitaryHeisCore) (hcoreO : UnitaryOuterHeisCore)
    (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2)
    {E : Subgroup (MulAut (primeFormP h (idGram K 3)))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) (hD : E ≤ primeFormD h (idGram K 3)) : PlaneGen E := by
  classical
  have hfin := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e₁, he₁, e₂, he₂, he₂1, he₁₂⟩ := exists_independent_pair Nat.prime_three E hE.2 hc
  have hcomm : e₂ * e₁ = e₁ * e₂ :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨e₂, he₂⟩ : E) ⟨e₁, he₁⟩)
  set κ := primeFormConjHom h (idGram K 3) with hκ
  obtain ⟨A₁, hA₁⟩ : ∃ A : primeFormUnitary h (idGram K 3), κ A = e₁ := hD he₁
  obtain ⟨A₂, hA₂⟩ : ∃ A : primeFormUnitary h (idGram K 3), κ A = e₂ := hD he₂
  set H : Subgroup (GL (Fin 3) K) :=
    (E.comap κ).map (primeFormUnitary h (idGram K 3)).subtype with hH
  have hHU : H ≤ primeFormUnitary h (idGram K 3) := by
    rintro _ ⟨B, -, rfl⟩; exact B.2
  have hmemH : ∀ B : primeFormUnitary h (idGram K 3), κ B ∈ E → (B : GL (Fin 3) K) ∈ H :=
    fun B hB => ⟨B, hB, rfl⟩
  have hHmem : ∀ g ∈ H, ∃ B : primeFormUnitary h (idGram K 3), (B : GL (Fin 3) K) = g ∧
      κ B ∈ E := by
    rintro _ ⟨B, hB, rfl⟩; exact ⟨B, rfl, hB⟩
  have hscal : ∀ c : Kˣ, h.bar (c : K) * c = 1 →
      Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H := fun c hc1 => by
    have hcm := scalar_mem_primeFormUnitary h hc1
    refine hmemH ⟨_, hcm⟩ ?_
    have : κ ⟨_, hcm⟩ = 1 :=
      (conjHom_eq_one_iff h _).2 ⟨c, by rw [UnitaryFieldData.norm, mul_comm]; exact hc1, rfl⟩
    rw [this]; exact E.one_mem
  obtain ⟨α, hα⟩ : ∃ α : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) α =
      (A₁ : GL (Fin 3) K) ^ 3 := by
    have h1 : κ (A₁ ^ 3) = 1 := by rw [map_pow, hA₁]; exact hE.2 _ he₁
    obtain ⟨c, -, hc'⟩ := (conjHom_eq_one_iff h _).1 h1
    exact ⟨c, by rw [← hc']; rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) β =
      (A₂ : GL (Fin 3) K) ^ 3 := by
    have h1 : κ (A₂ ^ 3) = 1 := by rw [map_pow, hA₂]; exact hE.2 _ he₂
    obtain ⟨c, -, hc'⟩ := (conjHom_eq_one_iff h _).1 h1
    exact ⟨c, by rw [← hc']; rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) ω =
      (A₂ : GL (Fin 3) K) * A₁ * ((A₁ : GL (Fin 3) K) * A₂)⁻¹ := by
    have h1 : κ (A₂ * A₁ * (A₁ * A₂)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, hA₁, hA₂, hcomm]; exact mul_inv_cancel _
    obtain ⟨c, -, hc'⟩ := (conjHom_eq_one_iff h _).1 h1
    exact ⟨c, by rw [← hc']; rfl⟩
  have hyx : (A₂ : GL (Fin 3) K) * A₁ = Matrix.GeneralLinearGroup.scalar (Fin 3) ω *
      ((A₁ : GL (Fin 3) K) * A₂) := by
    rw [hω, inv_mul_cancel_right]
  have hind : ∀ a b : ℕ, (∃ c : Kˣ, (A₁ : GL (Fin 3) K) ^ a * (A₂ : GL (Fin 3) K) ^ b =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c) → 3 ∣ a ∧ 3 ∣ b := by
    rintro a b ⟨c, hcab⟩
    have hmem : (A₁ : GL (Fin 3) K) ^ a * (A₂ : GL (Fin 3) K) ^ b ∈
        primeFormUnitary h (idGram K 3) := mul_mem (pow_mem A₁.2 a) (pow_mem A₂.2 b)
    have h1 : κ (A₁ ^ a * A₂ ^ b) = 1 := by
      refine (conjHom_eq_one_iff h _).2 ⟨c, ?_, ?_⟩
      · have := bar_mul_eq_one_of_scalar h hmem hcab
        rw [UnitaryFieldData.norm, mul_comm]; exact this
      · rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]; exact hcab
    rw [map_mul, map_pow, map_pow, hA₁, hA₂] at h1
    exact three_dvd_of_pow_mul_pow_eq_one (hE.2 _ he₁) (hE.2 _ he₂) he₂1 he₁₂ h1
  obtain ⟨x', hx', y', hy', n₁, n₂, n₃, n₄, hgen⟩ := exists_pair_closure_planeFixU hcoreI hcoreO h
    hq3 hq H hHU hscal (hmemH A₁ (by rw [hA₁]; exact he₁)) (hmemH A₂ (by rw [hA₂]; exact he₂))
    hyx hα.symm hβ.symm hind
  have hline : ∀ L ∈ H, NonScalarGL L → ∀ g ∈ FixU ℓ f K (L : Matrix (Fin 3) (Fin 3) K),
      toP h g ∈ {k | ∃ e ∈ E, e ≠ 1 ∧ e k = k} := by
    intro L hL hnon g hg
    obtain ⟨B, hB, hBE⟩ := hHmem L hL
    refine ⟨κ B, hBE, ?_, ?_⟩
    · intro h1
      obtain ⟨c, -, hc'⟩ := (conjHom_eq_one_iff h B).1 h1
      exact hnon c (hB ▸ hc')
    · exact conjHom_toP_of_mem_FixU h hq3 (A := B) (by rw [hB]; exact hg)
  unfold PlaneGen planeClosure
  rw [eq_top_iff]
  have hle : (Subgroup.closure (planeFixU ℓ f K x' y')).map (toP h) ≤
      Subgroup.closure {k : primeFormP h (idGram K 3) | ∃ e ∈ E, e ≠ 1 ∧ e k = k} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.subset_closure ?_
    rcases hg with ((hg | hg) | hg) | hg
    · exact hline x' hx' n₁ g hg
    · exact hline y' hy' n₂ g hg
    · exact hline (x' * y') (H.mul_mem hx' hy') n₃ g hg
    · exact hline (x' * y' ^ 2) (H.mul_mem hx' (H.pow_mem hy' 2)) n₄ g hg
  rw [hgen, Subgroup.map_top_of_surjective _ (toP_surjective h)] at hle
  exact hle

theorem inner_le_primeFormD (h : UnitaryFieldData ℓ f K) :
    CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP h (idGram K 3)) ≤
      primeFormD h (idGram K 3) := by
  intro α hα
  obtain ⟨s, rfl⟩ := (mem_inner_primeFormP h (idGram K 3) α).1 hα
  exact ⟨_, rfl⟩

theorem planeGen_of_unitaryDiagAut_equiv (hcoreI : UnitaryHeisCore)
    (hcoreO : UnitaryOuterHeisCore) (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    (hq : ℓ ^ f ≠ 2) {G : Type*} [Group G] (e : G ≃* primeFormP h (idGram K 3))
    {E : Subgroup (MulAut G)} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hD : E.map (MulAut.congr e).toMonoidHom ≤ primeFormD h (idGram K 3)) : PlaneGen E := by
  refine (planeGen_map_congr e E).1 ?_
  refine planeGen_of_unitaryDiagAut hcoreI hcoreO h hq3 hq ?_ ?_ hD
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE _
  · rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hc]

end CFSG.LieType.SeitzGeneration
