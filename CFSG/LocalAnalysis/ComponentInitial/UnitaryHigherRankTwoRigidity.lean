module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankTwoRestriction

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open Module Submodule
open scoped Pointwise commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {ε : ℕ}

theorem le_iff_of_fix {h : UnitaryFieldData p f K} {r : ℕ}
    {φ : Equiv.Perm (hypIsotropicLines h r ε)} {W : Submodule K (HypIndex r ε → K)}
    (hW : ∀ L : hypIsotropicLines h r ε, (L : Submodule K (HypIndex r ε → K)) ≤ W → φ L = L)
    (L : hypIsotropicLines h r ε) :
    (φ L : Submodule K (HypIndex r ε → K)) ≤ W ↔ (L : Submodule K (HypIndex r ε → K)) ≤ W := by
  constructor
  · intro hL
    rw [← φ.injective (hW (φ L) hL)]
    exact hL
  · intro hL
    rw [hW L hL]
    exact hL

theorem commute_leviPointGroup (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {φ : Equiv.Perm (hypIsotropicLines h 2 ε)} (hφ : φ ∈ lineNormalizer h 2 ε)
    (hX : ∀ L : hypIsotropicLines h 2 ε,
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε → φ L = L)
    (hY : ∀ L : hypIsotropicLines h 2 ε,
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε → φ L = L)
    {g : Equiv.Perm (hypIsotropicLines h 2 ε)} (hg : g ∈ leviPointGroup h 2 ε) :
    φ * g = g * φ := by
  obtain ⟨hD, -, hcen, -, -⟩ := unitary_rank_two_opposite_levi h hε
  have hconj : ∀ x ∈ xyPointStab h 2 ε, φ * x * φ⁻¹ ∈ xyPointStab h 2 ε := fun x hx =>
    conj_mem_xyPointStab hφ (le_iff_of_fix hX) (le_iff_of_fix hY) hx
  have hφinv : ∀ L : hypIsotropicLines h 2 ε,
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε → φ⁻¹ L = L := fun L hL => by
    rw [Equiv.Perm.inv_eq_iff_eq, hX L hL]
  have hχD : ∀ x ∈ xyPointStab h 2 ε, φ * x * φ⁻¹ * x⁻¹ ∈ xyPointStab h 2 ε := fun x hx =>
    mul_mem (hconj x hx) (inv_mem hx)
  have hχX : ∀ x ∈ xyPointStab h 2 ε, ∀ L : hypIsotropicLines h 2 ε,
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε → (φ * x * φ⁻¹ * x⁻¹) L = L := by
    intro x hx L hL
    have h1 : ((x⁻¹ L : hypIsotropicLines h 2 ε) : Submodule K (HypIndex 2 ε → K)) ≤
        hypX K 2 ε := (((mem_xyPointStab h).mp (inv_mem hx)).2.1 L).mpr hL
    simp only [Equiv.Perm.mul_apply]
    rw [hφinv _ h1, Equiv.Perm.coe_inv, Equiv.apply_symm_apply, hX L hL]
  have hcen' : ∀ x ∈ xyPointStab h 2 ε, ∀ y ∈ xyPointStab h 2 ε,
      φ * x * φ⁻¹ * x⁻¹ * y = y * (φ * x * φ⁻¹ * x⁻¹) := fun x hx y hy =>
    hcen _ (hχD x hx) (hχX x hx) y hy
  let χ : xyPointStab h 2 ε →* Equiv.Perm (hypIsotropicLines h 2 ε) :=
    { toFun := fun x => φ * x * φ⁻¹ * (x : Equiv.Perm (hypIsotropicLines h 2 ε))⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        have hc := hcen' y y.2 _ (inv_mem x.2)
        simp only [Subgroup.coe_mul]
        calc φ * (x * y : Equiv.Perm (hypIsotropicLines h 2 ε)) * φ⁻¹ *
              ((x * y : Equiv.Perm (hypIsotropicLines h 2 ε)))⁻¹ =
            φ * x * φ⁻¹ * ((φ * y * φ⁻¹ * (y : Equiv.Perm (hypIsotropicLines h 2 ε))⁻¹) *
              (x : Equiv.Perm (hypIsotropicLines h 2 ε))⁻¹) := by group
          _ = φ * x * φ⁻¹ * ((x : Equiv.Perm (hypIsotropicLines h 2 ε))⁻¹ *
              (φ * y * φ⁻¹ * (y : Equiv.Perm (hypIsotropicLines h 2 ε))⁻¹)) := by rw [hc]
          _ = _ := by group }
  have hle : ⁅xyPointStab h 2 ε, xyPointStab h 2 ε⁆ ≤
      Subgroup.centralizer ({φ} : Set (Equiv.Perm (hypIsotropicLines h 2 ε))) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have h1 : χ ⁅(⟨x, hx⟩ : xyPointStab h 2 ε), ⟨y, hy⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcen' x hx _ (hχD y hy)
    change φ * ⁅x, y⁆ * φ⁻¹ * ⁅x, y⁆⁻¹ = 1 at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact h1
  rw [← hD] at hg
  exact (Subgroup.mem_centralizer_iff.mp (hle hg) φ rfl)

section Elements

variable (h : UnitaryFieldData p f K)

@[expose] def rankTwoUpper (s : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, s; 0, 1], by simp [det_fin_two_of]⟩

@[expose] def rankTwoWeyl : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; -1, 0], by simp [det_fin_two_of]⟩

theorem leviDual_toGL_two (A : SpecialLinearGroup (Fin 2) K) :
    leviDual h (SpecialLinearGroup.toGL A) =
      !![h.bar ((A : Matrix (Fin 2) (Fin 2) K) 1 1), -h.bar ((A : Matrix (Fin 2) (Fin 2) K) 1 0);
        -h.bar ((A : Matrix (Fin 2) (Fin 2) K) 0 1),
          h.bar ((A : Matrix (Fin 2) (Fin 2) K) 0 0)] := by
  rw [leviDual, ← map_inv, SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rankTwoUpper_mulVec (s : K) :
    ((rankTwoUpper s : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      Pi.single 1 1 = s • Pi.single 0 1 + Pi.single 1 1 := by
  funext i
  fin_cases i <;> simp [rankTwoUpper, mulVec, dotProduct, Fin.sum_univ_two]

theorem leviDual_rankTwoUpper_mulVec (s t : K) :
    leviDual h (SpecialLinearGroup.toGL (rankTwoUpper s)) *ᵥ (t • Pi.single 0 1) =
      t • Pi.single 0 1 + (-(h.bar s) * t) • Pi.single 1 1 := by
  rw [leviDual_toGL_two]
  funext i
  fin_cases i <;> simp [rankTwoUpper, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

theorem rankTwoWeyl_mulVec :
    ((rankTwoWeyl : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      Pi.single 1 1 = Pi.single 0 1 := by
  funext i
  fin_cases i <;> simp [rankTwoWeyl, mulVec, dotProduct, Fin.sum_univ_two]

theorem leviDual_rankTwoWeyl_mulVec (t : K) :
    leviDual h (SpecialLinearGroup.toGL (rankTwoWeyl : SpecialLinearGroup (Fin 2) K)) *ᵥ
      (t • Pi.single 0 1) = (-t) • Pi.single 1 1 := by
  rw [leviDual_toGL_two]
  funext i
  fin_cases i <;> simp [rankTwoWeyl, mulVec, dotProduct, Fin.sum_univ_two]

theorem leviSU_mulVec_xy {r : ℕ} (A : SpecialLinearGroup (Fin r) K) (a b : Fin r → K) :
    (((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (hypXEmb r ε a + hypYEmb r ε b) =
      hypXEmb r ε ((A : Matrix (Fin r) (Fin r) K) *ᵥ a) +
        hypYEmb r ε (leviDual h (SpecialLinearGroup.toGL A) *ᵥ b) := by
  rw [mulVec_add, leviSU_mulVec, leviSU_mulVec, leviFun_hypXEmb, leviFun_hypYEmb]

theorem mapsSpan_leviSU {r : ℕ} {φ : Equiv.Perm (hypIsotropicLines h r ε)}
    {A : SpecialLinearGroup (Fin r) K}
    (hcomm : φ * hypProjLineAction h r ε (hypProj h r ε (leviSU h ε A)) =
      hypProjLineAction h r ε (hypProj h r ε (leviSU h ε A)) * φ)
    {v w : HypIndex r ε → K} (hvw : MapsSpan h φ v w) :
    MapsSpan h φ ((((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v)
      ((((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w) := by
  set g := hypProjLineAction h r ε (hypProj h r ε (leviSU h ε A)) with hg
  have hspan : ∀ u : HypIndex r ε → K, (leviSU h ε A : hypSU h r ε) •
      (K ∙ u) = K ∙ ((((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ u) := fun u => by
    change ((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) • (K ∙ u) = _
    rw [gl_smul_eq_map, Submodule.map_span, Set.image_singleton]
    rfl
  intro L' hL'
  have hgL : g (g⁻¹ L') = L' := by rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
  have hL : ((g⁻¹ L' : hypIsotropicLines h r ε) : Submodule K (HypIndex r ε → K)) = K ∙ v := by
    have h1 := congrArg Subtype.val hgL
    change (leviSU h ε A : hypSU h r ε) •
      ((g⁻¹ L' : hypIsotropicLines h r ε) : Submodule K (HypIndex r ε → K)) = _ at h1
    rw [hL', ← hspan] at h1
    exact smul_left_cancel _ h1
  have h2 := congrArg (fun k : Equiv.Perm (hypIsotropicLines h r ε) => k (g⁻¹ L')) hcomm
  simp only [Equiv.Perm.mul_apply, hgL] at h2
  rw [h2]
  change (leviSU h ε A : hypSU h r ε) •
    ((φ (g⁻¹ L') : hypIsotropicLines h r ε) : Submodule K (HypIndex r ε → K)) = _
  rw [hvw _ hL, hspan]

theorem eq_of_span_xy_eq {r : ℕ} {a b b' : Fin r → K} (ha : a ≠ 0)
    (he : K ∙ (hypXEmb r ε a + hypYEmb r ε b) = K ∙ (hypXEmb r ε a + hypYEmb r ε b')) :
    b = b' := by
  have hmem : hypXEmb r ε a + hypYEmb r ε b' ∈ K ∙ (hypXEmb r ε a + hypYEmb r ε b) := by
    rw [he]
    exact mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hci : c * a i = a i := by
    have := congrFun hc (.inl i)
    simpa [hypXEmb, hypYEmb] using this
  have hc1 : c = 1 := mul_right_cancel₀ hi (hci.trans (one_mul _).symm)
  funext j
  have := congrFun hc (.inr (.inr j))
  simp [hypXEmb, hypYEmb, hc1] at this
  exact this

end Elements

theorem unitary_rank_two_hyperbolic_rigidity (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    (φ : Equiv.Perm (hypIsotropicLines h 2 ε)) (hφ : φ ∈ lineNormalizer h 2 ε)
    (hX : ∀ L : hypIsotropicLines h 2 ε,
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε → φ L = L)
    (hY : ∀ L : hypIsotropicLines h 2 ε,
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε → φ L = L) :
    ∃ (c d : K) (hc : c ≠ 0) (hd : d ≠ 0), h.bar c = c ∧ h.norm d = c ∧
      ∃ hD : (⟨glOfLinearEquiv (hypDiagEquiv (r := 2) (ε := ε) hc hd), 1⟩ :
          SemiGL (HypIndex 2 ε) K) ∈ semilinearSimilitudes h 2 ε,
        ∀ L : hypIsotropicLines h 2 ε,
          (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε ⊔ hypY K 2 ε →
          φ L = semilinearPointAction h 2 ε ⟨_, hD⟩ L := by
  have hφo := (unitary_normalizer_preserves_orthogonality.{0} h (le_refl 2)).1 φ hφ
  have hcomm : ∀ A : SpecialLinearGroup (Fin 2) K,
      φ * hypProjLineAction h 2 ε (hypProj h 2 ε (leviSU h ε A)) =
        hypProjLineAction h 2 ε (hypProj h 2 ε (leviSU h ε A)) * φ := fun A =>
    commute_leviPointGroup h hε hφ hX hY ⟨A, rfl⟩
  have hSex : ∀ (i j : Fin 2) (α : K), ∃ s : K, i ≠ j → α ≠ 0 → s ≠ 0 ∧
      MapsSpan h φ (hypXEmb 2 ε (Pi.single j 1) + hypYEmb 2 ε (α • Pi.single i 1))
        (hypXEmb 2 ε (Pi.single j 1) + hypYEmb 2 ε (s • α • Pi.single i 1)) := by
    intro i j α
    by_cases hij : i = j
    · exact ⟨0, fun h0 => absurd hij h0⟩
    by_cases hα : α = 0
    · exact ⟨0, fun _ h0 => absurd hα h0⟩
    have hαi : α • Pi.single i (1 : K) ≠ 0 := fun h0 => by
      have := congrFun h0 i
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply] at this
      exact hα this
    obtain ⟨s, hs, hmaps⟩ := exists_mapsSpan_of_hdot h hφo hX hY hε (single_ne_zero j) hαi
      (hdot_single_smul_single h hij α)
    exact ⟨s, fun _ _ => ⟨hs, hmaps⟩⟩
  choose S hS using hSex
  have hS' : ∀ i j α, i ≠ j → α ≠ 0 → S i j α ≠ 0 ∧
      MapsSpan h φ (hypXEmb 2 ε (Pi.single j 1) + hypYEmb 2 ε (α • Pi.single i 1))
        (hypXEmb 2 ε (Pi.single j 1) + hypYEmb 2 ε (S i j α • α • Pi.single i 1)) := hS
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨e₀, he₀, he₀0⟩ := exists_mem_traceZero_ne_zero' h
  have he₀tr : e₀ + h.bar e₀ = 0 := (UnitaryFieldData.mem_traceZero h).mp he₀
  have hbe₀ : h.bar e₀ ≠ 0 := (map_ne_zero h.bar).mpr he₀0
  have hQiso : hdot h (Pi.single (0 : Fin 2) (1 : K)) (e₀ • Pi.single (0 : Fin 2) (1 : K)) +
      hdot h (e₀ • Pi.single (0 : Fin 2) (1 : K)) (Pi.single (0 : Fin 2) (1 : K)) = 0 := by
    rw [hdot_smul_right, hdot_single_left, hdot_smul_left, hdot_single_left, Pi.single_eq_same,
      mul_one, mul_one, he₀tr]
  obtain ⟨Q, hQ⟩ := exists_pt h (single_ne_zero (0 : Fin 2)) hQiso
  obtain ⟨sQ, τ, -, hQ'⟩ := rigid_shape h hφo hX hY Q (single_ne_zero 0) hQ
  have hS01 : ∀ t : K, t ≠ 0 → S 0 1 t = h.bar sQ := by
    intro t ht
    set s := -t / h.bar e₀ with hs
    have hmaps := mapsSpan_leviSU h (hcomm (rankTwoUpper s)) (hS' 0 1 t h01 ht).2
    rw [leviSU_mulVec_xy, leviSU_mulVec_xy, rankTwoUpper_mulVec,
      mulVec_smul (leviDual h (SpecialLinearGroup.toGL (rankTwoUpper s))) (S 0 1 t)
        (t • Pi.single 0 1), leviDual_rankTwoUpper_mulVec] at hmaps
    set aP : Fin 2 → K := s • Pi.single 0 1 + Pi.single 1 1 with haP
    set bP : Fin 2 → K := t • Pi.single 0 1 + (-(h.bar s) * t) • Pi.single 1 1 with hbP
    have haP0 : aP ≠ 0 := fun h0 => by
      have := congrFun h0 1
      simp [haP] at this
    have hab : hdot h aP bP = 0 := by
      simp [haP, hbP, hdot, dotProduct, Fin.sum_univ_two]
    have hPiso : hdot h aP bP + hdot h bP aP = 0 := by
      rw [hdot_comm h aP bP, hab, map_zero, add_zero]
    obtain ⟨M, hM⟩ := exists_pt h haP0 hPiso
    refine (rigid_coeff h hφo hQ hQ' hM (hmaps M hM) ?_ ?_).symm
    · simp [haP, hbP, hdot, dotProduct, Fin.sum_univ_two, hs]
      field_simp
      ring
    · simp [haP, hdot, dotProduct, Fin.sum_univ_two, hs]
      field_simp
      exact ⟨he₀0, ht, he₀0⟩
  have hS10 : ∀ α : K, α ≠ 0 → S 1 0 α = h.bar sQ := by
    intro α hα
    have ht : -α ≠ 0 := neg_ne_zero.mpr hα
    have hmaps := mapsSpan_leviSU h (hcomm rankTwoWeyl) (hS' 0 1 (-α) h01 ht).2
    rw [leviSU_mulVec_xy, leviSU_mulVec_xy, rankTwoWeyl_mulVec,
      mulVec_smul (leviDual h
        (SpecialLinearGroup.toGL (rankTwoWeyl : SpecialLinearGroup (Fin 2) K)))
        (S 0 1 (-α)) ((-α) • Pi.single 0 1), leviDual_rankTwoWeyl_mulVec, neg_neg,
      hS01 _ ht] at hmaps
    obtain ⟨L₁, hL₁⟩ := exists_pt h (single_ne_zero (0 : Fin 2))
      (pt_single_iso h (i := 1) (j := 0) (Ne.symm h01) α)
    have h1 := hmaps L₁ hL₁
    have h2 := (hS' 1 0 α (Ne.symm h01) hα).2 L₁ hL₁
    have h3 := congrFun (eq_of_span_xy_eq (single_ne_zero 0) (h1.symm.trans h2)) 1
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3
    exact (mul_right_cancel₀ hα h3).symm
  set c := h.bar sQ with hcdef
  have hcF : h.bar c = c := by
    have h1 := rigid_swap h hφo S hS' 0 1 h01 1 one_ne_zero
    rw [hS01 1 one_ne_zero, hS10 _ (by rw [map_one]; exact neg_ne_zero.mpr one_ne_zero)] at h1
    exact h1
  have hc0 : c ≠ 0 := by
    rw [← hS01 1 one_ne_zero]
    exact (hS' 0 1 1 h01 one_ne_zero).1
  have hSc : ∀ i j : Fin 2, i ≠ j → ∀ α : K, α ≠ 0 → S i j α = c := by
    intro i j hij α hα
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hS01 α hα
    · exact hS10 α hα
    · exact absurd rfl hij
  obtain ⟨d, hd⟩ := h.normHom_surjective ⟨c, (UnitaryFieldData.mem_fixedField h).mpr hcF⟩
  have hN : h.norm d = c := by
    have := congrArg Subtype.val hd
    rwa [UnitaryFieldData.coe_normHom] at this
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul] at hN
    exact hc0 hN.symm
  have hDmem : (⟨glOfLinearEquiv (hypDiagEquiv (r := 2) (ε := ε) hc0 hd0), 1⟩ :
      SemiGL (HypIndex 2 ε) K) ∈ semilinearSimilitudes h 2 ε :=
    ⟨c, hc0, hcF, hypDiag_similitude h hc0 hd0 hcF hN⟩
  refine ⟨c, d, hc0, hd0, hcF, hN, hDmem, fun L hL => ?_⟩
  obtain ⟨v, -, -, hLv⟩ := exists_eq_span_of_mem_hypIsotropicLines h L.2
  have hvH : v ∈ hypX K 2 ε ⊔ hypY K 2 ε := hL (by rw [hLv]; exact mem_span_singleton_self v)
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hvH
  rw [← hab] at hLv
  have hDL : (semilinearPointAction h 2 ε ⟨_, hDmem⟩ L : Submodule K (HypIndex 2 ε → K)) =
      K ∙ (hypXEmb 2 ε a + hypYEmb 2 ε (c • b)) := by
    change (⟨glOfLinearEquiv (hypDiagEquiv (r := 2) (ε := ε) hc0 hd0), 1⟩ :
      SemiGL (HypIndex 2 ε) K) • (L : Submodule K (HypIndex 2 ε → K)) = _
    rw [hLv, semiGL_smul_eq_map, Submodule.map_span, Set.image_singleton, semiLin_apply]
    congr 2
    change ((glOfLinearEquiv (hypDiagEquiv (r := 2) (ε := ε) hc0 hd0) : GL (HypIndex 2 ε) K) :
      Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *ᵥ (hypXEmb 2 ε a + hypYEmb 2 ε b) = _
    rw [glOfLinearEquiv_mulVec, hypDiagEquiv_apply, diagFun_xy]
  apply Subtype.ext
  rw [hDL]
  by_cases ha : a = 0
  · have hLY : (L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε := by
      rw [hLv, ha, map_zero, zero_add, span_singleton_le_iff_mem]
      exact ⟨b, rfl⟩
    rw [hY L hLY, hLv, ha, map_zero, zero_add, zero_add, map_smul,
      span_singleton_smul_eq (IsUnit.mk0 _ hc0)]
  by_cases hb : b = 0
  · have hLX : (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε := by
      rw [hLv, hb, map_zero, add_zero, span_singleton_le_iff_mem]
      exact ⟨a, rfl⟩
    rw [hX L hLX, hLv, hb, smul_zero]
  exact rigid_gen h hφo hX hY S hS' hcF hSc (le_refl 2) hε L ha hb hLv

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
