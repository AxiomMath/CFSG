module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFlagExtension
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPairExtension

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_diag_det (h : UnitaryFieldData p f K) {r ε : ℕ} (hε : ε ≤ 1)
    (hrε : 0 < 2 * r + ε) {u : K} (hu : h.norm u = 1) :
    ∃ c : HypIndex r ε → K, (∀ x, c x ≠ 0) ∧
      (∀ x, h.bar (c x) * c (hypPartner x) = 1) ∧ ∏ x, c x = u := by
  classical
  have hu0 : u ≠ 0 := fun h0 => by
    rw [h0, UnitaryFieldData.norm, map_zero, mul_zero] at hu
    exact zero_ne_one hu
  rcases Nat.eq_zero_or_pos ε with rfl | hε0
  · have hr0 : 0 < r := by omega
    obtain ⟨μ, hμ0, hμ⟩ := h.exists_div_bar_eq hu
    have hbμ : h.bar μ ≠ 0 := (map_ne_zero h.bar).mpr hμ0
    let i₀ : Fin r := ⟨0, hr0⟩
    refine ⟨fun x => match x with
      | .inl i => if i = i₀ then μ else 1
      | .inr (.inl _) => 1
      | .inr (.inr i) => if i = i₀ then (h.bar μ)⁻¹ else 1, fun x => ?_, fun x => ?_, ?_⟩
    · rcases x with i | l | i
      · change (if i = i₀ then μ else 1) ≠ 0
        split_ifs <;> simp [hμ0]
      · exact one_ne_zero
      · change (if i = i₀ then (h.bar μ)⁻¹ else 1) ≠ 0
        split_ifs <;> simp [hbμ]
    · rcases x with i | l | i
      · change h.bar (if i = i₀ then μ else 1) * (if i = i₀ then (h.bar μ)⁻¹ else 1) = 1
        split_ifs <;> simp [hbμ]
      · change h.bar 1 * 1 = 1
        simp
      · change h.bar (if i = i₀ then (h.bar μ)⁻¹ else 1) * (if i = i₀ then μ else 1) = 1
        split_ifs <;> simp [h.bar_bar, hμ0]
    · rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.prod_const_one,
        one_mul]
      rw [← hμ, div_eq_mul_inv]
  · obtain rfl : ε = 1 := by omega
    refine ⟨fun x => match x with
      | .inl _ => 1
      | .inr (.inl _) => u
      | .inr (.inr _) => 1, fun x => ?_, fun x => ?_, ?_⟩
    · rcases x with i | l | i <;> simp [hu0]
    · rcases x with i | l | i <;> simp only [hypPartner, map_one, one_mul]
      rw [mul_comm]
      exact hu
    · rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp

theorem exists_sesqSpecialUnitary_map_lines (h : UnitaryFieldData p f K) {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {r ε : ℕ} (hε : ε ≤ 1) (hrε : 0 < 2 * r + ε)
    (w w' : Module.Basis (HypIndex r ε) K V) (hw : ∀ x y, B (w x) (w y) = hypGram r ε K x y)
    (hw' : ∀ x y, B (w' x) (w' y) = hypGram r ε K x y) :
    ∃ g ∈ sesqSpecialUnitaryGroup B, ∀ x, (K ∙ w x).map (g : V →ₗ[K] V) = K ∙ w' x := by
  classical
  set g₀ : V →ₗ[K] V := (w.equiv w' (Equiv.refl _)).toLinearMap with hg₀def
  have hg₀ : ∀ x y, B (g₀ x) (g₀ y) = B x y :=
    isometry_basis_equiv w w' (fun x y => by rw [hw, hw'])
  have hg₀w : ∀ x, g₀ (w x) = w' x := fun x => by
    rw [hg₀def, LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hB hBl
  have hd : h.norm (LinearMap.det g₀) = 1 :=
    norm_det_of_isometry h e (mem_orthonormalFrames.mpr he) hg₀
  set d := LinearMap.det g₀ with hddef
  have hd0 : d ≠ 0 := fun h0 => by
    rw [h0, UnitaryFieldData.norm, map_zero, mul_zero] at hd
    exact zero_ne_one hd
  have hdinv : h.norm d⁻¹ = 1 := by
    rw [UnitaryFieldData.norm, map_inv₀, ← mul_inv, ← UnitaryFieldData.norm, hd, inv_one]
  obtain ⟨c, hc0, hcp, hcprod⟩ := exists_diag_det h hε hrε hdinv
  obtain ⟨φ, hφ, hφdet, hφw⟩ := exists_diagonal_isometry h w' hw' c hcp
  have hcomp : ∀ x y, B ((φ ∘ₗ g₀) x) ((φ ∘ₗ g₀) y) = B x y := fun x y => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hφ, hg₀]
  refine ⟨isometryUnit hBl hcomp, mem_sesqSpecialUnitaryGroup.mpr ⟨(isometryUnit hBl hcomp).2,
    ?_⟩, fun x => ?_⟩
  · rw [coe_isometryUnit, LinearMap.det_comp, hφdet, hcprod, ← hddef, inv_mul_cancel₀ hd0]
  · rw [coe_isometryUnit, Submodule.map_span, Set.image_singleton, LinearMap.comp_apply, hg₀w,
      hφw]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (hc0 x)) _

theorem exists_sesqSpecialUnitary_of_hyperbolic (h : UnitaryFieldData p f K) {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {a b a' b' : V} (ha : B a a = 0) (hb : B b b = 0)
    (hab : B a b = 1) (ha' : B a' a' = 0) (hb' : B b' b' = 0) (hab' : B a' b' = 1) :
    ∃ g ∈ sesqSpecialUnitaryGroup B, (K ∙ a).map (g : V →ₗ[K] V) = K ∙ a' ∧
      (K ∙ b).map (g : V →ₗ[K] V) = K ∙ b' := by
  have hwitt := (hermitian_witt_basis h hB hBl rfl).2.2.2
  obtain ⟨hr, w, hw, hwa, hwb⟩ := hwitt a b ha hb hab
  obtain ⟨hr', w', hw', hwa', hwb'⟩ := hwitt a' b' ha' hb' hab'
  obtain ⟨g, hg, hgw⟩ := exists_sesqSpecialUnitary_map_lines h hB hBl (by omega) (by omega)
    w w' hw hw'
  refine ⟨g, hg, ?_, ?_⟩
  · rw [← hwa, ← hwa', hgw]
  · rw [← hwb, ← hwb', hgw]

theorem exists_sesqSpecialUnitary_of_orthogonal (h : UnitaryFieldData p f K) {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {a₁ a₂ a₁' a₂' : V}
    (hli : LinearIndependent K ![a₁, a₂]) (h11 : B a₁ a₁ = 0) (h12 : B a₁ a₂ = 0)
    (h21 : B a₂ a₁ = 0) (h22 : B a₂ a₂ = 0) (hli' : LinearIndependent K ![a₁', a₂'])
    (h11' : B a₁' a₁' = 0) (h12' : B a₁' a₂' = 0) (h21' : B a₂' a₁' = 0)
    (h22' : B a₂' a₂' = 0) :
    ∃ g ∈ sesqSpecialUnitaryGroup B, (K ∙ a₁).map (g : V →ₗ[K] V) = K ∙ a₁' ∧
      (K ∙ a₂).map (g : V →ₗ[K] V) = K ∙ a₂' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, r, ε, hε, hn, w, hw, hwa₁, hwa₂, -, -⟩ :=
    hermitian_isotropic_pair_extension h hB hBl hli h11 h12 h21 h22
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, r', ε', hε', hn', w', hw', hwa₁', hwa₂', -,
    -⟩ := hermitian_isotropic_pair_extension h hB hBl hli' h11' h12' h21' h22'
  obtain rfl : r' = r := by omega
  obtain rfl : ε' = ε := by omega
  obtain ⟨g, hg, hgw⟩ := exists_sesqSpecialUnitary_map_lines h hB hBl hε (by omega) w w' hw hw'
  refine ⟨g, hg, ?_, ?_⟩
  · rw [← hwa₁, ← hwa₁', hgw]
  · rw [← hwa₂, ← hwa₂', hgw]

theorem exists_unitarySU_smul_eq_map (h : UnitaryFieldData p f K) {n : ℕ}
    {g' : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hg' : g' ∈ sesqSpecialUnitaryGroup (stdHermForm h n)) :
    ∃ g : unitarySU p f K n, ∀ L : Submodule K (Fin n → K),
      g • L = L.map (g' : (Fin n → K) →ₗ[K] Fin n → K) := by
  set A := Matrix.GeneralLinearGroup.toLin.symm g' with hAdef
  have hgA : g' = Matrix.GeneralLinearGroup.toLin A := by
    rw [hAdef, MulEquiv.apply_symm_apply]
  have hA : A ∈ unitarySU p f K n := by
    rw [hgA, stdHermForm_eq_gramForm] at hg'
    rw [unitarySU_eq_gramSU h]
    exact (toLin_mem_sesqSpecialUnitaryGroup_iff h _ A).mp hg'
  refine ⟨⟨A, hA⟩, fun L => ?_⟩
  rw [hgA]
  rfl

theorem exists_eq_span_of_mem_isotropicLines {h : UnitaryFieldData p f K} {n : ℕ}
    {L : Submodule K (Fin n → K)} (hL : L ∈ isotropicLines h n) :
    ∃ a, a ≠ 0 ∧ stdHermForm h n a a = 0 ∧ L = K ∙ a := by
  obtain ⟨hL1, hL2⟩ := mem_isotropicLines.mp hL
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := L) fun h0 => by
    rw [h0, finrank_bot] at hL1
    exact zero_ne_one hL1
  exact ⟨a, ha0, hL2 a ha, eq_span_singleton_of_mem_of_finrank_eq_one hL1 ha ha0⟩

theorem span_mem_isotropicLines {h : UnitaryFieldData p f K} {n : ℕ} {a : Fin n → K}
    (ha0 : a ≠ 0) (ha : stdHermForm h n a a = 0) : K ∙ a ∈ isotropicLines h n := by
  refine mem_isotropicLines.mpr ⟨finrank_span_singleton ha0, fun x hx => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  simp [ha]

theorem orth_span_iff {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]
    {B : V →ₛₗ[σ] V →ₗ[K] K} (a c : V) :
    (∀ x ∈ K ∙ a, ∀ y ∈ K ∙ c, B x y = 0) ↔ B a c = 0 := by
  refine ⟨fun hac => hac a (Submodule.mem_span_singleton_self a) c
    (Submodule.mem_span_singleton_self c), fun hac x hx y hy => ?_⟩
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
  simp [hac]

theorem linearIndependent_pair_of_span_ne {V : Type*} [AddCommGroup V] [Module K V] {a c : V}
    (ha : a ≠ 0) (hc : c ≠ 0) (hne : K ∙ a ≠ K ∙ c) : LinearIndependent K ![a, c] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right ha, rfl⟩
  · exfalso
    have hs : s ≠ 0 := fun hs => by
      subst hs
      rw [zero_smul, zero_add, smul_eq_zero] at hst
      exact hc (hst.resolve_left ht)
    have hc' : c ∈ K ∙ a := by
      rw [Submodule.mem_span_singleton]
      refine ⟨-(t⁻¹ * s), ?_⟩
      rw [neg_smul, mul_smul, ← smul_neg, ← eq_neg_of_add_eq_zero_right hst, smul_smul,
        inv_mul_cancel₀ ht, one_smul]
    have ha' : a ∈ K ∙ c := by
      rw [Submodule.mem_span_singleton]
      refine ⟨-(s⁻¹ * t), ?_⟩
      rw [neg_smul, mul_smul, ← smul_neg, ← eq_neg_of_add_eq_zero_left hst, smul_smul,
        inv_mul_cancel₀ hs, one_smul]
    exact hne (le_antisymm ((Submodule.span_singleton_le_iff_mem _ _).mpr ha')
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hc'))

theorem orth_smul_iff (h : UnitaryFieldData p f K) {n : ℕ} (g : unitarySU p f K n)
    (L M : Submodule K (Fin n → K)) :
    (∀ x ∈ g • L, ∀ y ∈ g • M, stdHermForm h n x y = 0) ↔
      ∀ x ∈ L, ∀ y ∈ M, stdHermForm h n x y = 0 := by
  constructor
  · intro hgLM x hx y hy
    rw [← stdHermForm_smul_smul h g]
    exact hgLM _ (Submodule.smul_mem_pointwise_smul x g L hx) _
      (Submodule.smul_mem_pointwise_smul y g M hy)
  · intro hLM x hx y hy
    obtain ⟨x', hx', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x g L).mp hx
    obtain ⟨y', hy', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y g M).mp hy
    rw [stdHermForm_smul_smul]
    exact hLM x' hx' y' hy'

theorem unitary_isotropic_pair_orbits (h : UnitaryFieldData p f K) {n : ℕ} (hn : 3 ≤ n) :
    Nonempty (isotropicLines h n) ∧
    (∀ L M : isotropicLines h n, ∃ g : unitarySU p f K n, g • L = M) ∧
    (∀ L M L' M' : isotropicLines h n, L ≠ M → L' ≠ M' →
      ((∃ g : unitarySU p f K n, g • L = L' ∧ g • M = M') ↔
        ((∀ x ∈ (L : Submodule K (Fin n → K)), ∀ y ∈ (M : Submodule K (Fin n → K)),
          stdHermForm h n x y = 0) ↔
          ∀ x ∈ (L' : Submodule K (Fin n → K)), ∀ y ∈ (M' : Submodule K (Fin n → K)),
            stdHermForm h n x y = 0))) ∧
    (n = 3 → ∀ L M : isotropicLines h n, L ≠ M →
      ¬ ∀ x ∈ (L : Submodule K (Fin n → K)), ∀ y ∈ (M : Submodule K (Fin n → K)),
        stdHermForm h n x y = 0) ∧
    (4 ≤ n → (∃ L M : isotropicLines h n, L ≠ M ∧
        ∀ x ∈ (L : Submodule K (Fin n → K)), ∀ y ∈ (M : Submodule K (Fin n → K)),
          stdHermForm h n x y = 0) ∧
      ∃ L M : isotropicLines h n, L ≠ M ∧
        ¬ ∀ x ∈ (L : Submodule K (Fin n → K)), ∀ y ∈ (M : Submodule K (Fin n → K)),
          stdHermForm h n x y = 0) := by
  have hB := stdHermForm_isSymm h n
  have hBl := stdHermForm_separatingLeft h n
  have hdim : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hsymm : ∀ x y : Fin n → K, stdHermForm h n x y = 0 → stdHermForm h n y x = 0 :=
    fun x y hxy => by rw [← hB.eq x y, hxy, map_zero]
  have hhyp : ∀ L M : isotropicLines h n, ¬ (∀ x ∈ (L : Submodule K (Fin n → K)),
      ∀ y ∈ (M : Submodule K (Fin n → K)), stdHermForm h n x y = 0) →
      ∃ a b, stdHermForm h n a a = 0 ∧ stdHermForm h n b b = 0 ∧ stdHermForm h n a b = 1 ∧
        (L : Submodule K (Fin n → K)) = K ∙ a ∧ (M : Submodule K (Fin n → K)) = K ∙ b := by
    intro L M hLM
    obtain ⟨a, ha0, ha, hLa⟩ := exists_eq_span_of_mem_isotropicLines L.2
    obtain ⟨c, hc0, hc, hMc⟩ := exists_eq_span_of_mem_isotropicLines M.2
    rw [hLa, hMc, orth_span_iff] at hLM
    refine ⟨a, (stdHermForm h n a c)⁻¹ • c, ha, by simp [hc], by
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hLM], hLa, ?_⟩
    rw [hMc, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hLM))]
  have horth : ∀ L M : isotropicLines h n, L ≠ M → (∀ x ∈ (L : Submodule K (Fin n → K)),
      ∀ y ∈ (M : Submodule K (Fin n → K)), stdHermForm h n x y = 0) →
      ∃ a₁ a₂, LinearIndependent K ![a₁, a₂] ∧ stdHermForm h n a₁ a₁ = 0 ∧
        stdHermForm h n a₁ a₂ = 0 ∧ stdHermForm h n a₂ a₁ = 0 ∧ stdHermForm h n a₂ a₂ = 0 ∧
        (L : Submodule K (Fin n → K)) = K ∙ a₁ ∧ (M : Submodule K (Fin n → K)) = K ∙ a₂ := by
    intro L M hne hLM
    obtain ⟨a, ha0, ha, hLa⟩ := exists_eq_span_of_mem_isotropicLines L.2
    obtain ⟨c, hc0, hc, hMc⟩ := exists_eq_span_of_mem_isotropicLines M.2
    rw [hLa, hMc, orth_span_iff] at hLM
    have hne' : K ∙ a ≠ K ∙ c := fun heq => hne (Subtype.ext (by rw [hLa, hMc, heq]))
    exact ⟨a, c, linearIndependent_pair_of_span_ne ha0 hc0 hne', ha, hLM, hsymm a c hLM, hc,
      hLa, hMc⟩
  have hext : ∀ L M L' M' : isotropicLines h n, ∀ g' ∈ sesqSpecialUnitaryGroup (stdHermForm h n),
      (L : Submodule K (Fin n → K)).map (g' : (Fin n → K) →ₗ[K] Fin n → K) = L' →
      (M : Submodule K (Fin n → K)).map (g' : (Fin n → K) →ₗ[K] Fin n → K) = M' →
      ∃ g : unitarySU p f K n, g • L = L' ∧ g • M = M' := by
    intro L M L' M' g' hg' hL hM
    obtain ⟨g, hg⟩ := exists_unitarySU_smul_eq_map h hg'
    exact ⟨g, Subtype.ext (by rw [← hL, ← hg]; rfl), Subtype.ext (by rw [← hM, ← hg]; rfl)⟩
  refine ⟨?_, fun L M => ?_, fun L M L' M' hne hne' => ⟨?_, fun hiff => ?_⟩, fun h3 L M hne
    hLM => ?_, fun h4 => ?_⟩
  · obtain ⟨a, ha0, ha⟩ := (hermitian_witt_basis h hB hBl hdim).2.1 (by omega)
    exact ⟨⟨_, span_mem_isotropicLines ha0 ha⟩⟩
  · obtain ⟨a, ha0, ha, hLa⟩ := exists_eq_span_of_mem_isotropicLines L.2
    obtain ⟨a', ha'0, ha', hMa'⟩ := exists_eq_span_of_mem_isotropicLines M.2
    obtain ⟨⟨b, hab, hbb⟩, -⟩ := hermitian_hyperbolic_splitting h hB hBl ha0 ha
    obtain ⟨⟨b', hab', hbb'⟩, -⟩ := hermitian_hyperbolic_splitting h hB hBl ha'0 ha'
    obtain ⟨g', hg', hgL, -⟩ :=
      exists_sesqSpecialUnitary_of_hyperbolic h hB hBl ha hbb hab ha' hbb' hab'
    obtain ⟨g, hg⟩ := exists_unitarySU_smul_eq_map h hg'
    exact ⟨g, Subtype.ext (by
      change g • (L : Submodule K (Fin n → K)) = M
      rw [hg, hLa, hgL, hMa'])⟩
  · rintro ⟨g, hgL, hgM⟩
    rw [← hgL, ← hgM]
    exact (orth_smul_iff h g L M).symm
  · by_cases hLM : ∀ x ∈ (L : Submodule K (Fin n → K)), ∀ y ∈ (M : Submodule K (Fin n → K)),
        stdHermForm h n x y = 0
    · obtain ⟨a₁, a₂, hli, h11, h12, h21, h22, hL, hM⟩ := horth L M hne hLM
      obtain ⟨a₁', a₂', hli', h11', h12', h21', h22', hL', hM'⟩ :=
        horth L' M' hne' (hiff.mp hLM)
      obtain ⟨g', hg', hg1, hg2⟩ := exists_sesqSpecialUnitary_of_orthogonal h hB hBl hli h11 h12
        h21 h22 hli' h11' h12' h21' h22'
      exact hext L M L' M' g' hg' (by rw [hL, hg1, hL']) (by rw [hM, hg2, hM'])
    · obtain ⟨a, b, ha, hb, hab, hL, hM⟩ := hhyp L M hLM
      obtain ⟨a', b', ha', hb', hab', hL', hM'⟩ := hhyp L' M' (fun h' => hLM (hiff.mpr h'))
      obtain ⟨g', hg', hg1, hg2⟩ :=
        exists_sesqSpecialUnitary_of_hyperbolic h hB hBl ha hb hab ha' hb' hab'
      exact hext L M L' M' g' hg' (by rw [hL, hg1, hL']) (by rw [hM, hg2, hM'])
  · obtain ⟨a₁, a₂, hli, h11, h12, h21, h22, -, -⟩ := horth L M hne hLM
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, r, ε, -, hn', -⟩ :=
      hermitian_isotropic_pair_extension h hB hBl hli h11 h12 h21 h22
    omega
  · obtain ⟨w, hw⟩ := (hermitian_witt_basis h hB hBl hdim).1
    have h0 : 0 < n / 2 := by omega
    have h1 : 1 < n / 2 := by omega
    have hne : ∀ x y, x ≠ y → K ∙ w x ≠ K ∙ w y := fun x y hxy heq => by
      have hy : w y ∈ K ∙ w x := heq ▸ Submodule.mem_span_singleton_self (w y)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
      have := congrArg (fun v => w.repr v y) hc
      simp [Module.Basis.repr_self, hxy] at this
    have hP : ∀ i : Fin (n / 2), K ∙ w (.inl i) ∈ isotropicLines h n := fun i =>
      span_mem_isotropicLines (w.ne_zero _) (by rw [hw]; simp)
    have hQ : ∀ i : Fin (n / 2), K ∙ w (.inr (.inr i)) ∈ isotropicLines h n := fun i =>
      span_mem_isotropicLines (w.ne_zero _) (by rw [hw]; simp)
    refine ⟨⟨⟨_, hP ⟨0, h0⟩⟩, ⟨_, hP ⟨1, h1⟩⟩, fun heq => hne _ _ (by simp)
      (congrArg Subtype.val heq), (orth_span_iff _ _).mpr (by rw [hw]; simp)⟩,
      ⟨_, hP ⟨0, h0⟩⟩, ⟨_, hQ ⟨0, h0⟩⟩, fun heq => hne _ _ (by simp)
      (congrArg Subtype.val heq), fun h' => ?_⟩
    have := (orth_span_iff _ _).mp h'
    rw [hw] at this
    simp at this

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
