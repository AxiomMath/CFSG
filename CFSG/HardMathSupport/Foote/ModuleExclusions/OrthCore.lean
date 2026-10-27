module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.OrthCases
public import CFSG.HardMathSupport.Foote.ModuleExclusions.OrthCW

public section

open Matrix LinearMap Module
open scoped commutatorElement

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG CFSG.Open CFSG.CGT.PushingUpLit.CGT6M

section Eig

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def eigSp (A : Matrix ι ι K) (s : K) : Submodule K (ι → K) :=
  LinearMap.ker (A.mulVecLin - s • LinearMap.id)

omit [DecidableEq ι] in
theorem mem_eigSp {A : Matrix ι ι K} {s : K} {x : ι → K} : x ∈ eigSp A s ↔ A *ᵥ x = s • x := by
  simp [eigSp, sub_eq_zero]

theorem eigSp_sup_eq_top {A : Matrix ι ι K} {c s : K} (hA : A * A = c • 1) (hss : s * s = c)
    (h2 : (2 : K) ≠ 0) (hs0 : s ≠ 0) : eigSp A s ⊔ eigSp A (-s) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hs2 : (2 * s : K) ≠ 0 := mul_ne_zero h2 hs0
  have h1 : A *ᵥ (A *ᵥ x + s • x) = s • (A *ᵥ x + s • x) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.smul_mulVec,
      Matrix.one_mulVec, ← hss]
    module
  have h2' : A *ᵥ (A *ᵥ x - s • x) = (-s) • (A *ᵥ x - s • x) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.smul_mulVec,
      Matrix.one_mulVec, ← hss]
    module
  have hx : x = (2 * s)⁻¹ • (A *ᵥ x + s • x) + (-(2 * s)⁻¹) • (A *ᵥ x - s • x) := by
    have : (2 * s)⁻¹ * s * 2 = 1 := by field_simp
    match_scalars <;> field_simp <;> ring
  rw [hx]
  exact Submodule.add_mem_sup
    (Submodule.smul_mem _ _ (mem_eigSp.mpr h1)) (Submodule.smul_mem _ _ (mem_eigSp.mpr h2'))

omit [DecidableEq ι] in
theorem eig_disjoint {A : Matrix ι ι K} {s : K} (h2 : (2 : K) ≠ 0) (hs0 : s ≠ 0) {x : ι → K}
    (h1 : x ∈ eigSp A s) (h2' : x ∈ eigSp A (-s)) : x = 0 := by
  rw [mem_eigSp] at h1 h2'
  have : (2 * s) • x = 0 := by
    have : s • x - (-s) • x = 0 := by rw [← h1, ← h2']; simp
    rw [← this]; module
  exact (smul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hs0)

theorem eigSp_top {A : Matrix ι ι K} {s : K} (h : eigSp A s = ⊤) : A = s • 1 := by
  apply gl_ext
  intro x
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  exact mem_eigSp.mp (by rw [h]; trivial)

omit [DecidableEq ι] in
theorem eig_orth {B : LinearMap.BilinForm K (ι → K)} {A : Matrix ι ι K}
    (hA : ∀ x y, B (A *ᵥ x) (A *ᵥ y) = B x y) {s t : K} (hst : s * t ≠ 1) {x y : ι → K}
    (hx : x ∈ eigSp A s) (hy : y ∈ eigSp A t) : B x y = 0 := by
  rw [mem_eigSp] at hx hy
  have := hA x y
  rw [hx, hy] at this
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  have h2 : (s * t - 1) * B x y = 0 := by linear_combination this
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hst)

omit [DecidableEq ι] in
theorem card_le_finrank_add {A : Matrix ι ι K} {s t : K} (h : eigSp A s ⊔ eigSp A t = ⊤) :
    Fintype.card ι ≤ finrank K (eigSp A s) + finrank K (eigSp A t) := by
  have h1 := Submodule.finrank_add_le_finrank_add_finrank (eigSp A s) (eigSp A t)
  rw [h, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  exact h1

omit [Fintype ι] [DecidableEq ι] in
theorem exists_indep_three {W : Submodule K (ι → K)} [FiniteDimensional K W] (h : 3 ≤ finrank K W) :
    ∃ a w₁ w₂ : ι → K, a ∈ W ∧ w₁ ∈ W ∧ w₂ ∈ W ∧
      ∀ r t₁ t₂ : K, r • a + t₁ • w₁ + t₂ • w₂ = 0 → r = 0 ∧ t₁ = 0 ∧ t₂ = 0 := by
  let b : Basis (Fin (finrank K W)) K W := finBasis K W
  let v : Fin 3 → (ι → K) := fun i => (b (Fin.castLE h i) : ι → K)
  have hli : LinearIndependent K v :=
    (b.linearIndependent.comp _ (Fin.castLE_injective h)).map' W.subtype (Submodule.ker_subtype W)
  refine ⟨v 0, v 1, v 2, (b _).2, (b _).2, (b _).2, fun r t₁ t₂ hr => ?_⟩
  rw [Fintype.linearIndependent_iff] at hli
  have := hli ![r, t₁, t₂] (by simpa [Fin.sum_univ_three] using hr)
  exact ⟨by simpa using this 0, by simpa using this 1, by simpa using this 2⟩

omit [Fintype ι] [DecidableEq ι] in
theorem exists_indep_two {W : Submodule K (ι → K)} [FiniteDimensional K W] (h : 2 ≤ finrank K W) :
    ∃ w₁ w₂ : ι → K, w₁ ∈ W ∧ w₂ ∈ W ∧ ∀ t₁ t₂ : K, t₁ • w₁ + t₂ • w₂ = 0 → t₁ = 0 ∧ t₂ = 0 := by
  let b : Basis (Fin (finrank K W)) K W := finBasis K W
  let v : Fin 2 → (ι → K) := fun i => (b (Fin.castLE h i) : ι → K)
  have hli : LinearIndependent K v :=
    (b.linearIndependent.comp _ (Fin.castLE_injective h)).map' W.subtype (Submodule.ker_subtype W)
  refine ⟨v 0, v 1, (b _).2, (b _).2, fun t₁ t₂ hr => ?_⟩
  rw [Fintype.linearIndependent_iff] at hli
  have := hli ![t₁, t₂] (by simpa [Fin.sum_univ_two] using hr)
  exact ⟨by simpa using this 0, by simpa using this 1⟩

variable {B : LinearMap.BilinForm K (ι → K)}

omit [DecidableEq ι] in
theorem exists_singular_mem [Finite K] {W : Submodule K (ι → K)} (h : 3 ≤ finrank K W) :
    ∃ a ∈ W, a ≠ 0 ∧ B a a = 0 := by
  obtain ⟨p, hp0, hp⟩ := exists_singular_of_injective B W.subtype h
  exact ⟨p, p.2, fun h0 => hp0 (Subtype.ext h0), hp⟩

omit [DecidableEq ι] in
theorem exists_two_singular [Finite K] (G : Good B) {W : Submodule K (ι → K)} (h : 5 ≤ finrank K W) :
    ∃ a b : ι → K, a ∈ W ∧ b ∈ W ∧ B a a = 0 ∧ B b b = 0 ∧ B a b = 0 ∧
      ∀ r t : K, r • a + t • b = 0 → r = 0 ∧ t = 0 := by
  obtain ⟨a, haW, ha0, haa⟩ := exists_singular_mem (B := B) (W := W) (by omega)
  obtain ⟨y, hy⟩ := G.exists_dual ha0
  let T : W →ₗ[K] K × K := ((B a).comp W.subtype).prod ((B y).comp W.subtype)
  have hrank := LinearMap.finrank_range_add_finrank_ker T
  have h1 : finrank K (LinearMap.range T) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range T)
    simpa using this
  have h3 : 3 ≤ finrank K (LinearMap.ker T) := by omega
  obtain ⟨p, hp0, hp⟩ := exists_singular_of_injective (P := LinearMap.ker T) B (W.subtype ∘ₗ (LinearMap.ker T).subtype) h3
  have hpT : T (p : W) = 0 := p.2
  have hT1 : B a ((p : W) : ι → K) = 0 := by
    have := congrArg Prod.fst hpT
    exact this
  have hT2 : B y ((p : W) : ι → K) = 0 := by
    have := congrArg Prod.snd hpT
    exact this
  refine ⟨a, ((p : W) : ι → K), haW, (p : W).2, haa, by simpa using hp, hT1, ?_⟩
  have hb0 : ((p : W) : ι → K) ≠ 0 := by
    intro h0
    apply hp0
    apply Subtype.ext
    apply Subtype.ext
    exact h0
  intro r t hrt
  have h4 := congrArg (fun v => B y v) hrt
  simp only [map_add, map_smul, smul_eq_mul, map_zero] at h4
  have hya : B y a = 1 := by rw [G.symm]; exact hy
  rw [hya, hT2] at h4
  have hr : r = 0 := by simpa using h4
  rw [hr, zero_smul, zero_add] at hrt
  exact ⟨hr, (smul_eq_zero.mp hrt).resolve_right hb0⟩

variable [CharP K 5] [Finite K]

omit [Finite K] in
theorem four_eq_neg_one : (2 : K) * 2 = -1 := by
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  linear_combination h5

theorem orth_core (G : Good B) (hD : 7 ≤ Fintype.card ι)
    (z : StatedProj (omegaGroup B)) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    (∃ Φ : C55 →* StatedProj (omegaGroup B), Function.Injective Φ ∧
      ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹) ∨
    (∃ X Y : StatedProj (omegaGroup B), X ^ 5 = 1 ∧ Y ^ 5 = 1 ∧ Commute ⁅Y, X⁆ X ∧
      Commute ⁅Y, X⁆ Y ∧ ⁅Y, X⁆ ≠ 1 ∧ z * X * z⁻¹ = X⁻¹) := by
  have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨⟨M, hMΩ⟩, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨c, hc, hM⟩ := scalar_sq_of_mk_sq (⟨M, hMΩ⟩ : omegaGroup B) hz2
  have hnon := not_scalar_of_mk_ne_one (⟨M, hMΩ⟩ : omegaGroup B) hz1
  have hMG : M ∈ isomGroup B := omegaGroup_le B hMΩ
  have hiso : ∀ x y, B ((M : Matrix ι ι K) *ᵥ x) ((M : Matrix ι ι K) *ᵥ y) = B x y := hMG
  set Mm : Matrix ι ι K := (M : Matrix ι ι K) with hMm
  have hM' : Mm * Mm = c • 1 := hM
  have hc2 : c * c = 1 := by
    obtain ⟨i⟩ := hne
    obtain ⟨y, hy⟩ : ∃ y, B (Pi.single i 1) y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have := G.nd _ hcon
      have h1 := congrFun this i
      simp at h1
    have h1 := hiso (Mm *ᵥ Pi.single i 1) (Mm *ᵥ y)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM', Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.one_mulVec] at h1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    have h2 : (c * c - 1) * B (Pi.single i 1) y = 0 := by
      have := hiso (Pi.single i 1) y
      linear_combination h1 + this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hy)
  have hm1 : (-1 : K) ≠ 1 := by
    intro h
    apply G.two
    linear_combination -h
  have hMmem : ∀ {s : K} {x : ι → K}, x ∈ eigSp Mm s → Mm *ᵥ x = s • x := fun h => mem_eigSp.mp h
  have caseA : ∀ s : K, s * s = 1 → 3 ≤ finrank K (eigSp Mm s) → 2 ≤ finrank K (eigSp Mm (-s)) →
      (∃ Φ : C55 →* StatedProj (omegaGroup B), Function.Injective Φ ∧
        ∀ u : C55, QuotientGroup.mk (⟨M, hMΩ⟩ : omegaGroup B) * Φ u *
          (QuotientGroup.mk (⟨M, hMΩ⟩ : omegaGroup B))⁻¹ = (Φ u)⁻¹) := by
    intro s hss h3 h2
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hss
      simp at hss
    obtain ⟨a, haW, ha0, haa⟩ := exists_singular_mem (B := B) (W := eigSp Mm s) h3
    obtain ⟨w₁, w₂, hw₁, hw₂, hw⟩ := exists_indep_two (W := eigSp Mm (-s)) h2
    have hst : s * -s ≠ 1 := by rw [mul_neg, hss]; exact hm1
    have haw₁ : B a w₁ = 0 := eig_orth hiso hst haW hw₁
    have haw₂ : B a w₂ = 0 := eig_orth hiso hst haW hw₂
    have hind : ∀ r t₁ t₂ : K, r • a + t₁ • w₁ + t₂ • w₂ = 0 → r = 0 ∧ t₁ = 0 ∧ t₂ = 0 := by
      intro r t₁ t₂ h
      have hu : t₁ • w₁ + t₂ • w₂ ∈ eigSp Mm (-s) :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ hw₁) (Submodule.smul_mem _ _ hw₂)
      have hv : r • a ∈ eigSp Mm s := Submodule.smul_mem _ _ haW
      have hv' : r • a ∈ eigSp Mm (-s) := by
        have : r • a = -(t₁ • w₁ + t₂ • w₂) := by
          rw [add_assoc] at h
          exact eq_neg_of_add_eq_zero_left h
        rw [this]
        exact Submodule.neg_mem _ hu
      have h0 := eig_disjoint G.two hs0 hv hv'
      have hr : r = 0 := (smul_eq_zero.mp h0).resolve_right ha0
      rw [hr, zero_smul, zero_add] at h
      obtain ⟨h1, h2⟩ := hw t₁ t₂ h
      exact ⟨hr, h1, h2⟩
    exact c55_case G hMΩ (lam := s) (mu := -s) (by rw [mul_neg, hss]) haa haw₁ haw₂ hind
      (hMmem haW) (hMmem hw₁) (hMmem hw₂)
  have caseNeg : ∀ t : K, t * t = -1 → 3 ≤ finrank K (eigSp Mm t) →
      (∃ Φ : C55 →* StatedProj (omegaGroup B), Function.Injective Φ ∧
        ∀ u : C55, QuotientGroup.mk (⟨M, hMΩ⟩ : omegaGroup B) * Φ u *
          (QuotientGroup.mk (⟨M, hMΩ⟩ : omegaGroup B))⁻¹ = (Φ u)⁻¹) := by
    intro t htt h3
    obtain ⟨a, w₁, w₂, ha, hw₁, hw₂, hind⟩ := exists_indep_three (W := eigSp Mm t) h3
    have hst : t * t ≠ 1 := by rw [htt]; exact hm1
    exact c55_case G hMΩ (lam := t) (mu := t) htt (eig_orth hiso hst ha ha)
      (eig_orth hiso hst ha hw₁) (eig_orth hiso hst ha hw₂) hind (hMmem ha) (hMmem hw₁)
      (hMmem hw₂)
  have caseB : ∀ s : K, s * s = 1 → eigSp Mm s ⊔ eigSp Mm (-s) = ⊤ →
      5 ≤ finrank K (eigSp Mm s) → finrank K (eigSp Mm (-s)) = 1 →
      (∃ X' Y' : StatedProj (omegaGroup B), X' ^ 5 = 1 ∧ Y' ^ 5 = 1 ∧ Commute ⁅Y', X'⁆ X' ∧
        Commute ⁅Y', X'⁆ Y' ∧ ⁅Y', X'⁆ ≠ 1 ∧
        (QuotientGroup.mk (⟨M, hMΩ⟩ : omegaGroup B) : StatedProj (omegaGroup B)) * X' *
          (QuotientGroup.mk (⟨M, hMΩ⟩ : omegaGroup B))⁻¹ = X'⁻¹) := by
    intro s hss hsup h5 h1
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hss
      simp at hss
    obtain ⟨a, b, haW, hbW, haa, hbb, hab, hind⟩ := exists_two_singular G (W := eigSp Mm s) h5
    obtain ⟨⟨e, heW⟩, he0, hespan⟩ := finrank_eq_one_iff'.mp h1
    have he0' : e ≠ 0 := fun h => he0 (Subtype.ext h)
    have hst : -s * s ≠ 1 := by rw [neg_mul, hss]; exact hm1
    have hst' : s * -s ≠ 1 := by rw [mul_neg, hss]; exact hm1
    have hae : B a e = 0 := eig_orth hiso hst' haW heW
    have hbe : B b e = 0 := eig_orth hiso hst' hbW heW
    have hee : B e e ≠ 0 := by
      intro hee0
      apply he0'
      apply G.nd
      intro y
      have hy : y ∈ eigSp Mm s ⊔ eigSp Mm (-s) := by rw [hsup]; trivial
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨t, ht⟩ := hespan ⟨y₂, hy₂⟩
      have ht' : t • e = y₂ := congrArg Subtype.val ht
      rw [map_add, eig_orth hiso hst heW hy₁, ← ht']
      simp [hee0]
    exact heis_case G hMΩ (lam := s) (mu := -s) (by rw [mul_neg, hss]) haa hbb hab hae hbe hee
      hind (hMmem haW) (hMmem heW)
  rcases mul_self_eq_one_iff.mp hc2 with rfl | rfl
  ·
    have hsup := eigSp_sup_eq_top (A := Mm) (c := 1) hM' (s := 1) (by simp) G.two one_ne_zero
    have hdim := card_le_finrank_add hsup
    have hp1 : 1 ≤ finrank K (eigSp Mm 1) := by
      by_contra hcon
      have h0 : finrank K (eigSp Mm 1) = 0 := by omega
      have hbot : eigSp Mm 1 = ⊥ := Submodule.finrank_eq_zero.mp h0
      rw [hbot, bot_sup_eq] at hsup
      exact hnon (-1) (eigSp_top hsup)
    have hm1' : 1 ≤ finrank K (eigSp Mm (-1)) := by
      by_contra hcon
      have h0 : finrank K (eigSp Mm (-1)) = 0 := by omega
      have hbot : eigSp Mm (-1) = ⊥ := Submodule.finrank_eq_zero.mp h0
      rw [hbot, sup_bot_eq] at hsup
      exact hnon 1 (eigSp_top hsup)
    by_cases hA1 : 3 ≤ finrank K (eigSp Mm 1) ∧ 2 ≤ finrank K (eigSp Mm (-1))
    · exact Or.inl (caseA 1 (by simp) hA1.1 hA1.2)
    by_cases hA2 : 3 ≤ finrank K (eigSp Mm (-1)) ∧ 2 ≤ finrank K (eigSp Mm 1)
    · refine Or.inl (caseA (-1) (by simp) hA2.1 ?_)
      rw [neg_neg]; exact hA2.2
    by_cases hB1 : 3 ≤ finrank K (eigSp Mm 1)
    · refine Or.inr (caseB 1 (by simp) hsup (by omega) (by omega))
    · have hsup' : eigSp Mm (-1) ⊔ eigSp Mm (-(-1)) = ⊤ := by
        rw [neg_neg, sup_comm]; exact hsup
      refine Or.inr (caseB (-1) (by simp) hsup' (by omega) ?_)
      rw [neg_neg]; omega
  ·
    have hsup := eigSp_sup_eq_top (A := Mm) (c := -1) hM' (s := 2) four_eq_neg_one G.two G.two
    have hdim := card_le_finrank_add hsup
    by_cases h2 : 3 ≤ finrank K (eigSp Mm 2)
    · exact Or.inl (caseNeg 2 four_eq_neg_one h2)
    · refine Or.inl (caseNeg (-2) (by rw [neg_mul_neg]; exact four_eq_neg_one) (by omega))

end Eig

end CFSG.HardMathSupport.Foote.ModuleExclusions
