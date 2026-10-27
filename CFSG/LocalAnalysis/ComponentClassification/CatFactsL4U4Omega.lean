module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Irr
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Module Matrix CFSG.Assembly.LowTwoRank

variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
theorem sq_eq_one_of_smul_isometry {V : Type*} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) {x₀ y₀ : V} (h₀ : B x₀ y₀ ≠ 0) {a : F}
    (ha : B (a • x₀) (a • y₀) = B x₀ y₀) : a ^ 2 = 1 := by
  have h := ha
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have h2 : (a ^ 2 - 1) * B x₀ y₀ = 0 := by linear_combination h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right h₀)

theorem eq_one_or_eq_neg_one_of_proj_commute {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {s e : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (he : 1 ≤ e)
    (hq : Odd (Fintype.card F)) (hsq : s ∣ Fintype.card F ^ 2 ^ e + 1)
    (hdim : finrank F V ≤ 2 ^ (e + 1)) (B : LinearMap.BilinForm F V)
    (hB : ∀ y, (∀ x, B x y = 0) → y = 0) {g k : Module.End F V} {a c d : F}
    (hgs : g ^ s = a • 1) (hg1 : ∀ t : F, g ≠ t • 1)
    (hgB : ∀ x y, B (g x) (g y) = B x y) (hkB : ∀ x y, B (k x) (k y) = B x y)
    (hgk : g * k = d • (k * g)) (hk2 : k * k = c • 1) : k = 1 ∨ k = -1 := by
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact hg1 0 (LinearMap.ext fun v => Subsingleton.elim _ _)
  obtain ⟨y₀, hy₀⟩ := exists_ne (0 : V)
  obtain ⟨x₀, h₀⟩ : ∃ x, B x y₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hy₀ (hB y₀ h)
  have hpowB : ∀ (n : ℕ) (x y : V), B ((g ^ n) x) ((g ^ n) y) = B x y := by
    intro n
    induction n with
    | zero => intro x y; rfl
    | succ n ih =>
      intro x y
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hgB]
  have ha2 : a ^ 2 = 1 := sq_eq_one_of_smul_isometry B h₀ (by
    have := hpowB s x₀ y₀
    rwa [hgs, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.one_apply] at this)
  have hkg₀ : B (k (g x₀)) (k (g y₀)) = B x₀ y₀ := by rw [hkB, hgB]
  have hd2 : d ^ 2 = 1 := sq_eq_one_of_smul_isometry B (hkg₀.symm ▸ h₀) (by
    have h1 : B ((g * k) x₀) ((g * k) y₀) = B x₀ y₀ := by
      rw [Module.End.mul_apply, Module.End.mul_apply, hgB, hkB]
    rw [hgk, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Module.End.mul_apply] at h1
    rw [h1, hkg₀])
  obtain ⟨m, hm⟩ := hs.odd_of_ne_two hs2
  set g₁ := a • g with hg₁
  have hg₁s : g₁ ^ s = 1 := by
    rw [hg₁, smul_pow, hgs, smul_smul, ← pow_succ, hm, show 2 * m + 1 + 1 = 2 * (m + 1) by ring,
      pow_mul, ha2, one_pow, one_smul]
  have hg₁k : g₁ * k = d • (k * g₁) := by
    rw [hg₁, smul_mul_assoc, hgk, mul_smul_comm, smul_comm]
  have hg₁B : ∀ x y, B (g₁ x) (g₁ y) = B x y := by
    intro x y
    simp only [hg₁, LinearMap.smul_apply, map_smul, smul_eq_mul, hgB]
    rw [← mul_assoc, ← sq, ha2, one_mul]
  set g₂ := g₁ * g₁ with hg₂
  have hg₂k : Commute g₂ k := by
    change g₁ * g₁ * k = k * (g₁ * g₁)
    rw [mul_assoc, hg₁k, mul_smul_comm, ← mul_assoc, hg₁k, smul_mul_assoc, smul_smul, ← sq, hd2,
      one_smul, mul_assoc]
  have hg₂s : g₂ ^ s = 1 := by
    rw [hg₂, ← sq, ← pow_mul, mul_comm, pow_mul, hg₁s, one_pow]
  have hg₂1 : g₂ ≠ 1 := by
    intro h1
    have hg₁1 : g₁ = 1 := by
      have : g₁ ^ s = g₁ := by
        rw [hm, pow_succ, pow_mul, sq, ← hg₂, h1, one_pow, one_mul]
      rw [← this, hg₁s]
    apply hg1 a
    have : a • g₁ = g := by rw [hg₁, smul_smul, ← sq, ha2, one_smul]
    rw [← this, hg₁1]
  have hg₂B : ∀ x y, B (g₂ x) (g₂ y) = B x y := by
    intro x y
    rw [hg₂, Module.End.mul_apply, Module.End.mul_apply, hg₁B, hg₁B]
  exact eq_one_or_eq_neg_one_of_isometry hs hs2 he hq hsq hdim B hB hg₂s hg₂1 hg₂B hkB hg₂k hk2

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Fintype K]

theorem commutator_le_self' {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

omit [Fintype K] in
theorem isometry_of_mem_statedOmega (Q : QuadraticForm K (ι → K)) {A : GL ι K}
    (hA : A ∈ StatedOmega ⇑Q) (v : ι → K) : Q ((A : Matrix ι ι K) *ᵥ v) = Q v := by
  let I : Subgroup (GL ι K) :=
    { carrier := {A | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}
      one_mem' := fun v => by simp
      mul_mem' := fun {A B} hA hB v => by
        rw [Set.mem_ofPred_eq] at hA hB
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
      inv_mem' := fun {A} hA v => by
        rw [Set.mem_ofPred_eq] at hA
        rw [← hA, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec] }
  have hle : Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} ≤ I :=
    (Subgroup.closure_le I).2 fun A hA => hA
  exact hle (commutator_le_self' _ hA) v

@[expose] noncomputable def glEnd : GL ι K →* Module.End K (ι → K) where
  toFun A := Matrix.toLin' (A : Matrix ι ι K)
  map_one' := by rw [Units.val_one, Matrix.toLin'_one]; rfl
  map_mul' A B := by rw [Units.val_mul, Matrix.toLin'_mul]; rfl

omit [Fintype K] in
theorem glEnd_apply (A : GL ι K) (v : ι → K) : glEnd A v = (A : Matrix ι ι K) *ᵥ v := rfl

omit [Fintype K] in
theorem glEnd_scalar (c : Kˣ) :
    glEnd (Matrix.GeneralLinearGroup.scalar ι c) = (c : K) • (1 : Module.End K (ι → K)) := by
  refine LinearMap.ext fun v => ?_
  rw [glEnd_apply, Matrix.GeneralLinearGroup.coe_scalar, LinearMap.smul_apply,
    Module.End.one_apply, Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  simp

omit [Fintype K] in
theorem mem_statedScalars_of_glEnd {A : GL ι K} {t : K} (hA : glEnd A = t • 1) :
    A ∈ StatedScalars ι K := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨1, Units.ext (Matrix.ext fun i => isEmptyElim i)⟩
  have ht : t ≠ 0 := by
    rintro rfl
    have h1 := congrArg (fun f : Module.End K (ι → K) => f (Pi.single i₀ 1)) hA
    simp only [zero_smul, LinearMap.zero_apply] at h1
    have h2 : glEnd A⁻¹ (glEnd A (Pi.single i₀ 1)) = Pi.single i₀ 1 := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [h1, map_zero] at h2
    have h3 := congrFun h2 i₀
    simp at h3
  refine ⟨Units.mk0 t ht, ?_⟩
  apply glEnd_injective
  rw [glEnd_scalar, Units.val_mk0, hA]
where
  glEnd_injective : Function.Injective (glEnd : GL ι K →* Module.End K (ι → K)) := by
    intro A B hAB
    apply Units.ext
    exact Matrix.toLin'.injective hAB

theorem false_of_proj_commute (Q : QuadraticForm K (ι → K)) {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {s e : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (he : 1 ≤ e) (hq : Odd (Fintype.card K)) (hsq : s ∣ Fintype.card K ^ 2 ^ e + 1)
    (hdim : Fintype.card ι ≤ 2 ^ (e + 1)) (k y : StatedProj (StatedOmega Q₀)) (hk1 : k ≠ 1)
    (hk2 : k ^ 2 = 1) (hys : y ^ s = 1) (hy1 : y ≠ 1) (hky : k * y = y * k) : False := by
  subst hQ₀
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective k
  obtain ⟨G, rfl⟩ := QuotientGroup.mk_surjective y
  set B := QuadraticMap.polarBilin Q with hB
  have hiso : ∀ X : StatedOmega ⇑Q, ∀ x y : ι → K,
      B (glEnd (X : GL ι K) x) (glEnd (X : GL ι K) y) = B x y := by
    intro X x y
    simp only [hB, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, glEnd_apply,
      ← Matrix.mulVec_add, isometry_of_mem_statedOmega Q X.2]
  have hscal : ∀ X : StatedOmega ⇑Q, (QuotientGroup.mk X : StatedProj (StatedOmega ⇑Q)) = 1 →
      ∃ t : K, glEnd (X : GL ι K) = t • 1 := by
    intro X hX
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hX
    obtain ⟨c, hc⟩ := hX
    exact ⟨c, by rw [← hc, glEnd_scalar]⟩
  obtain ⟨c, hc⟩ := hscal (A ^ 2) (by rw [QuotientGroup.mk_pow, hk2])
  obtain ⟨a, ha⟩ := hscal (G ^ s) (by rw [QuotientGroup.mk_pow, hys])
  obtain ⟨d, hd⟩ := hscal ((A * G)⁻¹ * (G * A)) (by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      hky, inv_mul_cancel])
  have hdimV : finrank K (ι → K) ≤ 2 ^ (e + 1) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact hdim
  have hgk : glEnd (G : GL ι K) * glEnd (A : GL ι K) =
      d • (glEnd (A : GL ι K) * glEnd (G : GL ι K)) := by
    have h1 : (G * A : StatedOmega ⇑Q) = (A * G) * ((A * G)⁻¹ * (G * A)) := by group
    have h2 : glEnd ((G * A : StatedOmega ⇑Q) : GL ι K) =
        glEnd ((A * G : StatedOmega ⇑Q) : GL ι K) * (d • 1) := by
      rw [h1, Subgroup.coe_mul, map_mul, hd]
    rw [mul_smul_comm, mul_one] at h2
    simpa only [Subgroup.coe_mul, map_mul] using h2
  have hk2' : glEnd (A : GL ι K) * glEnd (A : GL ι K) = c • 1 := by
    rw [← map_mul, ← hc, ← Subgroup.coe_mul, ← sq]
  have hgs : glEnd (G : GL ι K) ^ s = a • 1 := by
    rw [← map_pow, ← ha, Subgroup.coe_pow]
  have hg1 : ∀ t : K, glEnd (G : GL ι K) ≠ t • 1 := by
    intro t ht
    apply hy1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact mem_statedScalars_of_glEnd ht
  rcases eq_one_or_eq_neg_one_of_proj_commute hs hs2 he hq hsq hdimV B hQ.2 hgs hg1
    (hiso G) (hiso A) hgk hk2' with h | h
  · apply hk1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact mem_statedScalars_of_glEnd (t := 1) (by rw [h, one_smul])
  · apply hk1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact mem_statedScalars_of_glEnd (t := -1) (LinearMap.ext fun v => by rw [h]; simp)

omit [Fintype K] in
theorem coe_quadMinus (n : ℕ) (b c : K) :
    ⇑(CFSG.LieType.Universal.Spin.quadMinus n K b c) = StatedQuadMinus n K b c := by
  funext v
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
  rfl

theorem false_of_omegaMinus_eight (hq : Odd (Fintype.card K)) {b c : K}
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hsq : s ∣ Fintype.card K ^ 4 + 1)
    (k y : StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) (hk1 : k ≠ 1) (hk2 : k ^ 2 = 1)
    (hys : y ^ s = 1) (hy1 : y ≠ 1) (hky : k * y = y * k) : False := by
  exact false_of_proj_commute _ (coe_quadMinus 4 b c)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 4 K hirr) hs hs2
    (e := 2) (by norm_num) hq (by simpa using hsq) (by simp) k y hk1 hk2 hys hy1 hky

end CFSG.ComponentClassification.CatFactsL4U4
