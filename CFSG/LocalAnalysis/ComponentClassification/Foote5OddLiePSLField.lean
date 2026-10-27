module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLInner
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLTools

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBLinearSemilinear
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

abbrev fixedSL (n : ℕ) (K : Type) [Field K] (σ : K ≃+* K) : Subgroup SL(n, K) :=
  CFSG.ClassicalInvolution.Balance.fixedGroup (slFieldAut (Fin n) K σ)

theorem mem_fixedSL_iff {σ : K ≃+* K} {x : SL(n, K)} :
    x ∈ fixedSL n K σ ↔ ∀ i j, σ (x i j) = x i j := by
  rw [CFSG.ClassicalInvolution.Balance.mem_fixedGroup]
  constructor
  · intro h i j
    have := congrArg (fun y : SL(n, K) => y i j) h
    exact this
  · intro h
    ext i j
    exact h i j

theorem fixedSL_eq_range (σ : K ≃+* K) :
    fixedSL n K σ = (SpecialLinearGroup.map (fixedField K σ).subtype).range := by
  ext x
  rw [mem_fixedSL_iff]
  constructor
  · intro h
    let y : Matrix (Fin n) (Fin n) (fixedField K σ) := fun i j =>
      ⟨x i j, (mem_fixedField K σ _).mpr (h i j)⟩
    have hy : (fixedField K σ).subtype.mapMatrix y = (x : Matrix (Fin n) (Fin n) K) := by
      ext i j
      rfl
    have hdet : y.det = 1 := by
      apply (fixedField K σ).subtype.injective
      rw [map_one, RingHom.map_det, hy, x.2]
    exact ⟨⟨y, hdet⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩ i j
    exact fixedField_coe K σ _

theorem isQuasisimple_fixedSL (hn : 3 ≤ n) (σ : K ≃+* K) :
    Open.IsQuasisimple (fixedSL n K σ) := by
  have hinj : Function.Injective (SpecialLinearGroup.map (n := Fin n)
      (fixedField K σ).subtype) := by
    intro a b h
    ext i j
    have := congrArg (fun y : SL(n, K) => y i j) h
    have h2 := (fixedField K σ).subtype.injective this
    exact congrArg Subtype.val h2
  have e : SL(n, fixedField K σ) ≃* fixedSL n K σ :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (fixedSL_eq_range σ).symm)
  have hq : CFSG.IsQuasisimple SL(n, fixedField K σ) :=
    CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup hn
  have hq' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  exact (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
    ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq')

theorem pslFieldAut_conj (σ : K ≃+* K) (y : SL(n, K)) :
    pslFieldAut (Fin n) K σ * psi n K y * (pslFieldAut (Fin n) K σ)⁻¹ =
      psi n K (slFieldAut (Fin n) K σ y) := by
  rw [psi_apply, psi_apply, ← conj_apply_eq]
  rfl

theorem transvection_mem_fixedSL {σ : K ≃+* K} {i j : Fin n} (hij : i ≠ j) {t : K}
    (ht : σ t = t) : SpecialLinearGroup.transvection hij t ∈ fixedSL n K σ := by
  rw [mem_fixedSL_iff]
  intro a b
  rw [CFSG.ClassicalInvolution.RouteD.Gaps.coe_transvection_eq]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp [ht]

theorem innerDiagonalAction_scalar (c : Kˣ) :
    innerDiagonalAction n K (GeneralLinearGroup.scalar (Fin n) c) = 1 := by
  rw [innerDiagonalAction_eq_pglAction, ProjGenLinGroup.mk_eq_one.mpr (by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩), map_one]

theorem eq_one_field [Finite K] (hn : 3 ≤ n)
    (hZ : center (ProjectiveSpecialLinearGroup (Fin n) K) = ⊥) (h2 : (2 : K) ≠ 0)
    (σ : K ≃+* K) (hσ : σ ≠ 1) (hσ2 : σ * σ = 1)
    {R : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) K))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * pslFieldAut (Fin n) K σ = pslFieldAut (Fin n) K σ * r)
    (hRc : ∀ s, pslFieldAut (Fin n) K σ s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r ∈ R, r = 1 := by
  have := psi_range_normal (n := n) (k := K)
  set fσ := pslFieldAut (Fin n) K σ with hfσ
  set Z := center SL(n, K) with hZdef
  have hQ0 : Open.IsComponentOf (fixedSL n K σ)
      (CFSG.ClassicalInvolution.Balance.fixedGroup (slFieldAut (Fin n) K σ)) :=
    ⟨le_rfl, Open.IsSubnormal.refl _, isQuasisimple_fixedSL hn σ⟩
  have hQ := CFSG.ClassicalInvolution.Balance.isComponentOf_map_centralizer (psi_ker hZ) 1 fσ
    (slFieldAut (Fin n) K σ) (fun y => by simpa using pslFieldAut_conj σ y) hQ0
  have e : (MulAut.conj (1 : SL(n, K))).toMonoidHom = MonoidHom.id _ := by
    ext; simp
  rw [e, MonoidHom.comp_id] at hQ
  have hRconj : ∀ s ∈ (psi n K).range ⊓ centralizer ({fσ} : Set _), Odd (orderOf s) →
      ∀ r ∈ R, s * r * s⁻¹ ∈ R := by
    intro s hs hso r hr
    rw [psi_surjective_range] at hs
    exact conj_mem_of_mem_range hZ hRc hs hso hr
  intro r hr
  have hfix : ∀ x ∈ fixedSL n K σ, r (QuotientGroup.mk' Z x) = QuotientGroup.mk' Z x := by
    intro x hx
    have h1 := commute_of_isComponentOf (L := (psi n K).range) hRodd hRi hRconj hQ hr
      ⟨x, hx, rfl⟩
    apply conj_injective hZ
    rw [conj_apply_eq, ← psi_apply]
    calc r * psi n K x * r⁻¹ = psi n K x * r * r⁻¹ := by rw [h1]
      _ = psi n K x := by group
  have hodd : Odd (orderOf r) := by
    have h := orderOf_dvd_natCard (⟨r, hr⟩ : R)
    rw [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat hRodd h
  obtain ⟨B, ρ, rfl⟩ := exists_semilinear_of_odd hn hodd
  have hperf : commutator (fixedSL n K σ) = ⊤ := (isQuasisimple_fixedSL hn σ).1
  have hsl := fun x hx => eq_of_fix_perfect hperf hfix (x := x) hx
  have htr : ∀ (i j : Fin n) (hij : i ≠ j) (t : K), σ t = t →
      B.val * (1 + Matrix.single i j (ρ t)) = (1 + Matrix.single i j t) * B.val := by
    intro i j hij t ht
    have h1 := congrArg (fun y : SL(n, K) => (y : Matrix (Fin n) (Fin n) K))
      (hsl _ (transvection_mem_fixedSL hij ht))
    simp only [slSemilinearAction_matrix, CFSG.ClassicalInvolution.RouteD.Gaps.coe_transvection_eq]
      at h1
    have h3 : ρ.toRingHom.mapMatrix (1 + Matrix.single i j t) = 1 + Matrix.single i j (ρ t) := by
      rw [map_add, map_one]
      congr 1
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.single_apply]
      split_ifs <;> simp
    rw [h3] at h1
    calc B.val * (1 + Matrix.single i j (ρ t)) =
        B.val * (1 + Matrix.single i j (ρ t)) * ((B⁻¹).val * B.val) := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = (1 + Matrix.single i j t) * B.val := by rw [← Matrix.mul_assoc, h1]
  have hBs : B.val ∈ Set.range (Matrix.scalar (Fin n)) := by
    refine Matrix.mem_range_scalar_of_commute_single fun i j hij => ?_
    have h := htr i j hij 1 (map_one σ)
    rw [map_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact (add_left_cancel h).symm
  obtain ⟨c, hc⟩ := hBs
  have hc0 : c ≠ 0 := by
    intro h0
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have := congrArg Matrix.det hc
    rw [h0, map_zero, Matrix.det_zero] at this
    exact (B.isUnit.map Matrix.detMonoidHom).ne_zero this.symm
  have hB : B = GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0) := by
    ext a b
    rw [← hc]
    rfl
  have hρ : ∀ t, σ t = t → ρ t = t := by
    intro t ht
    have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have h := htr _ _ hij t ht
    rw [← hc, Matrix.scalar_apply] at h
    have h' := congrFun (congrFun h ⟨0, by omega⟩) ⟨1, by omega⟩
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h'
    simp only [Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.single_apply_same,
      zero_add] at h'
    exact mul_left_cancel₀ hc0 (h'.trans (mul_comm t c))
  obtain ⟨y₀, hy₀⟩ : ∃ y, σ y ≠ y := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  set θ := y₀ - σ y₀ with hθ
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : K ≃+* K => τ x) hσ2
    simpa using this
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, hσσ]; ring
  have hθ0 : θ ≠ 0 := fun h => hy₀ (by rw [hθ, sub_eq_zero] at h; exact h.symm)
  have hθ2 : ρ (θ * θ) = θ * θ := hρ _ (by rw [map_mul, hσθ]; ring)
  have hρθ : ρ (ρ θ) = θ := by
    have hsq : (ρ θ - θ) * (ρ θ + θ) = 0 := by
      have := hθ2
      rw [map_mul] at this
      linear_combination this
    rcases mul_eq_zero.mp hsq with h | h
    · rw [sub_eq_zero.mp h, sub_eq_zero.mp h]
    · have h1 : ρ θ = -θ := by linear_combination h
      rw [h1, map_neg, h1, neg_neg]
  have hρ2 : ρ * ρ = 1 := by
    refine RingEquiv.ext fun y => ?_
    set a := (y + σ y) / 2 with ha
    set b := (y - σ y) / (2 * θ) with hb
    have hya : y = a + b * θ := by
      rw [ha, hb]
      field_simp
      ring
    have hσa : σ a = a := by
      rw [ha, map_div₀, map_add, hσσ, map_ofNat]
      ring
    have hσb : σ b = b := by
      rw [hb, map_div₀, map_sub, hσσ, map_mul, hσθ, map_ofNat]
      field_simp
      ring
    change ρ (ρ y) = y
    rw [hya, map_add, map_add, map_mul, map_mul, hρ a hσa, hρ a hσa, hρ b hσb, hρ b hσb, hρθ]
  have hr2 : semilinearAction n K B ρ ^ 2 = 1 := by
    rw [sq, semilinearAction, hB, innerDiagonalAction_scalar, one_mul, ← map_mul, hρ2, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hr2
  have h1 : orderOf (semilinearAction n K B ρ) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

end CFSG.ComponentClassification.Foote5.OddLieCore
