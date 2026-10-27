module

public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.ClassicalGroups.Alternating.TransvectionGeneration
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem Tsp_mul_Tsp (hBN : BN.IsAlt) (x : N) (c d : K) :
    Tsp hBN x c * Tsp hBN x d = Tsp hBN x (c + d) :=
  Subtype.ext (symplecticTransvection_mul hBN x c d)

theorem Tsp_smul (hBN : BN.IsAlt) (c : K) (x : N) (d : K) :
    Tsp hBN (c • x) d = Tsp hBN x (c ^ 2 * d) :=
  Subtype.ext (SteinbergBQ.symplecticTransvection_smul hBN c x d)

theorem Tsp_conj (hBN : BN.IsAlt) (g : Gsp BN) (x : N) (c : K) :
    g * Tsp hBN x c * g⁻¹ = Tsp hBN (g.app x) c := by
  refine Subtype.ext ?_
  have h := SteinbergBQ.symplecticTransvection_conj hBN
    (g := (g : LinearMap.GeneralLinearGroup K N)) (fun x y => g.2 x y) x c
  simpa only [Tsp, Subgroup.coe_mul, Subgroup.coe_inv, Gsp.app] using h

theorem Tsp_comm (hBN : BN.IsAlt) {x y : N} (hxy : BN x y = 0) (c d : K) :
    Tsp hBN x c * Tsp hBN y d = Tsp hBN y d * Tsp hBN x c :=
  Subtype.ext (symplecticTransvection_comm hBN hxy c d)

theorem Tsp_eq_one_iff (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) (x : N) (c : K) :
    Tsp hBN x c = 1 ↔ x = 0 ∨ c = 0 := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    refine Or.inr ?_
    obtain ⟨z, hz⟩ : ∃ z, BN z x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (hBNnd.2 x hcon)
    have h1 : (Tsp hBN x c).app z = z := by rw [h]; rfl
    rw [Tsp_app, add_eq_left] at h1
    exact (mul_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hx)).resolve_right hz
  · rintro (rfl | rfl)
    · refine Gsp.ext' fun z => ?_
      rw [Tsp_app, map_zero, smul_zero, add_zero]
      rfl
    · exact Subtype.ext (symplecticTransvection_zero hBN x)

theorem Tsp_injective_one [CharP K 2] (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) {x y : N}
    (h : Tsp hBN x 1 = Tsp hBN y 1) : x = y := by
  have hex : ∀ w : N, w ≠ 0 → ∃ z, BN z w ≠ 0 := fun w hw => by
    by_contra hcon
    push Not at hcon
    exact hw (hBNnd.2 w hcon)
  have hz : ∀ z, BN z x • x = BN z y • y := fun z => by
    have := congrArg (fun g : Gsp BN => g.app z) h
    simpa only [Tsp_app, one_mul, add_right_inj] using this
  by_cases hx : x = 0
  · subst hx
    have : Tsp hBN y 1 = 1 := by
      rw [← h]
      exact (Tsp_eq_one_iff hBN hBNnd 0 1).mpr (Or.inl rfl)
    rcases (Tsp_eq_one_iff hBN hBNnd y 1).mp this with hy | hy
    · exact hy.symm
    · exact absurd hy one_ne_zero
  have hy : y ≠ 0 := by
    rintro rfl
    have : Tsp hBN x 1 = 1 := by
      rw [h]
      exact (Tsp_eq_one_iff hBN hBNnd 0 1).mpr (Or.inl rfl)
    rcases (Tsp_eq_one_iff hBN hBNnd x 1).mp this with hx' | hx'
    · exact hx hx'
    · exact absurd hx' one_ne_zero
  obtain ⟨z₀, hz₀⟩ := hex x hx
  obtain ⟨z₁, hz₁⟩ := hex y hy
  set s : K := (BN z₀ x)⁻¹ * BN z₀ y with hs
  have hxs : x = s • y := by
    have := congrArg ((BN z₀ x)⁻¹ • ·) (hz z₀)
    simpa only [smul_smul, inv_mul_cancel₀ hz₀, one_smul, hs] using this
  have hss : s ^ 2 = 1 := by
    have h1 := hz z₁
    simp only [hxs, map_smul, smul_eq_mul, smul_smul] at h1
    have h2 : (s * BN z₁ y * s - BN z₁ y) • y = 0 := by
      rw [sub_smul, h1, sub_self]
    have h3 := (smul_eq_zero.mp h2).resolve_right hy
    have h4 : (s ^ 2 - 1) * BN z₁ y = 0 := by linear_combination h3
    have h5 := (mul_eq_zero.mp h4).resolve_right hz₁
    linear_combination h5
  have hs1 : s = 1 := CharTwo.sq_inj.mp (by rw [hss, one_pow])
  rw [hxs, hs1, one_smul]

theorem exists_gsp_conj_Tsp_eq [Finite K] [CharP K 2] (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) {u v : N} (hu : u ≠ 0) (hv : v ≠ 0) {c d : K} (hc : c ≠ 0)
    (hd : d ≠ 0) : ∃ g : Gsp BN, g * Tsp hBN u c * g⁻¹ = Tsp hBN v d := by
  obtain ⟨r₁, hr₁⟩ := isSquare_of_charTwo' c
  obtain ⟨r₂, hr₂⟩ := isSquare_of_charTwo' d
  have hr₁0 : r₁ ≠ 0 := by
    rintro rfl
    exact hc (by rw [hr₁, mul_zero])
  have hr₂0 : r₂ ≠ 0 := by
    rintro rfl
    exact hd (by rw [hr₂, mul_zero])
  obtain ⟨g, hg⟩ := CFSG.ClassicalGroups.Symplectic.exists_gsp_apply_eq hBN hBNnd
    (smul_ne_zero hr₁0 hu) (smul_ne_zero hr₂0 hv)
  refine ⟨g, ?_⟩
  have e1 : Tsp hBN u c = Tsp hBN (r₁ • u) 1 := by
    rw [Tsp_smul, mul_one, hr₁, sq]
  have e2 : Tsp hBN v d = Tsp hBN (r₂ • v) 1 := by
    rw [Tsp_smul, mul_one, hr₂, sq]
  rw [e1, e2, Tsp_conj, hg]

theorem app_Tsp_mul_Tsp_mul_Tsp_left (hBN : BN.IsAlt) {a b : N} {α l : K}
    (h : α * l * BN a b ^ 2 = 1) :
    (Tsp hBN a α * Tsp hBN b l * Tsp hBN a α).app a = (l * BN a b) • b := by
  have hba : BN b a = -BN a b := (hBN.neg_eq a b).symm
  rw [Gsp.app_mul, Gsp.app_mul, Tsp_app hBN a α a, Tsp_app hBN b l, Tsp_app hBN a α]
  simp only [hBN.self_eq_zero, mul_zero, zero_smul, add_zero, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hba]
  linear_combination (norm := module) (-1 : K) • (h • a)

theorem Tsp_mul_Tsp_mul_Tsp_conj (hBN : BN.IsAlt) {a b : N} {α l : K}
    (h : α * l * BN a b ^ 2 = 1) (c : K) :
    (Tsp hBN a α * Tsp hBN b l * Tsp hBN a α) * Tsp hBN a c *
      (Tsp hBN a α * Tsp hBN b l * Tsp hBN a α)⁻¹ = Tsp hBN b ((l * BN a b) ^ 2 * c) := by
  rw [Tsp_conj, app_Tsp_mul_Tsp_mul_Tsp_left hBN h, Tsp_smul]

end CFSG.ClassicalGroups.Alternating
