module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Dickson
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

section Schur

variable {K : Type*} [Field K]

theorem schur_sl2 (Φ : (Fin 2 → K) →+ (Fin 2 → K))
    (hΦ : ∀ (A : SL(2, K)) (v : Fin 2 → K),
      Φ ((A : Matrix (Fin 2) (Fin 2) K).mulVec v) = (A : Matrix (Fin 2) (Fin 2) K).mulVec (Φ v)) :
    ∃ c : K, ∀ v : Fin 2 → K, Φ v = fun i => c * v i := by
  let up : K → SL(2, K) := fun s => ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩
  let lo : K → SL(2, K) := fun s => ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two]⟩
  have hup : ∀ (s x y : K), (up s : Matrix (Fin 2) (Fin 2) K).mulVec ![x, y] = ![x + s * y, y] := by
    intro s x y
    ext i
    fin_cases i <;> simp [up, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hlo : ∀ (s x y : K), (lo s : Matrix (Fin 2) (Fin 2) K).mulVec ![x, y] = ![x, s * x + y] := by
    intro s x y
    ext i
    fin_cases i <;> simp [lo, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hsplit : ∀ x y : K, Φ ![x, y] = Φ ![x, 0] + Φ ![0, y] := by
    intro x y
    rw [← map_add]
    congr 1
    ext i; fin_cases i <;> simp
  have h1 : ∀ s x y : K, Φ ![x + s * y, y] 0 = Φ ![x, y] 0 + s * Φ ![x, y] 1 := by
    intro s x y
    have := hΦ (up s) ![x, y]
    rw [hup] at this
    have h0 := congrFun this 0
    simpa [up, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  have h2 : ∀ s x y : K, Φ ![x + s * y, y] 1 = Φ ![x, y] 1 := by
    intro s x y
    have := hΦ (up s) ![x, y]
    rw [hup] at this
    have h0 := congrFun this 1
    simpa [up, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  have h3 : ∀ s x y : K, Φ ![x, s * x + y] 0 = Φ ![x, y] 0 := by
    intro s x y
    have := hΦ (lo s) ![x, y]
    rw [hlo] at this
    have h0 := congrFun this 0
    simpa [lo, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  have h4 : ∀ s x y : K, Φ ![x, s * x + y] 1 = s * Φ ![x, y] 0 + Φ ![x, y] 1 := by
    intro s x y
    have := hΦ (lo s) ![x, y]
    rw [hlo] at this
    have h0 := congrFun this 1
    simpa [lo, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  set c := Φ ![0, 1] 1 with hc
  have hq10 : ∀ x : K, Φ ![x, 0] 1 = 0 := by
    intro x
    have hs := hsplit x 1
    have : Φ ![x, 1] 1 = Φ ![0, 1] 1 := by simpa using h2 x 0 1
    rw [hs] at this
    simp only [Pi.add_apply] at this
    linear_combination this
  have hp10 : ∀ x : K, Φ ![x, 0] 0 = x * c := by
    intro x
    have h := h1 x 0 1
    simp only [mul_one, zero_add] at h
    have hs := hsplit x 1
    rw [hs] at h
    simp only [Pi.add_apply] at h
    linear_combination h
  have hp01 : ∀ y : K, Φ ![0, y] 0 = 0 := by
    intro y
    have h := h3 y 1 0
    simp only [mul_one, add_zero] at h
    have hs := hsplit 1 y
    rw [hs] at h
    simp only [Pi.add_apply] at h
    linear_combination h
  have hq01 : ∀ y : K, Φ ![0, y] 1 = y * c := by
    intro y
    have h := h4 y 1 0
    simp only [mul_one, add_zero] at h
    have hs := hsplit 1 y
    rw [hs] at h
    simp only [Pi.add_apply] at h
    have h10 : Φ ![1, 0] 0 = c := by simpa using hp10 1
    linear_combination h + y * h10
  refine ⟨c, fun v => ?_⟩
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> simp
  rw [hv, hsplit]
  ext i
  fin_cases i
  · simp [hp10, hp01, mul_comm]
  · simp [hq10, hq01, mul_comm]

theorem schur_twist {K : Type} [Field K] (σ : K ≃+* K) (Gm : SL(2, K))
    (Ψ : SL(2, K) ≃* SL(2, K))
    (hG : ∀ Y : SL(2, K), Ψ Y * Gm = Gm * Matrix.SpecialLinearGroup.map σ.toRingHom Y)
    (φ : (Fin 2 → K) →+ (Fin 2 → K))
    (hφ : ∀ (A : SL(2, K)) (v : Fin 2 → K),
      φ ((A : Matrix (Fin 2) (Fin 2) K).mulVec v) =
        ((Ψ A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).mulVec (φ v)) :
    ∃ c : K, ∀ v : Fin 2 → K,
      φ v = (Gm : Matrix (Fin 2) (Fin 2) K).mulVec (fun i => c * σ (v i)) := by
  obtain ⟨Gi, hGiG, hGGi, hconj⟩ : ∃ Gi : Matrix (Fin 2) (Fin 2) K,
      Gi * (Gm : Matrix (Fin 2) (Fin 2) K) = 1 ∧ (Gm : Matrix (Fin 2) (Fin 2) K) * Gi = 1 ∧
      ∀ A : SL(2, K), Gi * ((Ψ A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        ((Matrix.SpecialLinearGroup.map σ.toRingHom A : SL(2, K)) :
          Matrix (Fin 2) (Fin 2) K) * Gi := by
    refine ⟨((Gm⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K), ?_, ?_, ?_⟩
    · have := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K)) (inv_mul_cancel Gm)
      simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using this
    · have := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K)) (mul_inv_cancel Gm)
      simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using this
    · intro A
      have h := hG A
      have h2 : Gm⁻¹ * Ψ A = (Matrix.SpecialLinearGroup.map σ.toRingHom A) * Gm⁻¹ := by
        calc Gm⁻¹ * Ψ A = Gm⁻¹ * (Ψ A * Gm) * Gm⁻¹ := by group
          _ = Gm⁻¹ * (Gm * Matrix.SpecialLinearGroup.map σ.toRingHom A) * Gm⁻¹ := by rw [h]
          _ = (Matrix.SpecialLinearGroup.map σ.toRingHom A) * Gm⁻¹ := by group
      have := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K)) h2
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
  let χ' : (Fin 2 → K) →+ (Fin 2 → K) :=
    { toFun := fun v i => σ.symm ((Gi.mulVec (φ v)) i)
      map_zero' := by ext i; simp
      map_add' := fun v w => by ext i; simp [Matrix.mulVec_add] }
  have hχ' : ∀ (A : SL(2, K)) (v : Fin 2 → K),
      χ' ((A : Matrix (Fin 2) (Fin 2) K).mulVec v) =
        (A : Matrix (Fin 2) (Fin 2) K).mulVec (χ' v) := by
    intro A v
    ext i
    show σ.symm ((Gi.mulVec (φ ((A : Matrix (Fin 2) (Fin 2) K).mulVec v))) i) =
      ((A : Matrix (Fin 2) (Fin 2) K).mulVec (fun j => σ.symm ((Gi.mulVec (φ v)) j))) i
    rw [hφ, Matrix.mulVec_mulVec, hconj, ← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, map_add, map_mul]
  obtain ⟨c, hc'⟩ := schur_sl2 χ' hχ'
  refine ⟨σ c, fun v => ?_⟩
  have h2 : Gi.mulVec (φ v) = fun i => σ c * σ (v i) := by
    ext i
    have h1 : σ.symm ((Gi.mulVec (φ v)) i) = c * v i := congrFun (hc' v) i
    calc (Gi.mulVec (φ v)) i = σ (σ.symm ((Gi.mulVec (φ v)) i)) := by simp
      _ = σ (c * v i) := by rw [h1]
      _ = σ c * σ (v i) := map_mul σ c (v i)
  calc φ v = (Gm : Matrix (Fin 2) (Fin 2) K).mulVec (Gi.mulVec (φ v)) := by
        rw [Matrix.mulVec_mulVec, hGGi, Matrix.one_mulVec]
    _ = _ := by rw [h2]

end Schur

section Core

variable {G : Type*} [Group G]

theorem upper_commute {K : Type*} [Field K] (Gm : SL(2, K)) (w s : K)
    (h : (slUpper w : SL(2, K)) * Gm = Gm * slUpper s) :
    (Gm : Matrix (Fin 2) (Fin 2) K) 1 0 * s = 0 ∧
      (Gm : Matrix (Fin 2) (Fin 2) K) 1 1 * w = (Gm : Matrix (Fin 2) (Fin 2) K) 0 0 * s := by
  have h00 := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) 1 1) h
  have h01 := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, slUpper_val, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val'] at h00 h01
  constructor
  · linear_combination -h00
  · linear_combination h01

theorem link_core {K : Type} [Field K] [Finite K] (hK2 : (2 : K) = 0) {L U R : Subgroup G}
    (α : L →* SL(2, K)) (hα : Function.Surjective α)
    (β : U →* Multiplicative (Fin 2 → K)) (hβ : Function.Surjective β)
    (hβeq : ∀ ℓ : L, ∀ u v : U, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u)))
    (hLU : ∀ ℓ ∈ L, ∀ u ∈ U, ℓ * u * ℓ⁻¹ ∈ U)
    (hP : ∀ ℓ : L, (ℓ : G) ∈ R ↔ α ℓ ∈ slUni K)
    {f : G} (hff : f * f = 1)
    (hfL : ∀ x ∈ L, f * x * f⁻¹ ∈ L) (hfU : ∀ x ∈ U, f * x * f⁻¹ ∈ U)
    (hfR : ∀ x ∈ R, f * x * f⁻¹ ∈ R)
    (Ψ : SL(2, K) ≃* SL(2, K)) (hΨ : ∀ ℓ : L, Ψ (α ℓ) = α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩)
    (Φ : Multiplicative (Fin 2 → K) ≃* Multiplicative (Fin 2 → K))
    (hΦ : ∀ u : U, Φ (β u) = β ⟨f * u * f⁻¹, hfU u u.2⟩)
    (hP1 : ∃ (σ : K ≃+* K) (G : SL(2, K)),
      ∀ Y : SL(2, K), Ψ Y * G = G * Matrix.SpecialLinearGroup.map σ.toRingHom Y) :
    ∃ (σ : K ≃+* K) (a c' : K), a ≠ 0 ∧ (∀ v, σ (σ v) = v) ∧ a * a * σ (a * a) = 1 ∧
      c' * a⁻¹ * σ (c' * a⁻¹) = 1 ∧ c' * a * σ (c' * a) = 1 ∧
      (∀ r : L, (r : G) ∈ R →
        (α ⟨f * r * f⁻¹, hfL r r.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 =
          a * a * σ ((α r : Matrix (Fin 2) (Fin 2) K) 0 1)) ∧
      (∀ u : U, (Multiplicative.toAdd (β ⟨f * u * f⁻¹, hfU u u.2⟩)) 1 =
        c' * a⁻¹ * σ (Multiplicative.toAdd (β u) 1)) ∧
      (∀ u : U, Multiplicative.toAdd (β u) 1 = 0 →
        (Multiplicative.toAdd (β ⟨f * u * f⁻¹, hfU u u.2⟩)) 0 =
          c' * a * σ (Multiplicative.toAdd (β u) 0)) ∧
      (∀ ℓ : L, (α ℓ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
        (α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 =
          σ ((α ℓ : Matrix (Fin 2) (Fin 2) K) 0 0)) ∧
      (∃ Gm : SL(2, K), (Gm : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
        (Gm : Matrix (Fin 2) (Fin 2) K) 0 0 = a ∧
        σ ((Gm : Matrix (Fin 2) (Fin 2) K) 0 1) = (Gm : Matrix (Fin 2) (Fin 2) K) 0 1 ∧
        (∀ ℓ : L, α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ * Gm =
          Gm * Matrix.SpecialLinearGroup.map σ.toRingHom (α ℓ)) ∧
        (∀ u : U, Multiplicative.toAdd (β ⟨f * u * f⁻¹, hfU u u.2⟩) =
          (Gm : Matrix (Fin 2) (Fin 2) K).mulVec
            (fun i => c' * σ (Multiplicative.toAdd (β u) i)))) ∧
      (σ = 1 → ∃ k : SL(2, K), ∀ ℓ : L, α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ = k * α ℓ * k⁻¹) := by
  obtain ⟨σ, Gm, hG⟩ := hP1
  have hmap : ∀ v : K, Matrix.SpecialLinearGroup.map σ.toRingHom (slUpper v) = slUpper (σ v) := by
    intro v
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slUpper_val]
  have hup : ∀ v : K, ∃ w : K, Ψ (slUpper v) = slUpper w := by
    intro v
    obtain ⟨ℓ, hℓ⟩ := hα (slUpper v)
    have hℓR : (ℓ : G) ∈ R := (hP ℓ).2 (hℓ ▸ slUpper_mem_slUni v)
    have h1 : (f * ℓ * f⁻¹) ∈ R := hfR _ hℓR
    have h2 : α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ ∈ slUni K := (hP _).1 h1
    rw [← hΨ ℓ, hℓ] at h2
    exact mem_slUni.1 h2
  have hc : (Gm : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    obtain ⟨w, hw⟩ := hup 1
    have h := hG (slUpper 1)
    rw [hw, hmap, map_one] at h
    have := (upper_commute Gm w 1 h).1
    simpa using this
  set a := (Gm : Matrix (Fin 2) (Fin 2) K) 0 0 with ha_def
  set d := (Gm : Matrix (Fin 2) (Fin 2) K) 1 1 with hd_def
  have hdet : a * d = 1 := by
    have := Gm.det_coe
    rw [Matrix.det_fin_two, hc] at this
    simpa using this
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hd : d = a⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have hd' : (Gm : Matrix (Fin 2) (Fin 2) K) 1 1 = a⁻¹ := hd
  have hT : ∀ v w : K, Ψ (slUpper v) = slUpper w → w = a * a * σ v := by
    intro v w hw
    have h := hG (slUpper v)
    rw [hw, hmap] at h
    have h2 : d * w = a * σ v := (upper_commute Gm w (σ v) h).2
    rw [hd] at h2
    calc w = a * (a⁻¹ * w) := by rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
      _ = a * (a * σ v) := by rw [h2]
      _ = a * a * σ v := by ring
  have hTop : ∀ r : L, (r : G) ∈ R →
      (α ⟨f * r * f⁻¹, hfL r r.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 =
        a * a * σ ((α r : Matrix (Fin 2) (Fin 2) K) 0 1) := by
    intro r hr
    obtain ⟨v, hv⟩ := mem_slUni.1 ((hP r).1 hr)
    obtain ⟨w, hw⟩ := hup v
    have h1 : α ⟨f * r * f⁻¹, hfL r r.2⟩ = slUpper w := by rw [← hΨ r, hv, hw]
    rw [h1, hv]
    simpa [slUpper_val] using hT v w hw
  have hff2 : ∀ x : G, f * (f * x * f⁻¹) * f⁻¹ = x := by
    intro x
    calc f * (f * x * f⁻¹) * f⁻¹ = (f * f) * x * (f * f)⁻¹ := by group
      _ = x := by rw [hff]; group
  have hRsq : ∀ v : K, a * a * σ (a * a * σ v) = v := by
    intro v
    obtain ⟨r, hr⟩ := hα (slUpper v)
    have hrR : (r : G) ∈ R := (hP r).2 (hr ▸ slUpper_mem_slUni v)
    have h1 := hTop r hrR
    have hr'R : f * (r : G) * f⁻¹ ∈ R := hfR _ hrR
    have h2 := hTop ⟨f * r * f⁻¹, hfL r r.2⟩ hr'R
    have hr'' : (⟨f * (f * (r : G) * f⁻¹) * f⁻¹, hfL _ (hfL r r.2)⟩ : L) = r :=
      Subtype.ext (hff2 r)
    rw [hr'', h1, hr] at h2
    simpa [slUpper_val] using h2.symm
  have hmul : a * a * σ (a * a) = 1 := by
    have h1 := hRsq 1
    simpa [map_one] using h1
  have hσσ : ∀ v, σ (σ v) = v := by
    intro v
    have h0 := hRsq v
    calc σ (σ v) = (a * a * σ (a * a)) * σ (σ v) := by rw [hmul, one_mul]
      _ = a * a * σ (a * a * σ v) := by rw [map_mul σ (a * a) (σ v)]; ring
      _ = v := h0
  let φ : (Fin 2 → K) →+ (Fin 2 → K) :=
    { toFun := fun v => Multiplicative.toAdd (Φ (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := fun v w => by simp [ofAdd_add, map_mul] }
  have hφβ : ∀ u : U, φ (Multiplicative.toAdd (β u)) =
      Multiplicative.toAdd (β ⟨f * u * f⁻¹, hfU u u.2⟩) := by
    intro u
    show Multiplicative.toAdd (Φ (Multiplicative.ofAdd (Multiplicative.toAdd (β u)))) = _
    rw [ofAdd_toAdd, hΦ]
  have hφ : ∀ (A : SL(2, K)) (v : Fin 2 → K),
      φ ((A : Matrix (Fin 2) (Fin 2) K).mulVec v) =
        ((Ψ A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).mulVec (φ v) := by
    intro A v
    obtain ⟨ℓ, rfl⟩ := hα A
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd v)
    have hv : v = Multiplicative.toAdd (β u) := by rw [hu]; rfl
    subst hv
    have hu'U : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ U := hLU ℓ ℓ.2 u u.2
    have h1 : Multiplicative.toAdd (β ⟨(ℓ : G) * u * (ℓ : G)⁻¹, hu'U⟩) =
        (α ℓ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u)) :=
      hβeq ℓ u ⟨(ℓ : G) * u * (ℓ : G)⁻¹, hu'U⟩ rfl
    rw [← h1, hφβ]
    have h3 : f * ((ℓ : G) * u * (ℓ : G)⁻¹) * f⁻¹ =
        (f * ℓ * f⁻¹) * (f * u * f⁻¹) * (f * ℓ * f⁻¹)⁻¹ := by group
    have h4 := hβeq ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ ⟨f * u * f⁻¹, hfU u u.2⟩
      ⟨f * ((ℓ : G) * u * (ℓ : G)⁻¹) * f⁻¹, hfU _ hu'U⟩ h3
    rw [h4, ← hΨ ℓ, hφβ]
  obtain ⟨c', hφv⟩ := schur_twist σ Gm Ψ hG φ hφ
  have hφφ : ∀ v : Fin 2 → K, φ (φ v) = v := by
    intro v
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd v)
    have hv : v = Multiplicative.toAdd (β u) := by rw [hu]; rfl
    subst hv
    have hu' : f * (u : G) * f⁻¹ ∈ U := hfU u u.2
    rw [hφβ u, hφβ ⟨f * u * f⁻¹, hu'⟩]
    exact congrArg (fun w : U => Multiplicative.toAdd (β w)) (Subtype.ext (hff2 u))
  have ha' : (Gm : Matrix (Fin 2) (Fin 2) K) 0 0 = a := ha_def.symm
  have hc2 : c' * a⁻¹ * σ (c' * a⁻¹) = 1 := by
    have h := congrFun (hφφ ![0, 1]) 1
    rw [hφv (φ ![0, 1]), hφv ![0, 1]] at h
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc, hd'] at h
    rw [map_mul, map_inv₀]
    linear_combination h
  have hc1 : c' * a * σ (c' * a) = 1 := by
    have h := congrFun (hφφ ![1, 0]) 0
    rw [hφv (φ ![1, 0]), hφv ![1, 0]] at h
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc, ha'] at h
    rw [map_mul]
    linear_combination h
  have hdiag : ∀ ℓ : L, (α ℓ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
      (α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 =
        σ ((α ℓ : Matrix (Fin 2) (Fin 2) K) 0 0) := by
    intro ℓ hℓ
    have key : (Ψ (α ℓ) : Matrix (Fin 2) (Fin 2) K) 0 0 * a =
        a * σ ((α ℓ : Matrix (Fin 2) (Fin 2) K) 0 0) := by
      have h := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) 0 0) (hG (α ℓ))
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hc, hℓ, ha'] using h
    rw [← hΨ ℓ]
    exact mul_right_cancel₀ ha (key.trans (mul_comm _ _))
  have haσ : a * σ a = 1 := by
    have h1 : (a * σ a) ^ 2 = 1 := by
      have := hmul
      rw [map_mul] at this
      linear_combination this
    have h0 : (a * σ a - 1) ^ 2 = 0 := by
      linear_combination h1 - (a * σ a) * hK2 + hK2
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  have hcc : c' * σ c' = 1 := by
    have h1 := hc1
    rw [map_mul] at h1
    calc c' * σ c' = c' * σ c' * (a * σ a) := by rw [haσ, mul_one]
      _ = c' * a * (σ c' * σ a) := by ring
      _ = 1 := h1
  have hb : σ ((Gm : Matrix (Fin 2) (Fin 2) K) 0 1) = (Gm : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    obtain ⟨b, hbdef⟩ : ∃ b, (Gm : Matrix (Fin 2) (Fin 2) K) 0 1 = b := ⟨_, rfl⟩
    rw [hbdef]
    have h := congrFun (hφφ ![0, 1]) 0
    rw [hφv (φ ![0, 1]), hφv ![0, 1]] at h
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd', ha'] at h
    rw [hbdef] at h
    have hσa : (σ a)⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact haσ)
    rw [hσa] at h
    have h2 : a * (σ b + b) * (c' * σ c') = 0 := by linear_combination h
    rw [hcc, mul_one] at h2
    have h3 : σ b + b = 0 := (mul_eq_zero.1 h2).resolve_left ha
    linear_combination h3 - b * hK2
  have hGdata : ∃ Gm' : SL(2, K), (Gm' : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      (Gm' : Matrix (Fin 2) (Fin 2) K) 0 0 = a ∧
      σ ((Gm' : Matrix (Fin 2) (Fin 2) K) 0 1) = (Gm' : Matrix (Fin 2) (Fin 2) K) 0 1 ∧
      (∀ ℓ : L, α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ * Gm' =
        Gm' * Matrix.SpecialLinearGroup.map σ.toRingHom (α ℓ)) ∧
      (∀ u : U, Multiplicative.toAdd (β ⟨f * u * f⁻¹, hfU u u.2⟩) =
        (Gm' : Matrix (Fin 2) (Fin 2) K).mulVec
          (fun i => c' * σ (Multiplicative.toAdd (β u) i))) := by
    refine ⟨Gm, hc, ha', hb, fun ℓ => ?_, fun u => ?_⟩
    · rw [← hΨ ℓ]; exact hG (α ℓ)
    · rw [← hφβ u, hφv]
  refine ⟨σ, a, c', ha, hσσ, hmul, hc2, hc1, hTop, ?_, ?_, hdiag, hGdata, ?_⟩
  · intro u
    rw [← hφβ u, hφv]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc, hd']
    ring
  · intro u hu
    rw [← hφβ u, hφv]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hu]
    ring
  · intro hσ1
    refine ⟨Gm, fun ℓ => ?_⟩
    have h := hG (α ℓ)
    have h1 : Matrix.SpecialLinearGroup.map σ.toRingHom (α ℓ) = α ℓ := by
      subst hσ1
      apply Subtype.ext
      ext i j
      simp
    rw [h1] at h
    rw [← hΨ ℓ]
    exact eq_mul_inv_of_mul_eq h

end Core

end CFSG.QuasithinUnique.Lin2
