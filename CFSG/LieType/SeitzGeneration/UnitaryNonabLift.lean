module

public import CFSG.LieType.SeitzGeneration.InnerThreeUnitaryLeaves

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem closure_centralizers_of_forall (E : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K)))
    (S : Set (unitarySU ℓ f K n))
    (hS : ∀ g ∈ S, ∃ z ∈ E, z ≠ 1 ∧ piSUn ℓ f n K g * z = z * piSUn ℓ f n K g)
    (hgen : Subgroup.closure S = ⊤) :
    Subgroup.closure {k : StatedProj (StatedSU n (ℓ ^ f) K) |
      ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} = ⊤ := by
  set C := Subgroup.closure {k : StatedProj (StatedSU n (ℓ ^ f) K) |
    ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} with hC
  have hle : S ⊆ (C.comap (piSUn ℓ f n K) : Set (unitarySU ℓ f K n)) := by
    intro g hg
    obtain ⟨z, hzE, hz1, hcomm⟩ := hS g hg
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    exact Subgroup.subset_closure ⟨z, hzE, hz1, hcomm⟩
  have hKpre : C.comap (piSUn ℓ f n K) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    exact hle
  rw [eq_top_iff]
  intro k _
  obtain ⟨g, rfl⟩ := piSUn_surjective k
  exact Subgroup.mem_comap.1 (hKpre ▸ Subgroup.mem_top g)

theorem coe_pow_eq_smul_one_of_piSUn_p (hn : 0 < n) {x : unitarySU ℓ f K n}
    (hx : piSUn ℓ f n K x ^ p = 1) :
    ∃ α : K, α ≠ 0 ∧ (((x : GL (Fin n) K) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      α • 1 := by
  obtain ⟨c, hc⟩ := exists_smul_of_piSUn_eq (a := x ^ p) (b := 1)
    (by rw [map_pow, map_one]; exact hx)
  have hc' : (((x : GL (Fin n) K) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1 := by
    simpa using hc
  refine ⟨c, ?_, hc'⟩
  rintro rfl
  have h1 : ((((x : GL (Fin n) K) ^ p)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((x : GL (Fin n) K) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hc', zero_smul, Matrix.mul_zero] at h1
  simpa using congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩

theorem exists_psu_lift_pair_p (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hn : 0 < n)
    (E : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K)))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    ∃ x y : unitarySU ℓ f K n, piSUn ℓ f n K x ∈ E ∧ piSUn ℓ f n K y ∈ E ∧
      piSUn ℓ f n K y ≠ 1 ∧ piSUn ℓ f n K x ∉ Subgroup.zpowers (piSUn ℓ f n K y) ∧
      ∃ α β c : K, α ≠ 0 ∧ β ≠ 0 ∧
        (((x : GL (Fin n) K) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1 ∧
        (((y : GL (Fin n) K) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1 ∧
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          c • (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha, b, hb, hb1, hab⟩ := exists_independent_pair hp E hexp hcard
  obtain ⟨x, rfl⟩ := piSUn_surjective a
  obtain ⟨y, rfl⟩ := piSUn_surjective b
  obtain ⟨α, hα, hx3⟩ := coe_pow_eq_smul_one_of_piSUn_p hn (hexp _ ha)
  obtain ⟨β, hβ, hy3⟩ := coe_pow_eq_smul_one_of_piSUn_p hn (hexp _ hb)
  obtain ⟨c, hc⟩ := exists_smul_of_piSUn_eq (a := y * x) (b := x * y)
    (by rw [map_mul, map_mul]; exact hcomm _ hb _ ha)
  exact ⟨x, y, ha, hb, hb1, hab, α, β, c, hα, hβ, hx3, hy3, by simpa using hc⟩

theorem pow_eq_one_of_smul_comm_p (hn : 0 < n) {x y : GL (Fin n) K} {α c : K} (hα : α ≠ 0)
    (hx : ((x ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hc : (y : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      c • ((x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K))) : c ^ p = 1 := by
  have hx' : (x : Matrix (Fin n) (Fin n) K) ^ p = α • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hx
  have h3 := mat_mul_pow_eq_smul hc p
  rw [hx', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at h3
  have hYinv : (y : Matrix (Fin n) (Fin n) K) *
      ((y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h4 := congrArg (fun M => M * ((y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h3
  simp only [Matrix.smul_mul, hYinv] at h4
  have h5 := congrFun (congrFun h4 ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h5
  exact mul_right_cancel₀ hα (by rw [one_mul]; exact h5.symm)

theorem dvd_of_pow_mul_pow_eq_one_p {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {e₁ e₂ : G}
    (h1 : e₁ ^ p = 1) (h2 : e₂ ^ p = 1) (he₂ : e₂ ≠ 1) (he₁ : e₁ ∉ Subgroup.zpowers e₂) {a b : ℕ}
    (hab : e₁ ^ a * e₂ ^ b = 1) : p ∣ a ∧ p ∣ b := by
  have : Fact p.Prime := ⟨hp⟩
  have ha : p ∣ a := by
    by_contra ha
    apply he₁
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd hp).2 ha).symm hp.one_lt
    have h3 : e₁ ^ a ∈ Subgroup.zpowers e₂ := by
      have : e₁ ^ a = (e₂ ^ b)⁻¹ := eq_inv_of_mul_eq_one_left hab
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) b)
    have h5 : e₁ = (e₁ ^ a) ^ m := by
      rw [← pow_mul, pow_eq_pow_mod (a * m) h1, hm, pow_one]
    rw [h5]
    exact Subgroup.pow_mem _ h3 m
  refine ⟨ha, ?_⟩
  obtain ⟨k, rfl⟩ := ha
  have h6 : e₂ ^ b = 1 := by
    rw [pow_mul, h1, one_pow, one_mul] at hab; exact hab
  rw [← orderOf_eq_prime h2 he₂]
  exact orderOf_dvd_of_pow_eq_one h6

theorem dvd_of_scalar_pow_mul_pow_p (hp : p.Prime) (hn : 0 < n) {x y : unitarySU ℓ f K n}
    (hx : piSUn ℓ f n K x ^ p = 1) (hy : piSUn ℓ f n K y ^ p = 1)
    (hy1 : piSUn ℓ f n K y ≠ 1) (hxy : piSUn ℓ f n K x ∉ Subgroup.zpowers (piSUn ℓ f n K y))
    {a b : ℕ} {c : K}
    (hc : (((x : GL (Fin n) K) ^ a * (y : GL (Fin n) K) ^ b : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = c • 1) : p ∣ a ∧ p ∣ b := by
  obtain ⟨u, hu⟩ := exists_scalarGL_of_coe_eq hn hc
  have h1 : piSUn ℓ f n K x ^ a * piSUn ℓ f n K y ^ b = 1 := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_one (piSUn ℓ f n K), piSUn_eq_iff]
    refine ⟨u⁻¹, ?_⟩
    have h2 : ((x ^ a * y ^ b : unitarySU ℓ f K n) : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) u := by
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]; exact hu
    rw [mul_one, Subgroup.coe_inv, h2, map_inv]
  exact dvd_of_pow_mul_pow_eq_one_p hp hx hy hy1 hxy h1

end CFSG.LieType.SeitzGeneration
