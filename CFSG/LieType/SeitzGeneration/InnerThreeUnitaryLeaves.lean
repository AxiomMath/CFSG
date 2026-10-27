module

public import CFSG.LieType.SeitzGeneration.ClassicalThreeLeaves
public import CFSG.LieType.SeitzGeneration.UnitaryAbelianAll
public import CFSG.LieType.SeitzGeneration.UnitaryTwoInduct
public import CFSG.LieType.SeitzGeneration.ClassicalAssembly

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n : ℕ} {K : Type} [Field K]

section Projection

@[expose] def piSUn (ℓ f n : ℕ) (K : Type) [Field K] :
    unitarySU ℓ f K n →* StatedProj (StatedSU n (ℓ ^ f) K) :=
  QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (unitarySU ℓ f K n))

theorem piSUn_surjective : Function.Surjective (piSUn ℓ f n K) := QuotientGroup.mk'_surjective _

theorem piSUn_eq_iff {a b : unitarySU ℓ f K n} :
    piSUn ℓ f n K a = piSUn ℓ f n K b ↔
      ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin n) u =
        ((a⁻¹ * b : unitarySU ℓ f K n) : GL (Fin n) K) := by
  unfold piSUn
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    StatedScalars, MonoidHom.mem_range]

theorem exists_smul_of_piSUn_eq {a b : unitarySU ℓ f K n}
    (hab : piSUn ℓ f n K a = piSUn ℓ f n K b) :
    ∃ c : K, ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨u, hu⟩ := (piSUn_eq_iff).1 hab
  refine ⟨((u⁻¹ : Kˣ) : K), ?_⟩
  have h1 : ((b : unitarySU ℓ f K n) : GL (Fin n) K) =
      (a : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) u := by
    rw [hu]; simp
  have h2 : ((a : unitarySU ℓ f K n) : GL (Fin n) K) =
      (b : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) u⁻¹ := by
    rw [h1, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [h2, Units.val_mul, GeneralLinearGroup.coe_scalar]
  simp [Matrix.scalar_apply, Matrix.smul_eq_mul_diagonal]

theorem piSUn_commute_of_smul (h : UnitaryFieldData ℓ f K) (hn : 0 < n)
    (a b : unitarySU ℓ f K n) (c : K)
    (hab : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • (((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    piSUn ℓ f n K a * piSUn ℓ f n K b = piSUn ℓ f n K b * piSUn ℓ f n K a := by
  have hda := ((mem_unitarySU_iff h).1 a.2).1
  have hdb := ((mem_unitarySU_iff h).1 b.2).1
  have hc : c ≠ 0 := by
    rintro rfl
    have hdet := congrArg Matrix.det hab
    rw [Matrix.det_mul, zero_smul, hda, hdb] at hdet
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [Matrix.det_zero] at hdet
    simp at hdet
  rw [← map_mul, ← map_mul, piSUn_eq_iff]
  refine ⟨(Units.mk0 c hc)⁻¹, ?_⟩
  have hGL : ((a * b : unitarySU ℓ f K n) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc) *
        ((b * a : unitarySU ℓ f K n) : GL (Fin n) K) := by
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    rw [hab]
    simp [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hcom := commute_scalar (Units.mk0 c hc) ((b : GL (Fin n) K) * (a : GL (Fin n) K))
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [show ((a : GL (Fin n) K) * (b : GL (Fin n) K)) =
      GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc) * ((b : GL (Fin n) K) * (a : GL (Fin n) K))
      from by simpa using hGL, _root_.mul_inv_rev, map_inv]
  rw [mul_assoc, ← hcom.inv_right.eq, inv_mul_cancel_left]

theorem coe_pow_eq_smul_one_of_piSUn (hn : 0 < n) {x : unitarySU ℓ f K n}
    (hx : piSUn ℓ f n K x ^ 3 = 1) :
    ∃ α : K, α ≠ 0 ∧ (((x : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      α • 1 := by
  obtain ⟨c, hc⟩ := exists_smul_of_piSUn_eq (a := x ^ 3) (b := 1)
    (by rw [map_pow, map_one]; exact hx)
  have hc' : (((x : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1 := by
    simpa using hc
  refine ⟨c, ?_, hc'⟩
  rintro rfl
  have h1 : ((((x : GL (Fin n) K) ^ 3)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((x : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hc', zero_smul, Matrix.mul_zero] at h1
  simpa using congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩

end Projection

section Props

@[expose] def planeFixUn (ℓ f n : ℕ) (K : Type) [Field K] (x y : GL (Fin n) K) :
    Set (unitarySU ℓ f K n) :=
  FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪ FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K) ∪
    FixUn ℓ f n K ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∪
    FixUn ℓ f n K ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

@[expose] def UnitaryHeisTensorPlanes : Prop :=
  ∀ (ℓ f n : ℕ) (K : Type) [Field K], UnitaryFieldData ℓ f K → 3 ∣ ℓ ^ f + 1 → 6 ≤ n →
    3 ∣ n → ∀ x y : GL (Fin n) K, x ∈ unitarySU ℓ f K n → y ∈ unitarySU ℓ f K n →
      ∀ ω : K, IsPrimitiveRoot ω 3 →
        (y : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
          ω • ((x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)) →
        (∃ α : K, ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1) →
        (∃ β : K, ((y ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1) →
          Subgroup.closure (planeFixUn ℓ f n K x y) = ⊤

@[expose] def UnitaryTwoOrderNinePlanes : Prop :=
  ∀ (ℓ f n : ℕ) (K : Type) [Field K], UnitaryFieldData ℓ f K → ℓ ^ f = 2 → 5 ≤ n →
    ∀ x y : GL (Fin n) K, x ∈ unitarySU ℓ f K n → y ∈ unitarySU ℓ f K n → x * y = y * x →
      ∀ α β : K, ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1 →
        ((y ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1 → (α ≠ 1 ∨ β ≠ 1) →
        (∀ a b : ℕ, (∃ c : K, ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          c • 1) → 3 ∣ a ∧ 3 ∣ b) →
          Subgroup.closure (planeFixUn ℓ f n K x y) = ⊤

end Props

section Lines

theorem closure_centralizers_of_planeFixUn (h : UnitaryFieldData ℓ f K) (hn : 0 < n)
    (E : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K))) {x y : unitarySU ℓ f K n}
    (hxE : piSUn ℓ f n K x ∈ E) (hyE : piSUn ℓ f n K y ∈ E) (hy1 : piSUn ℓ f n K y ≠ 1)
    (hxy : piSUn ℓ f n K x ∉ Subgroup.zpowers (piSUn ℓ f n K y))
    (hgen : Subgroup.closure (planeFixUn ℓ f n K (x : GL (Fin n) K) (y : GL (Fin n) K)) = ⊤) :
    Subgroup.closure {k : StatedProj (StatedSU n (ℓ ^ f) K) |
      ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} = ⊤ := by
  have hne : ∀ k : ℕ, piSUn ℓ f n K x * piSUn ℓ f n K y ^ k ≠ 1 := by
    intro k hk
    apply hxy
    have : piSUn ℓ f n K x = (piSUn ℓ f n K y ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k)
  have hnx : piSUn ℓ f n K x ≠ 1 := fun h1 => hxy (h1 ▸ Subgroup.one_mem _)
  have hnxy : piSUn ℓ f n K (x * y) ≠ 1 := by
    rw [map_mul]; simpa using hne 1
  have hnxy2 : piSUn ℓ f n K (x * y ^ 2) ≠ 1 := by
    rw [map_mul, map_pow]; exact hne 2
  have hxyE : piSUn ℓ f n K (x * y) ∈ E := by rw [map_mul]; exact E.mul_mem hxE hyE
  have hxy2E : piSUn ℓ f n K (x * y ^ 2) ∈ E := by
    rw [map_mul, map_pow]; exact E.mul_mem hxE (E.pow_mem hyE 2)
  set C := Subgroup.closure {k : StatedProj (StatedSU n (ℓ ^ f) K) |
    ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} with hC
  have hle : planeFixUn ℓ f n K (x : GL (Fin n) K) (y : GL (Fin n) K) ⊆
      (C.comap (piSUn ℓ f n K) : Set (unitarySU ℓ f K n)) := by
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    refine Subgroup.subset_closure ?_
    rcases hg with ((⟨c, hc⟩ | ⟨c, hc⟩) | ⟨c, hc⟩) | ⟨c, hc⟩
    · exact ⟨_, hxE, hnx, piSUn_commute_of_smul h hn g x c hc⟩
    · exact ⟨_, hyE, hy1, piSUn_commute_of_smul h hn g y c hc⟩
    · exact ⟨_, hxyE, hnxy, piSUn_commute_of_smul h hn g (x * y) c hc⟩
    · exact ⟨_, hxy2E, hnxy2, piSUn_commute_of_smul h hn g (x * y ^ 2) c hc⟩
  have hKpre : C.comap (piSUn ℓ f n K) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    exact hle
  rw [eq_top_iff]
  intro k _
  obtain ⟨g, rfl⟩ := piSUn_surjective k
  exact Subgroup.mem_comap.1 (hKpre ▸ Subgroup.mem_top g)

theorem three_dvd_of_scalar_pow_mul_pow (hn : 0 < n) {x y : unitarySU ℓ f K n}
    (hx3 : piSUn ℓ f n K x ^ 3 = 1) (hy3 : piSUn ℓ f n K y ^ 3 = 1)
    (hy1 : piSUn ℓ f n K y ≠ 1) (hxy : piSUn ℓ f n K x ∉ Subgroup.zpowers (piSUn ℓ f n K y))
    {a b : ℕ} {c : K}
    (hc : (((x : GL (Fin n) K) ^ a * (y : GL (Fin n) K) ^ b : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = c • 1) : 3 ∣ a ∧ 3 ∣ b := by
  obtain ⟨u, hu⟩ := exists_scalarGL_of_coe_eq hn hc
  have h1 : piSUn ℓ f n K x ^ a * piSUn ℓ f n K y ^ b = 1 := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_one (piSUn ℓ f n K), piSUn_eq_iff]
    refine ⟨u⁻¹, ?_⟩
    have h2 : ((x ^ a * y ^ b : unitarySU ℓ f K n) : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) u := by
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]; exact hu
    rw [mul_one, Subgroup.coe_inv, h2, map_inv]
  exact three_dvd_of_pow_mul_pow_eq_one hx3 hy3 hy1 hxy h1

theorem exists_psu_lift_pair (h : UnitaryFieldData ℓ f K) (hn : 0 < n)
    (E : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K)))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ 3 = 1)
    (hcard : Nat.card E = 3 ^ 2) :
    ∃ x y : unitarySU ℓ f K n, piSUn ℓ f n K x ∈ E ∧ piSUn ℓ f n K y ∈ E ∧
      piSUn ℓ f n K y ≠ 1 ∧ piSUn ℓ f n K x ∉ Subgroup.zpowers (piSUn ℓ f n K y) ∧
      ∃ α β c : K, α ≠ 0 ∧ β ≠ 0 ∧
        (((x : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1 ∧
        (((y : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1 ∧
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          c • (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, b, hb, hb1, hab⟩ := exists_independent_pair Nat.prime_three E hexp hcard
  obtain ⟨x, rfl⟩ := piSUn_surjective a
  obtain ⟨y, rfl⟩ := piSUn_surjective b
  obtain ⟨α, hα, hx3⟩ := coe_pow_eq_smul_one_of_piSUn hn (hexp _ ha)
  obtain ⟨β, hβ, hy3⟩ := coe_pow_eq_smul_one_of_piSUn hn (hexp _ hb)
  obtain ⟨c, hc⟩ := exists_smul_of_piSUn_eq (a := y * x) (b := x * y)
    (by rw [map_mul, map_mul]; exact hcomm _ hb _ ha)
  exact ⟨x, y, ha, hb, hb1, hab, α, β, c, hα, hβ, hx3, hy3, by simpa using hc⟩

end Lines

section Heisenberg

theorem mat_mul_pow_eq_smul {X Y : Matrix (Fin n) (Fin n) K} {c : K} (h : Y * X = c • (X * Y))
    (k : ℕ) : Y * X ^ k = c ^ k • (X ^ k * Y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc Y * X ^ (k + 1) = (Y * X) * X ^ k := by rw [pow_succ', Matrix.mul_assoc]
      _ = c • (X * (Y * X ^ k)) := by rw [h, Matrix.smul_mul, Matrix.mul_assoc]
      _ = c • (X * (c ^ k • (X ^ k * Y))) := by rw [ih]
      _ = c ^ (k + 1) • (X ^ (k + 1) * Y) := by
        rw [Matrix.mul_smul, smul_smul, pow_succ', pow_succ', Matrix.mul_assoc]

theorem cube_eq_one_of_smul_comm (hn : 0 < n) {x y : GL (Fin n) K} {α c : K} (hα : α ≠ 0)
    (hx3 : ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hc : (y : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      c • ((x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K))) : c ^ 3 = 1 := by
  have hx3' : (x : Matrix (Fin n) (Fin n) K) ^ 3 = α • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hx3
  have h3 := mat_mul_pow_eq_smul hc 3
  rw [hx3', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at h3
  have hYinv : (y : Matrix (Fin n) (Fin n) K) *
      ((y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h4 := congrArg (fun M => M * ((y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h3
  simp only [Matrix.smul_mul, hYinv] at h4
  have h5 := congrFun (congrFun h4 ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h5
  exact mul_right_cancel₀ hα (by rw [one_mul]; exact h5.symm)

theorem closure_planeFixUn_of_heis (hH : UnitaryHeisTensorPlanes) (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hn : 4 ≤ n) {x y : unitarySU ℓ f K n} {α β c : K} (hα : α ≠ 0)
    (hx3 : (((x : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hy3 : (((y : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1)
    (hc : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hxy : x * y ≠ y * x) :
    Subgroup.closure (planeFixUn ℓ f n K (x : GL (Fin n) K) (y : GL (Fin n) K)) = ⊤ := by
  have hn0 : 0 < n := by omega
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hxy
    rw [one_smul] at hc
    exact Subtype.ext (Units.ext hc.symm)
  have hc3 := cube_eq_one_of_smul_comm hn0 hα hx3 hc
  have hω : IsPrimitiveRoot c 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [← orderOf_eq_prime hc3 hc1]
    exact IsPrimitiveRoot.orderOf c
  have hdx := ((mem_unitarySU_iff h).1 x.2).1
  have hdy := ((mem_unitarySU_iff h).1 y.2).1
  have hcn : c ^ n = 1 := by
    have h1 := congrArg Matrix.det hc
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, hdx, hdy, Fintype.card_fin] at h1
    simpa using h1.symm
  have h3n : 3 ∣ n := hω.dvd_of_pow_eq_one n hcn
  exact hH ℓ f n K h hq3 (by omega) h3n x y x.2 y.2 c hω hc ⟨α, hx3⟩ ⟨β, hy3⟩

end Heisenberg

section TwoElementary

theorem comm_pair_pow_mul {G : Type*} [Group G] {x y : G} (hxy : Commute x y) (a b c d : ℕ) :
    (x ^ a * y ^ b) * (x ^ c * y ^ d) = x ^ (a + c) * y ^ (b + d) := by
  calc (x ^ a * y ^ b) * (x ^ c * y ^ d) = x ^ a * (y ^ b * x ^ c) * y ^ d := by
        simp only [mul_assoc]
    _ = x ^ a * (x ^ c * y ^ b) * y ^ d := by rw [(hxy.symm.pow_pow b c).eq]
    _ = x ^ (a + c) * y ^ (b + d) := by rw [pow_add, pow_add]; simp only [mul_assoc]

@[expose] def commPairSubgroup {G : Type*} [Group G] {x y : G} (hxy : Commute x y) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) : Subgroup G where
  carrier := {z | ∃ a b : ℕ, z = x ^ a * y ^ b}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, comm_pair_pow_mul hxy a b c d⟩
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    refine ⟨2 * a, 2 * b, inv_eq_of_mul_eq_one_right ?_⟩
    rw [comm_pair_pow_mul hxy, show a + 2 * a = 3 * a by ring, show b + 2 * b = 3 * b by ring,
      pow_mul, pow_mul, hx3, hy3, one_pow, one_pow, one_mul]

theorem commPairSubgroup_comm {G : Type*} [Group G] {x y : G} (hxy : Commute x y) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) : ∀ a ∈ commPairSubgroup hxy hx3 hy3, ∀ b ∈ commPairSubgroup hxy hx3 hy3,
      a * b = b * a := by
  rintro _ ⟨a, b, rfl⟩ _ ⟨c, d, rfl⟩
  rw [comm_pair_pow_mul hxy, comm_pair_pow_mul hxy, add_comm a c, add_comm b d]

theorem commPairSubgroup_exp {G : Type*} [Group G] {x y : G} (hxy : Commute x y) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) : ∀ a ∈ commPairSubgroup hxy hx3 hy3, a ^ 3 = 1 := by
  rintro _ ⟨a, b, rfl⟩
  rw [(hxy.pow_pow a b).mul_pow 3, ← pow_mul, ← pow_mul, mul_comm a 3, mul_comm b 3, pow_mul,
    pow_mul, hx3, hy3, one_pow, one_pow, one_mul]

theorem card_commPairSubgroup {G : Type*} [Group G] {x y : G} (hxy : Commute x y) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hind : ∀ a b : ℕ, x ^ a * y ^ b = 1 → 3 ∣ a ∧ 3 ∣ b) :
    Nat.card (commPairSubgroup hxy hx3 hy3) = 3 ^ 2 := by
  let φ : Fin 3 × Fin 3 → commPairSubgroup hxy hx3 hy3 := fun p =>
    ⟨x ^ (p.1 : ℕ) * y ^ (p.2 : ℕ), p.1, p.2, rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨i, j⟩ ⟨k, l⟩ hφ'
      have h1 : x ^ (i : ℕ) * y ^ (j : ℕ) = x ^ (k : ℕ) * y ^ (l : ℕ) := congrArg Subtype.val hφ'
      have h2 : x ^ ((i : ℕ) + 2 * k) * y ^ ((j : ℕ) + 2 * l) = 1 := by
        rw [← comm_pair_pow_mul hxy, h1, comm_pair_pow_mul hxy,
          show (k : ℕ) + 2 * k = 3 * k by ring, show (l : ℕ) + 2 * l = 3 * l by ring, pow_mul,
          pow_mul, hx3, hy3, one_pow, one_pow, one_mul]
      obtain ⟨h4, h5⟩ := hind _ _ h2
      have hi := i.2
      have hj := j.2
      have hk := k.2
      have hl := l.2
      have hik : (i : ℕ) = k := by omega
      have hjl : (j : ℕ) = l := by omega
      exact Prod.ext (Fin.ext hik) (Fin.ext hjl)
    · rintro ⟨z, a, b, rfl⟩
      refine ⟨(⟨a % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨b % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      apply Subtype.ext
      show x ^ (a % 3) * y ^ (b % 3) = x ^ a * y ^ b
      rw [← pow_eq_pow_mod a hx3, ← pow_eq_pow_mod b hy3]
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ)]
  simp

end TwoElementary

section Model

theorem closure_centralizers_statedProj_su_two_elem (h : UnitaryFieldData ℓ f K)
    (hq : ℓ ^ f = 2) (hn : 5 ≤ n) (E : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K)))
    (hexp : ∀ a ∈ E, a ^ 3 = 1) {x y : unitarySU ℓ f K n}
    (hxE : piSUn ℓ f n K x ∈ E) (hyE : piSUn ℓ f n K y ∈ E) (hy1 : piSUn ℓ f n K y ≠ 1)
    (hxy : piSUn ℓ f n K x ∉ Subgroup.zpowers (piSUn ℓ f n K y)) (hcomm : x * y = y * x)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) :
    Subgroup.closure {k : StatedProj (StatedSU n (ℓ ^ f) K) |
      ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} = ⊤ := by
  classical
  have hind : ∀ a b : ℕ, x ^ a * y ^ b = 1 → 3 ∣ a ∧ 3 ∣ b := by
    intro a b hab
    have h1 : piSUn ℓ f n K x ^ a * piSUn ℓ f n K y ^ b = 1 := by
      rw [← map_pow, ← map_pow, ← map_mul, hab, map_one]
    exact three_dvd_of_pow_mul_pow_eq_one (hexp _ hxE) (hexp _ hyE) hy1 hxy h1
  have hc : Commute x y := hcomm
  have hcl := closure_centralizers_unitarySU_two h hq hn (commPairSubgroup hc hx3 hy3)
    (commPairSubgroup_comm hc hx3 hy3) (commPairSubgroup_exp hc hx3 hy3)
    (card_commPairSubgroup hc hx3 hy3 hind)
  have hle : (Subgroup.closure {g : unitarySU ℓ f K n |
      ∃ z ∈ commPairSubgroup hc hx3 hy3, z ≠ 1 ∧ g * z = z * g}).map (piSUn ℓ f n K) ≤
      Subgroup.closure {k : StatedProj (StatedSU n (ℓ ^ f) K) |
        ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨z, ⟨a, b, rfl⟩, hz1, hg⟩, rfl⟩
    refine Subgroup.subset_closure ⟨piSUn ℓ f n K (x ^ a * y ^ b), ?_, ?_, ?_⟩
    · rw [map_mul, map_pow, map_pow]
      exact E.mul_mem (E.pow_mem hxE a) (E.pow_mem hyE b)
    · intro h1
      apply hz1
      rw [map_mul, map_pow, map_pow] at h1
      obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ :=
        three_dvd_of_pow_mul_pow_eq_one (hexp _ hxE) (hexp _ hyE) hy1 hxy h1
      rw [pow_mul, pow_mul, hx3, hy3, one_pow, one_pow, one_mul]
    · rw [← map_mul, ← map_mul, hg]
  rw [hcl, Subgroup.map_top_of_surjective _ piSUn_surjective] at hle
  exact top_le_iff.1 hle

theorem closure_centralizers_statedProj_su_ne_two (hH : UnitaryHeisTensorPlanes)
    (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) (hn : 4 ≤ n)
    (E : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K)))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ 3 = 1)
    (hcard : Nat.card E = 3 ^ 2) :
    Subgroup.closure {k : StatedProj (StatedSU n (ℓ ^ f) K) |
      ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} = ⊤ := by
  have hn0 : 0 < n := by omega
  obtain ⟨x, y, hxE, hyE, hy1, hxy, α, β, c, hα, hβ, hx3, hy3, hc⟩ :=
    exists_psu_lift_pair h hn0 E hcomm hexp hcard
  refine closure_centralizers_of_planeFixUn h hn0 E hxE hyE hy1 hxy ?_
  by_cases hxy' : x * y = y * x
  · have hxU := CFSG.RankThree.PartOne.KFU.unitarySU_le_primeFormUnitary h x.2
    have hyU := CFSG.RankThree.PartOne.KFU.unitarySU_le_primeFormUnitary h y.2
    refine closure_planeFixUn_abelian h hq3 hq2 (by omega) hxU hyU (congrArg Subtype.val hxy')
      hα hβ hx3 hy3 ?_
    rintro a b ⟨c', hc'⟩
    exact three_dvd_of_scalar_pow_mul_pow hn0 (hexp _ hxE) (hexp _ hyE) hy1 hxy hc'
  · exact closure_planeFixUn_of_heis hH h hq3 hn hα hx3 hy3 hc hxy'

theorem closure_centralizers_statedProj_su_two (hH : UnitaryHeisTensorPlanes)
    (h9 : UnitaryTwoOrderNinePlanes) (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) (hn : 5 ≤ n)
    (E : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K)))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ 3 = 1)
    (hcard : Nat.card E = 3 ^ 2) :
    Subgroup.closure {k : StatedProj (StatedSU n (ℓ ^ f) K) |
      ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} = ⊤ := by
  have hn0 : 0 < n := by omega
  have hq3 : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  obtain ⟨x, y, hxE, hyE, hy1, hxy, α, β, c, hα, hβ, hx3, hy3, hc⟩ :=
    exists_psu_lift_pair h hn0 E hcomm hexp hcard
  by_cases hxy' : x * y = y * x
  · by_cases hαβ : α = 1 ∧ β = 1
    · obtain ⟨rfl, rfl⟩ := hαβ
      refine closure_centralizers_statedProj_su_two_elem h hq hn E hexp hxE hyE hy1 hxy hxy' ?_ ?_
      · exact Subtype.ext (Units.ext (by simpa using hx3))
      · exact Subtype.ext (Units.ext (by simpa using hy3))
    · refine closure_centralizers_of_planeFixUn h hn0 E hxE hyE hy1 hxy ?_
      refine h9 ℓ f n K h hq hn x y x.2 y.2 (congrArg Subtype.val hxy') α β hx3 hy3
        (not_and_or.1 hαβ) ?_
      rintro a b ⟨c', hc'⟩
      exact three_dvd_of_scalar_pow_mul_pow hn0 (hexp _ hxE) (hexp _ hyE) hy1 hxy hc'
  · exact closure_centralizers_of_planeFixUn h hn0 E hxE hyE hy1 hxy
      (closure_planeFixUn_of_heis hH h hq3 (by omega) hα hx3 hy3 hc hxy')

end Model

section Leaves

theorem planeGen_inner_unitary_of_model {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ} (hp : p.Prime)
    (hP : ∀ E₁ : Subgroup (StatedProj (StatedSU (m + 1)
        (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ ^
          TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
        (GaloisField (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
          (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)))),
      IsElemAbelian p E₁ → Nat.card E₁ = p ^ 2 →
        Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ k * x = x * k} = ⊤)
    {E : Subgroup (MulAut (Cat ⟨.twistedA m q, hv⟩))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hinner : InnerPlane ⟨.twistedA m q, hv⟩ p E) : PlaneGen E := by
  have : Fact p.Prime := ⟨hp⟩
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have hqcard : ℓ ^ f = q.card := by simp [hℓ, hf, TauCeti.ValidLieTypeIndex.characteristic,
    TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.PrimePower.card_def]
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  have hfin := hU.finite
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSU (m + 1) (ℓ ^ f)
      (GaloisField ℓ (2 * f)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField ℓ (2 * f)) ℓ f
      (by rw [hU.card, pow_mul']) (m + 1) (by omega) (by
        intro h32
        obtain ⟨h31, h2⟩ := Prod.mk.inj h32
        have h3 := hrange.2 (by omega)
        rw [hqcard] at h2
        omega)
  have : IsSimpleGroup (Cat ⟨.twistedA m q, hv⟩) := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.twistedA m q, hv⟩)
    (range_conj_ne_bot_of_inner hp hc hinner)
  exact planeGen_of_inner_model hinj e hP hE hc hinner

theorem seitzInnerThreeUnitaryNonabHigh_of_heis (hH : UnitaryHeisTensorPlanes) :
    SeitzInnerThreeUnitaryNonabHigh := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp3, m, q, hd, hq2, hq3, hm1, hm3⟩
  obtain rfl : d = .twistedA m q := hd
  subst hp3
  refine planeGen_inner_unitary_of_model hv hp ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have hqcard : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ = q.card := by
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.PrimePower.card_def]
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE₁.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  exact closure_centralizers_statedProj_su_ne_two hH hU (by rw [hqcard]; exact hq3)
    (by rw [hqcard]; exact hq2) (by omega) E₁ hcomm hE₁.2 hcard₁

theorem seitzInnerThreeUnitaryTwo_of (hH : UnitaryHeisTensorPlanes)
    (h9 : UnitaryTwoOrderNinePlanes) : SeitzInnerThreeUnitaryTwo := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp3, m, q, hd, hq2⟩
  obtain rfl : d = .twistedA m q := hd
  subst hp3
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm4 : 4 ≤ m := by
    have hm2 := hrange.1
    rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | h4
    · have := hrange.2 rfl
      omega
    · exact absurd (isD2SeitzException_unitary_four hq2) hex
    · exact h4
  refine planeGen_inner_unitary_of_model hv hp ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have hqcard : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ = q.card := by
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.PrimePower.card_def]
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE₁.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  exact closure_centralizers_statedProj_su_two hH h9 hU (by rw [hqcard]; exact hq2)
    (by omega) E₁ hcomm hE₁.2 hcard₁

end Leaves

end CFSG.LieType.SeitzGeneration
