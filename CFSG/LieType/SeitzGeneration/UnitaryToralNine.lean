module

public import CFSG.LieType.SeitzGeneration.UnitaryToral
public import CFSG.LieType.SeitzGeneration.OutdiagPlane
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitaryScope

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryModel

theorem three_dvd_of_pow_mul_pow_eq_one {G : Type*} [Group G] {e₁ e₂ : G} (h1 : e₁ ^ 3 = 1)
    (h2 : e₂ ^ 3 = 1) (he₂ : e₂ ≠ 1) (he₁ : e₁ ∉ Subgroup.zpowers e₂) {a b : ℕ}
    (hab : e₁ ^ a * e₂ ^ b = 1) : 3 ∣ a ∧ 3 ∣ b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha : 3 ∣ a := by
    by_contra ha
    apply he₁
    have h3 : e₁ ^ a ∈ Subgroup.zpowers e₂ := by
      have : e₁ ^ a = (e₂ ^ b)⁻¹ := eq_inv_of_mul_eq_one_left hab
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) b)
    rcases (by omega : a % 3 = 1 ∨ a % 3 = 2) with h | h
    · rwa [pow_eq_pow_mod a h1, h, pow_one] at h3
    · have h5 : e₁ = (e₁ ^ a) ^ 2 := by
        rw [← pow_mul, pow_eq_pow_mod (a * 2) h1, show a * 2 % 3 = 1 by omega, pow_one]
      rw [h5]
      exact Subgroup.pow_mem _ h3 2
  refine ⟨ha, ?_⟩
  obtain ⟨k, rfl⟩ := ha
  have h6 : e₂ ^ b = 1 := by
    rw [pow_mul, h1, one_pow, one_mul] at hab; exact hab
  rw [← orderOf_eq_prime h2 he₂]
  exact orderOf_dvd_of_pow_eq_one h6

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem coe_pow_eq_smul_one_of_piSU {x : unitarySU ℓ f K 3}
    (hx : piSU ℓ f K x ^ 3 = 1) :
    ∃ α : K, α ≠ 0 ∧ (((x : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      α • 1 := by
  obtain ⟨c, hc⟩ := exists_smul_of_piSU_eq (a := x ^ 3) (b := 1)
    (by rw [map_pow, map_one]; exact hx)
  have hc' : (((x : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
    simpa using hc
  refine ⟨c, ?_, hc'⟩
  rintro rfl
  have h1 : ((((x : GL (Fin 3) K) ^ 3)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((x : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hc', zero_smul, Matrix.mul_zero] at h1
  exact zero_ne_one (congrFun (congrFun h1 0) 0)

theorem unitaryToralNine : UnitaryToralNine := by
  intro ℓ f K _ h hq3 hq2 E hcomm hexp hcard hlift
  classical
  have hfin := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, b, hb, hb1, hab⟩ := exists_independent_pair Nat.prime_three E hexp hcard
  obtain ⟨x, rfl⟩ := piSU_surjective a
  obtain ⟨y, rfl⟩ := piSU_surjective b
  have hxy : x * y = y * x := hlift x y ha hb
  obtain ⟨α, hα, hx3⟩ := coe_pow_eq_smul_one_of_piSU (hexp _ ha)
  obtain ⟨β, hβ, hy3⟩ := coe_pow_eq_smul_one_of_piSU (hexp _ hb)
  have hxU : (x : GL (Fin 3) K) ∈ primeFormUnitary h (idGram K 3) :=
    unitarySU_le_primeFormUnitary h x.2
  have hyU : (y : GL (Fin 3) K) ∈ primeFormUnitary h (idGram K 3) :=
    unitarySU_le_primeFormUnitary h y.2
  have hind : ∀ a' b' : ℕ, (∃ c : K, (((x : GL (Fin 3) K) ^ a' * (y : GL (Fin 3) K) ^ b' :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) → 3 ∣ a' ∧ 3 ∣ b' := by
    rintro a' b' ⟨c, hc⟩
    obtain ⟨u, hu⟩ := exists_scalarGL_of_coe_eq (by norm_num) hc
    have h1 : piSU ℓ f K x ^ a' * piSU ℓ f K y ^ b' = 1 := by
      rw [← map_pow, ← map_pow, ← map_mul, ← map_one (piSU ℓ f K), piSU_eq_iff]
      refine ⟨u⁻¹, ?_⟩
      have h2 : ((x ^ a' * y ^ b' : unitarySU ℓ f K 3) : GL (Fin 3) K) =
          Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
        rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]; exact hu
      rw [mul_one, Subgroup.coe_inv, h2, map_inv]
    exact three_dvd_of_pow_mul_pow_eq_one (hexp _ ha) (hexp _ hb) hb1 hab h1
  have hne : ∀ k : ℕ, piSU ℓ f K x * piSU ℓ f K y ^ k ≠ 1 := by
    intro k hk
    apply hab
    have : piSU ℓ f K x = (piSU ℓ f K y ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k)
  have hnx : piSU ℓ f K x ≠ 1 := fun h1 => hab (h1 ▸ Subgroup.one_mem _)
  have hnxy : piSU ℓ f K (x * y) ≠ 1 := by
    rw [map_mul]; simpa using hne 1
  have hnxy2 : piSU ℓ f K (x * y ^ 2) ≠ 1 := by
    rw [map_mul, map_pow]; exact hne 2
  have hxyE : piSU ℓ f K (x * y) ∈ E := by rw [map_mul]; exact E.mul_mem ha hb
  have hxy2E : piSU ℓ f K (x * y ^ 2) ∈ E := by
    rw [map_mul, map_pow]; exact E.mul_mem ha (E.pow_mem hb 2)
  set C := Subgroup.closure {k : StatedProj (StatedSU 3 (ℓ ^ f) K) |
    ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} with hC
  have hle : planeFixU ℓ f K (x : GL (Fin 3) K) (y : GL (Fin 3) K) ⊆
      (C.comap (piSU ℓ f K) : Set (unitarySU ℓ f K 3)) := by
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    refine Subgroup.subset_closure ?_
    rcases hg with ((⟨c, hc⟩ | ⟨c, hc⟩) | ⟨c, hc⟩) | ⟨c, hc⟩
    · exact ⟨_, ha, hnx, piSU_commute_of_smul h g x c hc⟩
    · exact ⟨_, hb, hb1, piSU_commute_of_smul h g y c hc⟩
    · exact ⟨_, hxyE, hnxy, piSU_commute_of_smul h g (x * y) c hc⟩
    · exact ⟨_, hxy2E, hnxy2, piSU_commute_of_smul h g (x * y ^ 2) c hc⟩
  have hclosure := closure_planeFixU_abelian h hq3 hq2 hxU hyU (congrArg Subtype.val hxy) hα hβ
    hx3 hy3 hind
  have hKpre : C.comap (piSU ℓ f K) = ⊤ := by
    rw [eq_top_iff, ← hclosure, Subgroup.closure_le]
    exact hle
  rw [eq_top_iff]
  intro k _
  obtain ⟨g, rfl⟩ := piSU_surjective k
  exact Subgroup.mem_comap.1 (hKpre ▸ Subgroup.mem_top g)

end CFSG.LieType.SeitzGeneration
