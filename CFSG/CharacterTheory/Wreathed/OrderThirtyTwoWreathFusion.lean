module

public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusionOutside
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusionExistence

public noncomputable section

namespace CFSG.Wreathed.OrderThirtyTwo

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.AdaptedBaseFusion

universe u

variable {G : Type u} [Group G]

theorem exists_two_pow_of_mem_base [Finite G] {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ 2)} {y : G}
    (hy : y ∈ modelBase S e) : ∃ k : ℕ, orderOf y = 2 ^ k := by
  have hdvd : orderOf y ∣ 2 ^ 2 :=
    orderOf_dvd_of_pow_eq_one (pow_modulus_eq_one_of_mem_modelBase S e hy)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨k, hk⟩

theorem order_thirty_two_model [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ x y : G, x * y ≠ y * x) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ 2)) :
    let s := wreathModelHom S e (Original.s (2 ^ 2))
    let t := wreathModelHom S e (Original.t (2 ^ 2))
    let w := wreathModelHom S e (Original.z (2 ^ 2))
    let U := Subgroup.closure {s, t}
    let a := s * t
    let x := a ^ 2
    let ρ := s * w
    (∃ σ υ g : G, ((σ = s ∧ υ = t) ∨ (σ = s ^ 2 * t ^ 3 ∧ υ = s ^ 3 * t ^ 2)) ∧
      IsAdaptedBase U a w σ υ g) ∧
    ∀ σ υ g : G, IsAdaptedBase U a w σ υ g →
      let b := σ * υ⁻¹
      let O : Fin 5 → Set G := ![{1}, {x, σ ^ 2, υ ^ 2}, {a, σ⁻¹, υ⁻¹}, {a⁻¹, σ, υ},
        {b, b⁻¹, σ * υ ^ 2, σ ^ 2 * υ, σ ^ 3 * υ ^ 2, σ ^ 2 * υ ^ 3}]
      let r : Fin 6 → G := ![x, a, a⁻¹, b, ρ, ρ ^ 3]
      (∀ i, O i ⊆ U) ∧ (∀ u ∈ U, ∃! i, u ∈ O i) ∧
      (∀ u ∈ U, ∀ v ∈ U, IsConj u v ↔ ∃ i, u ∈ O i ∧ v ∈ O i) ∧
      (∀ y : G, (∃ k : ℕ, orderOf y = 2 ^ k) →
        (∃ u ∈ U, IsConj y u) ∨ IsConj y ρ ∨ IsConj y (ρ ^ 3)) ∧
      (∀ u ∈ U, ¬ IsConj ρ u ∧ ¬ IsConj (ρ ^ 3) u) ∧ ¬ IsConj ρ (ρ ^ 3) ∧
      {y : G | y ∈ (S : Subgroup G) ∧ IsConj ρ y} =
        {y : G | ∃ j k : ℕ, (j + k) % 4 = 1 ∧ y = s ^ j * t ^ k * w} ∧
      {y : G | y ∈ (S : Subgroup G) ∧ IsConj (ρ ^ 3) y} =
        {y : G | ∃ j k : ℕ, (j + k) % 4 = 3 ∧ y = s ^ j * t ^ k * w} ∧
      (∀ i, r i ≠ 1 ∧ ∃ k : ℕ, orderOf (r i) = 2 ^ k) ∧
      (∀ i j, IsConj (r i) (r j) → i = j) ∧
      (∀ y : G, y ≠ 1 → (∃ k : ℕ, orderOf y = 2 ^ k) → ∃ i, IsConj y (r i)) ∧
      IsConj b b⁻¹ ∧ ¬ IsConj b a ∧ ¬ IsConj b a⁻¹ ∧
      Subgroup.centralizer {b} ⊓ (S : Subgroup G) = U ∧
      ∀ b' ∈ (S : Subgroup G), IsConj b b' →
        Nat.card (Subgroup.centralizer {b'} ⊓ (S : Subgroup G) : Subgroup G) ≤ 16 := by
  intro s t w U a x ρ
  have hU : U = modelBase S e := by
    rw [modelBase, ← Original.U_eq, Original.U, MonoidHom.map_closure, Set.image_pair]
  have ha : a = wreathModelHom S e (Original.a (2 ^ 2)) := by
    rw [Original.a, map_mul]
  clear_value U a
  subst hU ha
  refine ⟨exists_isAdaptedBase_special hnonab, ?_⟩
  intro σ υ g h b O r
  have hUU : ∀ p q : ZMod 4 × ZMod 4, IsConj (coord σ υ p) (coord σ υ q) ↔ orbitRel p q :=
    isConj_coord_iff h
  have hxc : x = coord σ υ (2, 2) := by
    change wreathModelHom S e (Original.a (2 ^ 2)) ^ 2 = _
    rw [a_eq_coord h, coord_pow' h]
    rfl
  have hac := a_eq_coord h
  have haic : (wreathModelHom S e (Original.a (2 ^ 2)))⁻¹ = coord σ υ (3, 3) := by
    rw [hac, coord_inv' h]
    rfl
  have hbc : b = coord σ υ (1, 3) := b_eq_coord h
  have hbic : b⁻¹ = coord σ υ (3, 1) := by
    rw [hbc, coord_inv' h]
    rfl
  have hρU := fun u (hu : u ∈ modelBase S e) => not_isConj_root_base S e hu
  have hρρ := not_isConj_root_root_cube S e
  have hstw : ∀ j k : ℕ, s ^ j * t ^ k * w ∈ (S : Subgroup G) := fun j k =>
    (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
      ((S : Subgroup G).pow_mem (wreathModelHom_mem S e _) _)
      ((S : Subgroup G).pow_mem (wreathModelHom_mem S e _) _)) (wreathModelHom_mem S e _)
  have hnotZ : ∀ c : G, c ∈ modelCenter S e → ¬ IsConj b c := by
    intro c hc hbc'
    rw [modelCenter_eq_zpowers] at hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [hbc, hac, coord_zpow' h, hUU] at hbc'
    have hk : ∀ c : ZMod 4, ¬ orbitRel (1, 3) (c, c) := by decide
    have hk' : (k • ((1, 1) : ZMod 4 × ZMod 4)) = ((k : ZMod 4), (k : ZMod 4)) :=
      Prod.ext (by simp) (by simp)
    rw [hk'] at hbc'
    exact hk (k : ZMod 4) hbc'
  have hbZ : b ∉ modelCenter S e := fun hb => hnotZ b hb (IsConj.refl b)
  have hbB : b ∈ modelBase S e := by
    rw [hbc]
    exact coord_mem_base h _
  have hr0 : r 0 = coord σ υ (2, 2) := hxc
  have hr1 : r 1 = coord σ υ (1, 1) := hac
  have hr2 : r 2 = coord σ υ (3, 3) := haic
  have hr3 : r 3 = coord σ υ (1, 3) := hbc
  have hne1 : ∀ p : ZMod 4 × ZMod 4, p ≠ 0 → coord σ υ p ≠ 1 := by
    intro p hp hp1
    apply hp
    apply coord_inj h
    rw [hp1, coord_zero]
  have hρ8 := orderOf_root S e
  have hρ38 := orderOf_root_cube S e
  have hUU' : ∀ p q : ZMod 4 × ZMod 4, IsConj (coord σ υ p) (coord σ υ q) → orbitRel p q :=
    fun p q hpq => (hUU p q).mp hpq
  refine ⟨fun i => baseClasses_subset h i, fun u hu => existsUnique_mem_baseClasses h hu,
    fun u hu v hv => isConj_iff_mem_baseClasses h hu hv, two_element_cases S e hnonab,
    hρU, hρρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, centralizer_inf_sylow_eq S e hbB hbZ, ?_⟩
  · ext y
    constructor
    · rintro ⟨hy, hc⟩
      exact (isConj_root_iff S e hy).mp hc
    · rintro ⟨j, k, hjk, rfl⟩
      exact ⟨hstw j k, (isConj_root_iff S e (hstw j k)).mpr ⟨j, k, hjk, rfl⟩⟩
  · ext y
    constructor
    · rintro ⟨hy, hc⟩
      exact (isConj_root_cube_iff S e hy).mp hc
    · rintro ⟨j, k, hjk, rfl⟩
      exact ⟨hstw j k, (isConj_root_cube_iff S e (hstw j k)).mpr ⟨j, k, hjk, rfl⟩⟩
  ·
    have hcase : ∀ p : ZMod 4 × ZMod 4, p ≠ 0 →
        coord σ υ p ≠ 1 ∧ ∃ k : ℕ, orderOf (coord σ υ p) = 2 ^ k :=
      fun p hp => ⟨hne1 p hp, exists_two_pow_of_mem_base (coord_mem_base h p)⟩
    intro i
    fin_cases i
    · show x ≠ 1 ∧ ∃ k : ℕ, orderOf x = 2 ^ k
      rw [hxc]
      exact hcase (2, 2) (by decide)
    · show wreathModelHom S e (Original.a (2 ^ 2)) ≠ 1 ∧
        ∃ k : ℕ, orderOf (wreathModelHom S e (Original.a (2 ^ 2))) = 2 ^ k
      rw [hac]
      exact hcase (1, 1) (by decide)
    · show (wreathModelHom S e (Original.a (2 ^ 2)))⁻¹ ≠ 1 ∧
        ∃ k : ℕ, orderOf (wreathModelHom S e (Original.a (2 ^ 2)))⁻¹ = 2 ^ k
      rw [haic]
      exact hcase (3, 3) (by decide)
    · show b ≠ 1 ∧ ∃ k : ℕ, orderOf b = 2 ^ k
      rw [hbc]
      exact hcase (1, 3) (by decide)
    · show ρ ≠ 1 ∧ ∃ k : ℕ, orderOf ρ = 2 ^ k
      refine ⟨fun h1 => ?_, 3, hρ8⟩
      change ρ = 1 at h1
      rw [show ρ = wreathModelHom S e (Original.s (2 ^ 2)) *
        wreathModelHom S e (Original.z (2 ^ 2)) from rfl] at h1
      rw [h1, orderOf_one] at hρ8
      omega
    · show ρ ^ 3 ≠ 1 ∧ ∃ k : ℕ, orderOf (ρ ^ 3) = 2 ^ k
      refine ⟨fun h1 => ?_, 3, hρ38⟩
      rw [show ρ = wreathModelHom S e (Original.s (2 ^ 2)) *
        wreathModelHom S e (Original.z (2 ^ 2)) from rfl] at h1
      rw [h1, orderOf_one] at hρ38
      omega
  ·
    have hmem : ∀ p : ZMod 4 × ZMod 4, coord σ υ p ∈ modelBase S e := coord_mem_base h
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [r, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] at hij
    all_goals first
      | rfl
      | (exfalso
         try simp only [hxc, hac, hbc, coord_inv' h] at hij
         first
          | exact absurd (hUU' _ _ hij) (by decide)
          | exact hρρ hij
          | exact hρρ hij.symm
          | exact (hρU _ (hmem _)).1 hij
          | exact (hρU _ (hmem _)).1 hij.symm
          | exact (hρU _ (hmem _)).2 hij
          | exact (hρU _ (hmem _)).2 hij.symm)
  ·
    intro y hy1 hy
    rcases two_element_cases S e hnonab y hy with ⟨u, hu, hyu⟩ | hyρ | hyρ3
    · obtain ⟨p, rfl⟩ := exists_coord_of_mem h hu
      have hp : p ≠ 0 := by
        rintro rfl
        rw [coord_zero, isConj_one_left] at hyu
        exact hy1 hyu
      have hcases : ∀ q : ZMod 4 × ZMod 4, q ≠ 0 → orbitRel q (2, 2) ∨ orbitRel q (1, 1) ∨
          orbitRel q (3, 3) ∨ orbitRel q (1, 3) := by decide
      rcases hcases p hp with hq | hq | hq | hq
      · exact ⟨0, hyu.trans (by rw [hr0]; exact (hUU _ _).mpr hq)⟩
      · exact ⟨1, hyu.trans (by rw [hr1]; exact (hUU _ _).mpr hq)⟩
      · exact ⟨2, hyu.trans (by rw [hr2]; exact (hUU _ _).mpr hq)⟩
      · exact ⟨3, hyu.trans (by rw [hr3]; exact (hUU _ _).mpr hq)⟩
    · exact ⟨4, hyρ⟩
    · exact ⟨5, hyρ3⟩
  · rw [hbic, hbc, hUU]
    decide
  · rw [hbc, hac, hUU]
    decide
  · rw [hbc, haic, hUU]
    decide
  · intro b' hb'S hbb'
    apply card_centralizer_inf_sylow_le S e hb'S
    intro hb'Z
    exact hnotZ b' hb'Z hbb'

theorem order_thirty_two_wreath_adapted_base_and_exact_two_fusion [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x) (S : Sylow 2 G)
    (e : S ≃* Wreath 4) :
    let s := wreathModelHom S e (Original.s 4)
    let t := wreathModelHom S e (Original.t 4)
    let w := wreathModelHom S e (Original.z 4)
    let U := Subgroup.closure {s, t}
    let a := s * t
    let x := a ^ 2
    let ρ := s * w
    (∃ σ υ g : G, ((σ = s ∧ υ = t) ∨ (σ = s ^ 2 * t ^ 3 ∧ υ = s ^ 3 * t ^ 2)) ∧
      IsAdaptedBase U a w σ υ g) ∧
    ∀ σ υ g : G, IsAdaptedBase U a w σ υ g →
      let b := σ * υ⁻¹
      let O : Fin 5 → Set G := ![{1}, {x, σ ^ 2, υ ^ 2}, {a, σ⁻¹, υ⁻¹}, {a⁻¹, σ, υ},
        {b, b⁻¹, σ * υ ^ 2, σ ^ 2 * υ, σ ^ 3 * υ ^ 2, σ ^ 2 * υ ^ 3}]
      let r : Fin 6 → G := ![x, a, a⁻¹, b, ρ, ρ ^ 3]
      (∀ i, O i ⊆ U) ∧ (∀ u ∈ U, ∃! i, u ∈ O i) ∧
      (∀ u ∈ U, ∀ v ∈ U, IsConj u v ↔ ∃ i, u ∈ O i ∧ v ∈ O i) ∧
      (∀ y : G, (∃ k : ℕ, orderOf y = 2 ^ k) →
        (∃ u ∈ U, IsConj y u) ∨ IsConj y ρ ∨ IsConj y (ρ ^ 3)) ∧
      (∀ u ∈ U, ¬ IsConj ρ u ∧ ¬ IsConj (ρ ^ 3) u) ∧ ¬ IsConj ρ (ρ ^ 3) ∧
      {y : G | y ∈ (S : Subgroup G) ∧ IsConj ρ y} =
        {y : G | ∃ j k : ℕ, (j + k) % 4 = 1 ∧ y = s ^ j * t ^ k * w} ∧
      {y : G | y ∈ (S : Subgroup G) ∧ IsConj (ρ ^ 3) y} =
        {y : G | ∃ j k : ℕ, (j + k) % 4 = 3 ∧ y = s ^ j * t ^ k * w} ∧
      (∀ i, r i ≠ 1 ∧ ∃ k : ℕ, orderOf (r i) = 2 ^ k) ∧
      (∀ i j, IsConj (r i) (r j) → i = j) ∧
      (∀ y : G, y ≠ 1 → (∃ k : ℕ, orderOf y = 2 ^ k) → ∃ i, IsConj y (r i)) ∧
      IsConj b b⁻¹ ∧ ¬ IsConj b a ∧ ¬ IsConj b a⁻¹ ∧
      Subgroup.centralizer {b} ⊓ (S : Subgroup G) = U ∧
      ∀ b' ∈ (S : Subgroup G), IsConj b b' →
        Nat.card (Subgroup.centralizer {b'} ⊓ (S : Subgroup G) : Subgroup G) ≤ 16 :=
  order_thirty_two_model hnonab S e

end CFSG.Wreathed.OrderThirtyTwo
