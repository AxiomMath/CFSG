module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

theorem exists_conj_eq_of_odd_of_two_classes {G : Type*} [Group G] (J : Subgroup G) {a b r : G}
    (ha : a * a = 1) (haJ : ∀ j ∈ J, a * j * a⁻¹ ∈ J)
    (hrJ : ∀ j ∈ J, r * j * r⁻¹ ∈ J) (hrJ' : ∀ j ∈ J, r⁻¹ * j * r ∈ J)
    (hS : ∀ x : G, a⁻¹ * x ∈ J → x * x = 1 → ∃ k ∈ J, x = k * a * k⁻¹ ∨ x = k * b * k⁻¹)
    (hra : a⁻¹ * (r * a * r⁻¹) ∈ J) (hodd : Odd (orderOf r)) :
    ∃ k ∈ J, r * a * r⁻¹ = k * a * k⁻¹ := by
  classical
  let T : Set G := {x | ∃ k ∈ J, x = k * a * k⁻¹}
  let S : Set G := {x | a⁻¹ * x ∈ J ∧ x * x = 1}
  let φ : G → G := fun x => r * x * r⁻¹
  have haT : a ∈ T := by
    exact ⟨1, J.one_mem, by simp⟩
  have haS : a ∈ S := by
    refine ⟨?_, ha⟩
    simp
  have hTS : T ⊆ S := by
    have ha_inv : a⁻¹ = a := mul_eq_one_iff_inv_eq.mp ha
    intro x hx
    simp only [T, Set.mem_setOf_eq] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    constructor
    · have hka : a * k * a ∈ J := by simpa [ha_inv] using haJ k hk
      have hEq : a⁻¹ * (k * a * k⁻¹) = (a * k * a) * k⁻¹ := by
        rw [ha_inv]
        group
      rw [hEq]
      exact J.mul_mem hka (J.inv_mem hk)
    · calc
        (k * a * k⁻¹) * (k * a * k⁻¹) = k * (a * a) * k⁻¹ := by group
        _ = 1 := by rw [ha]; group
  have hT_conj_inv : ∀ {k x : G}, k ∈ J → k * x * k⁻¹ ∈ T → x ∈ T := by
    intro k x hk hx
    simp only [T, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨j, hj, hjk⟩ := hx
    refine ⟨k⁻¹ * j, J.mul_mem (J.inv_mem hk) hj, ?_⟩
    calc
      x = k⁻¹ * (k * x * k⁻¹) * k := by group
      _ = k⁻¹ * (j * a * j⁻¹) * k := by rw [hjk]
      _ = (k⁻¹ * j) * a * (k⁻¹ * j)⁻¹ := by group
  have hφS : ∀ {x : G}, x ∈ S → φ x ∈ S := by
    intro x hx
    simp only [S, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨hxJ, hx2⟩ := hx
    constructor
    · have hEq : a⁻¹ * (r * x * r⁻¹) =
          (a⁻¹ * (r * a * r⁻¹)) * (r * (a⁻¹ * x) * r⁻¹) := by group
      rw [hEq]
      exact J.mul_mem hra (hrJ _ hxJ)
    · calc
        (r * x * r⁻¹) * (r * x * r⁻¹) = r * (x * x) * r⁻¹ := by group
        _ = 1 := by rw [hx2]; group
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    exact (MulAut.conj r).injective (by simpa [φ, MulAut.conj_apply] using hxy)
  by_contra hconcl
  have hφaT : φ a ∉ T := by
    intro hmem
    simp only [T, Set.mem_setOf_eq] at hmem
    obtain ⟨k, hk, hkφ⟩ := hmem
    exact hconcl ⟨k, hk, by simpa [φ] using hkφ⟩
  have hT_forward : ∀ {x : G}, x ∈ T → φ x ∉ T := by
    intro x hxT hφxT
    simp only [T, Set.mem_setOf_eq] at hxT
    obtain ⟨k, hk, rfl⟩ := hxT
    have hm : r * k * r⁻¹ ∈ J := hrJ k hk
    have hEq : φ (k * a * k⁻¹) =
        (r * k * r⁻¹) * φ a * (r * k * r⁻¹)⁻¹ := by
      simp only [φ]
      group
    exact hφaT (hT_conj_inv hm (hEq ▸ hφxT))
  have hT_backward : ∀ {x : G}, x ∈ S → φ x ∉ T → x ∈ T := by
    intro x hxS hφxT
    have hφxS : φ x ∈ S := hφS hxS
    have hφx_b : ∃ k ∈ J, φ x = k * b * k⁻¹ := by
      simp only [S, Set.mem_setOf_eq] at hφxS
      rcases hS (φ x) hφxS.1 hφxS.2 with ⟨k, hk, h | h⟩
      · exfalso
        exact hφxT (by simp only [T, Set.mem_setOf_eq]; exact ⟨k, hk, h⟩)
      · exact ⟨k, hk, h⟩
    have hφa_b : ∃ k ∈ J, φ a = k * b * k⁻¹ := by
      have hφaS : φ a ∈ S := hφS haS
      simp only [S, Set.mem_setOf_eq] at hφaS
      rcases hS (φ a) hφaS.1 hφaS.2 with ⟨k, hk, h | h⟩
      · exfalso
        exact hφaT (by simp only [T, Set.mem_setOf_eq]; exact ⟨k, hk, h⟩)
      · exact ⟨k, hk, h⟩
    obtain ⟨k, hk, hkx⟩ := hφx_b
    obtain ⟨k', hk', hka⟩ := hφa_b
    let m : G := k * k'⁻¹
    have hm : m ∈ J := J.mul_mem hk (J.inv_mem hk')
    have hconj : φ x = m * φ a * m⁻¹ := by
      rw [hkx, hka]
      simp only [m]
      group
    let d : G := r⁻¹ * m * r
    have hd : d ∈ J := hrJ' m hm
    have himage : m * φ a * m⁻¹ = φ (d * a * d⁻¹) := by
      simp only [d, φ]
      group
    have hxt : x = d * a * d⁻¹ := hφ_inj (by rw [hconj, himage])
    exact ⟨d, hd, hxt⟩
  have hkey : ∀ {x : G}, x ∈ S → (x ∈ T ↔ φ x ∉ T) := by
    intro x hxS
    exact ⟨fun hxT => hT_forward hxT, fun hφxT => hT_backward hxS hφxT⟩
  let x : ℕ → G := fun n => φ^[n] a
  have hxstep : ∀ n, x (n + 1) = φ (x n) := by
    intro n
    simp only [x, Function.iterate_succ_apply']
  have hxS : ∀ n, x n ∈ S := by
    intro n
    induction n with
    | zero => simpa [x] using haS
    | succ n ih => rw [hxstep]; exact hφS ih
  have hxT : ∀ n, x n ∈ T ↔ Even n := by
    intro n
    induction n with
    | zero =>
      have hx0 : x 0 = a := by simp [x]
      rw [hx0]
      exact ⟨fun _ => Even.zero, fun _ => haT⟩
    | succ n ih =>
      rw [hxstep, Nat.even_add_one, ← ih]
      exact ⟨fun hφ hx => (hkey (hxS n)).mp hx hφ,
        fun hx => by
          by_contra hφ
          exact hx ((hkey (hxS n)).mpr hφ)⟩
  have hxpow : ∀ n, x n = r ^ n * a * (r ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp [x]
    | succ n ih =>
      rw [hxstep, ih]
      simp only [φ, pow_succ]
      group
  have hxorder : x (orderOf r) = a := by
    rw [hxpow (orderOf r)]
    simp [pow_orderOf_eq_one]
  have hEven : Even (orderOf r) := by
    have hmem : x (orderOf r) ∈ T := by rwa [hxorder]
    exact (hxT (orderOf r)).mp hmem
  exact (Nat.not_even_iff_odd.mpr hodd) hEven

end CFSG.GroupTheory
