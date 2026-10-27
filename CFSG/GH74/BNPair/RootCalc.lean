module

public import CFSG.GH74.BNPair.RootGroups

public section

namespace CFSG.GH74.BNPair

universe u

open scoped Pointwise

section ChainProd

variable {X : Type*} [Group X]

theorem one_mem_chainProd (A : ℤ → Subgroup X) : ∀ l : List ℤ, (1 : X) ∈ chainProd A l
  | [] => by simp [chainProd]
  | k :: l => by
    simp only [chainProd, List.map_cons, List.prod_cons]
    exact Set.mem_mul.2 ⟨1, (A k).one_mem, 1, one_mem_chainProd A l, by simp⟩

theorem mem_chainProd_of_mem (A : ℤ → Subgroup X) {k : ℤ} {l : List ℤ} (hk : k ∈ l) {x : X}
    (hx : x ∈ A k) : x ∈ chainProd A l := by
  induction l with
  | nil => simp at hk
  | cons j l ih =>
    simp only [chainProd, List.map_cons, List.prod_cons]
    rcases List.mem_cons.1 hk with rfl | h'
    · exact Set.mem_mul.2 ⟨x, hx, 1, one_mem_chainProd A l, by simp⟩
    · exact Set.mem_mul.2 ⟨1, (A j).one_mem, x, ih h', by simp⟩

theorem chainProd_conj_mem (A : ℤ → Subgroup X) (P : Subgroup X) (g : X) :
    ∀ l : List ℤ, (∀ k ∈ l, ∀ y ∈ A k, g * y * g⁻¹ ∈ P) → ∀ x ∈ chainProd A l,
      g * x * g⁻¹ ∈ P
  | [], _, x, hx => by
    simp only [chainProd, List.map_nil, List.prod_nil, Set.mem_one] at hx
    subst hx
    simp
  | k :: l, h, x, hx => by
    simp only [chainProd, List.map_cons, List.prod_cons] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
    have h1 := h k (by simp) a ha
    have h2 := chainProd_conj_mem A P g l (fun k' hk' => h k' (by simp [hk'])) b hb
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact P.mul_mem h1 h2

theorem chainProd_cons (A : ℤ → Subgroup X) (k : ℤ) (l : List ℤ) :
    chainProd A (k :: l) = (A k : Set X) * chainProd A l := by
  simp [chainProd]

theorem chainProd_append (A : ℤ → Subgroup X) (l l' : List ℤ) :
    chainProd A (l ++ l') = chainProd A l * chainProd A l' := by
  simp [chainProd, List.map_append, List.prod_append]

theorem chainProd_singleton (A : ℤ → Subgroup X) (k : ℤ) :
    chainProd A [k] = (A k : Set X) := by
  simp [chainProd]

theorem intList_cons {i j : ℤ} (h : i ≤ j) : intList i j = i :: intList (i + 1) j := by
  apply List.ext_getElem
  · simp [intList]
    omega
  · intro t h1 h2
    simp only [intList, List.getElem_map, List.getElem_range]
    cases t with
    | zero => simp
    | succ t =>
      simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range]
      push_cast
      ring

theorem intList_snoc {i j : ℤ} (h : i ≤ j) : intList i j = intList i (j - 1) ++ [j] := by
  apply List.ext_getElem
  · simp [intList]
    omega
  · intro t h1 h2
    simp only [intList, List.getElem_map, List.getElem_range] at h1 ⊢
    by_cases ht : t < (List.map (fun k : ℕ => i + (k : ℤ)) (List.range (j - 1 + 1 - i).toNat)).length
    · rw [List.getElem_append_left (by simpa using ht)]
      simp
    · rw [List.getElem_append_right (by simpa using ht)]
      simp only [List.length_map, List.length_range] at ht
      have : t = (j - i).toNat := by simp at h1; omega
      simp [this]
      omega

end ChainProd

namespace RankTwoSystem

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem U_le_B : D.U ≤ D.B := by
  intro u hu
  have : u ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) :=
    Set.mem_mul.2 ⟨1, (D.B ⊓ D.N).one_mem, u, hu, by simp⟩
  rw [← D.isSplit.2] at this
  exact this

theorem root_le_U {k : ℤ} (hk1 : 1 ≤ k) (hkn : k ≤ n) : D.root k ≤ D.U := by
  intro x hx
  have : x ∈ chainProd D.root (intList 1 n) :=
    mem_chainProd_of_mem D.root (mem_intList_iff.2 ⟨hk1, hkn⟩) hx
  rw [← D.roots.carrier_eq] at this
  exact this

theorem root_le_B {k : ℤ} (hk1 : 1 ≤ k) (hkn : k ≤ n) : D.root k ≤ D.B :=
  (D.root_le_U hk1 hkn).trans D.U_le_B

theorem conj_mem_root₁ (m : D.N) (hm : (m : D.Weyl) = D.w₁) {k : ℤ} (hk1 : 2 ≤ k) (hkn : k ≤ n)
    {y : X} (hy : y ∈ D.root k) : (m : X) * y * (m : X)⁻¹ ∈ D.root ((n : ℤ) + 2 - k) := by
  have hm' : ((m⁻¹ : D.N) : D.Weyl) = D.w₁ := by
    rw [QuotientGroup.mk_inv, hm]
    exact inv_eq_of_mul_eq_one_right D.w₁_mul_self
  have h := (D.roots.action₁ (m⁻¹) hm').2.2 k hk1 hkn
  have hmem : (m : X) * y * (m : X)⁻¹ ∈ conjBy ((m⁻¹ : D.N) : X) (D.root k) :=
    ⟨y, hy, by simp [MulAut.conj_apply]⟩
  rw [h.1] at hmem
  exact hmem

theorem conj_mem_root₂ (m : D.N) (hm : (m : D.Weyl) = D.w₂) {k : ℤ} (hk1 : 1 ≤ k)
    (hkn : k ≤ (n : ℤ) - 1) {y : X} (hy : y ∈ D.root k) :
    (m : X) * y * (m : X)⁻¹ ∈ D.root ((n : ℤ) - k) := by
  have hm' : ((m⁻¹ : D.N) : D.Weyl) = D.w₂ := by
    rw [QuotientGroup.mk_inv, hm]
    exact inv_eq_of_mul_eq_one_right D.w₂_mul_self
  have h := (D.roots.action₂ (m⁻¹) hm').2.2 k hk1 hkn
  have hmem : (m : X) * y * (m : X)⁻¹ ∈ conjBy ((m⁻¹ : D.N) : X) (D.root k) :=
    ⟨y, hy, by simp [MulAut.conj_apply]⟩
  rw [h.1] at hmem
  exact hmem

theorem B_normalizes_V₁ {V : Subgroup X}
    (hVc : (V : Set X) = chainProd D.root (intList 2 n))
    (hVn : ∀ x ∈ D.root (2 - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) :
    ∀ b ∈ D.B, ∀ y ∈ V, b * y * b⁻¹ ∈ V := by
  intro b hb y hy
  have hn := D.three_le
  have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hb'
  have hu' : u ∈ chainProd D.root (intList 1 n) := D.roots.carrier_eq ▸ hu
  rw [intList_cons (by omega : (1 : ℤ) ≤ n), show (1 : ℤ) + 1 = 2 by norm_num,
    chainProd_cons] at hu'
  obtain ⟨x₁, hx₁, v₀, hv₀, rfl⟩ := Set.mem_mul.1 hu'
  have hv₀V : v₀ ∈ V := by
    rw [← SetLike.mem_coe, hVc]
    exact hv₀
  have step1 : v₀ * y * v₀⁻¹ ∈ V := V.mul_mem (V.mul_mem hv₀V hy) (V.inv_mem hv₀V)
  have step2 : x₁ * (v₀ * y * v₀⁻¹) * x₁⁻¹ ∈ V := hVn x₁ (by simpa using hx₁) _ step1
  have step3 : h * (x₁ * (v₀ * y * v₀⁻¹) * x₁⁻¹) * h⁻¹ ∈ V := by
    have hmem : x₁ * (v₀ * y * v₀⁻¹) * x₁⁻¹ ∈ chainProd D.root (intList 2 n) := by
      rw [← hVc]
      exact step2
    refine chainProd_conj_mem D.root V h (intList 2 n) (fun k hk y' hy' => ?_) _ hmem
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    have hinv := D.roots.invariant k ⟨by omega, by omega⟩ h hh y' hy'
    have hle : D.root k ≤ V := fun z hz => by
      rw [← SetLike.mem_coe, hVc]
      exact mem_chainProd_of_mem D.root hk hz
    exact hle hinv
  have e : (h * (x₁ * v₀)) * y * (h * (x₁ * v₀))⁻¹ =
      h * (x₁ * (v₀ * y * v₀⁻¹) * x₁⁻¹) * h⁻¹ := by group
  rw [e]
  exact step3

theorem B_normalizes_V₂ {V : Subgroup X}
    (hVc : (V : Set X) = chainProd D.root (intList 1 ((n : ℤ) - 1)))
    (hVn : ∀ x ∈ D.root ((n : ℤ) - 1 + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) :
    ∀ b ∈ D.B, ∀ y ∈ V, b * y * b⁻¹ ∈ V := by
  intro b hb y hy
  have hn := D.three_le
  have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hb'
  have hu' : u ∈ chainProd D.root (intList 1 n) := D.roots.carrier_eq ▸ hu
  rw [intList_snoc (by omega : (1 : ℤ) ≤ n), chainProd_append, chainProd_singleton] at hu'
  obtain ⟨v₀, hv₀, xn, hxn, rfl⟩ := Set.mem_mul.1 hu'
  have hv₀V : v₀ ∈ V := by
    rw [← SetLike.mem_coe, hVc]
    exact hv₀
  have step1 : xn * y * xn⁻¹ ∈ V := hVn xn (by simpa using hxn) _ hy
  have step2 : v₀ * (xn * y * xn⁻¹) * v₀⁻¹ ∈ V := V.mul_mem (V.mul_mem hv₀V step1) (V.inv_mem hv₀V)
  have step3 : h * (v₀ * (xn * y * xn⁻¹) * v₀⁻¹) * h⁻¹ ∈ V := by
    have hmem : v₀ * (xn * y * xn⁻¹) * v₀⁻¹ ∈ chainProd D.root (intList 1 ((n : ℤ) - 1)) := by
      rw [← hVc]
      exact step2
    refine chainProd_conj_mem D.root V h (intList 1 ((n : ℤ) - 1)) (fun k hk y' hy' => ?_) _ hmem
    obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    have hinv := D.roots.invariant k ⟨by omega, by omega⟩ h hh y' hy'
    have hle : D.root k ≤ V := fun z hz => by
      rw [← SetLike.mem_coe, hVc]
      exact mem_chainProd_of_mem D.root hk hz
    exact hle hinv
  have e : (h * (v₀ * xn)) * y * (h * (v₀ * xn))⁻¹ =
      h * (v₀ * (xn * y * xn⁻¹) * v₀⁻¹) * h⁻¹ := by group
  rw [e]
  exact step3

theorem root_core_w₁ (m : D.N) (hm : (m : D.Weyl) = D.w₁) {j : ℤ} (hj1 : 2 ≤ j) (hjn : j ≤ n)
    {p x : X} (hp : p ∈ D.B ∨ p ∈ dc D.B D.N D.w₁) (hx : x ∈ D.root j) :
    p * x * p⁻¹ ∈ D.B := by
  have hn := D.three_le
  have hxB : x ∈ D.B := D.root_le_B (by omega) hjn hx
  rcases hp with hp | hp
  · exact D.B.mul_mem (D.B.mul_mem hp hxB) (D.B.inv_mem hp)
  · obtain ⟨b, hb, b', hb', rfl⟩ := (mem_dc_of_lift hm).1 hp
    obtain ⟨V, hVc, -, hVn, -⟩ := D.roots.subgroup 2 (n : ℤ) (by norm_num) (by omega) le_rfl
    have hxV : x ∈ V := by
      rw [← SetLike.mem_coe, hVc]
      exact mem_chainProd_of_mem D.root (mem_intList_iff.2 ⟨hj1, hjn⟩) hx
    have hy : b' * x * b'⁻¹ ∈ V := D.B_normalizes_V₁ hVc (hVn (by norm_num)) b' hb' x hxV
    have hmy : (m : X) * (b' * x * b'⁻¹) * (m : X)⁻¹ ∈ D.B := by
      refine chainProd_conj_mem D.root D.B (m : X) (intList 2 n) (fun k hk y' hy' => ?_) _
        (by rw [← hVc]; exact hy)
      obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
      exact D.root_le_B (by omega) (by omega) (D.conj_mem_root₁ m hm hk1 hk2 hy')
    have e : b * (m : X) * b' * x * (b * (m : X) * b')⁻¹ =
        b * ((m : X) * (b' * x * b'⁻¹) * (m : X)⁻¹) * b⁻¹ := by group
    rw [e]
    exact D.B.mul_mem (D.B.mul_mem hb hmy) (D.B.inv_mem hb)

theorem root_core_w₂ (m : D.N) (hm : (m : D.Weyl) = D.w₂) {j : ℤ} (hj1 : 1 ≤ j)
    (hjn : j ≤ (n : ℤ) - 1) {p x : X} (hp : p ∈ D.B ∨ p ∈ dc D.B D.N D.w₂) (hx : x ∈ D.root j) :
    p * x * p⁻¹ ∈ D.B := by
  have hn := D.three_le
  have hxB : x ∈ D.B := D.root_le_B hj1 (by omega) hx
  rcases hp with hp | hp
  · exact D.B.mul_mem (D.B.mul_mem hp hxB) (D.B.inv_mem hp)
  · obtain ⟨b, hb, b', hb', rfl⟩ := (mem_dc_of_lift hm).1 hp
    obtain ⟨V, hVc, -, -, hVn⟩ :=
      D.roots.subgroup 1 ((n : ℤ) - 1) le_rfl (by omega) (by omega)
    have hxV : x ∈ V := by
      rw [← SetLike.mem_coe, hVc]
      exact mem_chainProd_of_mem D.root (mem_intList_iff.2 ⟨hj1, hjn⟩) hx
    have hy : b' * x * b'⁻¹ ∈ V := D.B_normalizes_V₂ hVc (hVn (by omega)) b' hb' x hxV
    have hmy : (m : X) * (b' * x * b'⁻¹) * (m : X)⁻¹ ∈ D.B := by
      refine chainProd_conj_mem D.root D.B (m : X) (intList 1 ((n : ℤ) - 1))
        (fun k hk y' hy' => ?_) _ (by rw [← hVc]; exact hy)
      obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
      exact D.root_le_B (by omega) (by omega) (D.conj_mem_root₂ m hm hk1 hk2 hy')
    have e : b * (m : X) * b' * x * (b * (m : X) * b')⁻¹ =
        b * ((m : X) * (b' * x * b'⁻¹) * (m : X)⁻¹) * b⁻¹ := by group
    rw [e]
    exact D.B.mul_mem (D.B.mul_mem hb hmy) (D.B.inv_mem hb)

end RankTwoSystem

end CFSG.GH74.BNPair
