module

public import CFSG.ClassicalInvolution.Asc77.AscSixEta

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

section Finite

variable [Finite G]

theorem exists_conj_sylow_ge {S : Sylow 2 G} {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H)
    {U : Subgroup G} (hU : IsPGroup 2 U) (hUH : U ≤ H) :
    ∃ h ∈ H, U ≤ conjSub h (S : Subgroup G) := by
  have hP : IsPGroup 2 (U.subgroupOf H) := hU.comap_subtype
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hP
  obtain ⟨h, hh⟩ := exists_conjSub_eq_of_sylow (G := ↥H) (S.subtype hSH) Q
  refine ⟨h, h.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hUH hx⟩ : ↥H) ∈ (Q : Subgroup ↥H) :=
    hQ (by simpa [Subgroup.mem_subgroupOf] using hx)
  rw [← hh, mem_conjSub_iff] at hxQ
  rw [mem_conjSub_iff]
  simpa [Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hxQ

theorem mem_zpowers_of_isUniqueInvolution {K : Subgroup G} {z w : G}
    (hz : IsUniqueInvolution K z) (hwK : w ∈ K) (hw1 : w ≠ 1)
    (hw2 : IsPGroup 2 (Subgroup.zpowers w)) : z ∈ Subgroup.zpowers w := by
  obtain ⟨n, hn⟩ := hw2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hw1
    rw [pow_zero, orderOf_eq_one_iff] at hn
    exact hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hyK : w ^ 2 ^ m ∈ K := K.pow_mem hwK _
  have hy2 : (w ^ 2 ^ m) * (w ^ 2 ^ m) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    rw [← hn]
    exact pow_orderOf_eq_one w
  have hy1 : w ^ 2 ^ m ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by positivity)
    rw [hn]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases hz.unique _ hyK hy2 with h | h
  · exact absurd h hy1
  · rw [← h]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers w) _

end Finite

theorem centralizer_zpowers_eq_singleton (u : G) :
    Subgroup.centralizer (Subgroup.zpowers u : Set G) = Subgroup.centralizer ({u} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem sq_eq_one_of_mem_closure {W : Subgroup G} (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    {X : Set G} (hXW : X ⊆ W) (hX : ∀ x ∈ X, x * x = 1) {e : G}
    (he : e ∈ Subgroup.closure X) : e * e = 1 := by
  have hcl : Subgroup.closure X ≤ W := (Subgroup.closure_le W).mpr hXW
  induction he using Subgroup.closure_induction with
  | mem x hx => exact hX x hx
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab : a * b = b * a := hW a (hcl ha) b (hcl hb)
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha =>
    have : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [this, iha, inv_one]

section Counting

variable [Finite G]

theorem natCard_le_sq_inf_centralizer {E : Subgroup G} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) {b : G} (hb2 : b * b = 1) (hbE : conjSub b E = E) :
    Nat.card E ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({b} : Set G)) ^ 2 := by
  have hmem : ∀ x : ↥E, b * (x : G) * b⁻¹ ∈ E := fun x => by
    have := conj_mem_conjSub (n := b) x.2
    rwa [hbE] at this
  let ψ : ↥E →* ↥E :=
    MonoidHom.mk' (fun x => x * ⟨b * (x : G) * b⁻¹, hmem x⟩) (fun x y => by
      apply Subtype.ext
      have hxy : (x : G) * (b * (y : G) * b⁻¹) = (b * (y : G) * b⁻¹) * x :=
        hcomm _ x.2 _ (hmem y)
      have hxy' : (y : G) * (b * (x : G) * b⁻¹) = (b * (x : G) * b⁻¹) * y :=
        hcomm _ y.2 _ (hmem x)
      show (x : G) * y * (b * ((x : G) * y) * b⁻¹) =
        ((x : G) * (b * x * b⁻¹)) * ((y : G) * (b * y * b⁻¹))
      calc (x : G) * y * (b * ((x : G) * y) * b⁻¹)
          = (x : G) * (y * (b * x * b⁻¹)) * (b * y * b⁻¹) := by group
        _ = (x : G) * ((b * x * b⁻¹) * y) * (b * y * b⁻¹) := by rw [hxy']
        _ = ((x : G) * (b * x * b⁻¹)) * ((y : G) * (b * y * b⁻¹)) := by group)
  set C : Subgroup ↥E := (E ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf E with hC
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hker : ψ.ker ≤ C := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (x : G) * (b * (x : G) * b⁻¹) = 1 := congrArg Subtype.val hx
    have h2 : b * (x : G) * b⁻¹ = (x : G) := by
      have h3 : b * (x : G) * b⁻¹ = (x : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h3]
      exact inv_eq_of_mul_eq_one_right (hsq x x.2)
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hrange : ψ.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨(ψ x).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxb : (b * (x : G) * b⁻¹) * (x : G) = (x : G) * (b * (x : G) * b⁻¹) :=
      (hcomm _ (hmem x) _ x.2)
    show ((x : G) * (b * x * b⁻¹)) * b = b * ((x : G) * (b * x * b⁻¹))
    have e : b * ((x : G) * (b * x * b⁻¹)) * b⁻¹ = (x : G) * (b * x * b⁻¹) := by
      calc b * ((x : G) * (b * x * b⁻¹)) * b⁻¹
          = (b * x * b⁻¹) * ((b * b) * x * (b * b)⁻¹) := by group
        _ = (b * x * b⁻¹) * x := by rw [hb2]; group
        _ = x * (b * x * b⁻¹) := hxb
    exact (mul_inv_eq_iff_eq_mul.mp e).symm
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have h2 : Nat.card ψ.ker ≤ Nat.card C := Subgroup.card_le_of_le hker
  have h3 : Nat.card ψ.range ≤ Nat.card C := Subgroup.card_le_of_le hrange
  have h4 : Nat.card C = Nat.card ↥(E ⊓ Subgroup.centralizer ({b} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← h1, pow_two, ← h4]
  exact Nat.mul_le_mul h2 h3

end Counting

theorem exists_two_ne_one_of_four_le {A : Subgroup G} (h : 4 ≤ Nat.card A) :
    ∃ u ∈ A, ∃ v ∈ A, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  by_contra hno
  push Not at hno
  by_cases h1 : ∀ x ∈ A, x = 1
  · have := natCard_subgroup_le_two_of_subset (A := A) (a := 1) (b := 1) fun x hx =>
      Or.inl (h1 x hx)
    omega
  · push Not at h1
    obtain ⟨u, hu, hu1⟩ := h1
    have := natCard_subgroup_le_two_of_subset (A := A) (a := 1) (b := u) fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hno x hx u hu hx1 hu1)
    omega

end CFSG.ClassicalInvolution.Asc77
