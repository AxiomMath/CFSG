module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {Γ : Type} [Group Γ]

private lemma card_conjClass_mul_card_centralizer (g : Γ) :
    Nat.card (conjugatesOf g) * Nat.card (Subgroup.centralizer ({g} : Set Γ)) =
      Nat.card Γ := by
  rw [Nat.card_coe_set_eq (conjugatesOf g), ← Subgroup.index_centralizer_eq_ncard]
  exact Subgroup.index_mul_card _

theorem a6c_lemmaE [Finite Γ] (g : Γ) (S C : Finset Γ) (hS : ∀ s ∈ S, IsConj g s)
    (hC : ∀ c ∈ C, c * g = g * c) (hcard : S.card * C.card = Nat.card Γ) :
    (∀ s, IsConj g s → s ∈ S) ∧ ∀ c, c * g = g * c → c ∈ C := by
  classical
  let K : Set Γ := conjugatesOf g
  let CF : Set Γ := Subgroup.centralizer ({g} : Set Γ)
  have hKfin : K.Finite := K.toFinite
  have hCFfin : CF.Finite := CF.toFinite
  have hSK : (S : Set Γ) ⊆ K := fun s hs => hS s hs
  have hCK : (C : Set Γ) ⊆ CF := fun c hc =>
    (Subgroup.mem_centralizer_singleton_iff).mpr (hC c hc)
  have hSprod : Nat.card (S : Set Γ) * Nat.card (C : Set Γ) = Nat.card Γ := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_coe_finset, Set.ncard_coe_finset]
    exact hcard
  have hKprod : Nat.card K * Nat.card CF = Nat.card Γ :=
    card_conjClass_mul_card_centralizer g
  have hGpos : 0 < Nat.card Γ := by
    haveI : Nonempty Γ := ⟨1⟩
    exact Nat.card_pos
  have hSpos : 0 < Nat.card (S : Set Γ) := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hSprod
    exact hGpos.ne' hSprod.symm
  have hCpos : 0 < Nat.card (C : Set Γ) := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hSprod
    exact hGpos.ne' hSprod.symm
  have hKpos : 0 < Nat.card K := by
    haveI : Nonempty K := ⟨⟨g, IsConj.refl g⟩⟩
    exact Nat.card_pos
  have hleSK : Nat.card (S : Set Γ) ≤ Nat.card K := by
    rw [Nat.card_coe_set_eq (S : Set Γ), Nat.card_coe_set_eq K]
    exact Set.ncard_le_ncard hSK hKfin
  have hleCCF : Nat.card (C : Set Γ) ≤ Nat.card CF := by
    rw [Nat.card_coe_set_eq (C : Set Γ), Nat.card_coe_set_eq CF]
    exact Set.ncard_le_ncard hCK hCFfin
  have hle1 : Nat.card (S : Set Γ) * Nat.card (C : Set Γ) ≤
      Nat.card K * Nat.card (C : Set Γ) :=
    mul_le_mul_left hleSK _
  have hle2 : Nat.card K * Nat.card (C : Set Γ) ≤ Nat.card K * Nat.card CF :=
    mul_le_mul_right hleCCF _
  have hEq1 : Nat.card K * Nat.card (C : Set Γ) = Nat.card K * Nat.card CF := by
    refine le_antisymm hle2 ?_
    rw [hKprod, ← hSprod]
    exact hle1
  have hCeq : Nat.card (C : Set Γ) = Nat.card CF :=
    mul_left_cancel₀ hKpos.ne' hEq1
  have hCeqSet : (C : Set Γ) = CF :=
    Set.Finite.eq_of_subset_of_card_le hCFfin hCK (le_of_eq hCeq.symm)
  have hSeq : Nat.card (S : Set Γ) = Nat.card K := by
    refine mul_right_cancel₀ hCpos.ne' ?_
    rw [hSprod, ← hKprod, hEq1]
  have hSeqSet : (S : Set Γ) = K :=
    Set.Finite.eq_of_subset_of_card_le hKfin hSK (le_of_eq hSeq.symm)
  constructor
  · intro s hs
    have hsK : s ∈ K := hs
    rw [← hSeqSet] at hsK
    exact hsK
  · intro c hc
    have hcCF : c ∈ CF := (Subgroup.mem_centralizer_singleton_iff).mpr hc
    rw [← hCeqSet] at hcCF
    exact hcCF

private lemma conj_pow_two_iterate {g0 n : Γ} (hn : n * g0 * n⁻¹ = g0 ^ 2) (m : ℕ) :
    n ^ m * g0 * (n ^ m)⁻¹ = g0 ^ (2 ^ m) := by
  have hφ : MulAut.conj n g0 = g0 ^ 2 := by
    rw [MulAut.conj_apply]
    exact hn
  have hiter : ∀ m : ℕ, ((MulAut.conj n) ^ m) g0 = g0 ^ (2 ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, MulAut.mul_apply, hφ, map_pow, ih, ← pow_mul, pow_succ]
  calc
    n ^ m * g0 * (n ^ m)⁻¹ = MulAut.conj (n ^ m) g0 := by rw [MulAut.conj_apply]
    _ = ((MulAut.conj n) ^ m) g0 := by rw [map_pow]
    _ = g0 ^ (2 ^ m) := hiter m

private lemma exists_conj_zpow_of_lt_five {g0 n : Γ} (hg0 : g0 ^ 5 = 1)
    (hn : n * g0 * n⁻¹ = g0 ^ 2) {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k < 5) :
    ∃ δ : Γ, δ * g0 ^ k * δ⁻¹ = g0 := by
  interval_cases k
  · exact ⟨1, by simp⟩
  · refine ⟨n⁻¹, ?_⟩
    have h := conj_pow_two_iterate (g0 := g0) (n := n) hn 1
    have h' : n * g0 * n⁻¹ = g0 ^ 2 := by simpa using h
    calc
      n⁻¹ * g0 ^ 2 * (n⁻¹)⁻¹ = n⁻¹ * (n * g0 * n⁻¹) * n := by rw [h']; group
      _ = g0 := by group
  · refine ⟨(n ^ 3)⁻¹, ?_⟩
    have h := conj_pow_two_iterate (g0 := g0) (n := n) hn 3
    have h3 : n ^ 3 * g0 * (n ^ 3)⁻¹ = g0 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 5 + 3 by norm_num, pow_add, hg0, one_mul] at h
      exact h
    calc
      (n ^ 3)⁻¹ * g0 ^ 3 * ((n ^ 3)⁻¹)⁻¹ =
          (n ^ 3)⁻¹ * (n ^ 3 * g0 * (n ^ 3)⁻¹) * n ^ 3 := by rw [h3]; group
      _ = g0 := by group
  · refine ⟨(n ^ 2)⁻¹, ?_⟩
    have h := conj_pow_two_iterate (g0 := g0) (n := n) hn 2
    calc
      (n ^ 2)⁻¹ * g0 ^ 4 * ((n ^ 2)⁻¹)⁻¹ =
          (n ^ 2)⁻¹ * (n ^ 2 * g0 * (n ^ 2)⁻¹) * n ^ 2 := by rw [h]; group
      _ = g0 := by group

theorem a6c_exists_conj_g0 [Finite Γ] (hΓ : ¬ 25 ∣ Nat.card Γ) {g0 n : Γ} (hg0 : g0 ^ 5 = 1)
    (hg1 : g0 ≠ 1) (hn : n * g0 * n⁻¹ = g0 ^ 2) {x : Γ} (hx : x ^ 5 = 1) (hx1 : x ≠ 1) :
    ∃ δ : Γ, δ * x * δ⁻¹ = g0 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hg0ord : orderOf g0 = 5 := orderOf_eq_prime hg0 hg1
  have hxord : orderOf x = 5 := orderOf_eq_prime hx hx1
  have h25 : ¬ 5 ^ 2 ∣ Nat.card Γ := by
    norm_num
    exact hΓ
  obtain ⟨y, hy⟩ := TauCeti.exists_mul_mul_inv_mem_zpowers_of_not_sq_dvd
    (p := 5) (G := Γ) (g := g0) (h := x) h25 hg0ord hxord
  have hy' := (mem_zpowers_iff_mem_range_orderOf (x := g0) (y := y * x * y⁻¹)).mp hy
  rw [hg0ord] at hy'
  obtain ⟨k, hkrange, hkeq⟩ := Finset.mem_image.mp hy'
  have hklt : k < 5 := Finset.mem_range.mp hkrange
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · exfalso
      apply hx1
      have hconj : MulAut.conj y x = 1 := by
        rw [MulAut.conj_apply, ← hkeq]
        simp [hk0]
      exact (MulAut.conj y).injective (by simpa using hconj)
    · exact hk
  obtain ⟨δ0, hδ0⟩ :=
    exists_conj_zpow_of_lt_five hg0 hn (Nat.succ_le_of_lt hkpos) hklt
  refine ⟨δ0 * y, ?_⟩
  calc
    δ0 * y * x * (δ0 * y)⁻¹ = δ0 * (y * x * y⁻¹) * δ0⁻¹ := by group
    _ = δ0 * g0 ^ k * δ0⁻¹ := by rw [hkeq]
    _ = g0 := hδ0

private noncomputable def conjCentralizerEquiv {x y δ : Γ} (h : δ * x * δ⁻¹ = y) :
    centralizer ({x} : Set Γ) ≃ centralizer ({y} : Set Γ) where
  toFun c := ⟨δ * (c : Γ) * δ⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : (c : Γ) * x = x * (c : Γ) :=
      (Subgroup.mem_centralizer_singleton_iff).mp c.2
    rw [← h]
    calc
      δ * (c : Γ) * δ⁻¹ * (δ * x * δ⁻¹) = δ * ((c : Γ) * x) * δ⁻¹ := by group
      _ = δ * (x * (c : Γ)) * δ⁻¹ := by rw [hc]
      _ = (δ * x * δ⁻¹) * (δ * (c : Γ) * δ⁻¹) := by group
    ⟩
  invFun d := ⟨δ⁻¹ * (d : Γ) * δ, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hd : (d : Γ) * y = y * (d : Γ) :=
      (Subgroup.mem_centralizer_singleton_iff).mp d.2
    have hx : x = δ⁻¹ * y * δ := by
      rw [← h]
      group
    rw [hx]
    calc
      δ⁻¹ * (d : Γ) * δ * (δ⁻¹ * y * δ) = δ⁻¹ * ((d : Γ) * y) * δ := by group
      _ = δ⁻¹ * (y * (d : Γ)) * δ := by rw [hd]
      _ = (δ⁻¹ * y * δ) * (δ⁻¹ * (d : Γ) * δ) := by group
    ⟩
  left_inv c := by
    apply Subtype.ext
    group
  right_inv d := by
    apply Subtype.ext
    group

theorem a6c_card_centralizer_eq [Finite Γ] (hΓ : ¬ 25 ∣ Nat.card Γ) {g0 n : Γ} (hg0 : g0 ^ 5 = 1)
    (hg1 : g0 ≠ 1) (hn : n * g0 * n⁻¹ = g0 ^ 2) {x : Γ} (hx : x ^ 5 = 1) (hx1 : x ≠ 1) :
    Nat.card (centralizer ({x} : Set Γ)) = Nat.card (centralizer ({g0} : Set Γ)) := by
  obtain ⟨δ, hδ⟩ := a6c_exists_conj_g0 hΓ hg0 hg1 hn hx hx1
  exact Nat.card_congr (conjCentralizerEquiv hδ)

private def a6StdA : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 2 3 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide⟩

private def a6StdX : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [0, 2, 1, 3, 4], by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

private theorem a6StdA_sq : a6StdA * a6StdA = 1 := by decide +kernel

private theorem a6StdA_ne : a6StdA ≠ 1 := by decide +kernel

private theorem a6StdX_pow : a6StdX ^ 5 = 1 := by decide +kernel

private theorem a6StdX_ne : a6StdX ≠ 1 := by decide +kernel

private theorem a6StdAX_pow : (a6StdA * a6StdX) ^ 4 = 1 := by decide +kernel

private theorem a6StdXAX_pow : (a6StdX * a6StdA * a6StdX) ^ 5 = 1 := by decide +kernel

theorem a6c_exists_std_pair {A : Subgroup Γ} (e : A ≃* alternatingGroup (Fin 6)) :
    ∃ a ∈ A, ∃ x ∈ A, a * a = 1 ∧ a ≠ 1 ∧ x ^ 5 = 1 ∧ x ≠ 1 ∧ (a * x) ^ 4 = 1 ∧
      (x * a * x) ^ 5 = 1 := by
  let a : A := e.symm a6StdA
  let x : A := e.symm a6StdX
  have haA : a * a = 1 := by
    apply e.injective
    rw [map_mul, map_one, show e a = a6StdA by simp [a], a6StdA_sq]
  have haA_ne : a ≠ 1 := by
    intro h
    apply a6StdA_ne
    simpa [a] using congrArg e h
  have hxA : x ^ 5 = 1 := by
    apply e.injective
    rw [map_pow, map_one, show e x = a6StdX by simp [x], a6StdX_pow]
  have hxA_ne : x ≠ 1 := by
    intro h
    apply a6StdX_ne
    simpa [x] using congrArg e h
  have hAxA : (a * x) ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, map_mul, map_one, show e a = a6StdA by simp [a],
      show e x = a6StdX by simp [x], a6StdAX_pow]
  have hXAxA : (x * a * x) ^ 5 = 1 := by
    apply e.injective
    rw [map_pow, map_mul, map_mul, map_one, show e a = a6StdA by simp [a],
      show e x = a6StdX by simp [x], a6StdXAX_pow]
  refine ⟨(a : Γ), a.2, (x : Γ), x.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val haA
    simpa using this
  · intro h
    exact haA_ne (Subtype.ext h)
  · have := congrArg Subtype.val hxA
    simpa using this
  · intro h
    exact hxA_ne (Subtype.ext h)
  · have := congrArg Subtype.val hAxA
    simpa using this
  · have := congrArg Subtype.val hXAxA
    simpa using this

end CFSG.OddStandard.SmallF3.Omega
