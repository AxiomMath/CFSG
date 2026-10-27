module

public import CFSG.ClassicalInvolution.Q3.Q3SAltMain
public import CFSG.ClassicalInvolution.Q3.Q3SNormal

public section

namespace CFSG.ClassicalInvolution.Q3

open Equiv

theorem NoWeakClassical3At.of_centralizer {F : Type} [Group F] {z : F}
    (h : NoWeakClassical3At (⟨z, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ :
      ↥(Subgroup.centralizer ({z} : Set F)))) : NoWeakClassical3At z := fun L hL =>
  h (L.subgroupOf (Subgroup.centralizer ({z} : Set F))) (hL.subgroupOf hL.le_centralizer)

theorem z0_moves_all : ∀ i : Fin 8, z0 i ≠ i := by decide +kernel

section Small

variable {n : ℕ}

theorem ext8_apply_small (h : 8 ≤ n) (σ : Perm (Fin 8)) (i : Fin 8) :
    ext8 n h σ (Fin.castLE h i) = Fin.castLE h (σ i) :=
  Perm.extendDomain_apply_image σ (fin8Equiv n h) i

theorem ext8_apply_big (h : 8 ≤ n) (σ : Perm (Fin 8)) (x : Fin n) (hx : ¬ x.val < 8) :
    ext8 n h σ x = x :=
  Perm.extendDomain_apply_not_subtype σ (fin8Equiv n h) hx

theorem eq_castLE_of_lt (h : 8 ≤ n) {x : Fin n} (hx : x.val < 8) :
    x = Fin.castLE h ⟨x.val, hx⟩ := Fin.ext rfl

theorem zStd_moves_iff (h8 : 8 ≤ n) (x : Fin n) :
    ((zStd n h8 : alternatingGroup (Fin n)) : Perm (Fin n)) x ≠ x ↔ x.val < 8 := by
  constructor
  · intro hne
    by_contra hx
    exact hne (ext8_apply_big h8 z0 x hx)
  · intro hx
    rw [eq_castLE_of_lt h8 hx]
    change ext8 n h8 z0 (Fin.castLE h8 ⟨x.val, hx⟩) ≠ Fin.castLE h8 ⟨x.val, hx⟩
    rw [ext8_apply_small]
    intro heq
    exact z0_moves_all _ (Fin.castLE_injective h8 heq)

theorem small_iff_of_mem_centralizer (h8 : 8 ≤ n) {g : alternatingGroup (Fin n)}
    (hg : g ∈ Subgroup.centralizer ({zStd n h8} : Set (alternatingGroup (Fin n)))) (x : Fin n) :
    (((g : alternatingGroup (Fin n)) : Perm (Fin n)) x).val < 8 ↔ x.val < 8 := by
  have hcomm : ∀ y : Fin n, ((g : alternatingGroup (Fin n)) : Perm (Fin n))
      (((zStd n h8 : alternatingGroup (Fin n)) : Perm (Fin n)) y) =
      ((zStd n h8 : alternatingGroup (Fin n)) : Perm (Fin n))
        (((g : alternatingGroup (Fin n)) : Perm (Fin n)) y) := fun y =>
    congrArg (fun p : alternatingGroup (Fin n) => (p : Perm (Fin n)) y)
      (Subgroup.mem_centralizer_singleton_iff.mp hg)
  rw [← zStd_moves_iff h8, ← zStd_moves_iff h8, ← hcomm x]
  exact ((g : alternatingGroup (Fin n)) : Perm (Fin n)).injective.ne_iff

@[expose] def smallFix (n : ℕ) : Subgroup (alternatingGroup (Fin n)) where
  carrier := {g | ∀ x : Fin n, x.val < 8 → ((g : alternatingGroup (Fin n)) : Perm (Fin n)) x = x}
  one_mem' := fun x _ => rfl
  mul_mem' := fun {a b} ha hb x hx => by
    change ((a : alternatingGroup (Fin n)) : Perm (Fin n))
      (((b : alternatingGroup (Fin n)) : Perm (Fin n)) x) = x
    rw [hb x hx, ha x hx]
  inv_mem' := fun {a} ha x hx => by
    change (((a : alternatingGroup (Fin n)) : Perm (Fin n))⁻¹) x = x
    exact Perm.inv_eq_iff_eq.2 (ha x hx).symm

theorem commute_ext8_of_fixes_small (h : 8 ≤ n) (σ : Perm (Fin 8)) (τ : Perm (Fin n))
    (hτ : ∀ x : Fin n, x.val < 8 → τ x = x) : τ * ext8 n h σ = ext8 n h σ * τ := by
  have hbig : ∀ x : Fin n, ¬ x.val < 8 → ¬ (τ x).val < 8 := by
    intro x hx hlt
    have h1 : τ (τ x) = τ x := hτ _ hlt
    have h2 : τ x = x := τ.injective h1
    exact hx (h2 ▸ hlt)
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x.val < 8
  · have hsm : (ext8 n h σ x).val < 8 := by
      rw [eq_castLE_of_lt h hx, ext8_apply_small]
      simp
    rw [hτ _ hx, hτ _ hsm]
  · rw [ext8_apply_big h σ x hx, ext8_apply_big h σ (τ x) (hbig x hx)]

end Small

@[expose] def dPerm : Perm (Fin 11) := swap 8 9 * swap 9 10

theorem dPerm_fixes_small : ∀ x : Fin 11, x.val < 8 → dPerm x = x := by decide +kernel

theorem dPerm_cube : dPerm ^ 3 = 1 := by decide +kernel

theorem dPerm_ne_one : dPerm ≠ 1 := by decide +kernel

theorem dPerm_sign : Perm.sign dPerm = 1 := by decide +kernel

theorem dPerm_orderOf : orderOf dPerm = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime dPerm_cube dPerm_ne_one

@[expose] def dA : alternatingGroup (Fin 11) := ⟨dPerm, Perm.mem_alternatingGroup.2 dPerm_sign⟩

theorem dA_orderOf : orderOf dA = 3 := by
  have : orderOf (dA : Perm (Fin 11)) = 3 := dPerm_orderOf
  rwa [Subgroup.orderOf_coe] at this

theorem dA_mem_smallFix : dA ∈ smallFix 11 := dPerm_fixes_small

theorem smallFix_no_involution {t : alternatingGroup (Fin 11)} (ht : t ∈ smallFix 11) :
    orderOf t ≠ 2 := by
  intro h2
  have hZ : orderOf (t : Perm (Fin 11)) = 2 := by rw [Subgroup.orderOf_coe]; exact h2
  have hs : Perm.sign (t : Perm (Fin 11)) = 1 := Perm.mem_alternatingGroup.mp t.2
  obtain ⟨m, -, hc⟩ := even_of_sign_eq_one hZ hs
  have hsub : (t : Perm (Fin 11)).support ⊆ Finset.univ.filter fun x : Fin 11 => 8 ≤ x.val := by
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hlt
    push Not at hlt
    exact (Perm.mem_support.1 hx) (ht x hlt)
  have hle := Finset.card_le_card hsub
  have h3 : (Finset.univ.filter fun x : Fin 11 => 8 ≤ x.val).card = 3 := by decide +kernel
  have hm0 : m = 0 := by omega
  have hsupp : (t : Perm (Fin 11)).support = ∅ := Finset.card_eq_zero.1 (by omega)
  have ht1 : (t : Perm (Fin 11)) = 1 := Perm.support_eq_empty_iff.1 hsupp
  have : orderOf (t : Perm (Fin 11)) = 1 := by rw [ht1]; exact orderOf_one
  omega

theorem not_twentySeven_dvd_card_centralizer_zStd_eleven (h8 : 8 ≤ 11) :
    ¬ 27 ∣ Nat.card (Subgroup.centralizer ({zStd 11 h8} : Set (alternatingGroup (Fin 11)))) := by
  intro h27
  have := h27.trans (card_centralizer_zStd_dvd h8)
  norm_num [Nat.factorial] at this

theorem noWeakClassical3At_zStd_eleven (h8 : 8 ≤ 11) : NoWeakClassical3At (zStd 11 h8) := by
  apply NoWeakClassical3At.of_centralizer
  set C : Subgroup (alternatingGroup (Fin 11)) :=
    Subgroup.centralizer ({zStd 11 h8} : Set (alternatingGroup (Fin 11))) with hC
  let z' : ↥C := ⟨zStd 11 h8, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hz : ∀ g : ↥C, g * z' = z' * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  let N : Subgroup ↥C := (smallFix 11).subgroupOf C
  have hNmem : ∀ g : ↥C, g ∈ N ↔ ∀ x : Fin 11, x.val < 8 →
      (((g : alternatingGroup (Fin 11)) : Perm (Fin 11))) x = x := fun g => Iff.rfl
  have hNnormal : N.Normal := ⟨fun n hn g x hx => by
    have hn' := (hNmem n).1 hn
    have hginv : ((g⁻¹ : ↥C) : alternatingGroup (Fin 11)) ∈ C := (g⁻¹ : ↥C).2
    have hxs : ((((g : alternatingGroup (Fin 11)) : Perm (Fin 11))⁻¹) x).val < 8 := by
      have := (small_iff_of_mem_centralizer h8 hginv x).2 hx
      exact this
    change ((g : alternatingGroup (Fin 11)) : Perm (Fin 11))
      (((n : alternatingGroup (Fin 11)) : Perm (Fin 11))
        ((((g : alternatingGroup (Fin 11)) : Perm (Fin 11))⁻¹) x)) = x
    rw [hn' _ hxs]
    simp⟩
  have hNodd : Odd (Nat.card N) := by
    by_contra hnot
    have h2 : 2 ∣ Nat.card N := by
      rw [Nat.not_odd_iff_even] at hnot
      exact even_iff_two_dvd.mp hnot
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2
    have hu' : orderOf (((u : ↥C) : alternatingGroup (Fin 11))) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hu
    exact smallFix_no_involution ((hNmem _).1 u.2 |> fun h => h) hu'
  have hdC : dA ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    change (dPerm : Perm (Fin 11)) * ext8 11 h8 z0 = ext8 11 h8 z0 * dPerm
    exact commute_ext8_of_fixes_small h8 z0 dPerm dPerm_fixes_small
  have hN3 : 3 ∣ Nat.card N := by
    have hdN : (⟨dA, hdC⟩ : ↥C) ∈ N := dA_mem_smallFix
    have h3 : orderOf (⟨(⟨dA, hdC⟩ : ↥C), hdN⟩ : N) = 3 := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact dA_orderOf
    rw [← h3]
    exact orderOf_dvd_natCard _
  have h27 : ¬ 27 ∣ Nat.card ↥C := not_twentySeven_dvd_card_centralizer_zStd_eleven h8
  exact NoWeakClassical3At.of_witness_normal (z := z') hz hNodd hN3 h27
    (g₁ := ⟨wit1A 11 h8, wit1A_mem h8⟩) (g₂ := ⟨wit2A 11 h8, wit2A_mem h8⟩)
    (Subtype.ext (wit1A_cube h8)) (Subtype.ext (wit2A_cube h8)) (Subtype.ext (witA_prod_sq h8))
    (fun h1 => witA_prod_ne_one h8 (congrArg Subtype.val h1))
    (fun h1 => witA_prod_ne_z h8 (congrArg Subtype.val h1))

theorem noWeakClassical3At_alternating_eleven {z : alternatingGroup (Fin 11)} (hz : orderOf z = 2)
    (hs : ((z : alternatingGroup (Fin 11)) : Perm (Fin 11)).support.card = 8) :
    NoWeakClassical3At z := by
  have h8 : 8 ≤ 11 := by norm_num
  obtain ⟨c, hc⟩ := exists_conj_zStd h8 hz hs
  have hez : MulAut.conjNormal (H := alternatingGroup (Fin 11)) c z = zStd 11 h8 :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hc)
  refine NoWeakClassical3At.of_map (MulAut.conjNormal (H := alternatingGroup (Fin 11)) c) ?_
  rw [hez]
  exact noWeakClassical3At_zStd_eleven h8

theorem noWeakClassical3_alternating {n : ℕ} (h8 : 8 ≤ n) (h11 : n ≤ 11) :
    NoWeakClassical3 (alternatingGroup (Fin n)) := by
  rcases Nat.lt_or_ge n 11 with h | h
  · exact noWeakClassical3_alternating_of_le_ten h8 (by omega)
  · obtain rfl : n = 11 := le_antisymm h11 h
    intro L z hL
    exact noWeakClassical3At_alternating_eleven hL.orderOf_eq_two
      (hL.card_support_eq_eight le_rfl) L hL

end CFSG.ClassicalInvolution.Q3
