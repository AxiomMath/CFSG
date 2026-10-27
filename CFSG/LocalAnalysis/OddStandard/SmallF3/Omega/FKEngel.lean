module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem fk_engel_aux {G : Type*} [Group G] {N : Subgroup G} (hN : N.IsSubnormal) :
    ∃ n : ℕ, ∀ g : G, ∀ k ∈ N, (fun x => x * k * x⁻¹ * k⁻¹)^[n] g ∈ N := by
  induction hN with
  | top => exact ⟨0, fun g k _ => by simp⟩
  | step H K hHK _ hHn ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 1, fun g k hk => ?_⟩
    rw [Function.iterate_succ_apply']
    have hkK : k ∈ K := hHK hk
    have hx : (fun x => x * k * x⁻¹ * k⁻¹)^[m] g ∈ K := hm g k hkK
    have hconj := hHn.conj_mem ⟨k, hkK⟩ (by simpa [mem_subgroupOf] using hk)
      ⟨(fun x => x * k * x⁻¹ * k⁻¹)^[m] g, hx⟩
    set y := (fun x => x * k * x⁻¹ * k⁻¹)^[m] g with hy
    have hconj' : y * k * y⁻¹ ∈ H := by
      simpa [mem_subgroupOf] using hconj
    simpa [mul_assoc] using H.mul_mem hconj' (H.inv_mem hk)

theorem fkEngel_of_subnormal {G : Type*} [Group G] {H K : Subgroup G} (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsSubnormal) :
    ∃ n : ℕ, ∀ g ∈ H, ∀ k ∈ K, (fun x => x * k * x⁻¹ * k⁻¹)^[n] g ∈ K := by
  obtain ⟨n, hn⟩ := fk_engel_aux hK
  refine ⟨n, fun g hg k hk => ?_⟩
  set k' : H := ⟨k, hKH hk⟩ with hk'
  have key : ∀ m : ℕ, (((fun x => x * k' * x⁻¹ * k'⁻¹)^[m] (⟨g, hg⟩ : H) : H) : G) =
      (fun x => x * k * x⁻¹ * k⁻¹)^[m] g := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  have h := hn ⟨g, hg⟩ ⟨k, hKH hk⟩ (by simpa [mem_subgroupOf] using hk)
  rw [mem_subgroupOf, key] at h
  exact h

private theorem fk_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem fk_sl23_sq {M : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)} (h : M * M = 1) :
    M = 1 ∨ M = -1 := by
  revert M; decide +kernel

theorem fkPocket_unique_involution {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsSL23Mod K) {z : G} (hz : orderOf z = 2) (hzK : z ∈ K)
    (hKz : K ≤ centralizer ({z} : Set G)) {t : G} (htK : t ∈ K) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) : t = z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hK
  set ψ : ↥K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore ↥K)) with hψ
  have hker : ∀ x : ↥K, ψ x = 1 → x ∈ CFSG.oddCore ↥K := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.oddCore ↥K) x = 1 :=
      e.injective (by rw [map_one]; exact hx)
    exact (QuotientGroup.eq_one_iff x).mp h1
  have himg : ∀ w : ↥K, w * w = 1 → w ≠ 1 → ψ w = -1 := by
    intro w hw2 hw1
    have hsq : ψ w * ψ w = 1 := by rw [← map_mul, hw2, map_one]
    rcases fk_sl23_sq hsq with h | h
    · exfalso
      have hmem := hker w h
      have hord : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
      have hodd : Odd (orderOf w) :=
        Odd.of_dvd_nat (fk_odd_card_oddCore ↥K) (Subgroup.orderOf_dvd_natCard _ hmem)
      rw [hord] at hodd
      exact absurd hodd (by decide)
    · exact h
  have hz2 : z * z = 1 := by rw [← pow_two]; exact hz ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  have hcomm : t * z = z * t := mem_centralizer_singleton_iff.mp (hKz htK)
  set t' : ↥K := ⟨t, htK⟩ with ht'
  set z' : ↥K := ⟨z, hzK⟩ with hz'
  have ht'2 : t' * t' = 1 := Subtype.ext ht2
  have hz'2 : z' * z' = 1 := Subtype.ext hz2
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hcomm' : z' * t' = t' * z' := (Subtype.ext hcomm).symm
  have hdiff : ψ (t' * z'⁻¹) = 1 := by
    rw [map_mul, map_inv, himg t' ht'2 ht'1, himg z' hz'2 hz'1, mul_inv_cancel]
  have hmem := hker _ hdiff
  have hodd : Odd (orderOf (t' * z'⁻¹)) :=
    Odd.of_dvd_nat (fk_odd_card_oddCore ↥K) (Subgroup.orderOf_dvd_natCard _ hmem)
  have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
  have hsq : (t' * z'⁻¹) * (t' * z'⁻¹) = 1 := by
    rw [hz'inv]
    calc t' * z' * (t' * z') = t' * (z' * t') * z' := by group
      _ = t' * (t' * z') * z' := by rw [hcomm']
      _ = (t' * t') * (z' * z') := by group
      _ = 1 := by rw [ht'2, hz'2, one_mul]
  have hdvd : orderOf (t' * z'⁻¹) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have hone : orderOf (t' * z'⁻¹) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hfin : t' * z'⁻¹ = 1 := orderOf_eq_one_iff.mp hone
  have : t' = z' := by
    rw [hz'inv] at hfin
    exact mul_eq_one_iff_eq_inv.mp hfin |>.trans hz'inv
  exact congrArg Subtype.val this

theorem fkPocket_no_free_involutions {G : Type} [Group G] [Finite G] {z : G} {K : Subgroup G}
    (hz : orderOf z = 2) (hP : Sl23PocketIn ⊤ z K) (E : Subgroup G)
    (hEz : E ≤ centralizer ({z} : Set G)) (hE2 : ∀ e ∈ E, e * e = 1) (hzE : z ∉ E) {k : G}
    (hk : k ∈ K) (hkE : ∀ e ∈ E, k * e * k⁻¹ ∈ E)
    (hfree : ∀ e ∈ E, e ≠ 1 → k * e * k⁻¹ ≠ e) {e : G} (he : e ∈ E) (he1 : e ≠ 1) : False := by
  obtain ⟨hzK, hKle, hsub, hSL⟩ := hP
  obtain ⟨n, hn⟩ := fkEngel_of_subnormal hKle hsub
  have hE : ∀ m : ℕ, (fun x => x * k * x⁻¹ * k⁻¹)^[m] e ∈ E ∧
      (fun x => x * k * x⁻¹ * k⁻¹)^[m] e ≠ 1 := by
    intro m
    induction m with
    | zero => exact ⟨he, he1⟩
    | succ m ih =>
      obtain ⟨hmE, hm1⟩ := ih
      rw [Function.iterate_succ_apply']
      set x := (fun x => x * k * x⁻¹ * k⁻¹)^[m] e with hx
      refine ⟨?_, ?_⟩
      · have h1 : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
        rw [h1]
        exact E.mul_mem hmE (hkE _ (E.inv_mem hmE))
      · intro h
        apply hfree x hmE hm1
        have h1 : x * k * x⁻¹ = k := mul_inv_eq_one.mp h
        have h2 : x * k = k * x := mul_inv_eq_iff_eq_mul.mp h1
        exact mul_inv_eq_iff_eq_mul.mpr h2.symm
  obtain ⟨hnE, hn1⟩ := hE n
  have heH : e ∈ (⊤ : Subgroup G) ⊓ centralizer ({z} : Set G) := ⟨Subgroup.mem_top e, hEz he⟩
  have hnK := hn e heH k hk
  have hKz : K ≤ centralizer ({z} : Set G) := hKle.trans inf_le_right
  have h2 := fkPocket_unique_involution hSL hz hzK hKz hnK (hE2 _ hnE) hn1
  exact hzE (h2 ▸ hnE)

end CFSG.OddStandard.SmallF3.Omega
