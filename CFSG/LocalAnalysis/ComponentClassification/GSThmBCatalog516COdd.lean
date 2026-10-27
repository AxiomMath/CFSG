module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CLift
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup

section IndexTwo

variable {G : Type*} [Group G]

theorem four_dvd_of_no_index_two [Finite G] (h2 : 2 ∣ Nat.card G)
    (h : ∀ H : Subgroup G, H.index ≠ 2) : 4 ∣ Nat.card G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h4
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hS1 : 2 ∣ Nat.card S := by
    have := S.pow_dvd_card_of_pow_dvd_card (n := 1) (by rw [pow_one]; exact h2)
    rwa [pow_one] at this
  have hSG : Nat.card S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card (S : Subgroup G)
  have hk1 : k = 1 := by
    rcases k with _ | _ | k
    · rw [hk, pow_zero] at hS1; omega
    · rfl
    · exfalso
      apply h4
      refine dvd_trans ?_ (hk ▸ hSG)
      exact ⟨2 ^ k, by ring⟩
  rw [hk1, pow_one] at hk
  have hcyc : IsCyclic S := isCyclic_of_prime_card hk
  obtain ⟨N, -, hNS⟩ := exists_normal_isComplement'_of_isCyclic_sylow_two S hcyc
  exact h N (by rw [hNS.symm.index_eq_card, hk])

theorem no_index_two_of_perfect [Group.IsPerfect G] (H : Subgroup G) : H.index ≠ 2 := by
  intro hH
  have hle : commutator G ≤ H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, mul_mem_iff_of_index_two hH, mul_mem_iff_of_index_two hH,
      mul_mem_iff_of_index_two hH, inv_mem_iff, inv_mem_iff]
    tauto
  rw [Group.IsPerfect.commutator_eq_top, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hH
  omega

theorem mem_of_index_two_of_odd {H : Subgroup G} (hH : H.index = 2) {g : G}
    (hg : Odd (orderOf g)) : g ∈ H := by
  obtain ⟨m, hm⟩ := hg
  have h1 : g = (g ^ (m + 1)) ^ 2 := by
    rw [← pow_mul, show (m + 1) * 2 = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h1]
  exact sq_mem_of_index_two hH _

theorem no_index_two_of_closure_odd {S : Set G} (hS : closure S = ⊤)
    (hodd : ∀ s ∈ S, Odd (orderOf s)) (H : Subgroup G) : H.index ≠ 2 := by
  intro hH
  have hle : closure S ≤ H := (closure_le H).mpr fun s hs => mem_of_index_two_of_odd hH (hodd s hs)
  rw [hS, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hH
  omega

theorem four_dvd_card_of_perfect [Finite G] {M : Subgroup G} (hM : ⁅M, M⁆ = M)
    (h2 : 2 ∣ Nat.card M) : 4 ∣ Nat.card M := by
  have : Group.IsPerfect M := ⟨by
    rw [← (Subgroup.map_injective M.subtype_injective).eq_iff, Subgroup.map_subtype_commutator,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hM⟩
  exact four_dvd_of_no_index_two h2 no_index_two_of_perfect

theorem four_dvd_card_closure_odd [Finite G] {T : Set G} (hT : ∀ t ∈ T, Odd (orderOf t))
    (h2 : 2 ∣ Nat.card (closure T)) : 4 ∣ Nat.card (closure T) := by
  refine four_dvd_of_no_index_two h2 (no_index_two_of_closure_odd (S := {x | x.val ∈ T}) ?_ ?_)
  · rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact subset_closure (show (⟨y, subset_closure hy⟩ : closure T).val ∈ T from hy)
    | one => exact one_mem _
    | mul y z hy hz ihy ihz => exact mul_mem ihy ihz
    | inv y hy ihy => exact inv_mem ihy
  · rintro ⟨s, hs⟩ (hsT : s ∈ T)
    rw [Subgroup.orderOf_mk]
    exact hT s hsT

end IndexTwo

section OddLift

variable {Y L : Type*} [Group Y] [Group L] (π : Y →* L)

@[expose] def oddLift (T : Set L) : Subgroup Y := closure {y | π y ∈ T ∧ Odd (orderOf y)}

variable {π}

theorem not_odd_orderOf_mul_central {y z : Y} (hy : Odd (orderOf y)) (hz : z ∈ center Y)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) : ¬ Odd (orderOf (y * z)) := by
  rintro ⟨m, hm⟩
  have hzz : ∀ k : ℕ, z ^ (2 * k + 1) = z := fun k => by
    rw [pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
  have hc : Commute y z := mem_center_iff.mp hz y
  have h1 : (y * z) ^ (orderOf (y * z)) = 1 := pow_orderOf_eq_one _
  rw [hc.mul_pow, hm, hzz m] at h1
  have h2 : y ^ (2 * m + 1) = z := by
    rw [← mul_one (y ^ (2 * m + 1)), ← hz2, ← mul_assoc, h1, one_mul]
  obtain ⟨j, hj⟩ := hy
  have h3 : z ^ orderOf y = 1 := by
    rw [← h2, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  rw [hj, hzz j] at h3
  exact hz1 h3

theorem exists_odd_lift (hπ : Function.Surjective π) (hker : π.ker ≤ center Y)
    (hk : ∀ k ∈ π.ker, k * k = 1) {t : L} (ht : Odd (orderOf t)) :
    ∃ y, π y = t ∧ Odd (orderOf y) := by
  obtain ⟨y₀, rfl⟩ := hπ t
  obtain ⟨m, hm⟩ := ht
  have hy : y₀ ^ (2 * m + 1) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, ← hm, pow_orderOf_eq_one]
  set k := y₀ ^ (2 * m + 1) with hkdef
  have hkk := hk k hy
  refine ⟨y₀ * k, ?_, ?_⟩
  · rw [map_mul, MonoidHom.mem_ker.mp hy, mul_one]
  · have hc : Commute y₀ k := mem_center_iff.mp (hker hy) y₀
    have h1 : (y₀ * k) ^ (2 * m + 1) = 1 := by
      rw [hc.mul_pow, ← hkdef]
      have : k ^ (2 * m + 1) = k := by rw [pow_succ, pow_mul, sq, hkk, one_pow, one_mul]
      rw [this, hkk]
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    exact Odd.of_dvd_nat ⟨m, rfl⟩ hdvd

theorem map_oddLift (hπ : Function.Surjective π) (hker : π.ker ≤ center Y)
    (hk : ∀ k ∈ π.ker, k * k = 1) {T : Set L} (hT : ∀ t ∈ T, Odd (orderOf t)) :
    (oddLift π T).map π = closure T := by
  rw [oddLift, MonoidHom.map_closure]
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
    exact subset_closure hy
  · rw [closure_le]
    intro t ht
    obtain ⟨y, rfl, hy⟩ := exists_odd_lift hπ hker hk (hT t ht)
    exact subset_closure ⟨y, ⟨ht, hy⟩, rfl⟩

theorem oddLift_fixed (hZ : Nat.card (center Y) = 2) (hker : π.ker = center Y) (α : MulAut Y)
    (ᾱ : MulAut L) (hcomm : ∀ y, π (α y) = ᾱ (π y)) {T : Set L} (hT : ∀ t ∈ T, ᾱ t = t) :
    ∀ y ∈ oddLift π T, α y = y := by
  have key : oddLift π T ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y) := by
    rw [oddLift, closure_le]
    rintro y ⟨hyT, hy⟩
    change α y = y
    have hk : y⁻¹ * α y ∈ center Y := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hcomm, hT _ hyT, inv_mul_cancel]
    by_contra hne
    have hk1 : y⁻¹ * α y ≠ 1 := fun h => hne (by rw [← mul_inv_cancel_left y (α y), h, mul_one])
    have hodd : Odd (orderOf (α y)) := by rw [MulEquiv.orderOf_eq]; exact hy
    apply not_odd_orderOf_mul_central hy hk (sq_eq_one_of_mem_center hZ hk) hk1
    rwa [mul_inv_cancel_left]
  exact fun y hy => key hy

theorem oddLift_le (hZ : Nat.card (center Y) = 2) (hker : π.ker = center Y) (α : MulAut Y)
    (ᾱ : MulAut L) (hcomm : ∀ y, π (α y) = ᾱ (π y)) {T : Set L} (hT : ∀ t ∈ T, ᾱ t = t) :
    oddLift π T ≤ closure {y : Y | α y = y ∧ Odd (orderOf y)} := by
  rw [oddLift, closure_le]
  rintro y ⟨hyT, hy⟩
  exact subset_closure ⟨oddLift_fixed hZ hker α ᾱ hcomm hT y (subset_closure ⟨hyT, hy⟩), hy⟩

theorem abelian_or_center_of_le_map (hZ : Nat.card (center Y) = 2) (hker : π.ker ≤ center Y)
    [Finite Y] {N : Subgroup Y} {B : Subgroup L} (hBN : B ≤ N.map π)
    (hBab : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u) (hB8 : Nat.card B = 8)
    (hBinv : ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ orderOf u = 2 ∧ orderOf v = 2) :
    center Y ≤ N ∨ ∃ A : Subgroup Y, A ≤ N ∧
      (∀ u ∈ A, ∀ v ∈ A, u * v = v * u) ∧ Nat.card A = 8 ∧
        ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ orderOf u = 2 ∧ orderOf v = 2 := by
  by_cases hc : center Y ≤ N
  · exact Or.inl hc
  right
  have hinjN : ∀ a ∈ N, ∀ b ∈ N, π a = π b → a = b := by
    intro a ha b hb hab
    have hk : a⁻¹ * b ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    by_contra hne
    have hk1 : a⁻¹ * b ≠ 1 := fun h => hne (by rw [← mul_inv_cancel_left a b, h, mul_one])
    apply hc
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]; exact one_mem _
    rw [eq_of_card_two hZ hz (hker hk) hz1 hk1]
    exact mul_mem (inv_mem ha) hb
  set A := (B.comap π) ⊓ N
  have hπA : Function.Injective (π.comp A.subtype) := fun a b hab =>
    Subtype.ext (hinjN a a.2.2 b b.2.2 hab)
  have hsurj : ∀ u ∈ B, ∃ a ∈ A, π a = u := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := hBN hu
    exact ⟨a, ⟨hu, ha⟩, rfl⟩
  have hAB : A.map π = B := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact ha.1
    · intro u hu
      obtain ⟨a, ha, hau⟩ := hsurj u hu
      exact ⟨a, ha, hau⟩
  have hcardA : Nat.card A = 8 := by
    have hr : (π.comp A.subtype).range = A.map π := by
      rw [MonoidHom.range_comp, A.range_subtype]
    rw [← hB8, ← hAB, ← hr]
    exact Nat.card_congr (MonoidHom.ofInjective hπA).toEquiv
  refine ⟨A, inf_le_right, fun u hu v hv => ?_, hcardA, ?_⟩
  · apply hinjN _ (mul_mem hu.2 hv.2) _ (mul_mem hv.2 hu.2)
    rw [map_mul, map_mul]
    exact hBab _ hu.1 _ hv.1
  · obtain ⟨u, hu, v, hv, huv, hu2, hv2⟩ := hBinv
    obtain ⟨a, ha, rfl⟩ := hsurj u hu
    obtain ⟨b, hb, rfl⟩ := hsurj v hv
    have hord : ∀ c ∈ A, orderOf (π c) = orderOf c := by
      intro c hc
      have h1 := orderOf_injective (π.comp A.subtype) hπA ⟨c, hc⟩
      simpa using h1
    refine ⟨a, ha, b, hb, fun h => huv (by rw [h]), ?_, ?_⟩
    · rw [← hord a ha]; exact hu2
    · rw [← hord b hb]; exact hv2

end OddLift

section Concl

variable {Y : Type*} [Group Y]

theorem piZ_comm (α : MulAut Y) (y : Y) : piZ (α y) = barAut α (piZ y) :=
  (barAut_mk α y).symm

theorem ker_piZ_eq : (piZ (Y := Y)).ker = center Y := QuotientGroup.ker_mk' _

theorem sq_ker_piZ (hZ : Nat.card (center Y) = 2) : ∀ k ∈ (piZ (Y := Y)).ker, k * k = 1 :=
  fun _ hk => sq_eq_one_of_mem_center hZ (ker_piZ (Y := Y) hk)

theorem concl_odd_outer [Finite Y] (hZ : Nat.card (center Y) = 2) (α : MulAut Y)
    {T : Set (Y ⧸ center Y)} (hT : ∀ t ∈ T, barAut α t = t) (hTo : ∀ t ∈ T, Odd (orderOf t))
    (hout : ∀ x, barAut α ≠ MulAut.conj x) (h4 : 4 ∣ Nat.card (closure T)) :
    ∃ N : Subgroup Y, (∀ y ∈ N, α y = y) ∧ N ≤ closure {y : Y | α y = y ∧ Odd (orderOf y)} ∧
      (∀ t : Y, α ≠ MulAut.conj t) ∧ 4 ∣ Nat.card N := by
  refine ⟨oddLift piZ T, oddLift_fixed hZ ker_piZ_eq α (barAut α) (piZ_comm α) hT,
    oddLift_le hZ ker_piZ_eq α (barAut α) (piZ_comm α) hT, not_inner_of_bar hout,
    h4.trans ?_⟩
  have := Subgroup.card_map_dvd (H := oddLift piZ T) (piZ (Y := Y))
  rwa [map_oddLift (QuotientGroup.mk'_surjective _) (ker_piZ (Y := Y)) (sq_ker_piZ hZ) hTo]
    at this

end Concl

end CFSG.ComponentClassification.GSThmB.Cent516
