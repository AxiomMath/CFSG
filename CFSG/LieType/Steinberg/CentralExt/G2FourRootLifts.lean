module

public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.CoverRoots

public section

namespace CFSG.LieType.Steinberg.CentralExt.G2Four

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.G2FieldFour CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.EvenSmallLie.GTwoFour CFSG.LocalAnalysis.ComponentInitial
open Subgroup

@[expose] def longRoots : Finset (Fin Tag.G2.rank → ℤ) :=
  {rootA, rootB, rootC, -rootA, -rootB, -rootC}

@[expose] def shortRoots : Finset (Fin Tag.G2.rank → ℤ) :=
  {rootR, rootU, rootV, -rootR, -rootU, -rootV}

theorem longRoots_union_shortRoots : longRoots ∪ shortRoots = rootFinset .G2 := by
  decide +kernel

theorem disjoint_longRoots_shortRoots : Disjoint longRoots shortRoots := by
  decide +kernel

theorem mem_longRoots_or_mem_shortRoots {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot .G2 γ) : γ ∈ longRoots ∨ γ ∈ shortRoots := by
  rw [← Finset.mem_union, longRoots_union_shortRoots, mem_rootFinset]
  exact hγ

theorem reflect_a_rootB : reflect .G2 g2ia rootB = rootC := List.ofFn_injective (by decide +kernel)

theorem reflect_r_rootA : reflect .G2 g2ir rootA = rootB := List.ofFn_injective (by decide +kernel)

theorem reflect_a_neg_rootA : reflect .G2 g2ia (-rootA) = rootA :=
  List.ofFn_injective (by decide +kernel)

theorem reflect_r_neg_rootB : reflect .G2 g2ir (-rootB) = -rootA :=
  List.ofFn_injective (by decide +kernel)

theorem reflect_a_neg_rootC : reflect .G2 g2ia (-rootC) = -rootB :=
  List.ofFn_injective (by decide +kernel)

theorem reflect_r_rootU : reflect .G2 g2ir rootU = rootV := List.ofFn_injective (by decide +kernel)

theorem reflect_a_rootR : reflect .G2 g2ia rootR = rootU := List.ofFn_injective (by decide +kernel)

theorem reflect_r_neg_rootR : reflect .G2 g2ir (-rootR) = rootR :=
  List.ofFn_injective (by decide +kernel)

theorem reflect_a_neg_rootU : reflect .G2 g2ia (-rootU) = -rootR :=
  List.ofFn_injective (by decide +kernel)

theorem reflect_r_neg_rootV : reflect .G2 g2ir (-rootV) = -rootU :=
  List.ofFn_injective (by decide +kernel)

variable {K : Type} [Field K]

theorem isConj_rootX_one_of_cartan
    (i : Fin Tag.G2.rank) {d : Fin Tag.G2.rank → ℤ} (hd : IsRoot .G2 d)
    (hi : ∑ j, Tag.G2.cartan i j * d j = 1) {s : K} (hs : s ≠ 0) :
    IsConj (rootX d s) (rootX d (1 : K)) := by
  refine (isConj_iff.2 ⟨⟨torusElt .G2 K i (Units.mk0 s hs), torusElt_mem_adjointGroup _ _⟩,
    Subtype.ext ?_⟩).symm
  change torusElt .G2 K i (Units.mk0 s hs) * pinnedX .G2 K d 1 *
    (torusElt .G2 K i (Units.mk0 s hs))⁻¹ = pinnedX .G2 K d s
  rw [root_torus_conjugation i hd, hi, zpow_one, Units.val_mk0, mul_one]

theorem exists_isConj_rootX_reflect
    (i : Fin Tag.G2.rank) {d : Fin Tag.G2.rank → ℤ}
    (hd : IsRoot .G2 d) :
    ∃ ε : K, ε ≠ 0 ∧ ∀ x : K, IsConj (rootX d x) (rootX (reflect .G2 i d) (ε * x)) := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hd
  exact ⟨ε, left_ne_zero_of_mul_eq_one hε, fun x =>
    isConj_iff.2 ⟨⟨weylElt .G2 K i 1, weylElt_mem_adjointGroup _ _⟩, Subtype.ext (h x)⟩⟩

theorem isConj_rootX_of_reflect
    {g : adjointGroup .G2 K} (i : Fin Tag.G2.rank)
    {d d' : Fin Tag.G2.rank → ℤ} (hd : IsRoot .G2 d) (hdd' : reflect .G2 i d = d')
    (h : ∀ s : K, s ≠ 0 → IsConj (rootX d' s) g) {s : K} (hs : s ≠ 0) :
    IsConj (rootX d s) g := by
  obtain ⟨ε, hε, hconj⟩ := exists_isConj_rootX_reflect (K := K) i hd
  subst hdd'
  exact (hconj s).trans (h _ (mul_ne_zero hε hs))

theorem isConj_rootX_long
    {γ : Fin Tag.G2.rank → ℤ} (hγ : γ ∈ longRoots) {s : K}
    (hs : s ≠ 0) : IsConj (rootX γ s) (rootX rootC (1 : K)) := by
  have hc : ∀ s : K, s ≠ 0 → IsConj (rootX rootC s) (rootX rootC (1 : K)) := fun _ =>
    isConj_rootX_one_of_cartan g2ia isRoot_g2c (by decide)
  have hb : ∀ s : K, s ≠ 0 → IsConj (rootX rootB s) (rootX rootC (1 : K)) := fun _ =>
    isConj_rootX_of_reflect g2ia isRoot_g2b reflect_a_rootB hc
  have ha : ∀ s : K, s ≠ 0 → IsConj (rootX rootA s) (rootX rootC (1 : K)) := fun _ =>
    isConj_rootX_of_reflect g2ir isRoot_g2a reflect_r_rootA hb
  have hna : ∀ s : K, s ≠ 0 → IsConj (rootX (-rootA) s) (rootX rootC (1 : K)) := fun _ =>
    isConj_rootX_of_reflect g2ia (IsRoot.neg isRoot_g2a) reflect_a_neg_rootA ha
  have hnb : ∀ s : K, s ≠ 0 → IsConj (rootX (-rootB) s) (rootX rootC (1 : K)) := fun _ =>
    isConj_rootX_of_reflect g2ir (IsRoot.neg isRoot_g2b) reflect_r_neg_rootB hna
  have hnc : ∀ s : K, s ≠ 0 → IsConj (rootX (-rootC) s) (rootX rootC (1 : K)) := fun _ =>
    isConj_rootX_of_reflect g2ia (IsRoot.neg isRoot_g2c) reflect_a_neg_rootC hnb
  simp only [longRoots, Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ha s hs, hb s hs, hc s hs, hna s hs, hnb s hs, hnc s hs]

theorem isConj_rootX_short
    {γ : Fin Tag.G2.rank → ℤ} (hγ : γ ∈ shortRoots) {s : K}
    (hs : s ≠ 0) : IsConj (rootX γ s) (rootX rootV (1 : K)) := by
  have hv : ∀ s : K, s ≠ 0 → IsConj (rootX rootV s) (rootX rootV (1 : K)) := fun _ =>
    isConj_rootX_one_of_cartan g2ir isRoot_g2v (by decide)
  have hu : ∀ s : K, s ≠ 0 → IsConj (rootX rootU s) (rootX rootV (1 : K)) := fun _ =>
    isConj_rootX_of_reflect g2ir isRoot_g2u reflect_r_rootU hv
  have hr : ∀ s : K, s ≠ 0 → IsConj (rootX rootR s) (rootX rootV (1 : K)) := fun _ =>
    isConj_rootX_of_reflect g2ia isRoot_g2r reflect_a_rootR hu
  have hnr : ∀ s : K, s ≠ 0 → IsConj (rootX (-rootR) s) (rootX rootV (1 : K)) := fun _ =>
    isConj_rootX_of_reflect g2ir (IsRoot.neg isRoot_g2r) reflect_r_neg_rootR hr
  have hnu : ∀ s : K, s ≠ 0 → IsConj (rootX (-rootU) s) (rootX rootV (1 : K)) := fun _ =>
    isConj_rootX_of_reflect g2ia (IsRoot.neg isRoot_g2u) reflect_a_neg_rootU hnr
  have hnv : ∀ s : K, s ≠ 0 → IsConj (rootX (-rootV) s) (rootX rootV (1 : K)) := fun _ =>
    isConj_rootX_of_reflect g2ir (IsRoot.neg isRoot_g2v) reflect_r_neg_rootV hnu
  simp only [shortRoots, Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hr s hs, hu s hs, hv s hs, hnr s hs, hnu s hs, hnv s hs]

theorem rootX_ne_one
    (d : Fin Tag.G2.rank → ℤ) {s : K} (hs : s ≠ 0) : rootX d s ≠ 1 := fun h =>
  hs (rootX_injective d (h.trans (rootX_zero d).symm))

section Cover

variable [CharP K 2] {M : Type*} [Group M] {π : M →* adjointGroup .G2 K} {z : M}

theorem orderOf_eq_two_of_isConj_long
    (hK : Nat.card K = 4) (hη : Function.Surjective π) (hker : ∀ k, π k = 1 → k ∈ center M)
    (hz1 : z ≠ 1) (hz : ∀ k, π k = 1 ↔ k = 1 ∨ k = z) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ ∈ longRoots) {s : K} (hs : s ≠ 0) {m : M} (hm : IsConj (π m) (rootX γ s)) :
    orderOf m = 2 := by
  have h2 : m * m = 1 :=
    mul_self_eq_one_of_isConj_rootX_c hz1 hz hK hη hker (hm.trans (isConj_rootX_long hγ hs))
  refine orderOf_eq_prime (by rw [sq, h2]) fun h1 => rootX_ne_one γ hs ?_
  rw [h1, map_one, isConj_one_right] at hm
  exact hm

theorem orderOf_eq_four_of_isConj_short
    (hK : Nat.card K = 4) [Finite M] [Group.IsPerfect M] (hη : Function.Surjective π)
    (hker : ∀ k, π k = 1 → k ∈ center M) (hz1 : z ≠ 1) (hz : ∀ k, π k = 1 ↔ k = 1 ∨ k = z)
    {γ : Fin Tag.G2.rank → ℤ} (hγ : γ ∈ shortRoots) {s : K} (hs : s ≠ 0) {m : M}
    (hm : IsConj (π m) (rootX γ s)) : orderOf m = 4 := by
  have h2 : m * m = z :=
    mul_self_eq_of_isConj_rootX_v hz1 hz hK hη hker (hm.trans (isConj_rootX_short hγ hs))
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := m) (by rw [pow_one, sq, h2]; exact hz1)
    (by rw [show 2 ^ (1 + 1) = 2 + 2 from rfl, pow_add, sq, h2, mul_self_z hz1 hz])
  rw [h]
  norm_num

end Cover

theorem exists_mem_iff_of_card_eq_two {L : Type*} [Group L] {H : Subgroup L}
    (hH : Nat.card H = 2) : ∃ z : L, z ≠ 1 ∧ ∀ k, k ∈ H ↔ k = 1 ∨ k = z := by
  obtain ⟨⟨z, hzH⟩, hz1, hu⟩ := (Nat.card_eq_two_iff' (1 : H)).1 hH
  refine ⟨z, fun h => hz1 (Subtype.ext h), fun k => ⟨fun hk => ?_, ?_⟩⟩
  · by_cases hk1 : k = 1
    · exact Or.inl hk1
    · exact Or.inr (congrArg Subtype.val (hu ⟨k, hk⟩ fun h => hk1 (congrArg Subtype.val h)))
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact hzH

theorem centralQuotient_eq_one_iff {L X : Type*} [Group L] [Group X]
    (e : L ⧸ center L ≃* X) (k : L) :
    e.toMonoidHom.comp (QuotientGroup.mk' (center L)) k = 1 ↔ k ∈ center L := by
  change e (k : L ⧸ center L) = 1 ↔ _
  rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]

theorem orderOf_eq_two_of_isConj_long_of_quotient
    {L : Type*} [Group L] (hZ : Nat.card (center L) = 2) (hK : Nat.card K = 4)
    (e : L ⧸ center L ≃* adjointGroup .G2 K) {γ : Fin Tag.G2.rank → ℤ} (hγ : γ ∈ longRoots)
    {s : K} (hs : s ≠ 0) {x : L} (hx : IsConj (e x) (rootX γ s)) : orderOf x = 2 := by
  have := LinearFieldFour.charP_two_of_card_eq_four hK
  obtain ⟨z, hz1, hzc⟩ := exists_mem_iff_of_card_eq_two hZ
  have hπ := centralQuotient_eq_one_iff e
  exact orderOf_eq_two_of_isConj_long (π := e.toMonoidHom.comp (QuotientGroup.mk' (center L))) hK
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (fun k hk => (hπ k).1 hk) hz1
    (fun k => (hπ k).trans (hzc k)) hγ hs hx

theorem orderOf_eq_four_of_isConj_short_of_quotient
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L] (hZ : Nat.card (center L) = 2)
    (hK : Nat.card K = 4) (e : L ⧸ center L ≃* adjointGroup .G2 K) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ ∈ shortRoots) {s : K} (hs : s ≠ 0) {x : L} (hx : IsConj (e x) (rootX γ s)) :
    orderOf x = 4 := by
  have := LinearFieldFour.charP_two_of_card_eq_four hK
  obtain ⟨z, hz1, hzc⟩ := exists_mem_iff_of_card_eq_two hZ
  have hπ := centralQuotient_eq_one_iff e
  exact orderOf_eq_four_of_isConj_short (π := e.toMonoidHom.comp (QuotientGroup.mk' (center L)))
    hK (e.surjective.comp (QuotientGroup.mk'_surjective _)) (fun k hk => (hπ k).1 hk) hz1
    (fun k => (hπ k).trans (hzc k)) hγ hs hx

theorem orderOf_eq_two_of_isConj_long_of_adjointQuotient
    {L : Type*} [Group L] (hZ : Nat.card (center L) = 2) (hK : Nat.card K = 4)
    (e : L ⧸ center L ≃* AdjointQuotient .G2 K) {γ : Fin Tag.G2.rank → ℤ} (hγ : γ ∈ longRoots)
    {s : K} (hs : s ≠ 0) {x : L} (hx : IsConj (e x) (rootX γ s : AdjointQuotient .G2 K)) :
    orderOf x = 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let eA : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  have heA : ∀ g : adjointGroup .G2 K, eA g = g := fun g => by
    rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  refine orderOf_eq_two_of_isConj_long_of_quotient hZ hK (e.trans eA) hγ hs ?_
  rw [MulEquiv.trans_apply, ← heA (rootX γ s)]
  exact eA.toMonoidHom.map_isConj hx

theorem orderOf_eq_four_of_isConj_short_of_adjointQuotient
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L] (hZ : Nat.card (center L) = 2)
    (hK : Nat.card K = 4) (e : L ⧸ center L ≃* AdjointQuotient .G2 K)
    {γ : Fin Tag.G2.rank → ℤ} (hγ : γ ∈ shortRoots) {s : K} (hs : s ≠ 0) {x : L}
    (hx : IsConj (e x) (rootX γ s : AdjointQuotient .G2 K)) : orderOf x = 4 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let eA : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  have heA : ∀ g : adjointGroup .G2 K, eA g = g := fun g => by
    rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  refine orderOf_eq_four_of_isConj_short_of_quotient hZ hK (e.trans eA) hγ hs ?_
  rw [MulEquiv.trans_apply, ← heA (rootX γ s)]
  exact eA.toMonoidHom.map_isConj hx

end CFSG.LieType.Steinberg.CentralExt.G2Four
