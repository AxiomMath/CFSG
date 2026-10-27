module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeCore
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd

public section

namespace CFSG.AGLEmbedding

open Equiv Equiv.Perm
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem three_of_mem_cycleType_of_pow_eq_one {σ : Perm α} (hσ : σ ^ 3 = 1) {n : ℕ}
    (hn : n ∈ σ.cycleType) : n = 3 := by
  have h1 : n ∣ 3 := (dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hσ)
  have h2 := two_le_of_mem_cycleType hn
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with rfl | rfl <;> omega

theorem card_support_eq_three_of_mem_cycleFactorsFinset {σ c : Perm α} (hσ : σ ^ 3 = 1)
    (hc : c ∈ σ.cycleFactorsFinset) : c.support.card = 3 :=
  three_of_mem_cycleType_of_pow_eq_one hσ (by
    rw [cycleType_def]
    exact Multiset.mem_map_of_mem _ hc)

theorem card_fixedPoints_le_four_of_isSolvable {σ : Perm α}
    (hs : Group.IsSolvable (Subgroup.centralizer ({σ} : Set (Perm α)))) :
    Fintype.card (Function.fixedPoints σ) ≤ 4 := by
  by_contra h
  set f : Perm (Function.fixedPoints σ) →* Subgroup.centralizer ({σ} : Set (Perm α)) :=
    (ofSubtype : Perm (Function.fixedPoints σ) →* Perm α).codRestrict _ fun v => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Disjoint.commute (disjoint_iff_disjoint_support.mpr (ofSubtype_support_disjoint v)))
  have hf : Function.Injective f := fun a b hab => ofSubtype_injective (congrArg Subtype.val hab)
  have := Group.isSolvable_of_isSolvable_injective hf
  refine Equiv.Perm.not_isSolvable _ ?_ this
  rw [Cardinal.mk_fintype]
  exact_mod_cast (by omega : 5 ≤ Fintype.card (Function.fixedPoints σ))

theorem card_cycleFactorsFinset_le_four_of_isSolvable {σ : Perm α} (hσ : σ ^ 3 = 1)
    (hs : Group.IsSolvable (Subgroup.centralizer ({σ} : Set (Perm α)))) :
    σ.cycleFactorsFinset.card ≤ 4 := by
  by_contra h
  have hsurj : Function.Surjective (OnCycleFactors.toPermHom σ) := by
    intro τ
    have hτ : τ ∈ (OnCycleFactors.toPermHom σ).range := by
      rw [OnCycleFactors.mem_range_toPermHom_iff]
      intro c
      rw [card_support_eq_three_of_mem_cycleFactorsFinset hσ (τ c).2,
        card_support_eq_three_of_mem_cycleFactorsFinset hσ c.2]
    exact hτ
  have := Group.isSolvable_of_surjective hsurj
  refine Equiv.Perm.not_isSolvable _ ?_ this
  rw [Cardinal.mk_fintype, Fintype.card_coe]
  exact_mod_cast (by omega : 5 ≤ σ.cycleFactorsFinset.card)

theorem prime_eq_two_or_three_of_dvd_card_centralizer {σ : Perm α} (hσ : σ ^ 3 = 1)
    (hs : Group.IsSolvable (Subgroup.centralizer ({σ} : Set (Perm α)))) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ Nat.card (Subgroup.centralizer ({σ} : Set (Perm α)))) : p = 2 ∨ p = 3 := by
  have hle : ∀ m : ℕ, p ≤ m → m ≤ 4 → p = 2 ∨ p = 3 := fun m h1 h2 => by
    have := hp.two_le
    have hp4 : p ≤ 4 := h1.trans h2
    interval_cases p <;> first | (left; rfl) | (right; rfl) | (exfalso; norm_num at hp)
  have hcard : Multiset.card σ.cycleType = σ.cycleFactorsFinset.card := by
    rw [cycleType_def, Multiset.card_map]
    rfl
  rw [nat_card_centralizer] at hpd
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rw [← card_fixedPoints] at h
      exact hle _ ((Nat.Prime.dvd_factorial hp).1 h) (card_fixedPoints_le_four_of_isSolvable hs)
    · obtain ⟨n, hn, hpn⟩ := hp.prime.exists_mem_multiset_dvd h
      rw [three_of_mem_cycleType_of_pow_eq_one hσ hn] at hpn
      exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpn)
  · obtain ⟨n, -, hpn⟩ := hp.prime.exists_mem_finset_dvd h
    refine hle _ ((Nat.Prime.dvd_factorial hp).1 hpn) ?_
    exact (Multiset.count_le_card _ _).trans
      (hcard ▸ card_cycleFactorsFinset_le_four_of_isSolvable hσ hs)

end Perm

section Alternating

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem isSolvable_centralizer_perm_of_alternating {a : alternatingGroup α}
    (hs : Group.IsSolvable (Subgroup.centralizer ({a} : Set (alternatingGroup α)))) :
    Group.IsSolvable (Subgroup.centralizer ({(a : Perm α)} : Set (Perm α))) := by
  set CA := Subgroup.centralizer ({a} : Set (alternatingGroup α))
  set CS := Subgroup.centralizer ({(a : Perm α)} : Set (Perm α))
  let f : CA →* CS :=
    { toFun := fun x => ⟨((x : alternatingGroup α) : Perm α), by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Group.isSolvable_of_ker_le_range f (sign.comp CS.subtype) ?_
  intro x hx
  have hxA : (x : Perm α) ∈ alternatingGroup α := hx
  refine ⟨⟨⟨x, hxA⟩, ?_⟩, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)

theorem eq_one_of_mem_centralizer_alternatingGroup {a : alternatingGroup α} (ha : a ^ 3 = 1)
    (hs : Group.IsSolvable (Subgroup.centralizer ({a} : Set (alternatingGroup α))))
    {x : alternatingGroup α} (hx : x ∈ Subgroup.centralizer ({a} : Set (alternatingGroup α)))
    (hx6 : Nat.Coprime 6 (orderOf x)) : x = 1 := by
  by_contra hne
  have hS := isSolvable_centralizer_perm_of_alternating hs
  have hσ : (a : Perm α) ^ 3 = 1 := by rw [← Subgroup.coe_pow, ha, Subgroup.coe_one]
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (orderOf_eq_one_iff.not.mpr hne)
  have hxS : (x : Perm α) ∈ Subgroup.centralizer ({(a : Perm α)} : Set (Perm α)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx)
  have hdvd : p ∣ Nat.card (Subgroup.centralizer ({(a : Perm α)} : Set (Perm α))) :=
    hpx.trans ((Subgroup.orderOf_coe x).symm ▸ Subgroup.orderOf_dvd_natCard _ hxS)
  have h6 : p ∣ 6 := by
    rcases prime_eq_two_or_three_of_dvd_card_centralizer hσ hS hp hdvd with rfl | rfl <;> norm_num
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hx6 h6 hpx)

end Alternating

theorem threeAutFixedTwoThree_alternatingGroup {n : ℕ} (hn : 5 ≤ n) :
    ThreeAutFixedTwoThree (alternatingGroup (Fin n)) := by
  intro α hα3 hfree x hx m hm hxm
  have hZ : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  rw [hZ, Subgroup.mem_bot] at hx hxm ⊢
  have hcop : (3 : ℕ).Coprime (Nat.card (Outer (alternatingGroup (Fin n)))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (not_dvd_card_outer_alternatingGroup n hn 3 Nat.prime_three (by norm_num))
  obtain ⟨a, rfl⟩ := exists_conj_eq_of_pow_eq_one_of_coprime hα3 hcop
  have ha3 : a ^ 3 = 1 := by
    have h1 := mem_center_of_mulAut_conj_eq_one (z := a ^ 3) (by rw [map_pow, hα3])
    rwa [hZ, Subgroup.mem_bot] at h1
  have hs : Group.IsSolvable (Subgroup.centralizer ({a} : Set (alternatingGroup (Fin n)))) := by
    refine isSolvable_of_perfect_eq_bot fun Q hQ => ?_
    have h1 := hfree (Q.map (Subgroup.centralizer _).subtype)
      (by rw [← Subgroup.map_commutator, hQ]) (fun y hy => by
        obtain ⟨z, -, rfl⟩ := hy
        have hz := Subgroup.mem_centralizer_singleton_iff.mp z.2
        rw [MulAut.conj_apply]
        change a * (z : alternatingGroup (Fin n)) * a⁻¹ = z
        rw [← hz, mul_inv_cancel_right])
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  have hxC : x ∈ Subgroup.centralizer ({a} : Set (alternatingGroup (Fin n))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : MulAut.conj a x = x := (inv_mul_eq_one.mp hx).symm
    rw [MulAut.conj_apply] at h1
    calc x * a = a * x * a⁻¹ * a := by rw [h1]
      _ = a * x := by group
  exact eq_one_of_mem_centralizer_alternatingGroup ha3 hs hxC
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxm) hm)

theorem threeAutFixedTwoThree_of_mulEquiv_alternatingGroup {X : Type*} [Group X] {n : ℕ}
    (e : X ≃* alternatingGroup (Fin n)) (hn : 5 ≤ n) : ThreeAutFixedTwoThree X :=
  ThreeAutFixedTwoThree.of_mulEquiv e (threeAutFixedTwoThree_alternatingGroup hn)

end CFSG.AGLEmbedding
