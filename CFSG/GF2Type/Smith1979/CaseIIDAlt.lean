module

public import CFSG.GF2Type.Smith1979.CaseIIDCrit
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GF2Type.Smith1979.Case2

open Equiv Equiv.Perm Subgroup

theorem isCycle_of_orderOf_seven {n : ℕ} (h13 : n ≤ 13) {y : Perm (Fin n)} (hy : orderOf y = 7) :
    y.IsCycle := by
  refine isCycle_of_prime_order' (by rw [hy]; decide) ?_
  rw [Fintype.card_fin, hy]
  omega

theorem apply_eq_of_commute_orderOf_seven {n : ℕ} (h13 : n ≤ 13) {π y : Perm (Fin n)}
    (hπ : π * π = 1) (hy : orderOf y = 7) (hc : π * y = y * π) {p : Fin n}
    (hp : p ∈ y.support) : π p = p := by
  have hcyc : y.IsCycle := isCycle_of_orderOf_seven h13 hy
  have hyp : y p ≠ p := Perm.mem_support.mp hp
  have hcom : ∀ x, π (y x) = y (π x) := fun x => by
    have := congrArg (fun f : Perm (Fin n) => f x) hc
    simpa using this
  have hyπ : y (π p) ≠ π p := by
    rw [← hcom]
    exact fun h => hyp (π.injective h)
  obtain ⟨i, hi⟩ := (hcyc.sameCycle hyp hyπ).exists_nat_pow_eq
  have hcomi : ∀ (k : ℕ) (x : Fin n), π ((y ^ k) x) = (y ^ k) (π x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [pow_succ, Perm.mul_apply, Perm.mul_apply, ih, hcom]
  have hππ : π (π p) = p := by
    have := congrArg (fun f : Perm (Fin n) => f p) hπ
    simpa using this
  have h2 : (y ^ (i + i)) p = p := by
    rw [pow_add, Perm.mul_apply, hi, ← hcomi, hi, hππ]
  have h3 : y ^ (i + i) = 1 := (hcyc.pow_eq_one_iff' hyp).mpr h2
  have h4 : 7 ∣ i + i := by
    rw [← hy]
    exact orderOf_dvd_of_pow_eq_one h3
  have h5 : 7 ∣ i := by omega
  have h6 : y ^ i = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hy]
    exact h5
  rw [← hi, h6]
  rfl

theorem card_fixSubgroup_conjNormal_ne {n : ℕ} (h8 : 8 ≤ n) (h12 : n ≤ 12) (π : Perm (Fin n))
    (hπ : π * π = 1) :
    Nat.card (fixSubgroup (MulAut.conjNormal π : MulAut (alternatingGroup (Fin n)))) ≠ 1344 := by
  intro hcard
  set σ : MulAut (alternatingGroup (Fin n)) := MulAut.conjNormal π with hσ
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h7 : 7 ∣ Nat.card (fixSubgroup σ) := by
    rw [hcard]
    norm_num
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 7 h7
  set y' : Perm (Fin n) := (((y : fixSubgroup σ) : alternatingGroup (Fin n)) : Perm (Fin n))
    with hy'def
  have hy' : orderOf y' = 7 := by
    rw [hy'def, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  have hfix : π * y' * π⁻¹ = y' := by
    have h := congrArg (fun a : alternatingGroup (Fin n) => (a : Perm (Fin n)))
      (mem_fixSubgroup.mp y.2)
    simpa [hσ] using h
  have hc : π * y' = y' * π := mul_inv_eq_iff_eq_mul.mp hfix
  have hπfix : ∀ p ∈ y'.support, π p = p := fun p hp =>
    apply_eq_of_commute_orderOf_seven (by omega) hπ hy' hc hp
  have hcyc : y'.IsCycle := isCycle_of_orderOf_seven (by omega) hy'
  have hs : Fintype.card y'.support = 7 := by
    rw [Fintype.card_coe, ← hcyc.orderOf, hy']
  have hnt : Nontrivial y'.support := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hcomm : ∀ a : alternatingGroup y'.support,
      π * (alternatingGroup.ofSubtype y'.support a : alternatingGroup (Fin n)) * π⁻¹ =
        (alternatingGroup.ofSubtype y'.support a : alternatingGroup (Fin n)) := by
    intro a
    rw [alternatingGroup.coe_ofSubtype]
    refine mul_inv_eq_iff_eq_mul.mpr (Disjoint.commute fun x => ?_).eq
    by_cases hx : x ∈ y'.support
    · exact Or.inl (hπfix x hx)
    · exact Or.inr (Perm.ofSubtype_apply_of_not_mem _ hx)
  let f : alternatingGroup y'.support →* fixSubgroup σ :=
    (alternatingGroup.ofSubtype y'.support).codRestrict (fixSubgroup σ) fun a =>
      mem_fixSubgroup.mpr (Subtype.ext (by simpa [hσ] using hcomm a))
  have hf : Function.Injective f := fun a b hab =>
    alternatingGroup.ofSubtype_injective (congrArg Subtype.val hab)
  have h1 := Nat.card_le_card_of_injective f hf
  rw [nat_card_alternatingGroup, hcard, Nat.card_eq_fintype_card, hs] at h1
  norm_num [Nat.factorial] at h1

theorem not_critII_alternating {n : ℕ} (h8 : 8 ≤ n) (h12 : n ≤ 12) :
    ¬ CritII (alternatingGroup (Fin n)) := by
  rintro ⟨σ, hσ2, -, hcard⟩
  obtain ⟨π, rfl⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    (by omega) (by omega)).2 σ
  have hinj := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    (by omega) (by omega)).1
  have hππ : π * π = 1 := by
    apply hinj
    rw [map_mul, map_one]
    exact hσ2
  exact card_fixSubgroup_conjNormal_ne h8 h12 π hππ (by rw [card_fixSubgroup]; exact hcard)

end CFSG.GF2Type.Smith1979.Case2
