module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.Omega

structure SwCentralTwo {Λ X : Type*} [Group Λ] [Group X] (τ : Λ →* X) : Prop where
  surj : Function.Surjective τ
  ker_card : Nat.card τ.ker = 2
  ker_central : τ.ker ≤ Subgroup.center Λ

namespace SwCentralTwo

variable {Λ X : Type*} [Group Λ] [Group X] {τ : Λ →* X}

private theorem ker_comm (hτ : SwCentralTwo τ) {e : Λ} (he : e ∈ τ.ker) (y : Λ) :
    e * y = y * e :=
  (Subgroup.mem_center_iff.mp (hτ.ker_central he) y).symm

private theorem mul_pow_central {G : Type*} [Group G] {e : G}
    (he : ∀ y : G, e * y = y * e) (k : ℕ) (y : G) : y * e ^ k = e ^ k * y := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, ← he y, ← mul_assoc]

theorem ker_sq (hτ : SwCentralTwo τ) {e : Λ} (he : e ∈ τ.ker) : e * e = 1 := by
  have h2 : (⟨e, he⟩ : τ.ker) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := (⟨e, he⟩ : τ.ker))
    rw [hτ.ker_card] at h
    exact h
  have h3 := congrArg Subtype.val h2
  simpa [pow_two] using h3

theorem eq_one_of_odd (hτ : SwCentralTwo τ) {o : Λ} (ho : Odd (orderOf o)) (h : τ o = 1) :
    o = 1 := by
  have he : o ∈ τ.ker := MonoidHom.mem_ker.mpr h
  have hsq : o * o = 1 := hτ.ker_sq he
  have hdvd : orderOf o ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa [pow_two] using hsq
  have hone : orderOf o = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ ho) (by decide)
  exact orderOf_eq_one_iff.mp hone

theorem odd_lift [Finite Λ] (hτ : SwCentralTwo τ) {x : X} (hx : Odd (orderOf x)) :
    ∃ o : Λ, Odd (orderOf o) ∧ τ o = x := by
  obtain ⟨l, hl⟩ := hτ.surj x
  set m := orderOf x with hm
  have hxm : x ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one x
  have hlm : τ (l ^ m) = 1 := by rw [map_pow, hl, hxm]
  have hsq : (l ^ m) * (l ^ m) = 1 := hτ.ker_sq (MonoidHom.mem_ker.mpr hlm)
  have hsq2 : (l ^ m) ^ 2 = 1 := by rw [pow_two]; exact hsq
  refine ⟨l ^ (m + 1), ?_, ?_⟩
  · have hx' : Odd m := by rw [hm]; exact hx
    obtain ⟨k, hk⟩ := hx
    have hm' : m = 2 * k + 1 := hm.trans hk
    have hexp : (m + 1) * m = m * 2 * (k + 1) := by rw [hm']; ring
    have h1 : (l ^ (m + 1)) ^ m = 1 := by
      calc (l ^ (m + 1)) ^ m = l ^ ((m + 1) * m) := by rw [pow_mul]
        _ = l ^ (m * 2 * (k + 1)) := by rw [hexp]
        _ = ((l ^ m) ^ 2) ^ (k + 1) := by rw [pow_mul, pow_mul]
        _ = 1 := by rw [hsq2, one_pow]
    have hdvd : orderOf (l ^ (m + 1)) ∣ m := orderOf_dvd_of_pow_eq_one h1
    exact hx'.of_dvd_nat hdvd
  · rw [map_pow, hl, pow_succ, hxm, one_mul]

theorem odd_comm (hτ : SwCentralTwo τ) {o z : Λ} (ho : Odd (orderOf o))
    (h : τ o * τ z = τ z * τ o) : o * z = z * o := by
  set m := orderOf o with hm
  have hom : o ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one o
  set e := o * z * o⁻¹ * z⁻¹ with he
  have heker : e ∈ τ.ker := by
    rw [MonoidHom.mem_ker, he]
    simp only [map_mul, map_inv, h]
    group
  have hec : ∀ y : Λ, e * y = y * e := hτ.ker_comm heker
  have hee : e * e = 1 := hτ.ker_sq heker
  have key : ∀ k : ℕ, o ^ k * z * (o ^ k)⁻¹ = e ^ k * z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc o ^ (k + 1) * z * (o ^ (k + 1))⁻¹
          = o * (o ^ k * z * (o ^ k)⁻¹) * o⁻¹ := by group
        _ = o * (e ^ k * z) * o⁻¹ := by rw [ih]
        _ = e ^ k * (o * z * o⁻¹) := by
              conv_lhs => rw [← mul_assoc, mul_pow_central hec k o]
              group
        _ = e ^ k * (e * z) := by
              congr 1
              rw [he]
              group
        _ = e ^ (k + 1) * z := by rw [pow_succ]; group
  have hz : z = e ^ m * z := by
    have h := key m
    rw [hom, inv_one, one_mul, mul_one] at h
    exact h
  have hem : e ^ m = 1 := by
    have h := congrArg (fun t => t * z⁻¹) hz
    simpa [mul_assoc] using h.symm
  have he_eq : e = 1 := by
    obtain ⟨k, hk⟩ := ho
    have hek : e ^ m = e := by
      have hee2 : e ^ 2 = 1 := by rw [pow_two]; exact hee
      rw [hm.trans hk, pow_succ, pow_mul, hee2, one_pow, one_mul]
    rw [← hek, hem]
  have hcom : o * z * o⁻¹ * z⁻¹ = 1 := he ▸ he_eq
  calc o * z = o * z * o⁻¹ * z⁻¹ * (z * o) := by group
    _ = 1 * (z * o) := by rw [hcom]
    _ = z * o := one_mul _

theorem odd_mem (hτ : SwCentralTwo τ) {A : Subgroup Λ} {o k : Λ} (ho : Odd (orderOf o))
    (hk : k ∈ A) (h : τ o = τ k) : o ∈ A := by
  set m := orderOf o with hm
  have hom : o ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one o
  set e := o⁻¹ * k with he
  have heker : e ∈ τ.ker := by
    rw [MonoidHom.mem_ker, he, map_mul, map_inv, h]
    group
  have hee : e * e = 1 := hτ.ker_sq heker
  have hcomm : Commute o e := Subgroup.mem_center_iff.mp (hτ.ker_central heker) o
  have hk_eq : k = o * e := by rw [he]; group
  have hek : e = k ^ m := by
    rw [hk_eq, hcomm.mul_pow, hom, one_mul]
    have hee2 : e ^ 2 = 1 := by rw [pow_two]; exact hee
    obtain ⟨j, hj⟩ := ho
    rw [hm.trans hj, pow_succ, pow_mul, hee2, one_pow, one_mul]
  have heA : e ∈ A := by rw [hek]; exact A.pow_mem hk m
  have ho_eq : o = k * e⁻¹ := by rw [hk_eq]; group
  rw [ho_eq]
  exact A.mul_mem hk (A.inv_mem heA)

theorem comp_conj (hτ : SwCentralTwo τ) (g : X) :
    SwCentralTwo ((MulAut.conj g).toMonoidHom.comp τ) := by
  have hker : ((MulAut.conj g).toMonoidHom.comp τ).ker = τ.ker :=
    MonoidHom.ker_comp_of_injective τ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  refine ⟨?_, ?_, ?_⟩
  · exact (MulAut.conj g).surjective.comp hτ.surj
  · rw [hker]; exact hτ.ker_card
  · rw [hker]; exact hτ.ker_central

theorem card_le_map [Finite Λ] (hτ : SwCentralTwo τ) (S : Subgroup Λ) :
    Nat.card S ≤ 2 * Nat.card (S.map τ) := by
  have hcard := Subgroup.card_ker_mul_card_range (τ.domRestrict S)
  rw [MonoidHom.domRestrict_range] at hcard
  have hker : Nat.card (τ.domRestrict S).ker ≤ 2 := by
    rw [MonoidHom.ker_domRestrict]
    have hle : (τ.ker.subgroupOf S).map S.subtype ≤ τ.ker := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hy
    have h1 : Nat.card ((τ.ker.subgroupOf S).map S.subtype) ≤ Nat.card τ.ker :=
      Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective S.subtype_injective, hτ.ker_card] at h1
    exact h1
  calc Nat.card S = Nat.card (τ.domRestrict S).ker * Nat.card (S.map τ) := hcard.symm
    _ ≤ 2 * Nat.card (S.map τ) := Nat.mul_le_mul_right _ hker

end SwCentralTwo

end CFSG.OddStandard.SmallF3.Omega
