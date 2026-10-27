module

public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.GH74.Uniqueness.Statements

public section

namespace CFSG.Asc75

open CFSG CFSG.GH74.Uniqueness

theorem isConj_of_involutions_bender {K : Type*} [Group K] [Finite K]
    (h : CFSG.BenderSuzuki.IsBenderGroup K) {x y : K} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y := by
  obtain ⟨n, i, e, hT⟩ := CFSG.GH74.Uniqueness.Bender.isBenderGroup_iff_exists_benderType.mp h
  have hx' := orderOf_eq_prime_iff.mp hx
  have hy' := orderOf_eq_prime_iff.mp hy
  exact hT.lemma_3_4_a (by simpa [sq] using hx'.1) hx'.2 (by simpa [sq] using hy'.1) hy'.2

theorem mem_of_involution_of_odd_kernel {Y K : Type*} [Group Y] [Group K] (q : Y →* K)
    (hq : Function.Surjective q) (hodd : ∀ o : Y, q o = 1 → Odd (orderOf o))
    (hconj : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    {Z' : Set Y} (hZ' : ∀ z ∈ Z', ∀ g : Y, g⁻¹ * z * g ∈ Z') {z₀ w : Y} (hz₀ : z₀ ∈ Z')
    (hz₀1 : z₀ ≠ 1) (hz₀2 : z₀ * z₀ = 1) (hw1 : w ≠ 1) (hw2 : w * w = 1) : w ∈ Z' := by
  have hq2 : ∀ v : Y, v ≠ 1 → v * v = 1 → orderOf (q v) = 2 := by
    intro v hv1 hv2
    refine orderOf_eq_prime (by rw [sq, ← map_mul, hv2, map_one]) (fun e => ?_)
    have ho := hodd v e
    have : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
    rw [this] at ho
    exact absurd ho (by decide)
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj _ _ (hq2 z₀ hz₀1 hz₀2) (hq2 w hw1 hw2))
  obtain ⟨l, rfl⟩ := hq c
  set z' : Y := l * z₀ * l⁻¹ with hz'def
  have hz'Z : z' ∈ Z' := by
    have := hZ' z₀ hz₀ l⁻¹
    simpa [hz'def] using this
  have hz'2 : z' * z' = 1 := by
    rw [hz'def]
    calc l * z₀ * l⁻¹ * (l * z₀ * l⁻¹) = l * (z₀ * z₀) * l⁻¹ := by group
      _ = 1 := by rw [hz₀2]; group
  have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
  have hqz : q z' = q w := by
    rw [hz'def, map_mul, map_mul, map_inv]; exact hc
  set o : Y := z'⁻¹ * w with hodef
  have hoodd : Odd (orderOf o) := by
    apply hodd
    rw [hodef, map_mul, map_inv, hqz]; simp
  obtain ⟨k, hk⟩ := CFSG.GH74.Uniqueness.Bender.exists_sq_eq_of_odd_orderOf hoodd
  have hwo : w = z' * o := by rw [hodef, hz'inv]; rw [← mul_assoc, hz'2, one_mul]
  have hzo : z' * o * z' = o⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have : z' * o * (z' * o) = 1 := by rw [← hwo]; exact hw2
    calc z' * o * z' * o = z' * o * (z' * o) := by group
      _ = 1 := this
  set s : Y := o ^ k with hs
  have hzs : z' * s * z' = s⁻¹ := by
    have h1 : (z' * o * z'⁻¹) ^ k = z' * o ^ k * z'⁻¹ := conj_pow
    rw [hz'inv, hzo, inv_pow] at h1
    exact h1.symm
  have e1 : z' * s = s⁻¹ * z' := by
    calc z' * s = (z' * s * z') * z' := by rw [mul_assoc (z' * s) z' z', hz'2, mul_one]
      _ = s⁻¹ * z' := by rw [hzs]
  have hw_eq : w = s⁻¹ * z' * s := by
    have e2 : w = o⁻¹ * z' := by
      calc w = z' * o := hwo
        _ = (z' * o * z') * z' := by rw [mul_assoc (z' * o) z' z', hz'2, mul_one]
        _ = o⁻¹ * z' := by rw [hzo]
    have hso : s * s = o := hk
    calc w = o⁻¹ * z' := e2
      _ = (s * s)⁻¹ * z' := by rw [hso]
      _ = s⁻¹ * (s⁻¹ * z') := by rw [mul_inv_rev, mul_assoc]
      _ = s⁻¹ * (z' * s) := by rw [e1]
      _ = s⁻¹ * z' * s := (mul_assoc s⁻¹ z' s).symm
  rw [hw_eq]
  exact hZ' z' hz'Z s

theorem mem_of_involution_of_perfect_bender
    {Y : Type*} [Group Y] [Finite Y]
    (hD : commutator Y = ⊤) (hB : CFSG.BenderSuzuki.IsBenderGroup (derivedBar Y)) {Z' : Set Y}
    (hZ' : ∀ z ∈ Z', ∀ g : Y, g⁻¹ * z * g ∈ Z') {z₀ w : Y} (hz₀ : z₀ ∈ Z') (hz₀1 : z₀ ≠ 1)
    (hz₀2 : z₀ * z₀ = 1) (hw1 : w ≠ 1) (hw2 : w * w = 1) : w ∈ Z' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ y : Y, y ∈ commutator Y := fun y => hD ▸ Subgroup.mem_top y
  let q : Y →* derivedBar Y :=
    (QuotientGroup.mk' ((pPrimeCore 2 Y).subgroupOf (commutator Y))).comp
      ((MonoidHom.id Y).codRestrict (commutator Y) hmem)
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨d, rfl⟩
  refine mem_of_involution_of_odd_kernel q hsurj (fun o ho => ?_)
    (fun x y hx hy => isConj_of_involutions_bender hB hx hy) hZ' hz₀ hz₀1 hz₀2 hw1 hw2
  have h0 : (⟨o, hmem o⟩ : ↥(commutator Y)) ∈ (pPrimeCore 2 Y).subgroupOf (commutator Y) :=
    (QuotientGroup.eq_one_iff _).mp ho
  have hoO : o ∈ pPrimeCore 2 Y := h0
  have h1 := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 Y) hoO
  have h2 := pPrimeCore_coprime_card (p := 2) (G := Y)
  exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h1 h2)

end CFSG.Asc75
