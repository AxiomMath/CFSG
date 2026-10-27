module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveLocal
public import CFSG.CGT.PushingUpLit.CGT6M.FiveComm

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

variable {V : Type} [CommGroup V] [Finite V]

theorem card_commSub_le_of_mul {a z y : MulAut V} (h : y = a * z) :
    Nat.card (commSub y) ≤ Nat.card (commSub a) * Nat.card (commSub z) := by
  let μ : ↥(commSub a) × ↥(commSub z) →* V :=
    { toFun := fun p => (p.1 : V) * (p.2 : V)
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        exact mul_mul_mul_comm _ _ _ _ }
  have hle : commSub y ≤ μ.range := by
    rintro w ⟨v, rfl⟩
    refine ⟨(⟨a (z v) * (z v)⁻¹, deltaHom_mem_commSub a (z v)⟩,
      ⟨z v * v⁻¹, deltaHom_mem_commSub z v⟩), ?_⟩
    simp only [μ, MonoidHom.coe_mk, OneHom.coe_mk, deltaHom_apply, h, MulAut.mul_apply]
    group
  calc Nat.card (commSub y) ≤ Nat.card μ.range := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (↥(commSub a) × ↥(commSub z)) :=
        Nat.card_le_card_of_surjective _ μ.rangeRestrict_surjective
    _ = Nat.card (commSub a) * Nat.card (commSub z) := Nat.card_prod _ _

theorem card_commSub_le_of_inverted {x z : MulAut V} (hz2 : z * z = 1) (hinv : z * x * z⁻¹ = x⁻¹)
    (hx5 : x ^ 5 = 1) : Nat.card (commSub x) ≤ Nat.card (commSub z) ^ 2 := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  set a := x * z * x⁻¹ with ha
  have hxx : x ^ 2 = a * z := by
    have h1 : z * x⁻¹ * z⁻¹ = x := by
      have := congrArg (fun e : MulAut V => e⁻¹) hinv
      simpa [mul_inv_rev, mul_assoc] using this
    calc x ^ 2 = x * (z * x⁻¹ * z⁻¹) := by rw [h1, sq]
      _ = x * z * x⁻¹ * z := by rw [hzi]; group
  have hca : Nat.card (commSub a) = Nat.card (commSub z) := card_commSub_conj x z
  have h2 := card_commSub_le_of_mul hxx
  rw [hca, ← sq] at h2
  rwa [commSub_pow_eq hx5 (k := 2) (m := 3) (by norm_num)] at h2

theorem false_of_inverted_C55 (hV : ∀ v : V, v ^ 2 = 1) {z : MulAut V} (hz2 : z * z = 1)
    (hW : Nat.card (commSub z) ≤ 4) (Φ : C55 →* MulAut V) (hΦ : Function.Injective Φ)
    (hinv : ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹) : False := by
  classical
  have h5 : ∀ u : C55, (Φ u) ^ 5 = 1 := by
    intro u
    rw [← map_pow]
    obtain ⟨⟨i, j⟩, rfl⟩ : ∃ w, u = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd u, rfl⟩
    rw [← ofAdd_nsmul]
    have h5' : (5 : ℕ) • ((i, j) : ZMod 5 × ZMod 5) = 0 := by
      have h5'' : (5 : ZMod 5) = 0 := by decide
      ext <;> simp [h5'']
    rw [h5']
    exact map_one Φ
  have hfix : ∀ u : C55, u ≠ 1 → 16 * Nat.card (fixSub (Φ u)) = Nat.card V := by
    intro u hu
    have hx1 : Φ u ≠ 1 := fun h => hu (hΦ (h.trans (map_one Φ).symm))
    have hle : Nat.card (commSub (Φ u)) ≤ 16 := by
      have h1 := card_commSub_le_of_inverted hz2 (hinv u) (h5 u)
      have h2 : Nat.card (commSub z) ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left hW 2
      omega
    rw [← card_commSub_eq_sixteen (h5 u) hx1 hV hle]
    exact card_commSub_mul_card_fixSub (Φ u)
  have hdvd := dvd_sum_card_fixSub Φ
  obtain ⟨d, hd⟩ := exists_card_eq_two_pow hV (⊤ : Subgroup V)
  rw [Subgroup.card_top] at hd
  have hfix1 : Nat.card (fixSub (Φ 1)) = Nat.card V := by
    rw [map_one, fixSub_one, Subgroup.card_top]
  have hsum : ∑ u : C55, Nat.card (fixSub (Φ u)) =
      Nat.card V + ∑ u ∈ Finset.univ.erase (1 : C55), Nat.card (fixSub (Φ u)) := by
    have := Finset.add_sum_erase Finset.univ (fun u : C55 => Nat.card (fixSub (Φ u)))
      (Finset.mem_univ (1 : C55))
    rw [hfix1] at this
    exact this.symm
  set N := Nat.card V with hN
  have hrest : 16 * ∑ u ∈ Finset.univ.erase (1 : C55), Nat.card (fixSub (Φ u)) = 24 * N := by
    rw [Finset.mul_sum]
    have : ∀ u ∈ Finset.univ.erase (1 : C55), 16 * Nat.card (fixSub (Φ u)) = N := fun u hu =>
      hfix u (Finset.ne_of_mem_erase hu)
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _)]
    have hc : Finset.univ.card (α := C55) = 25 := by
      rw [Finset.card_univ, Fintype.card_congr Multiplicative.toAdd, Fintype.card_prod, ZMod.card]
    rw [hc]
    simp
  rw [hsum] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  have h5N : 5 ∣ N := ⟨2 * c, by omega⟩
  rw [hd] at h5N
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5N)
  omega

end CFSG.CGT.PushingUpLit.CGT6M
