module

public import Mathlib.GroupTheory.Sylow
public import CFSG.ClassicalInvolution.Q3.Q3T6AutConj

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open Matrix
open scoped MatrixGroups

section Inn

theorem Aut.sl2Three_natCard : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem center_aux : ∀ g : SL(2, ZMod 3), (∀ h : SL(2, ZMod 3), g * h = h * g) →
    g = 1 ∨ g = -1 := by
  decide +kernel

private theorem neg_one_central_aux : ∀ h : SL(2, ZMod 3), (-1 : SL(2, ZMod 3)) * h = h * (-1) := by
  decide +kernel

theorem Aut.mem_center_sl2Three_iff (g : SL(2, ZMod 3)) :
    g ∈ Subgroup.center SL(2, ZMod 3) ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hg
    rw [Subgroup.mem_center_iff] at hg
    exact center_aux g fun h => (hg h).symm
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_center_iff.mpr fun h => (neg_one_central_aux h).symm

theorem Aut.orderOf_neg_one_sl2Three : orderOf (-1 : SL(2, ZMod 3)) = 2 := by
  refine orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem Aut.natCard_center_sl2Three : Nat.card (Subgroup.center SL(2, ZMod 3)) = 2 := by
  have : Subgroup.center SL(2, ZMod 3) = Subgroup.zpowers (-1) := by
    ext g
    rw [Aut.mem_center_sl2Three_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
    · rintro ⟨k, rfl⟩
      rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · left
        rw [← two_mul, zpow_mul, zpow_two, show (-1 : SL(2, ZMod 3)) * -1 = 1 by decide +kernel,
          one_zpow]
      · right
        rw [zpow_add_one, zpow_mul, zpow_two, show (-1 : SL(2, ZMod 3)) * -1 = 1 by decide +kernel,
          one_zpow, one_mul]
  rw [this, Nat.card_zpowers, Aut.orderOf_neg_one_sl2Three]

@[expose] def inn3 : Subgroup (MulAut SL(2, ZMod 3)) :=
  (MulAut.conj : SL(2, ZMod 3) →* MulAut SL(2, ZMod 3)).range

theorem mem_inn3_iff {α : MulAut SL(2, ZMod 3)} :
    α ∈ inn3 ↔ ∃ g : SL(2, ZMod 3), MulAut.conj g = α :=
  Iff.rfl

theorem conj_mem_inn3 (g : SL(2, ZMod 3)) : (MulAut.conj g : MulAut SL(2, ZMod 3)) ∈ inn3 :=
  ⟨g, rfl⟩

theorem Aut.ker_conj_sl2Three :
    (MulAut.conj : SL(2, ZMod 3) →* MulAut SL(2, ZMod 3)).ker = Subgroup.center SL(2, ZMod 3) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hg h
    have h1 := congrArg (fun α : MulAut SL(2, ZMod 3) => α h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  · intro hg
    ext h : 1
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← hg h]
    group

theorem natCard_inn3 : Nat.card inn3 = 12 := by
  have h := Subgroup.card_ker_mul_card_range
    (MulAut.conj : SL(2, ZMod 3) →* MulAut SL(2, ZMod 3))
  rw [Aut.ker_conj_sl2Three, Aut.natCard_center_sl2Three, Aut.sl2Three_natCard] at h
  unfold inn3
  omega

theorem inn3_index : inn3.index = 2 := by
  have h := Subgroup.card_mul_index inn3
  rw [natCard_inn3, sl2Three_card_mulAut] at h
  omega

instance inn3_normal : inn3.Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ α
    refine ⟨α g, ?_⟩
    ext h : 1
    simp [MulAut.conj_apply]

theorem conjAut_toGL (b : SL(2, ZMod 3)) :
    (conjAut (Matrix.SpecialLinearGroup.toGL b) : MulAut SL(2, ZMod 3)) = MulAut.conj b := by
  ext h : 1
  apply Subtype.ext
  simp [conjAut_apply, coe_conjSL, MulAut.conj_apply, Matrix.inv_def]

end Inn

section Orders

private theorem order_aux : ∀ g : SL(2, ZMod 3), (g ^ 4 = 1 ∨ g ^ 4 = -1) →
    (g ^ 2 = 1 ∨ g ^ 2 = -1) := by
  decide +kernel

theorem orderOf_ne_four_of_mem_inn3 {x : MulAut SL(2, ZMod 3)} (hx : x ∈ inn3) :
    orderOf x ≠ 4 := by
  obtain ⟨g, rfl⟩ := hx
  intro h4
  have h1 : (MulAut.conj g : MulAut SL(2, ZMod 3)) ^ 4 = 1 := by
    rw [← h4]
    exact pow_orderOf_eq_one _
  have h2 : (MulAut.conj g : MulAut SL(2, ZMod 3)) ^ 2 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  rw [← map_pow] at h1 h2
  have h1' : g ^ 4 ∈ Subgroup.center SL(2, ZMod 3) := by
    rw [← Aut.ker_conj_sl2Three]
    exact h1
  have h2' : g ^ 2 ∉ Subgroup.center SL(2, ZMod 3) := by
    rw [← Aut.ker_conj_sl2Three]
    exact h2
  rw [Aut.mem_center_sl2Three_iff] at h1' h2'
  exact h2' (order_aux g h1')

private noncomputable def autSinger : GL (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mk'' !![0, 1; 1, 1] (IsUnit.of_mul_eq_one (2 : ZMod 3) (by decide))

private theorem autSinger_pow_four : autSinger ^ 4 = -1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  show (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 4 = -1
  decide +kernel

private theorem autSinger_pow_two_ne : autSinger ^ 2 ≠ 1 ∧ autSinger ^ 2 ≠ -1 := by
  have h : ∀ a b : GL (Fin 2) (ZMod 3), (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ b → a ≠ b :=
    fun a b h hab => h (by rw [hab])
  constructor
  · refine h _ _ ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 2 ≠ 1
    decide +kernel
  · refine h _ _ ?_
    rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    show (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 2 ≠ -1
    decide +kernel

theorem exists_orderOf_four_mulAut : ∃ x : MulAut SL(2, ZMod 3), orderOf x = 4 := by
  have hker : ∀ g : GL (Fin 2) (ZMod 3), g ∈ Subgroup.center (GL (Fin 2) (ZMod 3)) ↔
      conjAut g = 1 := fun g => by
    rw [← conjAut3_ker, MonoidHom.mem_ker]
  refine ⟨conjAut autSinger, ?_⟩
  have e1 : (conjAut autSinger) ^ 2 ^ 1 ≠ 1 := by
    intro h
    rw [pow_one, ← map_pow, ← hker, Aut.mem_center_gl3_iff] at h
    exact h.elim autSinger_pow_two_ne.1 autSinger_pow_two_ne.2
  have e2 : (conjAut autSinger) ^ 2 ^ (1 + 1) = 1 := by
    rw [show 2 ^ (1 + 1) = 4 by norm_num, ← map_pow, ← hker, Aut.mem_center_gl3_iff]
    exact Or.inr autSinger_pow_four
  have := orderOf_eq_prime_pow e1 e2
  rwa [show 2 ^ (1 + 1) = 4 by norm_num] at this

theorem not_mem_inn3_of_orderOf_four {x : MulAut SL(2, ZMod 3)} (hx : orderOf x = 4) :
    x ∉ inn3 := fun h => orderOf_ne_four_of_mem_inn3 h hx

end Orders

section M3

private def autQuatR : SL(2, ZMod 3) := ⟨!![1, 1; 1, -1], by decide⟩

private theorem autQuatR_pow_four : autQuatR ^ 4 = 1 := by decide +kernel

private theorem commute_quat_aux : ∀ g : Matrix (Fin 2) (Fin 2) (ZMod 3),
    (∃ u : ZMod 3, g.det * u = 1) →
    g * (autGenS : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (autGenS : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g →
    g * (autQuatR : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (autQuatR : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g → g = 1 ∨ g = -1 := by
  decide +kernel

private theorem exponent_aux : ∀ x : SL(2, ZMod 3), x ^ 8 = 1 → x ^ 4 = 1 := by
  decide +kernel

private theorem q8_card_aux :
    (Finset.univ.filter fun x : SL(2, ZMod 3) => x ^ 4 = 1).card = 8 := by
  decide +kernel

private theorem factorization_two_card :
    (Nat.card SL(2, ZMod 3)).factorization 2 = 3 := by
  rw [Aut.sl2Three_natCard]
  have h : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem sl2Three_sylow_two_eq (P : Sylow 2 SL(2, ZMod 3)) :
    (P : Set SL(2, ZMod 3)) = {x | x ^ 4 = 1} := by
  have hcard : Nat.card (P : Subgroup SL(2, ZMod 3)) = 8 := by
    rw [Sylow.card_eq_multiplicity, factorization_two_card]
    norm_num
  have hsub : (P : Set SL(2, ZMod 3)) ⊆ {x | x ^ 4 = 1} := by
    intro x hx
    have h1 : orderOf x ∣ 8 := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : (P : Subgroup SL(2, ZMod 3)))
      rwa [Subgroup.orderOf_mk, hcard] at this
    exact exponent_aux x (orderOf_dvd_iff_pow_eq_one.mp h1)
  refine Set.eq_of_subset_of_ncard_le hsub ?_
  have h8 : (P : Set SL(2, ZMod 3)).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have hq : ({x : SL(2, ZMod 3) | x ^ 4 = 1}).ncard = 8 := by
    have : ({x : SL(2, ZMod 3) | x ^ 4 = 1}) =
        ↑(Finset.univ.filter fun x : SL(2, ZMod 3) => x ^ 4 = 1) := by
      ext
      simp
    rw [this, Set.ncard_coe_finset]
    exact q8_card_aux
  omega

private theorem mul_eq_of_eq_conj {R : Type*} [CommRing R] (G : GL (Fin 2) R)
    {x y : Matrix (Fin 2) (Fin 2) R}
    (h : y = (G : Matrix (Fin 2) (Fin 2) R) * x *
      ((G⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)) :
    (G : Matrix (Fin 2) (Fin 2) R) * x = y * (G : Matrix (Fin 2) (Fin 2) R) := by
  rw [h, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.mul_one]

theorem sl2Three_mulAut_eq_one_of_fixes_sylow (P : Sylow 2 SL(2, ZMod 3))
    (α : MulAut SL(2, ZMod 3)) (hfix : ∀ x ∈ P, α x = x) : α = 1 := by
  have hS : autGenS ∈ P := by
    have : autGenS ∈ (P : Set SL(2, ZMod 3)) := by
      rw [sl2Three_sylow_two_eq P]
      exact autGenS_pow_four
    exact this
  have hR : autQuatR ∈ P := by
    have : autQuatR ∈ (P : Set SL(2, ZMod 3)) := by
      rw [sl2Three_sylow_two_eq P]
      exact autQuatR_pow_four
    exact this
  obtain ⟨g, hg⟩ := sl2Three_aut_eq_conj α
  have hc : ∀ x ∈ P, (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (x : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (x : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    intro x hx
    refine mul_eq_of_eq_conj g ?_
    rw [← hg x, hfix x hx]
  have hdet : IsUnit (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  obtain ⟨u, hu⟩ := hdet.exists_right_inv
  have hα : α = conjAut g := by
    ext b : 1
    exact Subtype.ext (by rw [conjAut_apply, coe_conjSL]; exact hg b)
  rw [hα, ← MonoidHom.mem_ker, conjAut3_ker, Aut.mem_center_gl3_iff]
  rcases commute_quat_aux _ ⟨u, hu⟩ (hc _ hS) (hc _ hR) with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [Units.val_neg, Units.val_one]; exact h))

theorem sl2Three_mulAut_involution_structure (β : MulAut SL(2, ZMod 3)) (_hβ : β * β = 1) :
    ∃ g : GL (Fin 2) (ZMod 3), ∀ b, β b = conjSL g b := by
  obtain ⟨g, hg⟩ := sl2Three_aut_eq_conj β
  exact ⟨g, fun b => Subtype.ext (by rw [coe_conjSL]; exact hg b)⟩

theorem sl2Three_mulAut_involution_eq_one (β : MulAut SL(2, ZMod 3)) (_hβ : β * β = 1)
    (P : Sylow 2 SL(2, ZMod 3)) (hfix : ∀ x ∈ P, β x = x) : β = 1 :=
  sl2Three_mulAut_eq_one_of_fixes_sylow P β hfix

theorem sl2Three_mulAut_eq_one_of_pow_two_pow_eq_one (P : Sylow 2 SL(2, ZMod 3)) (n : ℕ) :
    ∀ β : MulAut SL(2, ZMod 3), β ^ 2 ^ n = 1 → (∀ x ∈ P, β x = x) → β = 1 :=
  fun β _ hfix => sl2Three_mulAut_eq_one_of_fixes_sylow P β hfix

end M3

end CFSG.ClassicalInvolution.Q3.Q3T6
