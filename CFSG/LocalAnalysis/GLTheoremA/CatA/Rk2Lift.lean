module

public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open
open scoped commutatorElement

theorem rk2_lift_elemAbelian {H S : Type} [Group H] [Finite H] [Group S] {q : ℕ} (hq : q.Prime)
    (α : H →* S) (hα : Function.Surjective α) (hker : ¬ q ∣ Nat.card α.ker)
    {A : Subgroup S} (hA : IsElemAbelian q A) :
    ∃ B : Subgroup H, IsElemAbelian q B ∧ Nat.card B = Nat.card A := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite S := Finite.of_surjective α hα
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hq hA
  set P : Subgroup H := A.comap α with hP
  have hcard : Nat.card P = Nat.card α.ker * Nat.card A := by
    have h1 : Nat.card P * P.index = Nat.card H := Subgroup.card_mul_index P
    have h2 : Nat.card A * A.index = Nat.card S := Subgroup.card_mul_index A
    have h3 : P.index = A.index := Subgroup.index_comap_of_surjective A hα
    have h4 : Nat.card α.ker * Nat.card α.range = Nat.card H := Subgroup.card_ker_mul_card_range α
    have h5 : Nat.card α.range = Nat.card S := by
      rw [MonoidHom.range_eq_top.2 hα]
      exact Subgroup.card_top
    have hidx : 0 < A.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right hidx
    calc Nat.card P * A.index = Nat.card P * P.index := by rw [h3]
      _ = Nat.card H := h1
      _ = Nat.card α.ker * Nat.card S := by rw [← h4, h5]
      _ = Nat.card α.ker * (Nat.card A * A.index) := by rw [h2]
      _ = Nat.card α.ker * Nat.card A * A.index := by ring
  obtain ⟨Sy⟩ : Nonempty (Sylow q P) := inferInstance
  set B : Subgroup H := (Sy : Subgroup P).map P.subtype with hB
  have hBcard : Nat.card B = q ^ k := by
    rw [hB, Subgroup.card_map_of_injective P.subtype_injective, Sylow.card_eq_multiplicity, hcard, hk,
      Nat.factorization_mul Nat.card_pos.ne' (pow_ne_zero _ hq.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, Nat.Prime.factorization_pow hq,
      Finsupp.single_eq_same, zero_add]
  have hBP : ∀ x ∈ B, x ∈ P := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hBker : ∀ z ∈ B, z ∈ α.ker → z = 1 := by
    intro z hzB hzk
    have h1 : orderOf z ∣ q ^ k := hBcard ▸ Subgroup.orderOf_dvd_natCard B hzB
    have h2 : orderOf z ∣ Nat.card α.ker := Subgroup.orderOf_dvd_natCard α.ker hzk
    have hcop : Nat.Coprime (q ^ k) (Nat.card α.ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).2 hker)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hαB : ∀ x ∈ B, α x ∈ A := fun x hx => hBP x hx
  refine ⟨B, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, hBcard.trans hk.symm⟩
  · apply Subtype.ext
    change (a : H) * b = b * a
    have hcomm : α a * α b = α b * α a := isElemAbelian_commute hA (hαB a a.2) (hαB b b.2)
    have hc : ⁅(a : H), (b : H)⁆ ∈ B := by
      rw [commutatorElement_def]
      exact B.mul_mem (B.mul_mem (B.mul_mem a.2 b.2) (B.inv_mem a.2)) (B.inv_mem b.2)
    have hck : ⁅(a : H), (b : H)⁆ ∈ α.ker := by
      rw [MonoidHom.mem_ker, commutatorElement_def]
      simp only [map_mul, map_inv]
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact hcomm
    exact (commutatorElement_eq_one_iff_mul_comm).1 (hBker _ hc hck)
  · have hxp : x ^ q ∈ B := B.pow_mem hx q
    have hxk : x ^ q ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hA.2 _ (hαB x hx)
    exact hBker _ hxp hxk

end CFSG.LocalAnalysis.GLTheoremA
