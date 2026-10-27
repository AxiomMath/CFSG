module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalData2

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {F : Type*} [Group F] {S A B Aa : Subgroup F} {z b : F}

set_option linter.unusedSectionVars false

theorem card_sq_kernel_le (W : ThLocalWitness S A B z)
    (Aa_comm : ∀ x ∈ Aa, ∀ y ∈ Aa, x * y = y * x) (Aa_card : Nat.card Aa = 2 ^ 8)
    (A_eq_sq : ∀ y, y ∈ A ↔ ∃ x ∈ Aa, x ^ 2 = y) {K : Subgroup F} (hK : K ≤ Aa)
    (hKsq : ∀ x ∈ K, x ^ 2 = 1) : Nat.card K ≤ 16 := by
  have sq_mem : ∀ x : ↥Aa, (x : F) ^ 2 ∈ A := fun x => (A_eq_sq _).2 ⟨x, x.2, rfl⟩
  let f : ↥Aa →* ↥A := MonoidHom.mk'
    (fun x => ⟨(x : F) ^ 2, sq_mem x⟩) (fun x y => by
      apply Subtype.ext
      have h := Aa_comm _ x.2 _ y.2
      show ((x : F) * y) ^ 2 = (x : F) ^ 2 * (y : F) ^ 2
      calc ((x : F) * y) ^ 2 = (x * y) * (x * y) := sq _
        _ = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← h]
        _ = (x * x) * (y * y) := by group
        _ = (x : F) ^ 2 * (y : F) ^ 2 := by rw [sq, sq])
  have hfinAa : Finite ↥Aa := Nat.finite_of_card_ne_zero (by rw [Aa_card]; norm_num)
  have hsurj : Function.Surjective f := by
    rintro ⟨a, ha⟩
    obtain ⟨x, hx, rfl⟩ := (A_eq_sq a).1 ha
    exact ⟨⟨x, hx⟩, rfl⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (↥Aa ⧸ f.ker) = Nat.card A := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv]
  rw [h2, Aa_card, W.A_card] at h1
  have hker : Nat.card f.ker = 16 := by omega
  have hle : K.subgroupOf Aa ≤ f.ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hKsq x (mem_subgroupOf.1 hx)
  have h3 := Subgroup.card_le_of_le hle
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv] at h3
  exact h3

theorem ThLocalWitness2.of_basic (W : ThLocalWitness S A B z)
    (Aa_le : Aa ≤ B) (Aa_comm : ∀ x ∈ Aa, ∀ y ∈ Aa, x * y = y * x) (Aa_card : Nat.card Aa = 2 ^ 8)
    (Aa_exp : ∀ x ∈ Aa, x ^ 4 = 1) (A_eq_sq : ∀ y, y ∈ A ↔ ∃ x ∈ Aa, x ^ 2 = y)
    (b_mem : b ∈ B) (b_not_mem : b ∉ Aa) (b_sq : b ^ 2 = 1)
    (b_inv : ∀ x ∈ Aa, b * x * b⁻¹ = x⁻¹) : ThLocalWitness2 B A Aa b := by
  refine ⟨Aa_le, Aa_comm, Aa_card, Aa_exp, A_eq_sq, ?_, b_mem, b_not_mem, b_sq, b_inv⟩
  intro Y hYB hYc hYcard
  have hfin : Finite B := Nat.finite_of_card_ne_zero (by rw [W.B_card]; norm_num)
  have hfinA : Finite Aa := Nat.finite_of_card_ne_zero (by rw [Aa_card]; norm_num)
  have hrel : Aa.relIndex B = 2 := by
    have h := Subgroup.card_mul_index (Aa.subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Aa_le).toEquiv, W.B_card, Aa_card] at h
    have : (Aa.subgroupOf B).index = 2 := by omega
    exact this
  by_contra hne
  have hYnle : ¬ Y ≤ Aa := fun h => hne (Subgroup.eq_of_le_of_card_ge h (by
    rw [Aa_card, hYcard]))
  obtain ⟨y, hyY, hyAa⟩ : ∃ y, y ∈ Y ∧ y ∉ Aa := by
    by_contra h
    push Not at h
    exact hYnle h
  obtain ⟨a0, ha0B, hxor⟩ := Subgroup.relIndex_eq_two_iff.1 hrel
  have hya : y * a0 ∈ Aa := by
    rcases hxor y (hYB hyY) with h | h
    · exact h.1
    · exact absurd h.1 hyAa
  have hBdec : ∀ w ∈ B, w ∈ Aa ∨ w * y⁻¹ ∈ Aa := fun w hw => by
    by_cases hwA : w ∈ Aa
    · exact Or.inl hwA
    · right
      have hwa : w * a0 ∈ Aa := by
        rcases hxor w hw with h | h
        · exact h.1
        · exact absurd h.1 hwA
      have := Aa.mul_mem hwa (Aa.inv_mem hya)
      simpa [mul_assoc] using this
  have hcentral : ∀ x ∈ Aa ⊓ Y, ∀ w ∈ B, x * w = w * x := fun x hx w hw => by
    rcases hBdec w hw with h | h
    · exact Aa_comm x hx.1 w h
    · have hw : w = (w * y⁻¹) * y := by group
      calc x * w = x * ((w * y⁻¹) * y) := by rw [← hw]
        _ = (x * (w * y⁻¹)) * y := (mul_assoc _ _ _).symm
        _ = ((w * y⁻¹) * x) * y := by rw [Aa_comm x hx.1 _ h]
        _ = (w * y⁻¹) * (x * y) := mul_assoc _ _ _
        _ = (w * y⁻¹) * (y * x) := by rw [hYc x hx.2 y hyY]
        _ = ((w * y⁻¹) * y) * x := (mul_assoc _ _ _).symm
        _ = w * x := by rw [← hw]
  have hsq : ∀ x ∈ Aa ⊓ Y, x ^ 2 = 1 := fun x hx => by
    have h1 := hcentral x hx b b_mem
    have h2 := b_inv x hx.1
    have h3 : b * x * b⁻¹ = x := by
      rw [← h1]
      group
    have h4 : x⁻¹ = x := h2.symm.trans h3
    calc x ^ 2 = x * x := sq x
      _ = x * x⁻¹ := by rw [h4]
      _ = 1 := mul_inv_cancel x
  have hK16 : Nat.card ↥(Aa ⊓ Y) ≤ 16 :=
    card_sq_kernel_le W Aa_comm Aa_card A_eq_sq inf_le_left hsq
  have hrelY : Aa.relIndex Y ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right hYB (by rw [hrel]; norm_num : Aa.relIndex B ≠ 0)
    rwa [hrel] at this
  have h5 := Subgroup.card_mul_index ((Aa ⊓ Y).subgroupOf Y)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Aa ⊓ Y ≤ Y)).toEquiv,
    hYcard] at h5
  have h6 : ((Aa ⊓ Y).subgroupOf Y).index ≤ 2 := by
    have : (Aa ⊓ Y).relIndex Y = Aa.relIndex Y := Subgroup.inf_relIndex_right Aa Y
    unfold Subgroup.relIndex at this
    rw [this]
    exact hrelY
  have h7 : 2 ^ 8 ≤ 16 * 2 := by
    calc 2 ^ 8 = Nat.card ↥(Aa ⊓ Y) * ((Aa ⊓ Y).subgroupOf Y).index := h5.symm
      _ ≤ 16 * 2 := Nat.mul_le_mul hK16 h6
  norm_num at h7

end CFSG.EvenSporadicStandard.ThStd
