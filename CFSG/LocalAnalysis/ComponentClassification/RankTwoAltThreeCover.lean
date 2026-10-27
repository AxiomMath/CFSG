module

public import CFSG.Alternating.Multipliers.Small

public section

namespace CFSG.ComponentClassification.RankTwoAlt.Three

open Equiv Equiv.Perm Subgroup CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers
open scoped commutatorElement

section Comm

variable {P : Type*} [Group P]

theorem commutatorElement_mul_mul_central {a b z w : P} (hz : z ∈ center P)
    (hw : w ∈ center P) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' : ∀ x : P, z * x * z⁻¹ = x := fun x => by
    rw [← mem_center_iff.1 hz x, mul_inv_cancel_right]
  have hw' : ∀ x : P, w * x * w⁻¹ = x := fun x => by
    rw [← mem_center_iff.1 hw x, mul_inv_cancel_right]
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by rw [hz']; group
    _ = ⁅a, b⁆ := by rw [hw', commutatorElement_def]

theorem commutatorElement_inv_right_of_mem_center {w c : P} (h : ⁅w, c⁆ ∈ center P) :
    ⁅w, c⁻¹⁆ = ⁅w, c⁆⁻¹ := by
  have h' : ⁅c, w⁆ ∈ center P := by
    rw [← commutatorElement_inv]
    exact inv_mem h
  rw [commutatorElement_inv_right, mem_center_iff.1 h' c⁻¹, inv_mul_cancel_right,
    commutatorElement_inv]

end Comm

section Core

variable {P : Type*} [Group P] [Finite P] {Q : Type*} [Group Q]

omit [Finite P] in
theorem commute_of_inverts {π : P →* Q} (hK : π.ker ≤ center P) (hodd : Odd (Nat.card π.ker))
    (α : P →* P) (hαK : ∀ z ∈ π.ker, α z = z) {w c : P} (hab : Commute (π w) (π c))
    (hαw : π (α w) = π w) (hαc : π (α c) = (π c)⁻¹) : Commute w c := by
  set k := ⁅w, c⁆ with hk
  have hkK : k ∈ π.ker := by
    rw [MonoidHom.mem_ker, hk, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hab
  have hz₁ : w⁻¹ * α w ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαw, inv_mul_cancel]
  have hz₂ : c * α c ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, hαc, mul_inv_cancel]
  have hαk : α k = k⁻¹ := by
    have e₁ : α w = w * (w⁻¹ * α w) := by group
    have e₂ : α c = c⁻¹ * (c * α c) := by group
    rw [hk, map_commutatorElement, e₁, e₂, commutatorElement_mul_mul_central (hK hz₁) (hK hz₂),
      commutatorElement_inv_right_of_mem_center (hK hkK)]
  have hkk : k * k = 1 := by
    have h := hαK k hkK
    rw [hαk] at h
    calc k * k = k * k⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel k
  have hord : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hkk)
  have hord' : orderOf k ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard _ hkK
  have h1 : orderOf k = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact h
    · rw [h] at hord'
      exact absurd (even_iff_two_dvd.mpr hord') (Nat.not_even_iff_odd.mpr hodd)
  rw [orderOf_eq_one_iff] at h1
  rw [← commutatorElement_eq_one_iff_commute]
  exact h1

open scoped IsMulCommutative in
theorem pow_index_eq_one_of_isPerfect (hP : commutator P = ⊤) (H : Subgroup P)
    [IsMulCommutative H] {z : P} (hz : z ∈ center P) : z ^ H.index = 1 := by
  have key : ∀ (k : ℕ) (g₀ : P), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    rw [mul_assoc, ← mem_center_iff.1 (pow_mem hz k) g₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have h := MonoidHom.transfer_eq_pow (MonoidHom.id H) z key
  have h1 : MonoidHom.transfer (MonoidHom.id H) z = 1 := by
    have hle := Abelianization.commutator_subset_ker (MonoidHom.transfer (MonoidHom.id H))
    rw [hP] at hle
    exact hle (mem_top z)
  rw [h1, MonoidHom.id_apply] at h
  exact (congrArg Subtype.val h).symm

end Core

section Small

variable {n : ℕ}

theorem six_le_of (hn : n = 6 ∨ n = 7) : 6 ≤ n := by omega

@[expose] def s45 (hn : 6 ≤ n) : Perm (Fin n) := swap ⟨4, by omega⟩ ⟨5, by omega⟩

@[expose] def c123 (hn : 6 ≤ n) : alternatingGroup (Fin n) :=
  ⟨swap ⟨1, by omega⟩ ⟨3, by omega⟩ * swap ⟨1, by omega⟩ ⟨2, by omega⟩, by
    simp [mem_alternatingGroup, sign_swap', Fin.ext_iff]⟩

@[expose] def c045 (hn : 6 ≤ n) : alternatingGroup (Fin n) :=
  ⟨swap ⟨0, by omega⟩ ⟨5, by omega⟩ * swap ⟨0, by omega⟩ ⟨4, by omega⟩, by
    simp [mem_alternatingGroup, sign_swap', Fin.ext_iff]⟩

theorem small_facts (hn : n = 6 ∨ n = 7) :
    c123 (six_le_of hn) * c045 (six_le_of hn) = c045 (six_le_of hn) * c123 (six_le_of hn) ∧
      s45 (six_le_of hn) * (c123 (six_le_of hn) : Perm (Fin n)) * s45 (six_le_of hn) =
        c123 (six_le_of hn) ∧
      s45 (six_le_of hn) * (c045 (six_le_of hn) : Perm (Fin n)) * s45 (six_le_of hn) =
        ((c045 (six_le_of hn))⁻¹ : alternatingGroup (Fin n)) ∧
      c123 (six_le_of hn) ^ 3 = 1 ∧ c045 (six_le_of hn) ^ 3 = 1 ∧
      [1, c123 (six_le_of hn), c123 (six_le_of hn) ^ 2, c045 (six_le_of hn)].Nodup := by
  rcases hn with rfl | rfl <;> decide

theorem card_alternatingGroup_small (hn : n = 6 ∨ n = 7) :
    Nat.card (alternatingGroup (Fin n)) = 9 * (if n = 6 then 40 else 280) := by
  rcases hn with rfl | rfl <;>
    · rw [nat_card_alternatingGroup, Nat.card_fin]
      decide

theorem index_closure_c123_c045 (hn : n = 6 ∨ n = 7) :
    (closure {c123 (six_le_of hn), c045 (six_le_of hn)}).index =
      if n = 6 then 40 else 280 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcomm, -, -, ha3, hb3, hnodup⟩ := small_facts hn
  set a := c123 (six_le_of hn)
  set b := c045 (six_le_of hn)
  set E := closure ({a, b} : Set (alternatingGroup (Fin n)))
  have hpair : ({a, b} : Set (alternatingGroup (Fin n))).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hcomm
    · exact hcomm.symm
    · exact Commute.refl _
  have hE : IsMulCommutative E := isMulCommutative_closure hpair
  have hcube : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ha3
      · exact hb3
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y :=
        congrArg Subtype.val (hE.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hp : IsPGroup 3 E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hcube g g.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
  have h4 : 4 ≤ Nat.card E := by
    have hmem : ∀ x ∈ [1, a, a ^ 2, b], x ∈ E := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact one_mem E
      · exact subset_closure (Set.mem_insert _ _)
      · exact pow_mem (subset_closure (Set.mem_insert _ _)) 2
      · exact subset_closure (Set.mem_insert_of_mem _ rfl)
    have : Fintype E := Fintype.ofFinite E
    have h := List.Nodup.length_le_card (α := E)
      (l := [1, a, a ^ 2, b].pmap (fun x hx => (⟨x, hx⟩ : E)) hmem)
      (hnodup.pmap fun _ _ _ _ h => congrArg Subtype.val h)
    rw [Nat.card_eq_fintype_card]
    simpa using h
  have hdvd : Nat.card E ∣ 9 * (if n = 6 then 40 else 280) :=
    card_alternatingGroup_small hn ▸ E.card_subgroup_dvd_card
  have hk2 : k = 2 := by
    have hk1 : 2 ≤ k := by
      by_contra h
      push Not at h
      have h3 : 3 ^ k ≤ 3 := by
        calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 3 := pow_one 3
      omega
    have hk3 : k < 3 := by
      by_contra h
      push Not at h
      have h27 : 3 ^ 3 ∣ Nat.card E := hk ▸ pow_dvd_pow 3 h
      have h27' := h27.trans hdvd
      rcases hn with rfl | rfl <;> norm_num at h27'
    omega
  have hidx := E.card_mul_index
  rw [hk, hk2, card_alternatingGroup_small hn] at hidx
  rcases hn with rfl | rfl <;> norm_num at hidx ⊢ <;> omega

end Small

section Kernel

variable {P : Type} [Group P] [Finite P] {n : ℕ}

omit [Finite P] in
theorem card_ker_dvd_six (hP : commutator P = ⊤)
    (hn : n = 6 ∨ n = 7) {π : P →* alternatingGroup (Fin n)} (hπ : Function.Surjective π)
    (hK : π.ker ≤ center P) : Nat.card π.ker ∣ 6 := by
  have : Group.IsPerfect P := (Group.isPerfect_def).2 hP
  have h := Subgroup.card_map_dvd (hopfMultiplier (alternatingGroup (Fin n))) (hopfLift π hπ hK)
  rw [map_hopfMultiplier_hopfLift π hπ hK] at h
  rcases hn with rfl | rfl
  · rwa [hopfMultiplier_alternatingGroup_six.2] at h
  · rwa [hopfMultiplier_alternatingGroup_seven.2] at h

theorem card_ker_eq_one_of_commute (hP : commutator P = ⊤)
    (hn : n = 6 ∨ n = 7) {π : P →* alternatingGroup (Fin n)} (hπ : Function.Surjective π)
    (hK : π.ker ≤ center P) (hodd : Odd (Nat.card π.ker)) {w c : P}
    (hw : π w = c123 (six_le_of hn)) (hc : π c = c045 (six_le_of hn)) (hwc : Commute w c) :
    Nat.card π.ker = 1 := by
  have h6 := card_ker_dvd_six hP hn hπ hK
  have h3 : Nat.card π.ker ∣ 3 := by
    have hcop : Nat.Coprime (Nat.card π.ker) 2 := Nat.coprime_two_right.mpr hodd
    exact hcop.dvd_of_dvd_mul_left (show Nat.card π.ker ∣ 2 * 3 from h6)
  set H := closure (({w, c} : Set P) ∪ (π.ker : Set P)) with hH
  have hpair : (({w, c} : Set P) ∪ (π.ker : Set P)).Pairwise Commute := by
    intro x hx y hy _
    rcases hy with hy | hy
    · rcases hx with hx | hx
      · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact Commute.refl _
        · exact hwc
        · exact hwc.symm
        · exact Commute.refl _
      · exact (mem_center_iff.1 (hK hx) y).symm
    · exact mem_center_iff.1 (hK hy) x
  have : IsMulCommutative H := isMulCommutative_closure hpair
  have hmap : H.map π = closure {c123 (six_le_of hn), c045 (six_le_of hn)} := by
    rw [hH, MonoidHom.map_closure, Set.image_union, Set.image_pair, hw, hc]
    apply le_antisymm
    · rw [closure_le]
      rintro x (hx | ⟨z, hz, rfl⟩)
      · exact subset_closure hx
      · rw [SetLike.mem_coe, MonoidHom.mem_ker] at hz
        rw [hz]
        exact one_mem _
    · exact closure_mono Set.subset_union_left
  have hkerH : π.ker ≤ H := fun z hz => subset_closure (Set.mem_union_right _ hz)
  have hidx : H.index = if n = 6 then 40 else 280 := by
    rw [← comap_map_eq_self hkerH, index_comap_of_surjective _ hπ, hmap]
    exact index_closure_c123_c045 hn
  have hz1 : ∀ z ∈ π.ker, z = 1 := by
    intro z hz
    have hpow := pow_index_eq_one_of_isPerfect hP H (hK hz)
    have hz3 : z ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact (Subgroup.orderOf_dvd_natCard _ hz).trans h3
    rw [hidx] at hpow
    split_ifs at hpow
    · calc z = (z ^ 3) ^ 13 * z := by rw [hz3, one_pow, one_mul]
        _ = z ^ 40 := by rw [← pow_mul, ← pow_succ]
        _ = 1 := hpow
    · calc z = (z ^ 3) ^ 93 * z := by rw [hz3, one_pow, one_mul]
        _ = z ^ 280 := by rw [← pow_mul, ← pow_succ]
        _ = 1 := hpow
  have hbot : π.ker = ⊥ := eq_bot_iff.mpr fun z hz => (mem_bot).mpr (hz1 z hz)
  rw [hbot, Subgroup.card_bot]

theorem card_ker_eq_one_of_swap45 (hP : commutator P = ⊤)
    (hn : n = 6 ∨ n = 7) {π : P →* alternatingGroup (Fin n)} (hπ : Function.Surjective π)
    (hK : π.ker ≤ center P) (hodd : Odd (Nat.card π.ker)) (α : P →* P)
    (hαK : ∀ z ∈ π.ker, α z = z)
    (hα : ∀ x : P, ((π (α x) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      s45 (six_le_of hn) * (π x : Perm (Fin n)) * s45 (six_le_of hn)) :
    Nat.card π.ker = 1 := by
  obtain ⟨hcomm, ha, hb, -, -, -⟩ := small_facts hn
  obtain ⟨w, hw⟩ := hπ (c123 (six_le_of hn))
  obtain ⟨c, hc⟩ := hπ (c045 (six_le_of hn))
  refine card_ker_eq_one_of_commute hP hn hπ hK hodd hw hc
    (commute_of_inverts hK hodd α hαK (by rw [hw, hc]; exact hcomm) ?_ ?_)
  · apply Subtype.ext
    rw [hα, hw]
    exact ha
  · apply Subtype.ext
    rw [hα, hc]
    exact hb

end Kernel

end CFSG.ComponentClassification.RankTwoAlt.Three
