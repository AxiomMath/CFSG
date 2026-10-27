module

public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

section QuatFacts

open QuaternionGroup

variable {N : ℕ}

theorem qp_two_mul_natCast : ((N : ZMod (2 * N)) + (N : ZMod (2 * N))) = 0 := by
  have : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := ZMod.natCast_self _
  rw [Nat.cast_mul, Nat.cast_ofNat] at this
  linear_combination this

theorem qp_inv_a (i : ZMod (2 * N)) : (a i : QuaternionGroup N)⁻¹ = a (-i) := by
  apply inv_eq_of_mul_eq_one_right
  rw [a_mul_a, add_neg_cancel, one_def]

theorem qp_inv_xa (i : ZMod (2 * N)) : (xa i : QuaternionGroup N)⁻¹ = xa ((N : ZMod (2 * N)) + i) := by
  apply inv_eq_of_mul_eq_one_right
  rw [xa_mul_xa, one_def]
  congr 1
  linear_combination qp_two_mul_natCast (N := N)

variable [NeZero N]

theorem qp_zmod_add_self_eq_zero {i : ZMod (2 * N)} (h : i + i = 0) : i = 0 ∨ i = (N : ZMod (2 * N)) := by
  have h1 : ((2 * i.val : ℕ) : ZMod (2 * N)) = 0 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    linear_combination h
  have h2 : 2 * N ∣ 2 * i.val := (ZMod.natCast_eq_zero_iff _ _).1 h1
  have h3 : N ∣ i.val := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  obtain ⟨c, hc⟩ := h3
  have hlt : i.val < 2 * N := ZMod.val_lt i
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc2 : c < 2 := by
    by_contra hcc
    have : N * 2 ≤ N * c := Nat.mul_le_mul_left N (by omega)
    omega
  interval_cases c
  · left
    have : i.val = 0 := by omega
    exact (ZMod.val_eq_zero i).1 this
  · right
    have h4 : i.val = N := by omega
    calc i = ((i.val : ℕ) : ZMod (2 * N)) := (ZMod.natCast_zmod_val i).symm
      _ = (N : ZMod (2 * N)) := by rw [h4]

theorem qp_natCast_ne_zero : (N : ZMod (2 * N)) ≠ 0 := by
  intro h
  have h2 : 2 * N ∣ N := (ZMod.natCast_eq_zero_iff _ _).1 h
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have := Nat.le_of_dvd hNpos h2
  omega

theorem qp_sq_eq_one {g : QuaternionGroup N} (hg : g * g = 1) :
    g = 1 ∨ g = a (N : ZMod (2 * N)) := by
  cases g with
  | a i =>
    rw [a_mul_a, one_def] at hg
    have hi : i + i = 0 := a.inj hg
    rcases qp_zmod_add_self_eq_zero hi with h | h
    · left; rw [one_def, h]
    · right; rw [h]
  | xa i =>
    exfalso
    rw [xa_mul_xa, one_def] at hg
    have h1 : (N : ZMod (2 * N)) + i - i = 0 := a.inj hg
    have h2 : (N : ZMod (2 * N)) = 0 := by simpa using h1
    exact qp_natCast_ne_zero h2

omit [NeZero N] in
theorem qp_central_sq : (a (N : ZMod (2 * N)) : QuaternionGroup N) * a (N : ZMod (2 * N)) = 1 := by
  rw [a_mul_a, one_def, qp_two_mul_natCast]

theorem qp_central_ne_one : (a (N : ZMod (2 * N)) : QuaternionGroup N) ≠ 1 := by
  intro h
  rw [one_def] at h
  exact qp_natCast_ne_zero (a.inj h)

omit [NeZero N] in
theorem qp_exists_inverting (hN : 2 ∣ N) {g : QuaternionGroup N} (hg : g * g = a (N : ZMod (2 * N))) :
    ∃ y : QuaternionGroup N, y * g * y⁻¹ = g⁻¹ ∧ y * y = a (N : ZMod (2 * N)) := by
  obtain ⟨m, hm⟩ := hN
  have hmm : (m : ZMod (2 * N)) + (m : ZMod (2 * N)) = (N : ZMod (2 * N)) := by
    have : ((m + m : ℕ) : ZMod (2 * N)) = (N : ZMod (2 * N)) := by
      congr 1; omega
    simpa using this
  cases g with
  | a i =>
    refine ⟨xa 0, ?_, ?_⟩
    · rw [qp_inv_a, qp_inv_xa, xa_mul_a, xa_mul_xa]
      congr 1
      linear_combination qp_two_mul_natCast (N := N)
    · rw [xa_mul_xa]; simp
  | xa j =>
    refine ⟨a (m : ZMod (2 * N)), ?_, ?_⟩
    · rw [qp_inv_xa, qp_inv_a, a_mul_xa, xa_mul_a]
      congr 1
      linear_combination (-1 : ZMod (2 * N)) * hmm + (-1 : ZMod (2 * N)) * qp_two_mul_natCast (N := N)
    · rw [a_mul_a, hmm]

end QuatFacts

section Transport

variable {X : Type} [Group X]

theorem qp_sub_facts {A : Subgroup X} {N : ℕ} [NeZero N] (hN : 2 ∣ N) (φ : ↥A ≃* QuaternionGroup N) :
    ∃ c ∈ A, c * c = 1 ∧ c ≠ 1 ∧ (∀ g ∈ A, g * g = 1 → g = 1 ∨ g = c) ∧
      ∀ g ∈ A, g * g = c → ∃ y ∈ A, y * g * y⁻¹ = g⁻¹ ∧ y * y = c := by
  set c' : ↥A := φ.symm (QuaternionGroup.a (N : ZMod (2 * N))) with hc'
  have hφc' : φ c' = QuaternionGroup.a (N : ZMod (2 * N)) := by rw [hc']; simp
  refine ⟨(c' : X), c'.2, ?_, ?_, ?_, ?_⟩
  · have h1 : c' * c' = 1 := by
      apply φ.injective
      rw [map_mul, hφc', qp_central_sq, map_one]
    simpa using congrArg Subtype.val h1
  · intro h
    have h1 : c' = 1 := Subtype.ext h
    have h2 : φ c' = 1 := by rw [h1, map_one]
    rw [hφc'] at h2
    exact qp_central_ne_one h2
  · intro g hg hgg
    have h1 : (⟨g, hg⟩ : ↥A) * ⟨g, hg⟩ = 1 := Subtype.ext hgg
    have h2 : φ ⟨g, hg⟩ * φ ⟨g, hg⟩ = 1 := by rw [← map_mul, h1, map_one]
    rcases qp_sq_eq_one h2 with h3 | h3
    · left
      have : (⟨g, hg⟩ : ↥A) = 1 := φ.injective (by rw [h3, map_one])
      simpa using congrArg Subtype.val this
    · right
      have : (⟨g, hg⟩ : ↥A) = c' := φ.injective (by rw [h3, hφc'])
      simpa using congrArg Subtype.val this
  · intro g hg hgg
    have h1 : (⟨g, hg⟩ : ↥A) * ⟨g, hg⟩ = c' := Subtype.ext hgg
    have h2 : φ ⟨g, hg⟩ * φ ⟨g, hg⟩ = QuaternionGroup.a (N : ZMod (2 * N)) := by
      rw [← map_mul, h1, hφc']
    obtain ⟨y', hy1, hy2⟩ := qp_exists_inverting hN h2
    refine ⟨((φ.symm y' : ↥A) : X), (φ.symm y').2, ?_, ?_⟩
    · have h3 : φ.symm y' * ⟨g, hg⟩ * (φ.symm y')⁻¹ = (⟨g, hg⟩ : ↥A)⁻¹ := by
        apply φ.injective
        rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, hy1]
      simpa using congrArg Subtype.val h3
    · have h3 : φ.symm y' * φ.symm y' = c' := by
        apply φ.injective
        rw [map_mul, MulEquiv.apply_symm_apply, hy2, hφc']
      simpa using congrArg Subtype.val h3

theorem qp_exists_mul_of_mem_sup {A B : Subgroup X}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : X} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup X :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        rw [mul_assoc, ← mul_assoc b, ← hAB a' ha' b hb]
        group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by rw [mul_one]⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by rw [mul_one]⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by rw [one_mul]⟩)
  exact hle hx

theorem qp_sq_eq_one_of_comm_inverting {a y : X} (hya : y * a = a * y) (hyinv : y * a * y⁻¹ = a⁻¹) :
    a * a = 1 := by
  have h1 : a = a⁻¹ := by
    rw [← hyinv, hya]; group
  calc a * a = a * a⁻¹ := congrArg (a * ·) h1
    _ = 1 := mul_inv_cancel a

theorem qp_prod_sq_cases {A B : Subgroup X} {c : X}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAB : ∀ x ∈ A ⊓ B, x = 1 ∨ x = c) (hA1 : ∀ g ∈ A, g * g = 1 → g = 1 ∨ g = c)
    (hB1 : ∀ g ∈ B, g * g = 1 → g = 1 ∨ g = c) (hc2 : c * c = 1)
    {a b : X} (ha : a ∈ A) (hb : b ∈ B) (h : (a * b) * (a * b) = 1) :
    ((a = 1 ∨ a = c) ∧ (b = 1 ∨ b = c)) ∨ (a * a = c ∧ b * b = c) := by
  have h1 : a * a * (b * b) = 1 := by
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcomm a ha b hb]
      _ = (a * b) * (a * b) := by group
      _ = 1 := h
  have h2 : a * a ∈ B := by
    have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]; exact inv_mem (mul_mem hb hb)
  have h3 : a * a ∈ A ⊓ B := Subgroup.mem_inf.2 ⟨mul_mem ha ha, h2⟩
  rcases hAB _ h3 with h4 | h4
  · left
    have h5 : b * b = 1 := by rw [h4, one_mul] at h1; exact h1
    exact ⟨hA1 a ha h4, hB1 b hb h5⟩
  · right
    refine ⟨h4, ?_⟩
    rw [h4] at h1
    have : b * b = c⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact inv_eq_of_mul_eq_one_right hc2

theorem exists_involution_comm_U_of_quatProd {X : Type} [Group X] {A B R : Subgroup X}
    (hR : IsCentralProd A B R) {n : ℕ} (hA : IVK.IsQuaternionTwoGroup ↥A n)
    (hB : IVK.IsQuaternionTwoGroup ↥B n)
    {U : Subgroup X} (hUR : U ≤ R) (hU4 : IVK.IsFourSubgroup U)
    {z t : X} (hzU : z ∈ U) (htU : t ∈ U) (hz1 : z ≠ 1) (hzR : ∀ r ∈ R, r * z = z * r)
    (htz : t ≠ z) (ht1 : t ≠ 1) :
    ∃ y ∈ R, y * y = 1 ∧ y ∉ U ∧ ∀ u ∈ U, y * u = u * y := by
  classical
  obtain ⟨hAB, hcomm, hcard⟩ := hR
  obtain ⟨hn3, ⟨φA⟩⟩ := hA
  obtain ⟨-, ⟨φB⟩⟩ := hB
  have : NeZero (2 ^ (n - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have h2dvd : 2 ∣ 2 ^ (n - 2) := dvd_pow_self 2 (by omega)
  obtain ⟨cA, hcA, hcA2, hcA1, hA1, hA3⟩ := qp_sub_facts h2dvd φA
  obtain ⟨cB, hcB, hcB2, hcB1, hB1, hB3⟩ := qp_sub_facts h2dvd φB
  have hAR : A ≤ R := hAB ▸ le_sup_left
  have hBR : B ≤ R := hAB ▸ le_sup_right
  have hsqAB : ∀ x ∈ A ⊓ B, x * x = 1 := by
    intro x hx
    have h1 : orderOf (⟨x, hx⟩ : ↥(A ⊓ B)) ∣ 2 := by
      have h0 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(A ⊓ B))
      rwa [hcard] at h0
    have h2 : (⟨x, hx⟩ : ↥(A ⊓ B)) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
    simpa [pow_two] using congrArg Subtype.val h2
  obtain ⟨x0, hx0, hx01⟩ : ∃ x ∈ A ⊓ B, x ≠ 1 := by
    have : Finite ↥(A ⊓ B) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
    have : Nontrivial ↥(A ⊓ B) := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; omega)
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(A ⊓ B))
    exact ⟨x.1, x.2, fun h => hx (Subtype.ext h)⟩
  have hx0A : x0 ∈ A := (Subgroup.mem_inf.1 hx0).1
  have hx0B : x0 ∈ B := (Subgroup.mem_inf.1 hx0).2
  have hxA : x0 = cA := (hA1 x0 hx0A (hsqAB x0 hx0)).resolve_left hx01
  have hxB : x0 = cB := (hB1 x0 hx0B (hsqAB x0 hx0)).resolve_left hx01
  have hcc : cB = cA := hxB.symm.trans hxA
  have hcAB' : cA ∈ B := hcc ▸ hcB
  have hcAB : cA ∈ A ⊓ B := Subgroup.mem_inf.2 ⟨hcA, hcAB'⟩
  have hB1' : ∀ g ∈ B, g * g = 1 → g = 1 ∨ g = cA := by
    intro g hg h
    rcases hB1 g hg h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans hcc)
  have hB3' : ∀ g ∈ B, g * g = cA → ∃ y ∈ B, y * g * y⁻¹ = g⁻¹ ∧ y * y = cA := by
    intro g hg h
    obtain ⟨y, hy, h1, h2⟩ := hB3 g hg (h.trans hcc.symm)
    exact ⟨y, hy, h1, h2.trans hcc⟩
  have hABc : ∀ x ∈ A ⊓ B, x = 1 ∨ x = cA :=
    fun x hx => hA1 x (Subgroup.mem_inf.1 hx).1 (hsqAB x hx)
  have := hU4.1
  have hUsq : ∀ u ∈ U, u * u = 1 := by
    intro u hu
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) u hu
    simpa [pow_two] using this
  have hzz : z * z = 1 := hUsq z hzU
  have htt : t * t = 1 := hUsq t htU
  have hUdescr : ∀ u ∈ U, u = 1 ∨ u = z ∨ u = t ∨ u = z * t := by
    intro u hu
    have : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hU4.2]; omega)
    have := Fintype.ofFinite ↥U
    have hc4 : Fintype.card ↥U = 4 := by rw [← Nat.card_eq_fintype_card]; exact hU4.2
    have hztU : z * t ∈ U := mul_mem hzU htU
    have hzt1 : z * t ≠ 1 := by
      intro h
      apply htz
      calc t = z⁻¹ * (z * t) := by group
        _ = z⁻¹ := by rw [h, mul_one]
        _ = z := inv_eq_of_mul_eq_one_right hzz
    have hztz : z * t ≠ z := by
      intro h
      exact ht1 (mul_left_cancel (a := z) (h.trans (mul_one z).symm))
    have hztt : z * t ≠ t := by
      intro h
      exact hz1 (mul_right_cancel (b := t) (h.trans (one_mul t).symm))
    have n1 : (1 : ↥U) ∉ ({⟨z, hzU⟩, ⟨t, htU⟩, ⟨z * t, hztU⟩} : Finset ↥U) := by
      simp [Subtype.ext_iff, hz1.symm, ht1.symm, hzt1.symm]
    have n2 : (⟨z, hzU⟩ : ↥U) ∉ ({⟨t, htU⟩, ⟨z * t, hztU⟩} : Finset ↥U) := by
      simp [Subtype.ext_iff, htz.symm, hztz.symm]
    have n3 : (⟨t, htU⟩ : ↥U) ∉ ({⟨z * t, hztU⟩} : Finset ↥U) := by
      simp [Subtype.ext_iff, hztt.symm]
    let S4 : Finset ↥U := {1, ⟨z, hzU⟩, ⟨t, htU⟩, ⟨z * t, hztU⟩}
    have hS4 : S4.card = 4 := by
      simp only [S4]
      rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
        Finset.card_insert_of_notMem n3, Finset.card_singleton]
    have hS : S4 = Finset.univ := Finset.eq_univ_of_card S4 (by rw [hS4, hc4])
    have hmem : (⟨u, hu⟩ : ↥U) ∈ S4 := by rw [hS]; exact Finset.mem_univ _
    simp only [S4, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] at hmem
    simpa using hmem
  have hzcA : z = cA := by
    obtain ⟨a', ha', b', hb', hzab⟩ := qp_exists_mul_of_mem_sup hcomm (hAB ▸ hUR hzU)
    have hzab2 : (a' * b') * (a' * b') = 1 := by rw [← hzab]; exact hzz
    rcases qp_prod_sq_cases hcomm hABc hA1 hB1' hcA2 ha' hb' hzab2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (show z = 1 by rw [hzab, h1, h2, one_mul]) hz1
      · rw [hzab, h1, h2, one_mul]
      · rw [hzab, h1, h2, mul_one]
      · exact absurd (show z = 1 by rw [hzab, h1, h2]; exact hcA2) hz1
    · exfalso
      obtain ⟨y, hy, hyinv, -⟩ := hA3 a' ha' h1
      have hya : y * a' = a' * y := by
        have h5 : y * (a' * b') = (a' * b') * y := by rw [← hzab]; exact hzR y (hAR hy)
        have h6 : (y * a') * b' = (a' * y) * b' := by
          calc (y * a') * b' = y * (a' * b') := by group
            _ = (a' * b') * y := h5
            _ = a' * (b' * y) := by group
            _ = a' * (y * b') := by rw [hcomm y hy b' hb']
            _ = (a' * y) * b' := by group
        exact mul_right_cancel h6
      exact hcA1 (h1.symm.trans (qp_sq_eq_one_of_comm_inverting hya hyinv))
  obtain ⟨a, ha, b, hb, htab⟩ := qp_exists_mul_of_mem_sup hcomm (hAB ▸ hUR htU)
  have htab2 : (a * b) * (a * b) = 1 := by rw [← htab]; exact htt
  rcases qp_prod_sq_cases hcomm hABc hA1 hB1' hcA2 ha hb htab2 with ⟨h1, h2⟩ | ⟨haa, hbb⟩
  · exfalso
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact ht1 (by rw [htab, h1, h2, one_mul])
    · exact htz (by rw [htab, h1, h2, one_mul, hzcA])
    · exact htz (by rw [htab, h1, h2, mul_one, hzcA])
    · exact ht1 (by rw [htab, h1, h2]; exact hcA2)
  · obtain ⟨y, hy, hyinv, hyy⟩ := hA3 a ha haa
    obtain ⟨y', hy', hy'inv, hy'y'⟩ := hB3' b hb hbb
    have hyy' : y * y' = y' * y := hcomm y hy y' hy'
    have hyα : ∀ α ∈ A, ∀ β ∈ B, y * y' = α * β → y = α ∨ y = α * cA := by
      intro α hα β hβ h
      have e : α⁻¹ * y = β * y'⁻¹ := by
        calc α⁻¹ * y = α⁻¹ * (y * y') * y'⁻¹ := by group
          _ = α⁻¹ * (α * β) * y'⁻¹ := by rw [h]
          _ = β * y'⁻¹ := by group
      have hm : α⁻¹ * y ∈ A ⊓ B :=
        Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hα) hy, e ▸ mul_mem hβ (inv_mem hy')⟩
      rcases hABc _ hm with h1 | h1
      · left
        calc y = α * (α⁻¹ * y) := by group
          _ = α := by rw [h1, mul_one]
      · right
        calc y = α * (α⁻¹ * y) := by group
          _ = α * cA := by rw [h1]
    have hysq : y ∉ A ⊓ B := by
      intro hm
      exact hcA1 (hyy.symm.trans (hsqAB y hm))
    have hcen : ∀ y₁, (y₁ = a ∨ y₁ = a * cA ∨ y₁ = cA * a ∨ y₁ = cA * a * cA) →
        y₁ * a = a * y₁ := by
      intro y₁ h
      have hca : cA ∈ Subgroup.centralizer ({a} : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact hcomm a ha cA hcAB'
      have haa' : a ∈ Subgroup.centralizer ({a} : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
      have hy₁ : y₁ ∈ Subgroup.centralizer ({a} : Set X) := by
        rcases h with h | h | h | h <;> rw [h]
        · exact haa'
        · exact mul_mem haa' hca
        · exact mul_mem hca haa'
        · exact mul_mem (mul_mem hca haa') hca
      have := Subgroup.mem_centralizer_iff.1 hy₁ a (Set.mem_singleton a)
      exact this.symm
    have hya : y * a = a⁻¹ * y := by
      have := hyinv
      rwa [mul_inv_eq_iff_eq_mul] at this
    have hy'b : y' * b = b⁻¹ * y' := by
      have := hy'inv
      rwa [mul_inv_eq_iff_eq_mul] at this
    refine ⟨y * y', ?_, ?_, ?_, ?_⟩
    · rw [← hAB]; exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hy')
    · calc y * y' * (y * y') = y * (y' * y) * y' := by group
        _ = y * (y * y') * y' := by rw [← hyy']
        _ = (y * y) * (y' * y') := by group
        _ = 1 := by rw [hyy, hy'y']; exact hcA2
    · intro hU
      rcases hUdescr _ hU with h | h | h | h
      ·
        have hyB : y ∈ B := by
          have : y = y'⁻¹ := eq_inv_of_mul_eq_one_left h
          rw [this]; exact inv_mem hy'
        exact hysq (Subgroup.mem_inf.2 ⟨hy, hyB⟩)
      ·
        rw [hzcA] at h
        have hyB : y ∈ B := by
          have : y = cA * y'⁻¹ := by
            calc y = (y * y') * y'⁻¹ := by group
              _ = cA * y'⁻¹ := by rw [h]
          rw [this]; exact mul_mem hcAB' (inv_mem hy')
        exact hysq (Subgroup.mem_inf.2 ⟨hy, hyB⟩)
      ·
        rcases hyα a ha b hb (h.trans htab) with h1 | h1
        · exact hcA1 (haa.symm.trans (qp_sq_eq_one_of_comm_inverting
            (hcen y (Or.inl h1)) hyinv))
        · exact hcA1 (haa.symm.trans (qp_sq_eq_one_of_comm_inverting
            (hcen y (Or.inr (Or.inl h1))) hyinv))
      ·
        rw [hzcA, htab] at h
        have h' : y * y' = (cA * a) * b := by rw [h]; group
        rcases hyα (cA * a) (mul_mem hcA ha) b hb h' with h1 | h1
        · exact hcA1 (haa.symm.trans (qp_sq_eq_one_of_comm_inverting
            (hcen y (Or.inr (Or.inr (Or.inl h1)))) hyinv))
        · exact hcA1 (haa.symm.trans (qp_sq_eq_one_of_comm_inverting
            (hcen y (Or.inr (Or.inr (Or.inr h1)))) hyinv))
    · have hinvab : a⁻¹ * b⁻¹ = a * b := by
        have h1 : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
          rw [mul_inv_rev]; exact hcomm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
        rw [h1]; exact inv_eq_of_mul_eq_one_right htab2
      have hyt : (y * y') * t = t * (y * y') := by
        rw [htab]
        calc y * y' * (a * b) = y * (y' * a) * b := by group
          _ = y * (a * y') * b := by rw [← hcomm a ha y' hy']
          _ = (y * a) * (y' * b) := by group
          _ = (a⁻¹ * y) * (b⁻¹ * y') := by rw [hya, hy'b]
          _ = a⁻¹ * (y * b⁻¹) * y' := by group
          _ = a⁻¹ * (b⁻¹ * y) * y' := by rw [hcomm y hy b⁻¹ (inv_mem hb)]
          _ = (a⁻¹ * b⁻¹) * (y * y') := by group
          _ = (a * b) * (y * y') := by rw [hinvab]
      have hyz : (y * y') * z = z * (y * y') :=
        hzR (y * y') (by rw [← hAB]; exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hy'))
      intro u hu
      rcases hUdescr u hu with h | h | h | h
      · rw [h]; simp
      · rw [h]; exact hyz
      · rw [h]; exact hyt
      · rw [h]
        calc y * y' * (z * t) = (y * y' * z) * t := by group
          _ = (z * (y * y')) * t := by rw [hyz]
          _ = z * ((y * y') * t) := by group
          _ = z * (t * (y * y')) := by rw [hyt]
          _ = z * t * (y * y') := by group

end Transport

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
