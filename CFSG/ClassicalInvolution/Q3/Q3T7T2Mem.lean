module

public import CFSG.ClassicalInvolution.Q3.Q3T7T2Grp
public import CFSG.ClassicalInvolution.Uniform.USylow

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7T2

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups

theorem natCard_sl2Three_aux : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem sl2Three_pow_four_of_two_pow {g : SL(2, ZMod 3)} {k : ℕ} (h : g ^ (2 ^ k) = 1) :
    g ^ 4 = 1 := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf g ∣ 24 := by
    rw [← natCard_sl2Three_aux]
    exact orderOf_dvd_natCard g
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj3 : j ≤ 3 := by
    by_contra hcon
    have h16 : 2 ^ 4 ∣ orderOf g := by
      rw [hj]
      exact pow_dvd_pow 2 (by omega)
    have := h16.trans h2
    norm_num at this
  apply sl2Three_pow_eight
  have : orderOf g ∣ 8 := by
    rw [hj]
    exact (pow_dvd_pow 2 hj3 : 2 ^ j ∣ 2 ^ 3)
  exact orderOf_dvd_iff_pow_eq_one.mp this

section Proj

variable {G : Type} [Group G] [Finite G]

theorem exists_proj {J : Subgroup G}
    (e : ↥J ⧸ classicalInvolutionOddCore ↥J ≃* SL(2, ZMod 3)) :
    ∃ π : ↥J →* SL(2, ZMod 3), Function.Surjective π ∧
      ∀ j, π j = 1 → j ∈ classicalInvolutionOddCore ↥J := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun j hj => ?_⟩
  have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥J) j = 1 := by
    apply e.injective
    simpa using hj
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem odd_closure_of_proj {J : Subgroup G} (π : ↥J →* SL(2, ZMod 3))
    (hsurj : Function.Surjective π) (hker : ∀ j, π j = 1 → j ∈ classicalInvolutionOddCore ↥J) :
    Subgroup.closure {x : G | x ∈ J ∧ Odd (orderOf x)} = J := by
  have hMJ : Subgroup.closure {x : G | x ∈ J ∧ Odd (orderOf x)} ≤ J :=
    (Subgroup.closure_le J).mpr fun x hx => hx.1
  refine le_antisymm hMJ ?_
  set M' : Subgroup ↥J := (Subgroup.closure {x : G | x ∈ J ∧ Odd (orderOf x)}).subgroupOf J
    with hM'
  have hodd : ∀ j : ↥J, Odd (orderOf j) → j ∈ M' := by
    intro j hj
    rw [hM', Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨j.2, by rwa [Subgroup.orderOf_coe]⟩
  have hO : classicalInvolutionOddCore ↥J ≤ M' := by
    intro j hj
    apply hodd
    have hdvd : orderOf j ∣ Nat.card (classicalInvolutionOddCore ↥J) :=
      Subgroup.orderOf_dvd_natCard _ hj
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥J).of_dvd_nat hdvd
  have hmod : ∀ k : ℕ, 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    intro k
    induction k with
    | zero => left; norm_num
    | succ k ih =>
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [this]
      generalize 2 ^ k = t at ih ⊢
      omega
  have h3 : ∀ a : SL(2, ZMod 3), a ^ 3 = 1 → ∃ m ∈ M', π m = a := by
    intro a ha
    obtain ⟨j₀, rfl⟩ := hsurj a
    obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos j₀).ne'
    have hdvd : 2 ^ k ∣ orderOf j₀ := ⟨m, hn⟩
    have hord : orderOf (j₀ ^ (2 ^ k)) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hn]
      exact Nat.mul_div_cancel_left m (by positivity)
    have hj1 : j₀ ^ (2 ^ k) ∈ M' := hodd _ (hord ▸ hm)
    have himg : π (j₀ ^ (2 ^ k)) = (π j₀) ^ (2 ^ k % 3) := by
      rw [map_pow]
      exact pow_eq_pow_mod _ ha
    rcases hmod k with h1 | h1
    · exact ⟨_, hj1, by rw [himg, h1, pow_one]⟩
    · refine ⟨(j₀ ^ (2 ^ k))⁻¹, M'.inv_mem hj1, ?_⟩
      have hsq : π j₀ ^ 2 = (π j₀)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ]
        exact ha
      rw [map_inv, himg, h1, hsq, inv_inv]
  have hgen' : ∀ g : SL(2, ZMod 3), ∃ m ∈ M', π m = g := by
    intro g
    obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := sl2Three_gen g
    obtain ⟨ma, hma, rfl⟩ := h3 a ha
    obtain ⟨mb, hmb, rfl⟩ := h3 b hb
    obtain ⟨mc, hmc, rfl⟩ := h3 c hc
    exact ⟨ma * mb * mc, M'.mul_mem (M'.mul_mem hma hmb) hmc, by simp⟩
  have htop : ∀ j : ↥J, j ∈ M' := by
    intro j
    obtain ⟨m, hm, hmπ⟩ := hgen' (π j)
    have h1 : m⁻¹ * j ∈ classicalInvolutionOddCore ↥J :=
      hker _ (by rw [map_mul, map_inv, hmπ, inv_mul_cancel])
    have := M'.mul_mem hm (hO h1)
    simpa using this
  intro x hx
  have := htop ⟨x, hx⟩
  rwa [hM', Subgroup.mem_subgroupOf] at this

theorem eight_le_card_of_proj {J D : Subgroup G} {w : G} (π : ↥J →* SL(2, ZMod 3))
    (hsurj : Function.Surjective π) (hker : ∀ j, π j = 1 → j ∈ classicalInvolutionOddCore ↥J)
    (hDJ : D ≤ J) (hD2 : IsPGroup 2 D) (hDn : ∀ j ∈ J, ∀ d ∈ D, j * d * j⁻¹ ∈ D)
    (hwD : w ∈ D) (hw1 : w ≠ 1) (hww : w * w = 1) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1)
    (hdw : d ≠ w) : 8 ≤ Nat.card D := by
  set D' : Subgroup ↥J := D.subgroupOf J with hD'
  have hD'2 : IsPGroup 2 D' := hD2.comap_subtype
  have hD'n : ∀ j : ↥J, ∀ x ∈ D', j * x * j⁻¹ ∈ D' := by
    intro j x hx
    rw [hD', Subgroup.mem_subgroupOf] at hx ⊢
    exact hDn j j.2 x hx
  have hinj : ∀ a ∈ D', ∀ b ∈ D', π a = π b → a = b := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ D' := D'.mul_mem (D'.inv_mem ha) hb
    have h1 : π (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    obtain ⟨k, hk⟩ := hD'2.exists_orderOf_eq_pow ⟨a⁻¹ * b, hmem⟩
    rw [Subgroup.orderOf_mk] at hk
    exact inv_mul_eq_one.mp (eq_one_of_mem_odd_of_orderOf_eq_two_pow
      (CFSG.ComponentClassification.OddCore.odd_card ↥J) (hker _ h1) hk)
  have hd'D : (⟨d, hDJ hd⟩ : ↥J) ∈ D' := by
    rw [hD', Subgroup.mem_subgroupOf]
    exact hd
  have hw'D : (⟨w, hDJ hwD⟩ : ↥J) ∈ D' := by
    rw [hD', Subgroup.mem_subgroupOf]
    exact hwD
  set d' : ↥J := ⟨d, hDJ hd⟩ with hd'def
  set w' : ↥J := ⟨w, hDJ hwD⟩ with hw'def
  have hg1 : π d' ≠ 1 := by
    intro h
    have : d' = 1 := hinj d' hd'D 1 D'.one_mem (by rw [h, map_one])
    exact hd1 (congrArg Subtype.val this)
  have hgm1 : π d' ≠ -1 := by
    intro h
    have hw2 : π w' * π w' = 1 := by
      rw [← map_mul]
      have : w' * w' = 1 := Subtype.ext hww
      rw [this, map_one]
    rcases sl2Three_sq _ hw2 with h1 | h1
    · have : w' = 1 := hinj w' hw'D 1 D'.one_mem (by rw [h1, map_one])
      exact hw1 (congrArg Subtype.val this)
    · have : d' = w' := hinj d' hd'D w' hw'D (by rw [h, h1])
      exact hdw (congrArg Subtype.val this)
  have hg4 : π d' ^ 4 = 1 := by
    obtain ⟨k, hk⟩ := hD'2.exists_orderOf_eq_pow ⟨d', hd'D⟩
    rw [Subgroup.orderOf_mk] at hk
    apply sl2Three_pow_four_of_two_pow (k := k)
    rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
  have hQ : ∀ h : SL(2, ZMod 3), h ^ 4 = 1 → ∃ m ∈ D', π m = h := by
    intro h hh
    rcases sl2Three_q8 (π d') h hg4 hg1 hgm1 hh with rfl | rfl | ⟨x, rfl⟩
    · exact ⟨1, D'.one_mem, map_one π⟩
    · exact ⟨d' * d', D'.mul_mem hd'D hd'D, by rw [map_mul]⟩
    · obtain ⟨x', rfl⟩ := hsurj x
      exact ⟨x' * d' * x'⁻¹, hD'n x' d' hd'D, by rw [map_mul, map_mul, map_inv]⟩
  have hQcard : Nat.card {h : SL(2, ZMod 3) // h ^ 4 = 1} = 8 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  choose f hfD hfπ using fun h : {h : SL(2, ZMod 3) // h ^ 4 = 1} => hQ h.1 h.2
  have hf_inj : Function.Injective (fun h => (⟨f h, hfD h⟩ : ↥D')) := by
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun x : ↥D' => π (x : ↥J)) hab
    simpa [hfπ] using this
  have h1 := Nat.card_le_card_of_injective _ hf_inj
  have h2 : Nat.card ↥D' = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDJ).toEquiv
  rw [hQcard, h2] at h1
  exact h1

theorem isSylow2In_of_eight_le {J D : Subgroup G}
    (e : ↥J ⧸ classicalInvolutionOddCore ↥J ≃* SL(2, ZMod 3)) (hDJ : D ≤ J)
    (hD2 : IsPGroup 2 D) (h8 : 8 ≤ Nat.card D) : IsSylow2In D J := by
  obtain ⟨V, hV⟩ := exists_isSylow2In J
  have hVcard : Nat.card V = 8 := by
    rw [natCard_isSylow2In_eq hV, Nat.card_congr e.toEquiv, natCard_sl2Three_aux]
    have : (Nat.factorization 24) 2 = 3 := by decide +kernel
    rw [this]
    norm_num
  exact hV.of_natCard_le hD2 hDJ (by omega)

theorem dichotomy {J D : Subgroup G} {w : G}
    (e : ↥J ⧸ classicalInvolutionOddCore ↥J ≃* SL(2, ZMod 3)) (hw : IsUniqueInvolution J w)
    (hDJ : D ≤ J) (hD2 : IsPGroup 2 D) (hDn : ∀ j ∈ J, ∀ d ∈ D, j * d * j⁻¹ ∈ D)
    (hwD : w ∈ D) : (∀ d ∈ D, d = 1 ∨ d = w) ∨ IsSylow2In D J := by
  by_cases h : ∀ d ∈ D, d = 1 ∨ d = w
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨d, hd, hd1, hdw⟩ := h
    obtain ⟨π, hsurj, hker⟩ := exists_proj e
    exact isSylow2In_of_eight_le e hDJ hD2
      (eight_le_card_of_proj π hsurj hker hDJ hD2 hDn hwD hw.ne_one hw.sq hd hd1 hdw)

end Proj

end CFSG.ClassicalInvolution.Q3.Q3T7T2
