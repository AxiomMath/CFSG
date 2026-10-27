module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.GorensteinWalter

theorem eq_one_of_mul_self_of_odd {G : Type*} [Group G] {y : G} (hyy : y * y = 1)
    (hodd : Odd (orderOf y)) : y = 1 := by
  have h2 : y ^ 2 = 1 := by rw [pow_two]; exact hyy
  have h := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem inverts_of_mem_sup_not_mem {G : Type*} [Group G] {U : Subgroup G} {w x : G}
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hww : w * w = 1)
    (hwinv : ∀ y ∈ U, w * y * w⁻¹ = y⁻¹) (hx : x ∈ U ⊔ Subgroup.zpowers w) (hxU : x ∉ U) :
    x * x = 1 ∧ ∀ y ∈ U, x * y * x⁻¹ = y⁻¹ := by
  have hwN : w ∈ Subgroup.normalizer (U : Set G) :=
    zpowers_le_normalizer_of_inverting hww hwinv (Subgroup.mem_zpowers w)
  rw [sup_comm, mem_zpowers_sup_iff hwN (by rw [pow_two]; exact hww)] at hx
  obtain ⟨l, hl, rfl | rfl⟩ := hx
  · exact absurd hl hxU
  · constructor
    · calc w * l * (w * l) = w * l * w⁻¹ * (w * w) * l := by group
        _ = 1 := by rw [hwinv l hl, hww]; group
    · intro y hy
      calc w * l * y * (w * l)⁻¹ = w * (l * y * l⁻¹) * w⁻¹ := by group
        _ = w * y * w⁻¹ := by rw [hUc l hl y hy]; group
        _ = y⁻¹ := hwinv y hy

theorem odd_orderOf_of_mem_outer_torus {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {s : PGL2 K}
    (hsJ : s ∉ pslRange K) {U : Subgroup (PGL2 K)}
    (hUcard : Nat.card U = outerTorusOrder (Nat.card K)) (hsU : s ∈ U) {x : PGL2 K}
    (hxU : x ∈ U) (hxJ : x ∈ pslRange K) : Odd (orderOf x) := by
  have h1 := card_eq_two_mul_card_comap hK hcard hsU hsJ
  have hm := outerTorusOrder_mod_four (odd_card_of_isOddPrimePower hK)
  obtain ⟨x', rfl⟩ := hxJ
  have hdvd := orderOf_dvd_natCard (⟨x', hxU⟩ : U.comap
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)))
  rw [← Subgroup.orderOf_coe] at hdvd
  rw [orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective]
  refine Odd.of_dvd_nat ?_ hdvd
  rw [Nat.odd_iff]
  omega

theorem exists_odd_mem_outer_torus {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {s : PGL2 K}
    (hsJ : s ∉ pslRange K) {U : Subgroup (PGL2 K)}
    (hUcard : Nat.card U = outerTorusOrder (Nat.card K)) (hsU : s ∈ U) :
    ∃ y ∈ U, y ∈ pslRange K ∧ y ≠ 1 ∧ Odd (orderOf y) := by
  have h1 := card_eq_two_mul_card_comap hK hcard hsU hsJ
  have hqodd := odd_card_of_isOddPrimePower hK
  have hm6 := six_le_outerTorusOrder hqodd (by obtain ⟨k, hk⟩ := hqodd; omega)
  have hlt : 1 < Nat.card (U.comap
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K))) := by omega
  obtain ⟨⟨y', hy'U⟩, hy'1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.one_lt_card_iff_ne_bot _).mp hlt)
  have hy'1' : y' ≠ 1 := by
    rintro rfl
    exact hy'1 rfl
  refine ⟨_, hy'U, ⟨y', rfl⟩, ?_, odd_orderOf_of_mem_outer_torus hK hcard hsJ hUcard hsU hy'U
    ⟨y', rfl⟩⟩
  intro h
  apply hy'1'
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [h, map_one]

theorem case_two_pgl2 {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {t g : PGL2 K} (htJ : t ∈ pslRange K) (htt : t * t = 1) (ht1 : t ≠ 1) (hg2 : g ^ 2 = 1)
    (hgJ : g ∉ pslRange K) (htg : t * g = g * t) (H : Subgroup (PGL2 K))
    (hHJ : H ≤ pslRange K) (htH : t ∈ H) (hgH : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hP1g : ∀ x ∈ pslRange K, x * g = g * x → Odd (orderOf x) → x ∈ H)
    (hP1tg : ∀ x ∈ pslRange K, x * (t * g) = t * g * x → Odd (orderOf x) → x ∈ H) :
    H = pslRange K := by
  classical
  have hJ2 := pslRange_index_eq_two hK
  obtain ⟨U, w, hUc, hUcard, hgU, hwU, hww, hwinv, hC⟩ :=
    outer_involution_centralizer hK hcard hg2 hgJ
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hg2)
  have hUodd : ∀ x ∈ U, x ∈ pslRange K → x ∈ H := fun x hxU hxJ =>
    hP1g x hxJ (hUcomm x hxU g hgU)
      (odd_orderOf_of_mem_outer_torus hK hcard hgJ hUcard hgU hxU hxJ)
  have hUH : U ≤ H ⊔ Subgroup.zpowers g := by
    intro u hu
    by_cases huJ : u ∈ pslRange K
    · exact Subgroup.mem_sup_left (hUodd u hu huJ)
    · have hugJ : u * g ∈ pslRange K :=
        (Subgroup.mul_mem_iff_of_index_two hJ2).mpr (iff_of_false huJ hgJ)
      have hugH : u * g ∈ H := hUodd _ (U.mul_mem hu hgU) hugJ
      have hu' : u = u * g * g := by rw [mul_assoc, ← pow_two, hg2, mul_one]
      rw [hu']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hugH)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have htU : t ∉ U := by
    intro htU
    have hodd := odd_orderOf_of_mem_outer_torus hK hcard hgJ hUcard hgU htU htJ
    rw [orderOf_eq_prime (by rw [pow_two]; exact htt) ht1] at hodd
    exact absurd hodd (by decide)
  have htC : t ∈ U ⊔ Subgroup.zpowers w := by
    rw [← hC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr htg
  have hwN : w ∈ Subgroup.normalizer (U : Set (PGL2 K)) :=
    zpowers_le_normalizer_of_inverting hww hwinv (Subgroup.mem_zpowers w)
  have hwH : w ∈ H ⊔ Subgroup.zpowers g := by
    have h := htC
    rw [sup_comm, mem_zpowers_sup_iff hwN (by rw [pow_two]; exact hww)] at h
    obtain ⟨l, hl, rfl | hl'⟩ := h
    · exact absurd hl htU
    · have hw' : w = t * l⁻¹ := by rw [hl']; group
      rw [hw']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left htH) (Subgroup.inv_mem _ (hUH hl))
  have hCH : Subgroup.centralizer ({g} : Set (PGL2 K)) ≤ H ⊔ Subgroup.zpowers g := by
    rw [hC]
    exact sup_le hUH (Subgroup.zpowers_le.mpr hwH)
  rcases outer_involution_centralizer_maximal hKcard hK hcard hg2 hgJ _ hCH with h | h
  ·
    exfalso
    have hs2 : (t * g) ^ 2 = 1 := by
      calc (t * g) ^ 2 = t * (g * t) * g := by rw [pow_two]; group
        _ = t * t * (g * g) := by rw [← htg]; group
        _ = 1 := by rw [htt, ← pow_two, hg2, one_mul]
    have hsJ : t * g ∉ pslRange K := by
      intro hs
      apply hgJ
      have : g = t⁻¹ * (t * g) := by group
      rw [this]
      exact (pslRange K).mul_mem ((pslRange K).inv_mem htJ) hs
    obtain ⟨U', -, hU'c, hU'card, hsU', -, -, -, -⟩ :=
      outer_involution_centralizer hK hcard hs2 hsJ
    obtain ⟨y, hyU', hyJ, hy1, hyodd⟩ := exists_odd_mem_outer_torus hK hcard hsJ hU'card hsU'
    have hys : y * (t * g) = t * g * y :=
      congrArg Subtype.val (hU'c.commGroup.mul_comm ⟨y, hyU'⟩ ⟨t * g, hsU'⟩)
    have hyH : y ∈ H := hP1tg y hyJ hys hyodd
    have hyC : y ∈ Subgroup.centralizer ({g} : Set (PGL2 K)) := h ▸ Subgroup.mem_sup_left hyH
    have hyg : y * g = g * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hyt : y * t = t * y := by
      calc y * t = y * (t * g) * g⁻¹ := by group
        _ = t * (g * y) * g⁻¹ := by rw [hys]; group
        _ = t * y := by rw [← hyg]; group
    have hyU : y ∈ U := by
      by_contra hyU
      obtain ⟨hyy, -⟩ := inverts_of_mem_sup_not_mem hUcomm hww hwinv (hC ▸ hyC) hyU
      exact hy1 (eq_one_of_mul_self_of_odd hyy hyodd)
    obtain ⟨-, htinv⟩ := inverts_of_mem_sup_not_mem hUcomm hww hwinv htC htU
    have h1 := htinv y hyU
    rw [← hyt] at h1
    have hyy : y * y = 1 := by
      calc y * y = y * (y * t * t⁻¹) := by group
        _ = y * y⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel y
    exact hy1 (eq_one_of_mul_self_of_odd hyy hyodd)
  ·
    apply le_antisymm hHJ
    intro j hj
    have hjtop : j ∈ H ⊔ Subgroup.zpowers g := h ▸ Subgroup.mem_top j
    have hgN : g ∈ Subgroup.normalizer (H : Set (PGL2 K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact hgH x
      · intro hx
        have h1 := hgH _ hx
        rwa [hg', show g * (g * x * g) * g = (g * g) * x * (g * g) by group, ← pow_two, hg2,
          one_mul, mul_one] at h1
    rw [sup_comm, mem_zpowers_sup_iff hgN hg2] at hjtop
    obtain ⟨l, hl, rfl | rfl⟩ := hjtop
    · exact hl
    · exfalso
      apply hgJ
      have : g = g * l * l⁻¹ := by group
      rw [this]
      exact (pslRange K).mul_mem hj ((pslRange K).inv_mem (hHJ hl))

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
