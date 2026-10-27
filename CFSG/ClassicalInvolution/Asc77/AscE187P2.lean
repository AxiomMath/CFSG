module

public import CFSG.ClassicalInvolution.Asc77.AscE187EndA

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem eq_or_eq_inv_of_orderOf_four_of_cyclic [Finite G] {U : Subgroup G} (hU : IsCyclic U)
    {x y : G} (hx : x ∈ U) (hy : y ∈ U) (hx4 : orderOf x = 4) (hy4 : orderOf y = 4) :
    y = x ∨ y = x⁻¹ := by
  classical
  have : Fintype U := Fintype.ofFinite _
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  have hd : 4 ∣ Fintype.card U := by
    rw [← Nat.card_eq_fintype_card, ← hx4]
    have := Subgroup.orderOf_dvd_natCard U hx
    exact this
  have hcard := IsCyclic.card_orderOf_eq_totient (α := U) hd
  have hX : orderOf (⟨x, hx⟩ : U) = 4 := by rw [Subgroup.orderOf_mk]; exact hx4
  have hXi : orderOf (⟨x, hx⟩ : U)⁻¹ = 4 := by rw [orderOf_inv]; exact hX
  have hY : orderOf (⟨y, hy⟩ : U) = 4 := by rw [Subgroup.orderOf_mk]; exact hy4
  have hsub : ({⟨x, hx⟩, (⟨x, hx⟩ : U)⁻¹, ⟨y, hy⟩} : Finset U) ⊆
      Finset.univ.filter (fun a : U => orderOf a = 4) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl <;> assumption
  have h1 : (⟨x, hx⟩ : U) ≠ (⟨x, hx⟩ : U)⁻¹ := by
    intro h
    have : (⟨x, hx⟩ : U) * ⟨x, hx⟩ = 1 := by
      calc (⟨x, hx⟩ : U) * ⟨x, hx⟩ = (⟨x, hx⟩ : U) * (⟨x, hx⟩ : U)⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel _
    have h2 := orderOf_dvd_of_pow_eq_one (show (⟨x, hx⟩ : U) ^ 2 = 1 by rw [pow_two]; exact this)
    rw [hX] at h2
    omega
  have h2 : (⟨y, hy⟩ : U) ≠ ⟨x, hx⟩ := fun h => hne1 (congrArg Subtype.val h)
  have h3 : (⟨y, hy⟩ : U) ≠ (⟨x, hx⟩ : U)⁻¹ := fun h => hne2 (congrArg Subtype.val h)
  have hcard3 : ({⟨x, hx⟩, (⟨x, hx⟩ : U)⁻¹, ⟨y, hy⟩} : Finset U).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using h3.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1, fun h => h2 h.symm⟩
  have := Finset.card_le_card hsub
  rw [hcard3, hcard] at this
  have ht : Nat.totient 4 = 2 := by decide
  omega

@[expose] def GoodFour (H : Subgroup G) (t : G) : Prop :=
  ∃ d₁ d₂ : G, GoodInv H t d₁ ∧ GoodInv H t d₂ ∧ GoodInv H t (d₁ * d₂) ∧ d₁ * d₂ = d₂ * d₁

@[expose] def GoodFourW (H W : Subgroup G) (t : G) : Prop :=
  ∃ d₁ d₂ : G, GoodInv H t d₁ ∧ GoodInv H t d₂ ∧ GoodInv H t (d₁ * d₂) ∧ d₁ * d₂ = d₂ * d₁ ∧
    d₁ ∈ W ∧ d₂ ∈ W

theorem sq_eq_of_orderOf_four {z u : G} {K : Subgroup G} (hz : IsUniqueInvolution K z)
    (huK : u ∈ K) (hu4 : orderOf u = 4) : u * u = z := by
  have h4 : u ^ 4 = 1 := by rw [← hu4]; exact pow_orderOf_eq_one u
  have h : (u * u) * (u * u) = 1 := by
    calc (u * u) * (u * u) = u ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h4
  rcases hz.unique (u * u) (K.mul_mem huK huK) h with h1 | h1
  · exfalso
    have : u ^ 2 = 1 := by rw [pow_two]; exact h1
    have := orderOf_dvd_of_pow_eq_one this
    rw [hu4] at this
    omega
  · exact h1

theorem isPGroup_zpowers_of_orderOf_four {u : G} (hu4 : orderOf u = 4) :
    IsPGroup 2 (Subgroup.zpowers u) :=
  IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu4]; norm_num)

section GoodFour

variable [Finite G]

theorem commute_of_mem_of_twin (hΩ : HypOmegaMod p f Ω) {K K' : Subgroup G} {z : G}
    {W : Subgroup G} (hW2 : IsPGroup 2 W) (hK : K ∈ Ω) (hK'Ω : K' ∈ Ω) (hKK' : K ≠ K')
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z) {u u' : G} (huK : u ∈ K)
    (huW : u ∈ W) (hu'K : u' ∈ K') (hu'W : u' ∈ W) : u * u' = u' * u :=
  hΩ.commutes_of_twin_of_isPGroup hK hK'Ω hKK' hz hz' (A := Subgroup.zpowers u)
    (B := Subgroup.zpowers u') (Subgroup.zpowers_le.mpr huK) (Subgroup.zpowers_le.mpr hu'K)
    (hW2.to_le (sup_le (Subgroup.zpowers_le.mpr huW) (Subgroup.zpowers_le.mpr hu'W))) u
    (Subgroup.mem_zpowers u) u' (Subgroup.mem_zpowers u')

omit [Finite G] in
theorem E187C.goodFour_core_of {K K' : Subgroup G} {z t : G} {H R₁ R₂ : Subgroup G}
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (htz : t * z = z * t) {u u' : G} (huK : u ∈ K) (huR : u ∈ R₁) (hu4 : orderOf u = 4)
    (hu'K : u' ∈ K') (hu'R : u' ∈ R₂) (hu'4 : orderOf u' = 4)
    (htd : (u * u') * t = t * (u * u')) (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ R₁ ⊔ R₂, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H)
    (huu' : u * u' = u' * u) (hno : ∀ x ∈ K, x ∈ K' → orderOf x = 4 → False) :
    GoodFour H t := by
  have hu2 : u * u = z := sq_eq_of_orderOf_four hz huK hu4
  have hu'2 : u' * u' = z := sq_eq_of_orderOf_four hz' hu'K hu'4
  have huR' : u ∈ R₁ ⊔ R₂ := Subgroup.mem_sup_left huR
  have hu'R' : u' ∈ R₁ ⊔ R₂ := Subgroup.mem_sup_right hu'R
  have hzu : z * u = u * z := hz.commute_of_mem huK
  have hzu' : z * u' = u' * z := hz'.commute_of_mem hu'K
  obtain ⟨d, hd⟩ : ∃ d, d = u * u' := ⟨_, rfl⟩
  have hdd : d * d = 1 := by
    calc d * d = u * (u' * u) * u' := by rw [hd]; group
      _ = u * (u * u') * u' := by rw [huu']
      _ = (u * u) * (u' * u') := by group
      _ = 1 := by rw [hu2, hu'2, hz.sq]
  have hd1 : d ≠ 1 := by
    intro h
    have h1 : u' = u⁻¹ := by
      have : u * u' = 1 := hd ▸ h
      exact (inv_eq_of_mul_eq_one_right this).symm
    have hu_K' : u ∈ K' := by
      have := K'.inv_mem hu'K
      rwa [h1, inv_inv] at this
    exact hno u huK hu_K' hu4
  have hdR : d ∈ R₁ ⊔ R₂ := hd ▸ (R₁ ⊔ R₂).mul_mem huR' hu'R'
  have hzR : z ∈ R₁ ⊔ R₂ := hu2 ▸ (R₁ ⊔ R₂).mul_mem huR' huR'
  have hzd : z * d = d * z := by
    calc z * d = (z * u) * u' := by rw [hd]; group
      _ = u * z * u' := by rw [hzu]
      _ = u * (z * u') := by group
      _ = u * (u' * z) := by rw [hzu']
      _ = d * z := by rw [hd]; group
  have htd' : d * t = t * d := hd ▸ htd
  have hzdne : z * d ≠ 1 := by
    intro h
    have h1 : u' = u⁻¹ * z := by
      have h2 : u * u' = z⁻¹ := by
        have : z * (u * u') = 1 := by rw [← hd]; exact h
        exact eq_inv_of_mul_eq_one_right this
      rw [inv_eq_of_mul_eq_one_right hz.sq] at h2
      calc u' = u⁻¹ * (u * u') := by group
        _ = u⁻¹ * z := by rw [h2]
    have hu'K0 : u' ∈ K := by rw [h1]; exact K.mul_mem (K.inv_mem huK) hz.mem
    exact hno u' hu'K0 hu'K hu'4
  have hzdsq : (z * d) * (z * d) = 1 := by
    calc (z * d) * (z * d) = z * (d * z) * d := by group
      _ = z * (z * d) * d := by rw [hzd]
      _ = (z * z) * (d * d) := by group
      _ = 1 := by rw [hz.sq, hdd, one_mul]
  refine ⟨z, d, ⟨hz.ne_one, hz.sq, htz.symm, hzcent⟩, ⟨hd1, hdd, htd', ?_⟩,
    ⟨hzdne, hzdsq, ?_, ?_⟩, hzd⟩
  · exact h2 d hdR hd1 hdd
  · calc z * d * t = z * (d * t) := by group
      _ = z * (t * d) := by rw [htd']
      _ = (z * t) * d := by group
      _ = (t * z) * d := by rw [htz]
      _ = t * (z * d) := by group
  · exact h2 (z * d) ((R₁ ⊔ R₂).mul_mem hzR hdR) hzdne hzdsq

theorem goodFour_core (hΩ : HypOmegaMod p f Ω) {K K' : Subgroup G} {z t : G}
    {H R₁ R₂ : Subgroup G} (hR2 : IsPGroup 2 ↥(R₁ ⊔ R₂)) (hK : K ∈ Ω) (hK'Ω : K' ∈ Ω)
    (hKK' : K ≠ K') (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (htz : t * z = z * t) {u u' : G} (huK : u ∈ K) (huR : u ∈ R₁) (hu4 : orderOf u = 4)
    (hu'K : u' ∈ K') (hu'R : u' ∈ R₂) (hu'4 : orderOf u' = 4)
    (htd : (u * u') * t = t * (u * u')) (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ R₁ ⊔ R₂, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H) :
    GoodFour H t :=
  E187C.goodFour_core_of hz hz' htz huK huR hu4 hu'K hu'R hu'4 htd hzcent h2
    (commute_of_mem_of_twin hΩ hR2 hK hK'Ω hKK' hz hz' huK (Subgroup.mem_sup_left huR) hu'K
      (Subgroup.mem_sup_right hu'R))
    (fun x hxK hxK' hx4 => by
      have h := hΩ.card_le_two_of_le_inf hK hK'Ω hKK' (isPGroup_zpowers_of_orderOf_four hx4)
        (Subgroup.zpowers_le.mpr hxK) (Subgroup.zpowers_le.mpr hxK')
      rw [Nat.card_zpowers, hx4] at h
      omega)

omit [Finite G] in
theorem E187C.goodFour_core_gen (htw : ∀ {K K' : Subgroup G} {z : G} {W : Subgroup G}
    {u u' : G}, IsPGroup 2 W → K ∈ Ω →
      K' ∈ Ω → K ≠ K' → IsUniqueInvolution K z → IsUniqueInvolution K' z → u ∈ K → u ∈ W →
      u' ∈ K' → u' ∈ W → u * u' = u' * u)
    (hle2 : ∀ {K J A : Subgroup G}, K ∈ Ω → J ∈ Ω → K ≠ J → IsPGroup 2 A → A ≤ K → A ≤ J →
      Nat.card A ≤ 2)
    {K K' : Subgroup G} {z t : G}
    {H R₁ R₂ : Subgroup G} (hR2 : IsPGroup 2 ↥(R₁ ⊔ R₂)) (hK : K ∈ Ω) (hK'Ω : K' ∈ Ω)
    (hKK' : K ≠ K') (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (htz : t * z = z * t) {u u' : G} (huK : u ∈ K) (huR : u ∈ R₁) (hu4 : orderOf u = 4)
    (hu'K : u' ∈ K') (hu'R : u' ∈ R₂) (hu'4 : orderOf u' = 4)
    (htd : (u * u') * t = t * (u * u')) (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ R₁ ⊔ R₂, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H) :
    GoodFour H t :=
  E187C.goodFour_core_of hz hz' htz huK huR hu4 hu'K hu'R hu'4 htd hzcent h2
    (htw hR2 hK hK'Ω hKK' hz hz' huK (Subgroup.mem_sup_left huR) hu'K
      (Subgroup.mem_sup_right hu'R))
    (fun x hxK hxK' hx4 => by
      have h := hle2 hK hK'Ω hKK' (isPGroup_zpowers_of_orderOf_four hx4)
        (Subgroup.zpowers_le.mpr hxK) (Subgroup.zpowers_le.mpr hxK')
      rw [Nat.card_zpowers, hx4] at h
      omega)

omit [Finite G] in
theorem E187C.goodFour_of_swap_gen (hc : ConjInvariant Ω)
    (htw : ∀ {K K' : Subgroup G} {z : G} {W : Subgroup G} {u u' : G}, IsPGroup 2 W → K ∈ Ω →
      K' ∈ Ω → K ≠ K' → IsUniqueInvolution K z → IsUniqueInvolution K' z → u ∈ K → u ∈ W →
      u' ∈ K' → u' ∈ W → u * u' = u' * u)
    (hle2 : ∀ {K J A : Subgroup G}, K ∈ Ω → J ∈ Ω → K ≠ J → IsPGroup 2 A → A ≤ K → A ≤ J →
      Nat.card A ≤ 2)
    {K : Subgroup G} {z t : G} {H R : Subgroup G}
    (hR2 : IsPGroup 2 ↥(R ⊔ conjSub t R)) (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht2 : t * t = 1) (htz : t * z = z * t) (hnK : conjSub t K ≠ K) {u : G} (huK : u ∈ K)
    (huR : u ∈ R) (hu4 : orderOf u = 4) (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ R ⊔ conjSub t R, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H) :
    GoodFour H t := by
  have htzt : t * z * t⁻¹ = z := by rw [htz]; group
  have hK'Ω : conjSub t K ∈ Ω := hc t K hK
  have hz' : IsUniqueInvolution (conjSub t K) z := by
    have := hz.conj t
    rwa [htzt] at this
  obtain ⟨u', hu'⟩ : ∃ u', u' = t * u * t⁻¹ := ⟨_, rfl⟩
  have hu'K : u' ∈ conjSub t K := hu' ▸ conj_mem_conjSub huK
  have hu'R : u' ∈ conjSub t R := hu' ▸ conj_mem_conjSub huR
  have hu'4 : orderOf u' = 4 := by rw [hu', orderOf_conj_mul_inv_eq, hu4]
  have huu' : u * u' = u' * u :=
    htw hR2 hK hK'Ω (Ne.symm hnK) hz hz' huK
      (Subgroup.mem_sup_left huR) hu'K (Subgroup.mem_sup_right hu'R)
  have htd : (u * u') * t = t * (u * u') := by
    have e1 : t * u' * t⁻¹ = u := by
      rw [hu']
      have : t * (t * u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
      rw [this, ht2]
      group
    have e : t * (u * u') * t⁻¹ = u * u' := by
      calc t * (u * u') * t⁻¹ = (t * u * t⁻¹) * (t * u' * t⁻¹) := by group
        _ = u' * u := by rw [e1, ← hu']
        _ = u * u' := huu'.symm
    exact mul_inv_eq_iff_eq_mul.mp e |>.symm
  exact E187C.goodFour_core_gen htw hle2 hR2 hK hK'Ω
      (Ne.symm hnK) hz hz' htz huK huR hu4 hu'K hu'R hu'4 htd
    hzcent h2

theorem E187C.goodFour_of_fixed_gen (htw : ∀ {K K' : Subgroup G} {z : G} {W : Subgroup G}
    {u u' : G}, IsPGroup 2 W → K ∈ Ω →
      K' ∈ Ω → K ≠ K' → IsUniqueInvolution K z → IsUniqueInvolution K' z → u ∈ K → u ∈ W →
      u' ∈ K' → u' ∈ W → u * u' = u' * u)
    (hle2 : ∀ {K J A : Subgroup G}, K ∈ Ω → J ∈ Ω → K ≠ J → IsPGroup 2 A → A ≤ K → A ≤ J →
      Nat.card A ≤ 2)
    {K K' : Subgroup G} {z t : G}
    {H W R₁ R₂ : Subgroup G} (hR2 : IsPGroup 2 ↥(R₁ ⊔ R₂)) (hK : K ∈ Ω) (hK'Ω : K' ∈ Ω)
    (hKK' : K ≠ K') (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (htz : t * z = z * t) (htK : conjSub t K = K) (htK' : conjSub t K' = K')
    (htW : conjSub t W = W) (hUK : IsCyclic ↥(K ⊓ W)) (hUK' : IsCyclic ↥(K' ⊓ W)) {u u' : G}
    (huK : u ∈ K) (huW : u ∈ W) (huR : u ∈ R₁) (hu4 : orderOf u = 4) (hu'K : u' ∈ K')
    (hu'W : u' ∈ W) (hu'R : u' ∈ R₂) (hu'4 : orderOf u' = 4)
    (hC : ∀ M ∈ Ω, IsUniqueInvolution M z → ∀ x ∈ M, orderOf x = 4 → t * x ≠ x * t)
    (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ R₁ ⊔ R₂, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H) :
    GoodFour H t := by
  have hinv : ∀ (M : Subgroup G), M ∈ Ω → IsUniqueInvolution M z → conjSub t M = M →
      IsCyclic ↥(M ⊓ W) → ∀ x ∈ M, x ∈ W → orderOf x = 4 → t * x * t⁻¹ = x⁻¹ := by
    intro M hM hzM htM hMW x hxM hxW hx4
    have h1 : t * x * t⁻¹ ∈ M ⊓ W := by
      refine ⟨?_, ?_⟩
      · have := conj_mem_conjSub (n := t) hxM
        rwa [htM] at this
      · have := conj_mem_conjSub (n := t) hxW
        rwa [htW] at this
    rcases eq_or_eq_inv_of_orderOf_four_of_cyclic hMW ⟨hxM, hxW⟩ h1
      hx4 (by rw [orderOf_conj_mul_inv_eq, hx4]) with h | h
    · exfalso
      apply hC M hM hzM x hxM hx4
      calc t * x = (t * x * t⁻¹) * t := by group
        _ = x * t := by rw [h]
    · exact h
  have huu' : u * u' = u' * u :=
    htw hR2 hK hK'Ω hKK' hz hz' huK (Subgroup.mem_sup_left huR) hu'K
      (Subgroup.mem_sup_right hu'R)
  have hd2 : (u * u') * (u * u') = 1 := by
    calc (u * u') * (u * u') = u * (u' * u) * u' := by group
      _ = u * (u * u') * u' := by rw [huu']
      _ = (u * u) * (u' * u') := by group
      _ = 1 := by rw [sq_eq_of_orderOf_four hz huK hu4, sq_eq_of_orderOf_four hz' hu'K hu'4, hz.sq]
  have htd : (u * u') * t = t * (u * u') := by
    have e : t * (u * u') * t⁻¹ = u * u' := by
      calc t * (u * u') * t⁻¹ = (t * u * t⁻¹) * (t * u' * t⁻¹) := by group
        _ = u⁻¹ * u'⁻¹ := by rw [hinv K hK hz htK hUK u huK huW hu4,
          hinv K' hK'Ω hz' htK' hUK' u' hu'K hu'W hu'4]
        _ = (u' * u)⁻¹ := by group
        _ = (u * u')⁻¹ := by rw [huu']
        _ = u * u' := inv_eq_of_mul_eq_one_right hd2
    exact mul_inv_eq_iff_eq_mul.mp e |>.symm
  exact E187C.goodFour_core_gen htw hle2 hR2 hK hK'Ω hKK' hz hz' htz huK huR hu4 hu'K hu'R hu'4 htd
      hzcent h2

theorem E187C.goodFour_coreW_gen (htw : ∀ {K K' : Subgroup G} {z : G} {W : Subgroup G} {u u' : G}, IsPGroup 2 W → K ∈ Ω →
      K' ∈ Ω → K ≠ K' → IsUniqueInvolution K z → IsUniqueInvolution K' z → u ∈ K → u ∈ W →
      u' ∈ K' → u' ∈ W → u * u' = u' * u)
    (hle2 : ∀ {K J A : Subgroup G}, K ∈ Ω → J ∈ Ω → K ≠ J → IsPGroup 2 A → A ≤ K → A ≤ J →
      Nat.card A ≤ 2)
    {K K' : Subgroup G} {z t : G}
    {H W R₁ R₂ : Subgroup G} (hR2 : IsPGroup 2 ↥(R₁ ⊔ R₂)) (hK : K ∈ Ω) (hK'Ω : K' ∈ Ω)
    (hKK' : K ≠ K') (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (htz : t * z = z * t) {u u' : G} (huK : u ∈ K) (huR : u ∈ R₁) (hu4 : orderOf u = 4)
    (hu'K : u' ∈ K') (hu'R : u' ∈ R₂) (hu'4 : orderOf u' = 4) (huW : u ∈ W) (hu'W : u' ∈ W)
    (htd : (u * u') * t = t * (u * u')) (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ R₁ ⊔ R₂, a ∈ W → a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H) :
    GoodFourW H W t := by
  have hu2 : u * u = z := sq_eq_of_orderOf_four hz huK hu4
  have hu'2 : u' * u' = z := sq_eq_of_orderOf_four hz' hu'K hu'4
  have huR' : u ∈ R₁ ⊔ R₂ := Subgroup.mem_sup_left huR
  have hu'R' : u' ∈ R₁ ⊔ R₂ := Subgroup.mem_sup_right hu'R
  have huu' : u * u' = u' * u :=
    htw hR2 hK hK'Ω hKK' hz hz' huK huR' hu'K hu'R'
  have hzu : z * u = u * z := hz.commute_of_mem huK
  have hzu' : z * u' = u' * z := hz'.commute_of_mem hu'K
  have hno : ∀ x ∈ K, x ∈ K' → orderOf x = 4 → False := by
    intro x hxK hxK' hx4
    have h := hle2 hK hK'Ω hKK' (isPGroup_zpowers_of_orderOf_four hx4)
      (Subgroup.zpowers_le.mpr hxK) (Subgroup.zpowers_le.mpr hxK')
    rw [Nat.card_zpowers, hx4] at h
    omega
  obtain ⟨d, hd⟩ : ∃ d, d = u * u' := ⟨_, rfl⟩
  have hdd : d * d = 1 := by
    calc d * d = u * (u' * u) * u' := by rw [hd]; group
      _ = u * (u * u') * u' := by rw [huu']
      _ = (u * u) * (u' * u') := by group
      _ = 1 := by rw [hu2, hu'2, hz.sq]
  have hd1 : d ≠ 1 := by
    intro h
    have h1 : u' = u⁻¹ := by
      have : u * u' = 1 := hd ▸ h
      exact (inv_eq_of_mul_eq_one_right this).symm
    have hu_K' : u ∈ K' := by
      have := K'.inv_mem hu'K
      rwa [h1, inv_inv] at this
    exact hno u huK hu_K' hu4
  have hdR : d ∈ R₁ ⊔ R₂ := hd ▸ (R₁ ⊔ R₂).mul_mem huR' hu'R'
  have hzR : z ∈ R₁ ⊔ R₂ := hu2 ▸ (R₁ ⊔ R₂).mul_mem huR' huR'
  have hzd : z * d = d * z := by
    calc z * d = (z * u) * u' := by rw [hd]; group
      _ = u * z * u' := by rw [hzu]
      _ = u * (z * u') := by group
      _ = u * (u' * z) := by rw [hzu']
      _ = d * z := by rw [hd]; group
  have htd' : d * t = t * d := hd ▸ htd
  have hzdne : z * d ≠ 1 := by
    intro h
    have h1 : u' = u⁻¹ * z := by
      have h2 : u * u' = z⁻¹ := by
        have : z * (u * u') = 1 := by rw [← hd]; exact h
        exact eq_inv_of_mul_eq_one_right this
      rw [inv_eq_of_mul_eq_one_right hz.sq] at h2
      calc u' = u⁻¹ * (u * u') := by group
        _ = u⁻¹ * z := by rw [h2]
    have hu'K0 : u' ∈ K := by rw [h1]; exact K.mul_mem (K.inv_mem huK) hz.mem
    exact hno u' hu'K0 hu'K hu'4
  have hzdsq : (z * d) * (z * d) = 1 := by
    calc (z * d) * (z * d) = z * (d * z) * d := by group
      _ = z * (z * d) * d := by rw [hzd]
      _ = (z * z) * (d * d) := by group
      _ = 1 := by rw [hz.sq, hdd, one_mul]
  have hzW' : z ∈ W := hu2 ▸ W.mul_mem huW huW
  have hdW : d ∈ W := hd ▸ W.mul_mem huW hu'W
  refine ⟨z, d, ⟨hz.ne_one, hz.sq, htz.symm, hzcent⟩, ⟨hd1, hdd, htd', ?_⟩,
    ⟨hzdne, hzdsq, ?_, ?_⟩, hzd, hzW', hdW⟩
  · exact h2 d hdR hdW hd1 hdd
  · calc z * d * t = z * (d * t) := by group
      _ = z * (t * d) := by rw [htd']
      _ = (z * t) * d := by group
      _ = (t * z) * d := by rw [htz]
      _ = t * (z * d) := by group
  · exact h2 (z * d) ((R₁ ⊔ R₂).mul_mem hzR hdR) (W.mul_mem hzW' hdW) hzdne hzdsq


theorem E187C.goodFour_of_swapW_gen (hc : ConjInvariant Ω)
    (htw : ∀ {K K' : Subgroup G} {z : G} {W : Subgroup G} {u u' : G}, IsPGroup 2 W → K ∈ Ω →
      K' ∈ Ω → K ≠ K' → IsUniqueInvolution K z → IsUniqueInvolution K' z → u ∈ K → u ∈ W →
      u' ∈ K' → u' ∈ W → u * u' = u' * u)
    (hle2 : ∀ {K J A : Subgroup G}, K ∈ Ω → J ∈ Ω → K ≠ J → IsPGroup 2 A → A ≤ K → A ≤ J →
      Nat.card A ≤ 2)
    {K : Subgroup G} {z t : G} {H W R : Subgroup G}
    (hR2 : IsPGroup 2 ↥(R ⊔ conjSub t R)) (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht2 : t * t = 1) (htz : t * z = z * t) (hnK : conjSub t K ≠ K) {u : G} (huK : u ∈ K)
    (huR : u ∈ R) (hu4 : orderOf u = 4) (huW : u ∈ W) (hWt : ∀ x ∈ W, t * x * t⁻¹ ∈ W)
    (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ R ⊔ conjSub t R, a ∈ W → a ≠ 1 → a * a = 1 →
      Subgroup.centralizer ({a} : Set G) ≤ H) :
    GoodFourW H W t := by
  have htzt : t * z * t⁻¹ = z := by rw [htz]; group
  have hK'Ω : conjSub t K ∈ Ω := hc t K hK
  have hz' : IsUniqueInvolution (conjSub t K) z := by
    have := hz.conj t
    rwa [htzt] at this
  obtain ⟨u', hu'⟩ : ∃ u', u' = t * u * t⁻¹ := ⟨_, rfl⟩
  have hu'K : u' ∈ conjSub t K := hu' ▸ conj_mem_conjSub huK
  have hu'R : u' ∈ conjSub t R := hu' ▸ conj_mem_conjSub huR
  have hu'4 : orderOf u' = 4 := by rw [hu', orderOf_conj_mul_inv_eq, hu4]
  have huu' : u * u' = u' * u :=
    htw hR2 hK hK'Ω (Ne.symm hnK) hz hz' huK
      (Subgroup.mem_sup_left huR) hu'K (Subgroup.mem_sup_right hu'R)
  have htd : (u * u') * t = t * (u * u') := by
    have e1 : t * u' * t⁻¹ = u := by
      rw [hu']
      have : t * (t * u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
      rw [this, ht2]
      group
    have e : t * (u * u') * t⁻¹ = u * u' := by
      calc t * (u * u') * t⁻¹ = (t * u * t⁻¹) * (t * u' * t⁻¹) := by group
        _ = u' * u := by rw [e1, ← hu']
        _ = u * u' := huu'.symm
    exact mul_inv_eq_iff_eq_mul.mp e |>.symm
  have hu'W : u' ∈ W := by rw [hu']; exact hWt u huW
  exact E187C.goodFour_coreW_gen htw hle2 hR2 hK hK'Ω (Ne.symm hnK) hz hz' htz huK huR hu4 hu'K hu'R hu'4 huW hu'W
    htd hzcent h2


theorem E187C.goodFour_of_fixedW_gen
    (htw : ∀ {K K' : Subgroup G} {z : G} {W : Subgroup G} {u u' : G}, IsPGroup 2 W → K ∈ Ω →
      K' ∈ Ω → K ≠ K' → IsUniqueInvolution K z → IsUniqueInvolution K' z → u ∈ K → u ∈ W →
      u' ∈ K' → u' ∈ W → u * u' = u' * u)
    (hle2 : ∀ {K J A : Subgroup G}, K ∈ Ω → J ∈ Ω → K ≠ J → IsPGroup 2 A → A ≤ K → A ≤ J →
      Nat.card A ≤ 2)
    {K K' : Subgroup G} {z t : G}
    {H W R₁ R₂ : Subgroup G} (hR2 : IsPGroup 2 ↥(R₁ ⊔ R₂)) (hK : K ∈ Ω) (hK'Ω : K' ∈ Ω)
    (hKK' : K ≠ K') (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (htz : t * z = z * t) (htK : conjSub t K = K) (htK' : conjSub t K' = K')
    (htW : conjSub t W = W) (hUK : IsCyclic ↥(K ⊓ W)) (hUK' : IsCyclic ↥(K' ⊓ W)) {u u' : G}
    (huK : u ∈ K) (huW : u ∈ W) (huR : u ∈ R₁) (hu4 : orderOf u = 4) (hu'K : u' ∈ K')
    (hu'W : u' ∈ W) (hu'R : u' ∈ R₂) (hu'4 : orderOf u' = 4)
    (hC : ∀ M ∈ Ω, IsUniqueInvolution M z → ∀ x ∈ M, orderOf x = 4 → t * x ≠ x * t)
    (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ R₁ ⊔ R₂, a ∈ W → a ≠ 1 → a * a = 1 →
      Subgroup.centralizer ({a} : Set G) ≤ H) :
    GoodFourW H W t := by
  have hinv : ∀ (M : Subgroup G), M ∈ Ω → IsUniqueInvolution M z → conjSub t M = M →
      IsCyclic ↥(M ⊓ W) → ∀ x ∈ M, x ∈ W → orderOf x = 4 → t * x * t⁻¹ = x⁻¹ := by
    intro M hM hzM htM hMW x hxM hxW hx4
    have h1 : t * x * t⁻¹ ∈ M ⊓ W := by
      refine ⟨?_, ?_⟩
      · have := conj_mem_conjSub (n := t) hxM
        rwa [htM] at this
      · have := conj_mem_conjSub (n := t) hxW
        rwa [htW] at this
    rcases eq_or_eq_inv_of_orderOf_four_of_cyclic hMW ⟨hxM, hxW⟩ h1
      hx4 (by rw [orderOf_conj_mul_inv_eq, hx4]) with h | h
    · exfalso
      apply hC M hM hzM x hxM hx4
      calc t * x = (t * x * t⁻¹) * t := by group
        _ = x * t := by rw [h]
    · exact h
  have huu' : u * u' = u' * u :=
    htw hR2 hK hK'Ω hKK' hz hz' huK (Subgroup.mem_sup_left huR) hu'K
      (Subgroup.mem_sup_right hu'R)
  have hd2 : (u * u') * (u * u') = 1 := by
    calc (u * u') * (u * u') = u * (u' * u) * u' := by group
      _ = u * (u * u') * u' := by rw [huu']
      _ = (u * u) * (u' * u') := by group
      _ = 1 := by rw [sq_eq_of_orderOf_four hz huK hu4, sq_eq_of_orderOf_four hz' hu'K hu'4, hz.sq]
  have htd : (u * u') * t = t * (u * u') := by
    have e : t * (u * u') * t⁻¹ = u * u' := by
      calc t * (u * u') * t⁻¹ = (t * u * t⁻¹) * (t * u' * t⁻¹) := by group
        _ = u⁻¹ * u'⁻¹ := by rw [hinv K hK hz htK hUK u huK huW hu4,
          hinv K' hK'Ω hz' htK' hUK' u' hu'K hu'W hu'4]
        _ = (u' * u)⁻¹ := by group
        _ = (u * u')⁻¹ := by rw [huu']
        _ = u * u' := inv_eq_of_mul_eq_one_right hd2
    exact mul_inv_eq_iff_eq_mul.mp e |>.symm
  exact E187C.goodFour_coreW_gen htw hle2 hR2 hK hK'Ω hKK' hz hz' htz huK huR hu4 hu'K hu'R hu'4 huW hu'W htd
    hzcent h2


theorem goodFour_of_swap (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} {z t : G} {H R : Subgroup G}
    (hR2 : IsPGroup 2 ↥(R ⊔ conjSub t R)) (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht2 : t * t = 1) (htz : t * z = z * t) (hnK : conjSub t K ≠ K) {u : G} (huK : u ∈ K)
    (huR : u ∈ R) (hu4 : orderOf u = 4) (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ R ⊔ conjSub t R, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H) :
    GoodFour H t :=
  E187C.goodFour_of_swap_gen hΩ.conjInvariant (fun hW hK hK' hKK' hz hz' huK huW hu'K hu'W =>
      commute_of_mem_of_twin hΩ hW hK hK' hKK' hz hz' huK huW hu'K hu'W)
    (fun hK hJ hKJ hA hAK hAJ => hΩ.card_le_two_of_le_inf hK hJ hKJ hA hAK hAJ)
    hR2 hK hz ht2 htz hnK huK huR hu4 hzcent h2

theorem goodFour_of_fixed (hΩ : HypOmegaMod p f Ω) {K K' : Subgroup G} {z t : G}
    {H W R₁ R₂ : Subgroup G} (hR2 : IsPGroup 2 ↥(R₁ ⊔ R₂)) (hK : K ∈ Ω) (hK'Ω : K' ∈ Ω)
    (hKK' : K ≠ K') (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (htz : t * z = z * t) (htK : conjSub t K = K) (htK' : conjSub t K' = K')
    (htW : conjSub t W = W) (hUK : IsCyclic ↥(K ⊓ W)) (hUK' : IsCyclic ↥(K' ⊓ W)) {u u' : G}
    (huK : u ∈ K) (huW : u ∈ W) (huR : u ∈ R₁) (hu4 : orderOf u = 4) (hu'K : u' ∈ K')
    (hu'W : u' ∈ W) (hu'R : u' ∈ R₂) (hu'4 : orderOf u' = 4)
    (hC : ∀ M ∈ Ω, IsUniqueInvolution M z → ∀ x ∈ M, orderOf x = 4 → t * x ≠ x * t)
    (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ R₁ ⊔ R₂, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H) :
    GoodFour H t :=
  E187C.goodFour_of_fixed_gen (fun hW hK hK' hKK' hz hz' huK huW hu'K hu'W =>
      commute_of_mem_of_twin hΩ hW hK hK' hKK' hz hz' huK huW hu'K hu'W)
    (fun hK hJ hKJ hA hAK hAJ => hΩ.card_le_two_of_le_inf hK hJ hKJ hA hAK hAJ)
    hR2 hK hK'Ω hKK' hz hz' htz htK htK' htW hUK hUK' huK huW huR hu4 hu'K hu'W hu'R hu'4 hC hzcent
    h2

end GoodFour

end CFSG.ClassicalInvolution.Asc77
