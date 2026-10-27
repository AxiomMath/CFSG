module

public import CFSG.GH74.Uniqueness.SU.SU7Rep
public import CFSG.GH74.Uniqueness.SU.SU5Map
public import CFSG.GH74.Uniqueness.SU.KInputs
public import CFSG.GH74.Uniqueness.Section4Lift

public section

namespace CFSG.GH74.Uniqueness.SU.SU7.Sec

open Subgroup CFSG.GH74.Uniqueness.SU.SU5

variable {X : Type} [Group X] [Finite X]

theorem exists_surj_alt5 (hKI4 : K.KI4) (hGH : SU0.GHGroup X)
    {z : X} (hzc : ∀ g : X, g * z = z * g) (hzz : z * z = 1) (hz1 : z ≠ 1)
    {S₀ R₀ : Subgroup X} (hS₀p : IsPGroup 2 S₀) (hS₀idx : ¬ 2 ∣ S₀.index)
    (hRS : R₀ ≤ S₀) (hzR : z ∈ R₀) (hS128 : Nat.card S₀ = 128) (hR32 : Nat.card R₀ = 32)
    (hRnS : ∀ s ∈ S₀, ∀ r ∈ R₀, s * r * s⁻¹ ∈ R₀)
    (hsq : ∀ r ∈ R₀, r * r = 1 ∨ r * r = z)
    (hsq2 : ∀ s ∈ S₀, s * s ∈ R₀)
    (hfaith : ∀ s ∈ S₀, (∀ r ∈ R₀, s * r * s⁻¹ * r⁻¹ = 1 ∨ s * r * s⁻¹ * r⁻¹ = z) → s ∈ R₀)
    (hsc : ∀ r ∈ R₀, ∀ h : X, h⁻¹ * r * h ∈ S₀ → h⁻¹ * r * h ∈ R₀)
    (hI10 : {r : X | r ∈ R₀ ∧ r * r = 1 ∧ r ≠ 1 ∧ r ≠ z}.ncard = 10)
    (hIgen : Subgroup.closure {r : X | r ∈ R₀ ∧ r * r = 1 ∧ r ≠ 1 ∧ r ≠ z} = R₀)
    (hIconj : ∀ r r' : X, r ∈ R₀ → r * r = 1 → r ≠ 1 → r ≠ z → r' ∈ R₀ → r' * r' = 1 →
      r' ≠ 1 → r' ≠ z → ∃ h : X, h⁻¹ * r * h = r') :
    ∃ ψ : X →* alternatingGroup (Fin 5), Function.Surjective ψ ∧
      ψ.ker = R₀ ⊔ pPrimeCore 2 X ∧
      ∀ c : X, (∀ r ∈ R₀, c * r * c⁻¹ * r⁻¹ ∈ pPrimeCore 2 X) → c ∈ R₀ ⊔ pPrimeCore 2 X := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup X := pPrimeCore 2 X with hO
  have hOnormal : O.Normal := inferInstanceAs (pPrimeCore 2 X).Normal
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))
  have hR2 : IsPGroup 2 ↥R₀ := hS₀p.to_le hRS
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  set π₁ : X →* X ⧸ O := QuotientGroup.mk' O with hπ₁
  set zb : X ⧸ O := π₁ z with hzb
  have hzbc : ∀ y : X ⧸ O, y * zb = zb * y := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    show π₁ g * π₁ z = π₁ z * π₁ g
    rw [← map_mul, ← map_mul, hzc]
  have hzOne : z ∉ O := by
    intro hzO
    have h1 := Subgroup.orderOf_dvd_natCard O hzO
    rw [hzord] at h1
    have := Nat.odd_iff.1 hOodd
    omega
  have hzb1 : zb ≠ 1 := fun h => hzOne ((QuotientGroup.eq_one_iff z).1 h)
  have hzbzb : zb * zb = 1 := by rw [hzb, ← map_mul, hzz, map_one]
  have hzbord : orderOf zb = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzbzb) hzb1
  set A : Subgroup (X ⧸ O) := zpowers zb with hA
  have hAn : A.Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := hn
    have hc : Commute g (zb ^ k) := (show Commute g zb from hzbc g).zpow_right k
    rw [hc.mul_inv_cancel]
    exact ⟨k, rfl⟩⟩
  have hAcenter : A ≤ center (X ⧸ O) := by
    rintro _ ⟨k, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact ((show Commute g zb from hzbc g).zpow_right k).eq
  have hA2 : Nat.card A = 2 := by rw [hA, Nat.card_zpowers, hzbord]
  have hOY : pPrimeCore 2 (X ⧸ O) = ⊥ := CFSG.GH74.Uniqueness.pPrimeCore_quotient_pPrimeCore X
  have hOH : pPrimeCore 2 ((X ⧸ O) ⧸ A) = ⊥ :=
    CFSG.GH74.Uniqueness.pPrimeCore_quotient_central_two hAcenter hA2 hOY
  set π₂ : (X ⧸ O) →* (X ⧸ O) ⧸ A := QuotientGroup.mk' A with hπ₂
  set π : X →* (X ⧸ O) ⧸ A := π₂.comp π₁ with hπ
  have hπsurj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective A).comp (QuotientGroup.mk'_surjective O)
  have hπO : ∀ o ∈ O, π o = 1 := fun o ho => by
    have : π₁ o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    simp [hπ, this]
  have hπz : π z = 1 := by
    have : π₂ zb = 1 := (QuotientGroup.eq_one_iff zb).2 (mem_zpowers zb)
    simpa [hπ, hzb] using this
  have hker : ∀ w : X, π w = 1 → w ∈ zpowers z ⊔ O := by
    intro w hw
    have h1 : π₁ w ∈ A := (QuotientGroup.eq_one_iff (π₁ w)).1 hw
    obtain ⟨k, hk⟩ := h1
    have h2 : π₁ (z ^ k) = π₁ w := by rw [map_zpow]; exact hk
    have h3 : (z ^ k)⁻¹ * w ∈ O := QuotientGroup.eq.1 h2
    have : w = z ^ k * ((z ^ k)⁻¹ * w) := by group
    rw [this]
    exact Subgroup.mul_mem_sup (zpow_mem_zpowers z k) h3
  have hSker : ∀ r ∈ S₀, π r = 1 → r = 1 ∨ r = z := by
    intro r hr hπr
    obtain ⟨j, o, ho, hjo⟩ :=
      Gen.exists_zpow_mul_of_mem_sup (x := z) (K := O) (fun k _ => hzc k) (hker r hπr)
    have ho1 : o = 1 := by
      have hoR : o ∈ S₀ := by
        have : o = z ^ (-j) * r := by rw [hjo]; group
        rw [this]; exact S₀.mul_mem (S₀.zpow_mem (hRS hzR) _) hr
      have : o ∈ S₀ ⊓ O := ⟨hoR, ho⟩
      rw [Gen.inf_eq_bot_of_isPGroup hS₀p hOodd, Subgroup.mem_bot] at this
      exact this
    rw [ho1, mul_one] at hjo
    have hz2' : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hzz]
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' j
    · left; rw [hjo, zpow_mul, hz2', one_zpow]
    · right; rw [hjo, zpow_add, zpow_mul, hz2', one_zpow, one_mul, zpow_one]
  have hRker : ∀ r ∈ R₀, π r = 1 → r = 1 ∨ r = z := fun r hr h => hSker r (hRS hr) h
  have hlift : ∀ P : Subgroup X, IsPGroup 2 ↥P → z ∈ P → ∀ y : X, (∃ n : ℕ, y ^ (2 ^ n) = 1) →
      π y ∈ P.map π → ∃ o ∈ O, o⁻¹ * y * o ∈ P := by
    intro P hP hzP y ⟨n, hyn⟩ hy
    obtain ⟨s, hsP, hsy⟩ := hy
    have h1 : π (y⁻¹ * s) = 1 := by rw [map_mul, map_inv, hsy, inv_mul_cancel]
    obtain ⟨j, o, ho, hjo⟩ :=
      Gen.exists_zpow_mul_of_mem_sup (x := z) (K := O) (fun k _ => hzc k) (hker _ h1)
    have hy' : y = (s * z ^ (-j)) * o⁻¹ := by
      have e1 : y = s * (y⁻¹ * s)⁻¹ := by group
      rw [e1, hjo]
      have hc : o⁻¹ * z ^ (-j) = z ^ (-j) * o⁻¹ :=
        ((show Commute o⁻¹ z from hzc o⁻¹).zpow_right (-j)).eq
      calc s * (z ^ j * o)⁻¹ = s * (o⁻¹ * z ^ (-j)) := by group
        _ = s * (z ^ (-j) * o⁻¹) := by rw [hc]
        _ = (s * z ^ (-j)) * o⁻¹ := by group
    have hyP : y ∈ O ⊔ P := by
      rw [sup_comm, hy']
      exact Subgroup.mul_mem_sup (P.mul_mem hsP (P.zpow_mem hzP _)) (O.inv_mem ho)
    obtain ⟨k, hk, hkP⟩ := Gen.exists_conj_mem_of_two_element hOodd hP
      (Gen.isPGroup_zpowers_of_pow hyn) hyP
    exact ⟨k, hk, hkP⟩
  have hSqp : IsPGroup 2 ↥(S₀.map π) := hS₀p.map π
  have hSqidx : ¬ 2 ∣ (S₀.map π).index := fun hd =>
    hS₀idx (hd.trans (Subgroup.index_map_dvd S₀ hπsurj))
  let Sq : Sylow 2 ((X ⧸ O) ⧸ A) := hSqp.toSylow hSqidx
  have hSq : (Sq : Subgroup ((X ⧸ O) ⧸ A)) = S₀.map π := rfl
  set I : Set X := {r : X | r ∈ R₀ ∧ r * r = 1 ∧ r ≠ 1 ∧ r ≠ z} with hI
  have hRsq : ∀ r ∈ R₀, π r * π r = 1 := by
    intro r hr
    rw [← map_mul]
    rcases hsq r hr with h | h
    · rw [h, map_one]
    · rw [h, hπz]
  have hRel : Open.IsElemAbelian 2 (R₀.map π) := by
    rw [isElemAbelian_iff]
    constructor
    · rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
      have h1 := hRsq (r * r') (R₀.mul_mem hr hr')
      have h2 := hRsq r hr
      have h3 := hRsq r' hr'
      rw [map_mul] at h1
      have ainv : (π r)⁻¹ = π r := inv_eq_of_mul_eq_one_right h2
      have binv : (π r')⁻¹ = π r' := inv_eq_of_mul_eq_one_right h3
      have h4 : (π r * π r')⁻¹ = π r * π r' := inv_eq_of_mul_eq_one_right h1
      rw [mul_inv_rev, ainv, binv] at h4
      exact h4.symm
    · rintro _ ⟨r, hr, rfl⟩
      rw [pow_two]
      exact hRsq r hr
  have hRker' : R₀ ⊓ π.ker = zpowers z := by
    apply le_antisymm
    · rintro r ⟨hr, hπr⟩
      rcases hRker r hr hπr with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · rintro w hw
      obtain ⟨k, rfl⟩ := hw
      refine ⟨R₀.zpow_mem hzR k, ?_⟩
      show π (z ^ k) = 1
      rw [map_zpow, hπz, one_zpow]
  have hRcard : Nat.card (R₀.map π) = 16 := by
    have := Gen.card_map_mul_card_inf_ker π R₀
    rw [hRker', Nat.card_zpowers, hzord, hR32] at this
    omega
  have hSker' : S₀ ⊓ π.ker = zpowers z := by
    apply le_antisymm
    · rintro r ⟨hr, hπr⟩
      rcases hSker r hr hπr with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · rintro w hw
      obtain ⟨k, rfl⟩ := hw
      refine ⟨S₀.zpow_mem (hRS hzR) k, ?_⟩
      show π (z ^ k) = 1
      rw [map_zpow, hπz, one_zpow]
  have hSq64 : Nat.card (S₀.map π) = 64 := by
    have := Gen.card_map_mul_card_inf_ker π S₀
    rw [hSker', Nat.card_zpowers, hzord, hS128] at this
    omega
  have hsc' : ∀ r ∈ R₀.map π, ∀ hq : (X ⧸ O) ⧸ A, hq⁻¹ * r * hq ∈ (Sq : Subgroup ((X ⧸ O) ⧸ A)) →
      hq⁻¹ * r * hq ∈ R₀.map π := by
    rintro _ ⟨r, hr, rfl⟩ hq hhq
    obtain ⟨h, rfl⟩ := hπsurj hq
    have hy : π (h⁻¹ * r * h) ∈ S₀.map π := by
      rw [map_mul, map_mul, map_inv]; exact hhq
    have hyn : ∃ n : ℕ, (h⁻¹ * r * h) ^ (2 ^ n) = 1 := by
      obtain ⟨n, hn⟩ := hS₀p ⟨r, hRS hr⟩
      refine ⟨n, ?_⟩
      have h1 : r ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
      have := conj_pow (a := h⁻¹) (b := r) (i := 2 ^ n)
      rw [inv_inv] at this
      rw [this, h1]; group
    obtain ⟨o, ho, hoS⟩ := hlift S₀ hS₀p (hRS hzR) _ hyn hy
    have hS : (h * o)⁻¹ * r * (h * o) ∈ S₀ := by
      have e : (h * o)⁻¹ * r * (h * o) = o⁻¹ * (h⁻¹ * r * h) * o := by group
      rw [e]; exact hoS
    have h3 := hsc r hr (h * o) hS
    refine ⟨(h * o)⁻¹ * r * (h * o), h3, ?_⟩
    simp [map_mul, map_inv, hπO o ho]
  have hσ : ∀ a ∈ I, a * z ∈ I := by
    rintro a ⟨ha, ha2, ha1, haz⟩
    refine ⟨R₀.mul_mem ha hzR, ?_, ?_, ?_⟩
    · calc a * z * (a * z) = a * (z * a) * z := by group
        _ = a * (a * z) * z := by rw [← hzc a]
        _ = (a * a) * (z * z) := by group
        _ = 1 := by rw [ha2, hzz, one_mul]
    · intro h
      apply haz
      have : a = z⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]; exact inv_eq_of_mul_eq_one_right hzz
    · intro h
      apply ha1
      have : a * z = 1 * z := by rw [h, one_mul]
      exact mul_right_cancel this
  have hσne : ∀ a ∈ I, a * z ≠ a := by
    intro a _ h
    apply hz1
    exact mul_left_cancel (show a * z = a * 1 by rw [mul_one]; exact h)
  have hfib : ∀ a ∈ I, ∀ b ∈ I, π a = π b ↔ b = a ∨ b = a * z := by
    intro a ha b hb
    constructor
    · intro hab
      have h1 : π (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
      have h2 : a⁻¹ * b ∈ R₀ := R₀.mul_mem (R₀.inv_mem ha.1) hb.1
      have hb' : b = a * (a⁻¹ * b) := by group
      rcases hRker _ h2 h1 with h | h
      · left; rw [hb', h, mul_one]
      · right; rw [hb', h]
    · rintro (rfl | rfl)
      · rfl
      · rw [map_mul, hπz, mul_one]
  set X₀ : Set ((X ⧸ O) ⧸ A) := π '' I with hX₀
  have hX₀R : X₀ ⊆ ((R₀.map π : Subgroup _) : Set ((X ⧸ O) ⧸ A)) := by
    rintro _ ⟨r, ⟨hr, -⟩, rfl⟩
    exact ⟨r, hr, rfl⟩
  have hX₀card : X₀.ncard = 5 := by
    have h := Gen.ncard_image_of_fibers_two π (Set.toFinite I) (fun r => r * z) hσ hσne hfib
    have h5 : (π '' I).ncard = 5 := by omega
    exact h5
  have hX₀ord : ∀ x ∈ X₀, orderOf x = 2 := by
    rintro _ ⟨r, ⟨hr, hr2, hr1, hrz⟩, rfl⟩
    have h1 : π r * π r = 1 := by rw [← map_mul, hr2, map_one]
    have h2 : π r ≠ 1 := fun h => by
      rcases hRker r hr h with h' | h'
      · exact hr1 h'
      · exact hrz h'
    exact orderOf_eq_prime (by rw [pow_two]; exact h1) h2
  have hX₀gen : Subgroup.closure X₀ = R₀.map π := by
    rw [hX₀, ← MonoidHom.map_closure, hIgen]
  have hX₀conj : ∀ x ∈ X₀, ∀ y ∈ X₀, ∃ h : (X ⧸ O) ⧸ A, h⁻¹ * x * h = y := by
    rintro _ ⟨r, ⟨hr, hr2, hr1, hrz⟩, rfl⟩ _ ⟨r', ⟨hr', hr'2, hr'1, hr'z⟩, rfl⟩
    obtain ⟨h, hh⟩ := hIconj r r' hr hr2 hr1 hrz hr' hr'2 hr'1 hr'z
    refine ⟨π h, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hh]
  have hX₀cl : ∀ x ∈ X₀, ∀ hq : (X ⧸ O) ⧸ A, hq⁻¹ * x * hq ∈ R₀.map π → hq⁻¹ * x * hq ∈ X₀ := by
    rintro _ ⟨r, ⟨hr, hr2, hr1, hrz⟩, rfl⟩ hq hhq
    obtain ⟨h, rfl⟩ := hπsurj hq
    have hy : π (h⁻¹ * r * h) ∈ R₀.map π := by
      rw [map_mul, map_mul, map_inv]; exact hhq
    have hyn : ∃ n : ℕ, (h⁻¹ * r * h) ^ (2 ^ n) = 1 := ⟨1, by
      rw [pow_one, pow_two]
      calc h⁻¹ * r * h * (h⁻¹ * r * h) = h⁻¹ * (r * r) * h := by group
        _ = 1 := by rw [hr2]; group⟩
    obtain ⟨o, ho, hoR⟩ := hlift R₀ hR2 hzR _ hyn hy
    refine ⟨o⁻¹ * (h⁻¹ * r * h) * o, ⟨hoR, ?_, ?_, ?_⟩, ?_⟩
    · calc o⁻¹ * (h⁻¹ * r * h) * o * (o⁻¹ * (h⁻¹ * r * h) * o)
          = o⁻¹ * h⁻¹ * (r * r) * h * o := by group
        _ = 1 := by rw [hr2]; group
    · intro h1
      apply hr1
      have : r = h * o * (o⁻¹ * (h⁻¹ * r * h) * o) * (h * o)⁻¹ := by group
      rw [this, h1]; group
    · intro h1
      apply hrz
      have : r = h * o * (o⁻¹ * (h⁻¹ * r * h) * o) * (h * o)⁻¹ := by group
      rw [this, h1]
      have hc := hzc (h * o)
      calc h * o * z * (h * o)⁻¹ = z * (h * o) * (h * o)⁻¹ := by rw [← hc]
        _ = z := by group
    · simp [map_mul, map_inv, hπO o ho]
  have hGH' : SU0.GHGroup ((X ⧸ O) ⧸ A) := (hGH.quotient O).quotient A
  have key := hKI4 ((X ⧸ O) ⧸ A) hGH' hOH Sq (R₀.map π) (hSq ▸ Subgroup.map_mono hRS) hRel hRcard
    hsc' X₀ hX₀R hX₀card hX₀ord hX₀gen hX₀conj hX₀cl
  have hOH' : ∀ N : Subgroup ((X ⧸ O) ⧸ A), N.Normal → Odd (Nat.card N) → N = ⊥ :=
    fun N hN hodd => CFSG.pPrimeCore_eq_bot_iff.1 hOH N hN (Nat.coprime_two_left.2 hodd)
  have hX₀cl' : ∀ x ∈ X₀, ∀ q : (X ⧸ O) ⧸ A, q * x * q⁻¹ ∈ X₀ := by
    intro x hx q
    have h1 : (q⁻¹)⁻¹ * x * q⁻¹ ∈ R₀.map π := key q⁻¹ x (hX₀R hx)
    have h2 := hX₀cl x hx q⁻¹ h1
    simpa using h2
  have hX₀conj' : ∀ x ∈ X₀, ∀ y ∈ X₀, ∃ q : (X ⧸ O) ⧸ A, q * x * q⁻¹ = y := by
    intro x hx y hy
    obtain ⟨q, hq⟩ := hX₀conj x hx y hy
    exact ⟨q⁻¹, by simpa using hq⟩
  have hfaith' : ∀ s ∈ S₀.map π, (∀ r ∈ R₀.map π, s * r = r * s) → s ∈ R₀.map π := by
    rintro _ ⟨s₀, hs₀, rfl⟩ hc
    have hs₀R : s₀ ∈ R₀ := by
      refine hfaith s₀ hs₀ (fun r hr => ?_)
      have hcomm' := hc (π r) ⟨r, hr, rfl⟩
      have hw : π (s₀ * r * s₀⁻¹ * r⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm']
        group
      exact hRker _ (R₀.mul_mem (hRnS s₀ hs₀ r hr) (R₀.inv_mem hr)) hw
    exact Subgroup.mem_map_of_mem π hs₀R
  have hsq' : ∀ s ∈ S₀.map π, s * s ∈ R₀.map π := by
    rintro _ ⟨s₀, hs₀, rfl⟩
    rw [← map_mul]
    exact Subgroup.mem_map_of_mem π (hsq2 s₀ hs₀)
  obtain ⟨ρ, hρact, hρker, ⟨e⟩⟩ := Rep.rep_A5 hOH' hSqp hSqidx (Subgroup.map_mono hRS)
    (isElemAbelian_iff.1 hRel).1 hRcard hX₀R hX₀card hX₀gen hX₀cl' hX₀conj' hfaith' hSq64 hsq'
  have hpre : ∀ w : X, π w ∈ R₀.map π → w ∈ R₀ ⊔ O := by
    intro w h4
    obtain ⟨r₁, hr₁, hr₁π⟩ := h4
    have h5 : π (r₁⁻¹ * w) = 1 := by rw [map_mul, map_inv, hr₁π, inv_mul_cancel]
    have h6 := hker _ h5
    have hW : r₁⁻¹ * w ∈ R₀ ⊔ O := (sup_le_sup_right (Subgroup.zpowers_le.2 hzR) O) h6
    have : w = r₁ * (r₁⁻¹ * w) := by group
    rw [this]
    exact (R₀ ⊔ O).mul_mem (Subgroup.mem_sup_left hr₁) hW
  refine ⟨e.toMonoidHom.comp (ρ.rangeRestrict.comp π),
    e.surjective.comp (ρ.rangeRestrict_surjective.comp hπsurj), ?_, ?_⟩
  · ext w
    constructor
    · intro hw
      have h1 : e (ρ.rangeRestrict (π w)) = 1 := hw
      have h2 : ρ.rangeRestrict (π w) = 1 := (MulEquiv.map_eq_one_iff e).1 h1
      have h3 : ρ (π w) = 1 := congrArg Subtype.val h2
      have h4 : π w ∈ ρ.ker := h3
      rw [hρker] at h4
      exact hpre w h4
    · intro hw
      have hmem : π w ∈ R₀.map π := by
        have hle : R₀ ⊔ O ≤ (R₀.map π).comap π := by
          refine sup_le ?_ ?_
          · intro r hr
            exact Subgroup.mem_map_of_mem π hr
          · intro o ho
            show π o ∈ R₀.map π
            rw [hπO o ho]
            exact one_mem _
        exact hle hw
      rw [← hρker] at hmem
      have h3 : ρ (π w) = 1 := hmem
      show e (ρ.rangeRestrict (π w)) = 1
      rw [MulEquiv.map_eq_one_iff e]
      exact Subtype.ext h3
  · intro c hc
    apply hpre
    rw [← hρker, MonoidHom.mem_ker]
    apply Equiv.ext
    rintro ⟨y, hy⟩
    obtain ⟨r, ⟨hrR, hr2, hr1, hrz⟩, rfl⟩ := hy
    apply Subtype.ext
    have h1 : π (c * r * c⁻¹ * r⁻¹) = 1 := hπO _ (hc r hrR)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    rw [hρact]
    show π c * π r * (π c)⁻¹ = π r
    calc π c * π r * (π c)⁻¹ = (π c * π r * (π c)⁻¹ * (π r)⁻¹) * π r := by group
      _ = π r := by rw [h1, one_mul]

end CFSG.GH74.Uniqueness.SU.SU7.Sec
