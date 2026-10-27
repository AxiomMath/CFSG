module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf32Psi

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace Out

theorem q8_center : ∀ q : Q8, (∀ y : Q8, q * y = y * q) → q = 1 ∨ q = QuaternionGroup.a 2 := by
  decide +kernel

theorem q8_sq_central : ∀ q y : Q8, q * q * y = y * (q * q) := by decide +kernel

end Out

open Out


variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

section Outer

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem z_comm_sup {y : G} (hy : y ∈ K ⊔ K') : z * y = y * z :=
  Subgroup.mem_centralizer_singleton_iff.mp (d.sup_le_centralizer_z hy) |>.symm

theorem exists_central_mul_oddCore {k : G} (hk : k ∈ K) (htr : k ∈ trivialOnQuot K) :
    ∃ c : G, (c = 1 ∨ c = z) ∧ ∃ n ∈ oddCoreOf K, k = c * n := by
  obtain ⟨e⟩ := kbar_equiv_q8 d
  have hzK : z ∈ K := d.viol.hzK.mem
  let mkK : ↥K →* Kbar K := QuotientGroup.mk' _
  have hcentral : ∀ (k₀ : G) (hk₀ : k₀ ∈ K), (∀ y ∈ K, ⁅k₀, y⁆ ∈ oddCoreOf K) →
      ∀ y : Kbar K, mkK ⟨k₀, hk₀⟩ * y = y * mkK ⟨k₀, hk₀⟩ := by
    intro k₀ hk₀ h y
    induction y using QuotientGroup.induction_on with
    | H y' =>
      show (QuotientGroup.mk (⟨k₀, hk₀⟩ * y') : Kbar K) = QuotientGroup.mk (y' * ⟨k₀, hk₀⟩)
      rw [QuotientGroup.eq_iff_div_mem]
      refine (mem_oddCoreOf_iff K _).mp ?_
      have := h y' y'.2
      simpa [commutatorElement_def, div_eq_mul_inv, mul_assoc] using this
  have hz1 : mkK ⟨z, hzK⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨z, hzK⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : z ∈ oddCoreOf K := (mem_oddCoreOf_iff K _).mpr h2
    have h4 : orderOf z ∣ Nat.card (oddCoreOf K) := Subgroup.orderOf_dvd_natCard _ h3
    have h5 : orderOf z = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact d.viol.hzK.sq) d.viol.hzK.ne_one
    rw [h5] at h4
    have := Odd.of_dvd_nat (oddCoreOf_odd_natCard K) h4
    exact (Nat.not_even_iff_odd.mpr this) even_two
  have hzc : ∀ y : Kbar K, mkK ⟨z, hzK⟩ * y = y * mkK ⟨z, hzK⟩ := by
    refine hcentral z hzK (fun y hy => ?_)
    have : ⁅z, y⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact z_comm_sup d (Subgroup.mem_sup_left hy)
    rw [this]; exact (oddCoreOf K).one_mem
  have hkc := hcentral k hk htr.2
  have ez : e (mkK ⟨z, hzK⟩) = QuaternionGroup.a 2 := by
    rcases q8_center _ (fun y => by
        have := hzc (e.symm y)
        simpa using congrArg e this) with h | h
    · exact absurd (e.injective (by rw [h, map_one])) hz1
    · exact h
  have ek : e (mkK ⟨k, hk⟩) = 1 ∨ e (mkK ⟨k, hk⟩) = QuaternionGroup.a 2 := by
    refine q8_center _ (fun y => ?_)
    have := hkc (e.symm y)
    simpa using congrArg e this
  rcases ek with h | h
  · have h1 : mkK ⟨k, hk⟩ = 1 := e.injective (by rw [h, map_one])
    have h2 : (⟨k, hk⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨1, Or.inl rfl, k, (mem_oddCoreOf_iff K _).mpr h2, by simp⟩
  · have h1 : mkK ⟨k, hk⟩ = mkK ⟨z, hzK⟩ := e.injective (by rw [h, ez])
    have h2 := (QuotientGroup.eq_iff_div_mem).mp h1
    have h3 := (mem_oddCoreOf_iff K _).mpr h2
    have hcomm : z * k = k * z := z_comm_sup d (Subgroup.mem_sup_left hk)
    refine ⟨z, Or.inr rfl, k * z⁻¹, ?_, ?_⟩
    · simpa [div_eq_mul_inv] using h3
    · rw [← mul_assoc, hcomm, mul_inv_cancel_right]

theorem sq_comm_of_one_or_z {c : G} (hc : c = 1 ∨ c = z) :
    c * c = 1 ∧ ∀ y ∈ K ⊔ K', c * y = y * c := by
  rcases hc with h | h
  · rw [h]; exact ⟨by simp, fun y _ => by simp⟩
  · rw [h]; exact ⟨d.viol.hzK.sq, fun y hy => z_comm_sup d hy⟩

theorem not_trivialOnQuot_of_invol {s : G} (hs : s ∈ K ⊔ K') (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hsz : s ≠ z) : s ∉ trivialOnQuot K := by
  intro htr
  have hs' : s ∈ ((K ⊔ K' : Subgroup G) : Set G) := hs
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K K' d.late_K_le] at hs'
  obtain ⟨k₁, hk₁, k₂, hk₂, hsk⟩ := hs'
  have hk₁tr : k₁ ∈ trivialOnQuot K := by
    have e : k₁ = s * k₂⁻¹ := by rw [← hsk]; group
    rw [e]
    exact (trivialOnQuot K).mul_mem htr ((trivialOnQuot K).inv_mem (le_trivialOnQuot_K d hk₂))
  obtain ⟨c, hc, n₁, hn₁, hk₁e⟩ := exists_central_mul_oddCore d hk₁ hk₁tr
  obtain ⟨hcc, hccomm⟩ := sq_comm_of_one_or_z d hc
  have hn₁K : n₁ ∈ K := oddCoreOf_le_self K hn₁
  have hcs : c * s = n₁ * k₂ := by
    rw [← hsk, hk₁e, ← mul_assoc, ← mul_assoc, hcc, one_mul]
  have hs'2 : (n₁ * k₂) * (n₁ * k₂) = 1 := by
    rw [← hcs]
    calc c * s * (c * s) = c * (s * c) * s := by group
      _ = c * (c * s) * s := by rw [hccomm s hs]
      _ = (c * c) * (s * s) := by group
      _ = 1 := by rw [hcc, hs2, one_mul]
  have hkN : k₂ ∈ Subgroup.normalizer (oddCoreOf K : Set G) :=
    mem_normalizer_oddCore_of_mem_normalizer (d.late_K'_le hk₂)
  have hn₁' : k₂ * n₁ * k₂⁻¹ ∈ oddCoreOf K := (Subgroup.mem_normalizer_iff.mp hkN n₁).mp hn₁
  have hk₂sq : k₂ * k₂ ∈ oddCoreOf K := by
    have e : (n₁ * (k₂ * n₁ * k₂⁻¹)) * (k₂ * k₂) = 1 := by
      calc (n₁ * (k₂ * n₁ * k₂⁻¹)) * (k₂ * k₂) = (n₁ * k₂) * (n₁ * k₂) := by group
        _ = 1 := hs'2
    have := eq_inv_of_mul_eq_one_right e
    rw [this]
    exact (oddCoreOf K).inv_mem ((oddCoreOf K).mul_mem hn₁ hn₁')
  have hm₀ : Odd (orderOf (k₂ * k₂)) :=
    Odd.of_dvd_nat (oddCoreOf_odd_natCard K) (Subgroup.orderOf_dvd_natCard _ hk₂sq)
  set m₀ := orderOf (k₂ * k₂) with hm₀def
  have hpow : (k₂ * k₂) ^ m₀ = 1 := pow_orderOf_eq_one _
  have hx2 : k₂ ^ m₀ * k₂ ^ m₀ = 1 := by
    calc k₂ ^ m₀ * k₂ ^ m₀ = k₂ ^ (m₀ + m₀) := (pow_add _ _ _).symm
      _ = k₂ ^ (2 * m₀) := by rw [two_mul]
      _ = (k₂ ^ 2) ^ m₀ := pow_mul _ _ _
      _ = (k₂ * k₂) ^ m₀ := by rw [pow_two]
      _ = 1 := hpow
  have hxK' : k₂ ^ m₀ ∈ K' := K'.pow_mem hk₂ _
  have hx : k₂ ^ m₀ = 1 ∨ k₂ ^ m₀ = z := d.late_hzK'.unique _ hxK' hx2
  obtain ⟨r, hr⟩ := hm₀
  have hy : k₂ ^ (m₀ + 1) ∈ oddCoreOf K := by
    have : k₂ ^ (m₀ + 1) = (k₂ * k₂) ^ (r + 1) := by
      calc k₂ ^ (m₀ + 1) = k₂ ^ (2 * (r + 1)) := by rw [show m₀ + 1 = 2 * (r + 1) by omega]
        _ = (k₂ ^ 2) ^ (r + 1) := pow_mul _ _ _
        _ = (k₂ * k₂) ^ (r + 1) := by rw [pow_two]
    rw [this]
    exact (oddCoreOf K).pow_mem hk₂sq _
  have hk₂xy : k₂ = k₂ ^ m₀ * k₂ ^ (m₀ + 1) := by
    calc k₂ = (k₂ * k₂) ^ m₀ * k₂ := by rw [hpow, one_mul]
      _ = k₂ ^ (2 * m₀) * k₂ := by rw [pow_mul, pow_two]
      _ = k₂ ^ (2 * m₀ + 1) := (pow_succ _ _).symm
      _ = k₂ ^ (m₀ + (m₀ + 1)) := by rw [show m₀ + (m₀ + 1) = 2 * m₀ + 1 by omega]
      _ = k₂ ^ m₀ * k₂ ^ (m₀ + 1) := pow_add _ _ _
  obtain ⟨hxx, hxcomm⟩ := sq_comm_of_one_or_z d hx
  have hyK : k₂ ^ (m₀ + 1) ∈ K := oddCoreOf_le_self K hy
  set x := k₂ ^ m₀ with hxdef
  set y := k₂ ^ (m₀ + 1) with hydef
  have hn₁sup : n₁ ∈ K ⊔ K' := Subgroup.mem_sup_left hn₁K
  have hysup : y ∈ K ⊔ K' := Subgroup.mem_sup_left hyK
  have hcx : ∃ c' : G, (c' = 1 ∨ c' = z) ∧ c * x = c' := by
    rcases hc with h1 | h1 <;> rcases hx with h2 | h2
    · exact ⟨1, Or.inl rfl, by rw [h1, h2, one_mul]⟩
    · exact ⟨z, Or.inr rfl, by rw [h1, h2, one_mul]⟩
    · exact ⟨z, Or.inr rfl, by rw [h1, h2, mul_one]⟩
    · exact ⟨1, Or.inl rfl, by rw [h1, h2]; exact d.viol.hzK.sq⟩
  obtain ⟨c', hc', hcxc⟩ := hcx
  obtain ⟨hc'c', hc'comm⟩ := sq_comm_of_one_or_z d hc'
  have hsq : s = c' * (n₁ * y) := by
    calc s = k₁ * k₂ := hsk.symm
      _ = c * n₁ * (x * y) := by rw [hk₁e, ← hk₂xy]
      _ = c * (n₁ * x) * y := by group
      _ = c * (x * n₁) * y := by rw [hxcomm n₁ hn₁sup]
      _ = (c * x) * (n₁ * y) := by group
      _ = c' * (n₁ * y) := by rw [hcxc]
  have hqmem : n₁ * y ∈ oddCoreOf K := (oddCoreOf K).mul_mem hn₁ hy
  have hqq : (n₁ * y) * (n₁ * y) = 1 := by
    have h1 : s * s = (c' * c') * ((n₁ * y) * (n₁ * y)) := by
      calc s * s = c' * (n₁ * y) * (c' * (n₁ * y)) := by rw [← hsq]
        _ = c' * ((n₁ * y) * c') * (n₁ * y) := by group
        _ = c' * (c' * (n₁ * y)) * (n₁ * y) := by
            rw [hc'comm (n₁ * y) ((oddCoreOf_le_self K).trans le_sup_left hqmem)]
        _ = (c' * c') * ((n₁ * y) * (n₁ * y)) := by group
    rw [hs2, hc'c', one_mul] at h1
    exact h1.symm
  have hq1 : n₁ * y = 1 := by
    have h2 : orderOf (n₁ * y) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hqq)
    have h3 : Odd (orderOf (n₁ * y)) :=
      Odd.of_dvd_nat (oddCoreOf_odd_natCard K) (Subgroup.orderOf_dvd_natCard _ hqmem)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h3
      exact absurd h3 (by decide)
  rw [hq1, mul_one] at hsq
  rcases hc' with h | h
  · exact hs1 (hsq.trans h)
  · exact hsz (hsq.trans h)

theorem sq_mem_trivialOnQuot_of_innerOn {u : G} (hu : u ∈ Subgroup.normalizer (K : Set G))
    (h : InnerOn K u) : u * u ∈ trivialOnQuot K := by
  obtain ⟨e⟩ := kbar_equiv_q8 d
  obtain ⟨k, hk, hkk⟩ := h
  have h1 : rhoK K ⟨u, hu⟩ = MulAut.conj (QuotientGroup.mk ⟨k, hk⟩ : Kbar K) :=
    (rhoK_eq_conj_iff K ⟨u, hu⟩ ⟨k, hk⟩).mpr (fun y => hkk y y.2)
  have huu : u * u ∈ Subgroup.normalizer (K : Set G) := (Subgroup.normalizer (K : Set G)).mul_mem hu hu
  have h2 : rhoK K ⟨u * u, huu⟩ = MulAut.conj (1 : Kbar K) := by
    have e1 : (⟨u * u, huu⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨u, hu⟩ * ⟨u, hu⟩ := rfl
    rw [e1, map_mul, h1, ← map_mul, map_one]
    apply MulEquiv.ext
    intro y
    simp only [MulAut.conj_apply, inv_one, mul_one, one_mul]
    set q : Kbar K := QuotientGroup.mk ⟨k, hk⟩ with hq
    have hc : (q * q) * y = y * (q * q) := by
      apply e.injective
      simp only [map_mul]
      exact q8_sq_central _ _
    rw [hc, mul_inv_cancel_right]
    rfl
  refine ⟨huu, fun y hy => ?_⟩
  have h4 := (rhoK_eq_conj_iff K ⟨u * u, huu⟩ 1).mp (by
    rw [h2]; simp) ⟨y, hy⟩
  simpa [commutatorElement_def, oddCoreIn_eq_oddCoreOf] using h4

omit d in
theorem innerOn_swap' {g x : G} {K : Subgroup G} (h : InnerOn (conjSub g K) x) :
    InnerOn K (g⁻¹ * x * g) := by
  have h' : InnerOn (conjSub g K) ((g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹) := by
    have e : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]; exact h
  have := innerOn_swap h'
  rwa [conjSub_inv_conjSub] at this

omit d in
theorem frame203Outer : Frame203Outer := by
  intro G _ _ _ K K' J S R R' W V z t d w hwV hw2
  obtain ⟨g, hg, hgK⟩ := d.swap
  have hXN := frameX_le_N d
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  have hwX : w ∈ sec20X (CoreAssembly.conjClass K) z K K' := tw.hVX hwV
  have hcR := Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ d.hV d.late_mem_K d.hR
  have hV4 : Nat.card V = 4 := by rw [d.card8] at hcR; omega
  have hw4 : w ^ 4 = 1 := by
    have := pow_card_eq_one' (G := ↥V) (x := ⟨w, hwV⟩)
    rw [hV4] at this
    simpa using congrArg Subtype.val this
  have hww : (w * w) * (w * w) = 1 := by
    calc (w * w) * (w * w) = w ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := hw4
  have hwt : w * w = t := d.eq_t_of_invol_mem_V (V.mul_mem hwV hwV) hww hw2
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  have ht1 : t ≠ 1 := d.viol.hzJ.ne_one
  have htz : t ≠ z := d.late_ne_inv
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := sq_mem_trivialOnQuot_of_innerOn d (hXN hwX) h
    rw [hwt] at this
    exact not_trivialOnQuot_of_invol d d.htKK ht2 ht1 htz this
  · have hw' : g⁻¹ * w * g ∈ Subgroup.normalizer (K : Set G) :=
      conj_swap_mem_normalizer d hg hgK ((sec20X_le_normalizers_frame d) hwX).2
    rw [← hgK] at h
    have h' := innerOn_swap' h
    have := sq_mem_trivialOnQuot_of_innerOn d hw' h'
    have e : (g⁻¹ * w * g) * (g⁻¹ * w * g) = g⁻¹ * t * g := by
      rw [← hwt]; group
    rw [e] at this
    refine not_trivialOnQuot_of_invol d (conj_swap_sup d hg hgK d.htKK) ?_ ?_ ?_ this
    · calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [ht2]; group
    · intro h1
      apply ht1
      have : t = g * 1 * g⁻¹ := by rw [← h1]; group
      simpa using this
    · intro h1
      apply htz
      have hgz : g * z = z * g := (Subgroup.mem_centralizer_singleton_iff.mp hg).symm.symm
      have : t = g * z * g⁻¹ := by rw [← h1]; group
      rw [this, hgz]; group

end Outer


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
