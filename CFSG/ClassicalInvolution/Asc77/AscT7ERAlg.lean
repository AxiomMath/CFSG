module

public import CFSG.ClassicalInvolution.Asc77.AscL62Quat
import CFSG.ClassicalInvolution.Asc77.AscT7ASetup

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace T7ER

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_sq {b : G} (hb : b * b = 1) : IsPGroup 2 (Subgroup.zpowers b) := by
  have hdvd : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hb)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)

theorem exists_conj_eq_mul_inv {R : Subgroup G} (hR : IsQuatSub R) {z₀ : G}
    (hz₀ : IsUniqueInvolution R z₀) {b : G} (hb2 : b * b = 1)
    (hbR : ∀ r ∈ R, b * r * b⁻¹ ∈ R) (hfix : ∀ x ∈ R, orderOf x = 4 → b * x * b⁻¹ ≠ x) :
    ∃ ρ ∈ R, b * ρ * b⁻¹ = ρ * z₀ := by
  have hbN : b ∈ Subgroup.normalizer (R : Set G) := Subgroup.mem_normalizer_fintype hbR
  have hV2 := isPGroup_zpowers_of_sq hb2
  have hVR : ∀ y ∈ Subgroup.zpowers b, conjSub y R = R := fun y hy =>
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.zpowers_le.mpr hbN) hy)
  obtain ⟨C, hCR, hCc, hCcard, hCinv⟩ := AscL62.exists_invariant_cyclic hR hz₀ hV2 hVR
  have hbC : conjSub b C = C := hCinv b (Subgroup.mem_zpowers b)
  have hbCm : ∀ x ∈ C, b * x * b⁻¹ ∈ C := fun x hx => by
    have := conj_mem_conjSub (n := b) hx
    rwa [hbC] at this
  obtain ⟨k, hk, hkc⟩ := hR.natCard_eq
  have hCk : Nat.card C = 2 ^ (k + 1) := by
    have : 2 * Nat.card C = 2 * 2 ^ (k + 1) := by rw [← hCcard, hkc]; ring
    omega
  have h4 : 4 ∣ Nat.card C := by
    rw [hCk]
    exact (pow_dvd_pow 2 (by omega : 2 ≤ k + 1) : 2 ^ 2 ∣ 2 ^ (k + 1))
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
  have hgord : orderOf (g : G) = Nat.card C := by
    rw [Subgroup.orderOf_coe]; exact orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨m, hm⟩ := h4
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card C := Nat.card_pos
    omega
  set u : G := (g : G) ^ m with hu
  have huC : u ∈ C := C.pow_mem g.2 m
  have hu4 : orderOf u = 4 := by
    rw [hu, orderOf_pow_of_dvd hm0 ⟨4, by rw [hgord, hm]; ring⟩, hgord, hm]
    exact Nat.mul_div_cancel 4 (Nat.pos_of_ne_zero hm0)
  have hb1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  obtain ⟨j, hj⟩ : ∃ j : ℤ, b * (g : G) * b⁻¹ = (g : G) ^ j := by
    have hmem : b * (g : G) * b⁻¹ ∈ C := hbCm _ g.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨_, hmem⟩)
    exact ⟨j, by simpa using (congrArg Subtype.val hj).symm⟩
  have hτu : b * u * b⁻¹ = u ^ j := by
    have h1 : b * u * b⁻¹ = (b * (g : G) * b⁻¹) ^ m := by
      rw [hu]
      exact (conj_pow : (b * (g : G) * b⁻¹) ^ m = b * (g : G) ^ m * b⁻¹).symm
    rw [h1, hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hu, zpow_natCast]
  have huR : u ∈ R := hCR huC
  have hsq : u * u = z₀ := T7A.sq_eq_of_orderOf_four hz₀ huR hu4
  have hτo : orderOf (u ^ j) = 4 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj b) u
    simp only [MulAut.conj_apply] at h1
    rw [← hτu, h1, hu4]
  have hmod : u ^ j = u ^ (j % 4) := by
    have h1 := zpow_mod_orderOf u j
    rw [hu4] at h1
    simpa using h1.symm
  have hcases : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  · exfalso
    rw [hmod, h] at hτo
    simp at hτo
  · exfalso
    rw [hmod, h, zpow_one] at hτu
    exact hfix u huR hu4 hτu
  · exfalso
    have h4' : u ^ 4 = 1 := by
      have := pow_orderOf_eq_one u
      rwa [hu4] at this
    have h1 : (u ^ j) ^ 2 = 1 := by
      rw [hmod, h]
      have : (u ^ (2 : ℤ)) ^ 2 = u ^ 4 := by
        rw [← zpow_natCast, ← zpow_mul]
        norm_num
      rw [this, h4']
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hτo] at h2
    omega
  · refine ⟨u, huR, ?_⟩
    rw [hτu, hmod, h]
    have : u ^ (3 : ℤ) = u * (u * u) := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_succ, pow_two]
      simp [mul_assoc]
    rw [this, hsq]

theorem exists_orderOf_four_of_cyclic {C : Subgroup G} (hC : IsCyclic ↥C) (h4 : 4 ∣ Nat.card C) :
    ∃ u ∈ C, orderOf u = 4 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
  have hord : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨m, hm⟩ := h4
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card C := Nat.card_pos
    omega
  refine ⟨((g ^ m : ↥C) : G), (g ^ m).2, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd hm0 ⟨4, by rw [hord, hm]; ring⟩, hord, hm]
  exact Nat.mul_div_cancel 4 (Nat.pos_of_ne_zero hm0)

omit [Finite G] in
theorem eq_one_or_of_fixed {R : Subgroup G} (hR : IsQuatSub R) {z₀ : G}
    (hz₀ : IsUniqueInvolution R z₀) {b : G}
    (hfix : ∀ x ∈ R, orderOf x = 4 → b * x * b⁻¹ ≠ x) {w : G} (hw : w ∈ R)
    (hbw : b * w * b⁻¹ = w) : w = 1 ∨ w = z₀ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := AscL62.orderOf_eq_two_pow_of_isQuatSub hR hw
  have hw1 : w ≠ 1 := hcon.1
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hw1 (orderOf_eq_one_iff.mp (by simpa using hj))
  have hj1 : j ≠ 1 := by
    rintro rfl
    have hsq : w * w = 1 := by
      have := pow_orderOf_eq_one w
      rw [hj, pow_one, pow_two] at this
      exact this
    rcases hz₀.unique w hw hsq with h | h
    · exact hcon.1 h
    · exact hcon.2 h
  have hj2 : 2 ≤ j := by omega
  have hdvd : 2 ^ (j - 2) ∣ orderOf w := by
    rw [hj]; exact pow_dvd_pow 2 (by omega)
  have hw4 : orderOf (w ^ 2 ^ (j - 2)) = 4 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hj]
    have : 2 ^ j = 2 ^ (j - 2) * 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    rw [this]
    exact Nat.mul_div_cancel_left 4 (by positivity)
  refine hfix _ (R.pow_mem hw _) hw4 ?_
  rw [← conj_pow, hbw]

theorem exists_twist_orderOf_four {R : Subgroup G} (hR : IsQuatSub R) {z₀ : G}
    (hz₀ : IsUniqueInvolution R z₀) {b : G} (hbR : ∀ r ∈ R, b * r * b⁻¹ ∈ R)
    (hfix : ∀ x ∈ R, orderOf x = 4 → b * x * b⁻¹ ≠ x) :
    ∃ x ∈ R, orderOf ((b * x * b⁻¹)⁻¹ * x) = 4 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hCR, hCc, hCcard⟩ := hR.exists_cyclic_index_two
  obtain ⟨k, hk, hkc⟩ := hR.natCard_eq
  have hCk : Nat.card C = 2 ^ (k + 1) := by
    have : 2 * Nat.card C = 2 * 2 ^ (k + 1) := by rw [← hCcard, hkc]; ring
    omega
  have h4 : 4 ∣ Nat.card C := by
    rw [hCk]
    exact (pow_dvd_pow 2 (by omega : 2 ≤ k + 1) : 2 ^ 2 ∣ 2 ^ (k + 1))
  obtain ⟨u, huC, hu4⟩ := exists_orderOf_four_of_cyclic hCc h4
  have huR : u ∈ R := hCR huC
  have hsq : ∀ g ∈ R, g ∉ C → orderOf g = 4 := by
    intro g hg hgC
    have h1 : g * g = z₀ := AscL62.sq_eq_of_not_mem hR hz₀ hCR hCc hCcard hg hgC
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · rw [pow_one, pow_two, h1]; exact hz₀.ne_one
    · have : g ^ 2 ^ (1 + 1) = (g * g) * (g * g) := by
        rw [show 2 ^ (1 + 1) = 4 by norm_num]
        simp [pow_succ, mul_assoc]
      rw [this, h1]; exact hz₀.sq
  have : Fintype ↥R := Fintype.ofFinite _
  let τ : ↥R → ↥R := fun x => ⟨b * (x : G) * b⁻¹, hbR x x.2⟩
  let c : ↥R → ↥R := fun x => (τ x)⁻¹ * x
  let Cf : Finset ↥R := Finset.univ.filter (fun x => (x : G) ∈ C)
  let N : Finset ↥R := Finset.univ.filter (fun x => orderOf (x : G) ≠ 4)
  let u0 : ↥R := ⟨u, huR⟩
  let u1 : ↥R := ⟨u⁻¹, R.inv_mem huR⟩
  have hu01 : u1 ≠ u0 := by
    intro h
    have h' : u⁻¹ = u := congrArg Subtype.val h
    have : u * u = 1 := by
      calc u * u = u * u⁻¹ := by rw [h']
        _ = 1 := mul_inv_cancel u
    have h3 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact this)
    rw [hu4] at h3
    omega
  have hu0C : u0 ∈ Cf := by simp [Cf, u0, huC]
  have hu1C : u1 ∈ Cf := by simp [Cf, u1, C.inv_mem huC]
  have hCf : Cf.card = Nat.card C := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr
      ⟨fun x => ⟨(x.1 : G), (Finset.mem_filter.mp x.2).2⟩,
        fun y => ⟨⟨y.1, hCR y.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2⟩⟩,
        fun _ => rfl, fun _ => rfl⟩
  have hunivcard : (Finset.univ : Finset ↥R).card = 2 * Nat.card C := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hCcard]
  have hNsub : N ⊆ (Cf.erase u0).erase u1 := by
    intro x hx
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Cf, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      apply hx
      have : (x : G) = u⁻¹ := congrArg Subtype.val h
      rw [this, orderOf_inv, hu4]
    · intro h
      apply hx
      have : (x : G) = u := congrArg Subtype.val h
      rw [this, hu4]
    · by_contra hxC
      exact hx (hsq x x.2 hxC)
  have hNcard : N.card + 2 ≤ Cf.card := by
    have h1 : ((Cf.erase u0).erase u1).card = Cf.card - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hu01, hu1C⟩),
        Finset.card_erase_of_mem hu0C]
      omega
    have h2 := Finset.card_le_card hNsub
    have h3 : 2 ≤ Cf.card := by
      have := Finset.card_le_card (show ({u0, u1} : Finset ↥R) ⊆ Cf by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hu0C
        · exact hu1C)
      rwa [Finset.card_pair hu01.symm] at this
    omega
  have himg : Finset.univ.image c ⊆ N := by
    intro a ha
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcon x x.2
  have hfib : ∀ a ∈ Finset.univ.image c, (Finset.univ.filter (fun x => c x = a)).card ≤ 2 := by
    intro a ha
    obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp ha
    refine (Finset.card_le_card (t := {x₀, ⟨z₀, hz₀.mem⟩ * x₀}) ?_).trans Finset.card_le_two
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have h := congrArg Subtype.val hx
    simp only [c, τ, Subgroup.coe_mul, Subgroup.coe_inv] at h
    have hw : b * ((x : G) * (x₀ : G)⁻¹) * b⁻¹ = (x : G) * (x₀ : G)⁻¹ := by
      have h1 : (x : G) = (b * (x : G) * b⁻¹) * ((b * (x₀ : G) * b⁻¹)⁻¹ * (x₀ : G)) := by
        rw [← h]; group
      calc b * ((x : G) * (x₀ : G)⁻¹) * b⁻¹
          = (b * (x : G) * b⁻¹) * (b * (x₀ : G) * b⁻¹)⁻¹ := by group
        _ = (x : G) * (x₀ : G)⁻¹ := by
          conv_rhs => rw [h1]
          group
    have hwR : (x : G) * (x₀ : G)⁻¹ ∈ R := R.mul_mem x.2 (R.inv_mem x₀.2)
    rcases eq_one_or_of_fixed hR hz₀ hfix hwR hw with h2 | h2
    · left
      apply Subtype.ext
      have : (x : G) = (x₀ : G) := by
        have := congrArg (fun y => y * (x₀ : G)) h2
        simpa using this
      exact this
    · right
      apply Subtype.ext
      have : (x : G) = z₀ * (x₀ : G) := by
        have := congrArg (fun y => y * (x₀ : G)) h2
        simpa using this
      exact this
  have hmain := Finset.card_le_mul_card_image (Finset.univ : Finset ↥R) 2 hfib
  have himgcard := Finset.card_le_card himg
  have h5 : 4 ≤ Nat.card C := by
    have := hR.eight_le
    omega
  omega

theorem exists_twisted_conj {R R' : Subgroup G} {z t : G} (hRq : IsQuatSub R)
    (hR'q : IsQuatSub R') (hzR : IsUniqueInvolution R z) (hzR' : IsUniqueInvolution R' z)
    (hc : Commutes R R') (hinf : ∀ y ∈ R, y ∈ R' → orderOf y ≠ 4) (ht2 : t * t = 1)
    (htR : ∀ r ∈ R, t * r * t⁻¹ ∈ R) (htR' : ∀ r ∈ R', t * r * t⁻¹ ∈ R')
    (hfixR : ∀ x ∈ R, orderOf x = 4 → t * x * t⁻¹ ≠ x)
    (hfixR' : ∀ x ∈ R', orderOf x = 4 → t * x * t⁻¹ ≠ x) :
    ∃ x c₁ ω : G, c₁ ∈ R ∧ orderOf c₁ = 4 ∧ ω * c₁ = c₁ * ω ∧ ω * ω = 1 ∧ t * ω = ω * t ∧
      ω ≠ 1 ∧ ω ≠ z ∧ x⁻¹ * t * x = t * ω := by
  obtain ⟨x₁, hx₁R, hx₁'⟩ := exists_twist_orderOf_four hRq hzR htR hfixR
  obtain ⟨x₂, hx₂R, hx₂'⟩ := exists_twist_orderOf_four hR'q hzR' htR' hfixR'
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : G, c₁ = (t * x₁ * t⁻¹)⁻¹ * x₁ := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : G, c₂ = (t * x₂ * t⁻¹)⁻¹ * x₂ := ⟨_, rfl⟩
  have hx₁ : orderOf c₁ = 4 := by rw [hc₁]; exact hx₁'
  have hx₂ : orderOf c₂ = 4 := by rw [hc₂]; exact hx₂'
  have hc₁R : c₁ ∈ R := by rw [hc₁]; exact R.mul_mem (R.inv_mem (htR x₁ hx₁R)) hx₁R
  have hc₂R : c₂ ∈ R' := by rw [hc₂]; exact R'.mul_mem (R'.inv_mem (htR' x₂ hx₂R)) hx₂R
  have hc₁sq : c₁ * c₁ = z := T7A.sq_eq_of_orderOf_four hzR hc₁R hx₁
  have hc₂sq : c₂ * c₂ = z := T7A.sq_eq_of_orderOf_four hzR' hc₂R hx₂
  have hzc₂ : c₂ * z = z * c₂ := AscL62.uniqueInvolution_comm hzR' hc₂R
  have hcc : c₁ * c₂ = c₂ * c₁ := hc c₁ hc₁R c₂ hc₂R
  have hzz : z * z = 1 := hzR.sq
  have hinv₁ : c₁⁻¹ = c₁ * z := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc c₁ * (c₁ * z) = (c₁ * c₁) * z := by group
      _ = 1 := by rw [hc₁sq, hzz]
  have hinv₂ : c₂⁻¹ = c₂ * z := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc c₂ * (c₂ * z) = (c₂ * c₂) * z := by group
      _ = 1 := by rw [hc₂sq, hzz]
  have hτ2 : ∀ x : G, t * (t * x * t⁻¹) * t⁻¹ = x := by
    intro x
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [ht2]; group
  have hτc₁ : t * c₁ * t⁻¹ = c₁⁻¹ := by
    calc t * c₁ * t⁻¹ = (t * (t * x₁ * t⁻¹) * t⁻¹)⁻¹ * (t * x₁ * t⁻¹) := by
          rw [hc₁]; simp [mul_assoc]
      _ = x₁⁻¹ * (t * x₁ * t⁻¹) := by rw [hτ2 x₁]
      _ = c₁⁻¹ := by rw [hc₁]; group
  have hτc₂ : t * c₂ * t⁻¹ = c₂⁻¹ := by
    calc t * c₂ * t⁻¹ = (t * (t * x₂ * t⁻¹) * t⁻¹)⁻¹ * (t * x₂ * t⁻¹) := by
          rw [hc₂]; simp [mul_assoc]
      _ = x₂⁻¹ * (t * x₂ * t⁻¹) := by rw [hτ2 x₂]
      _ = c₂⁻¹ := by rw [hc₂]; group
  obtain ⟨ω, hω⟩ : ∃ ω : G, ω = c₁ * c₂ := ⟨_, rfl⟩
  have hω2 : ω * ω = 1 := by
    calc ω * ω = c₁ * (c₂ * c₁) * c₂ := by rw [hω]; group
      _ = c₁ * (c₁ * c₂) * c₂ := by rw [hcc]
      _ = (c₁ * c₁) * (c₂ * c₂) := by group
      _ = 1 := by rw [hc₁sq, hc₂sq, hzz]
  have hτω : t * ω * t⁻¹ = ω := by
    calc t * ω * t⁻¹ = (t * c₁ * t⁻¹) * (t * c₂ * t⁻¹) := by rw [hω]; group
      _ = c₁⁻¹ * c₂⁻¹ := by rw [hτc₁, hτc₂]
      _ = (c₁ * z) * (c₂ * z) := by rw [hinv₁, hinv₂]
      _ = c₁ * (z * c₂) * z := by group
      _ = c₁ * (c₂ * z) * z := by rw [hzc₂]
      _ = c₁ * c₂ * (z * z) := by group
      _ = ω := by rw [hzz, hω]; group
  have htω : t * ω = ω * t := by
    have := congrArg (fun y => y * t) hτω
    simpa [mul_assoc] using this
  have hz' : z ∈ R' := hzR'.mem
  have hω1 : ω ≠ 1 := by
    intro h
    have : c₁ = c₂⁻¹ := by
      have : c₁ * c₂ = 1 := hω ▸ h
      exact eq_inv_of_mul_eq_one_left this
    exact hinf c₁ hc₁R (this ▸ R'.inv_mem hc₂R) hx₁
  have hωz : ω ≠ z := by
    intro h
    have : c₁ = z * c₂⁻¹ := by
      have : c₁ * c₂ = z := hω ▸ h
      calc c₁ = c₁ * c₂ * c₂⁻¹ := by group
        _ = z * c₂⁻¹ := by rw [this]
    exact hinf c₁ hc₁R (this ▸ R'.mul_mem hz' (R'.inv_mem hc₂R)) hx₁
  have hωc₁ : ω * c₁ = c₁ * ω := by
    calc ω * c₁ = c₁ * (c₂ * c₁) := by rw [hω]; group
      _ = c₁ * (c₁ * c₂) := by rw [hcc]
      _ = c₁ * ω := by rw [hω]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hA : ∀ x : G, x⁻¹ * t * x = t * ((t * x * t⁻¹)⁻¹ * x) := by
    intro x
    calc x⁻¹ * t * x = x⁻¹ * t⁻¹ * x := by rw [hti]
      _ = (t * t) * x⁻¹ * t⁻¹ * x := by rw [ht2]; group
      _ = t * ((t * x * t⁻¹)⁻¹ * x) := by simp [mul_assoc]
  have hy : (t * x₂ * t⁻¹)⁻¹ * c₁ = c₁ * (t * x₂ * t⁻¹)⁻¹ :=
    (hc c₁ hc₁R _ (R'.inv_mem (htR' x₂ hx₂R))).symm
  have hcx : (t * (x₁ * x₂) * t⁻¹)⁻¹ * (x₁ * x₂) = ω := by
    calc (t * (x₁ * x₂) * t⁻¹)⁻¹ * (x₁ * x₂)
        = (t * x₂ * t⁻¹)⁻¹ * ((t * x₁ * t⁻¹)⁻¹ * x₁) * x₂ := by group
      _ = (t * x₂ * t⁻¹)⁻¹ * c₁ * x₂ := by rw [hc₁]
      _ = c₁ * (t * x₂ * t⁻¹)⁻¹ * x₂ := by rw [hy]
      _ = c₁ * ((t * x₂ * t⁻¹)⁻¹ * x₂) := by group
      _ = ω := by rw [hω, hc₂]
  refine ⟨x₁ * x₂, c₁, ω, hc₁R, hx₁, hωc₁, hω2, htω, hω1, hωz, ?_⟩
  rw [hA, hcx]

end T7ER

end CFSG.ClassicalInvolution.Asc77
