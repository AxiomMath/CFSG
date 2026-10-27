module

public import CFSG.LieType.Chevalley.TrialityCoverTorus

public noncomputable section

namespace CFSG.LieType.Chevalley.TrialityCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem sq_ne_one_of_odd {G : Type*} [Group G] [Finite G] (hG : Odd (Nat.card G)) {x : G}
    (hx : x ≠ 1) : x ^ 2 ≠ 1 := by
  intro h
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
  have h3 : orderOf x = 1 ∨ orderOf x = 2 := (Nat.dvd_prime Nat.prime_two).1 h1
  rcases h3 with h3 | h3
  · exact hx (orderOf_eq_one_iff.1 h3)
  · rw [h3] at h2
    exact (Nat.not_even_iff_odd.2 hG) (even_iff_two_dvd.2 h2)

theorem inv_ne_one' {G : Type*} [Group G] {x : G} (hx : x ≠ 1) : x⁻¹ ≠ 1 :=
  fun h => hx (inv_eq_one.1 h)

theorem cartanCoord_trialityRoot_zero :
    cartanCoord (trialityRoot 0) ⟨0, by decide⟩ = 2 ∧
      cartanCoord (trialityRoot 0) ⟨1, by decide⟩ = 0 ∧
      cartanCoord (trialityRoot 0) ⟨2, by decide⟩ = -1 ∧
      cartanCoord (trialityRoot 0) ⟨3, by decide⟩ = 0 := by
  decide +kernel

theorem cartanCoord_trialityRoot_one :
    cartanCoord (trialityRoot 1) ⟨0, by decide⟩ = -1 ∧
      cartanCoord (trialityRoot 1) ⟨1, by decide⟩ = -1 ∧
      cartanCoord (trialityRoot 1) ⟨2, by decide⟩ = 2 ∧
      cartanCoord (trialityRoot 1) ⟨3, by decide⟩ = -1 := by
  decide +kernel

theorem cartanCoord_trialityRoot_two :
    cartanCoord (trialityRoot 2) ⟨0, by decide⟩ = 1 ∧
      cartanCoord (trialityRoot 2) ⟨1, by decide⟩ = -1 ∧
      cartanCoord (trialityRoot 2) ⟨2, by decide⟩ = 1 ∧
      cartanCoord (trialityRoot 2) ⟨3, by decide⟩ = -1 := by
  decide +kernel

theorem cartanCoord_trialityRoot_three :
    cartanCoord (trialityRoot 3) ⟨0, by decide⟩ = -1 ∧
      cartanCoord (trialityRoot 3) ⟨1, by decide⟩ = 1 ∧
      cartanCoord (trialityRoot 3) ⟨2, by decide⟩ = 0 ∧
      cartanCoord (trialityRoot 3) ⟨3, by decide⟩ = 1 := by
  decide +kernel

theorem cartanCoord_trialityRoot_four :
    cartanCoord (trialityRoot 4) ⟨0, by decide⟩ = 1 ∧
      cartanCoord (trialityRoot 4) ⟨1, by decide⟩ = 1 ∧
      cartanCoord (trialityRoot 4) ⟨2, by decide⟩ = -1 ∧
      cartanCoord (trialityRoot 4) ⟨3, by decide⟩ = 1 := by
  decide +kernel

theorem cartanCoord_trialityRoot_five :
    cartanCoord (trialityRoot 5) ⟨0, by decide⟩ = 0 ∧
      cartanCoord (trialityRoot 5) ⟨1, by decide⟩ = 0 ∧
      cartanCoord (trialityRoot 5) ⟨2, by decide⟩ = 1 ∧
      cartanCoord (trialityRoot 5) ⟨3, by decide⟩ = 0 := by
  decide +kernel

section Weights

variable (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ)

local notation "σu" => unitsSigma σ
local notation "fu" => trialityFixedUnit K σ

theorem rootChar_trialityRoot_zero :
    rootChar K (trialityRoot 0) (torusParam σ (a, b)) = a ^ 2 * (fu b)⁻¹ := by
  obtain ⟨h0, h1, h2, h3⟩ := cartanCoord_trialityRoot_zero
  rw [rootChar_torusParam, h0, h1, h2, h3]
  unit_arith

theorem rootChar_trialityRoot_one :
    rootChar K (trialityRoot 1) (torusParam σ (a, b)) = (a * σu a * σu (σu a))⁻¹ * fu b ^ 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := cartanCoord_trialityRoot_one
  rw [rootChar_torusParam, h0, h1, h2, h3]
  unit_arith

theorem rootChar_trialityRoot_two :
    rootChar K (trialityRoot 2) (torusParam σ (a, b)) = a * (σu a)⁻¹ * fu b * (σu (σu a))⁻¹ := by
  obtain ⟨h0, h1, h2, h3⟩ := cartanCoord_trialityRoot_two
  rw [rootChar_torusParam, h0, h1, h2, h3]
  unit_arith

theorem rootChar_trialityRoot_three :
    rootChar K (trialityRoot 3) (torusParam σ (a, b)) = a⁻¹ * σu a * σu (σu a) := by
  obtain ⟨h0, h1, h2, h3⟩ := cartanCoord_trialityRoot_three
  rw [rootChar_torusParam, h0, h1, h2, h3]
  unit_arith

theorem rootChar_trialityRoot_four :
    rootChar K (trialityRoot 4) (torusParam σ (a, b)) = a * σu a * σu (σu a) * (fu b)⁻¹ := by
  obtain ⟨h0, h1, h2, h3⟩ := cartanCoord_trialityRoot_four
  rw [rootChar_torusParam, h0, h1, h2, h3]
  unit_arith

theorem rootChar_trialityRoot_five :
    rootChar K (trialityRoot 5) (torusParam σ (a, b)) = fu b := by
  obtain ⟨h0, h1, h2, h3⟩ := cartanCoord_trialityRoot_five
  rw [rootChar_torusParam, h0, h1, h2, h3]
  unit_arith

end Weights

section Witnesses

local notation "σu" => unitsSigma σ
local notation "fu" => trialityFixedUnit K σ

theorem units_map_fu (b : (trialityFixedField K σ.toRingHom)ˣ) : σu (fu b) = fu b :=
  units_map_trialityFixedUnit b

theorem fu_injective : Function.Injective (trialityFixedUnit K σ) := fun _ _ h =>
  Units.ext (Subtype.ext (congrArg (fun u : Kˣ => (u : K)) h))

theorem weights_normOne {a : Kˣ} (ha : a * σu a * σu (σu a) = 1) :
    rootChar K (trialityRoot 0) (torusParam σ (a, 1)) = a ^ 2 ∧
      rootChar K (trialityRoot 1) (torusParam σ (a, 1)) = 1 ∧
      rootChar K (trialityRoot 2) (torusParam σ (a, 1)) = a ^ 2 ∧
      rootChar K (trialityRoot 3) (torusParam σ (a, 1)) = (a ^ 2)⁻¹ ∧
      rootChar K (trialityRoot 4) (torusParam σ (a, 1)) = 1 ∧
      rootChar K (trialityRoot 5) (torusParam σ (a, 1)) = 1 := by
  have hs : σu (σu a) = (a * σu a)⁻¹ := eq_inv_of_mul_eq_one_right ha
  rw [rootChar_trialityRoot_zero, rootChar_trialityRoot_one, rootChar_trialityRoot_two,
    rootChar_trialityRoot_three, rootChar_trialityRoot_four, rootChar_trialityRoot_five, ha,
    map_one, hs]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩ <;> unit_arith

theorem weights_fixed (b : (trialityFixedField K σ.toRingHom)ˣ) :
    rootChar K (trialityRoot 0) (torusParam σ (1, b)) = (fu b)⁻¹ ∧
      rootChar K (trialityRoot 1) (torusParam σ (1, b)) = fu b ^ 2 ∧
      rootChar K (trialityRoot 2) (torusParam σ (1, b)) = fu b ∧
      rootChar K (trialityRoot 3) (torusParam σ (1, b)) = 1 ∧
      rootChar K (trialityRoot 4) (torusParam σ (1, b)) = (fu b)⁻¹ ∧
      rootChar K (trialityRoot 5) (torusParam σ (1, b)) = fu b := by
  rw [rootChar_trialityRoot_zero, rootChar_trialityRoot_one, rootChar_trialityRoot_two,
    rootChar_trialityRoot_three, rootChar_trialityRoot_four, rootChar_trialityRoot_five, map_one,
    map_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩ <;> unit_arith

theorem weights_diag (c : (trialityFixedField K σ.toRingHom)ˣ) :
    rootChar K (trialityRoot 0) (torusParam σ (fu c, c)) = fu c ∧
      rootChar K (trialityRoot 1) (torusParam σ (fu c, c)) = (fu c)⁻¹ ∧
      rootChar K (trialityRoot 2) (torusParam σ (fu c, c)) = 1 ∧
      rootChar K (trialityRoot 3) (torusParam σ (fu c, c)) = fu c ∧
      rootChar K (trialityRoot 4) (torusParam σ (fu c, c)) = fu c ^ 2 ∧
      rootChar K (trialityRoot 5) (torusParam σ (fu c, c)) = fu c := by
  rw [rootChar_trialityRoot_zero, rootChar_trialityRoot_one, rootChar_trialityRoot_two,
    rootChar_trialityRoot_three, rootChar_trialityRoot_four, rootChar_trialityRoot_five,
    units_map_fu, units_map_fu]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩ <;> unit_arith

theorem weights_norm (hσ : σ ^ 3 = 1) (a : Kˣ) :
    rootChar K (trialityRoot 1) (torusParam σ (a, trialityNorm σ hσ a)) =
        a * σu a * σu (σu a) ∧
      rootChar K (trialityRoot 4) (torusParam σ (a, trialityNorm σ hσ a)) = 1 := by
  rw [rootChar_trialityRoot_one, rootChar_trialityRoot_four, trialityFixedUnit_norm]
  refine ⟨?_, ?_⟩ <;> unit_arith

theorem weights_outer (a : Kˣ) :
    rootChar K (trialityRoot 1) (torusParam σ (a, 1)) = (a * σu a * σu (σu a))⁻¹ ∧
      rootChar K (trialityRoot 4) (torusParam σ (a, 1)) = a * σu a * σu (σu a) ∧
      rootChar K (trialityRoot 5) (torusParam σ (a, 1)) = 1 := by
  rw [rootChar_trialityRoot_one, rootChar_trialityRoot_four, rootChar_trialityRoot_five,
    map_one]
  refine ⟨?_, ?_, rfl⟩ <;> unit_arith

variable [Finite K]

theorem exists_norm_one_ne_one (hσ : σ ^ 3 = 1)
    (hlt : Nat.card (trialityFixedField K σ.toRingHom) < Nat.card K) :
    ∃ a : Kˣ, a ≠ 1 ∧ a * σu a * σu (σu a) = 1 := by
  by_contra h
  push Not at h
  have hinj : Function.Injective (trialityNorm σ hσ) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    by_contra hne
    refine h a hne ?_
    rw [← trialityFixedUnit_norm hσ, ha, map_one]
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_units, Nat.card_units] at hle
  have : 0 < Nat.card (trialityFixedField K σ.toRingHom) := Nat.card_pos
  omega

theorem exists_fixedUnit_ne_one (hk : 3 ≤ Nat.card (trialityFixedField K σ.toRingHom)) :
    ∃ b : (trialityFixedField K σ.toRingHom)ˣ, b ≠ 1 := by
  have : Finite (trialityFixedField K σ.toRingHom) := inferInstance
  have h1 : 1 < Nat.card (trialityFixedField K σ.toRingHom)ˣ := by
    rw [Nat.card_units]
    omega
  have : Nontrivial (trialityFixedField K σ.toRingHom)ˣ := Finite.one_lt_card_iff_nontrivial.1 h1
  exact exists_ne 1

theorem exists_norm_ne_one {q : ℕ} (hq : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 3)
    (h4 : 4 ≤ q) : ∃ a : Kˣ, a * σu a * σu (σu a) ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  refine ⟨g, fun h => ?_⟩
  have hN : g ^ (1 + q + q ^ 2) = 1 := by
    rw [← h]
    refine Units.ext ?_
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass,
      RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hq]
    ring
  have hdvd := orderOf_dvd_of_pow_eq_one hN
  rw [hg, Nat.card_units, hK] at hdvd
  have hle := Nat.le_of_dvd (by positivity) hdvd
  have h3 : q ^ 3 = q * q * q := by ring
  have h2 : q ^ 2 = q * q := by ring
  rw [h3, h2] at hle
  have hy : 4 * q ≤ q * q := by nlinarith
  have hx : 4 * (q * q) ≤ q * q * q := by nlinarith
  omega

end Witnesses

section Separation

local notation "σu" => unitsSigma σ
local notation "fu" => trialityFixedUnit K σ

@[expose] def Separated (i j : Fin 6) : Prop :=
  ∃ p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ,
    (rootChar K (trialityRoot i) (torusParam σ p) = 1 ∧
        rootChar K (trialityRoot j) (torusParam σ p) ≠ 1) ∨
      (rootChar K (trialityRoot j) (torusParam σ p) = 1 ∧
        rootChar K (trialityRoot i) (torusParam σ p) ≠ 1)

theorem Separated.symm {i j : Fin 6} (h : Separated σ i j) : Separated σ j i := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.symm⟩

theorem unitsSigma_ne_one {a : Kˣ} (ha : a ≠ 1) : σu a ≠ 1 := fun h => ha (Units.ext (by
  have h' := congrArg (fun u : Kˣ => (u : K)) h
  simp only [Units.coe_map, MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Units.val_one] at h'
  rw [Units.val_one]
  exact σ.injective (h'.trans (map_one σ).symm)))

variable [Finite K] [CharP K 2]

theorem separated_of_ne (hσ : σ ^ 3 = 1)
    (hlt : Nat.card (trialityFixedField K σ.toRingHom) < Nat.card K)
    (hk : 3 ≤ Nat.card (trialityFixedField K σ.toRingHom))
    (hN : ∃ a : Kˣ, a * σu a * σu (σu a) ≠ 1) {i j : Fin 6} (hij : i ≠ j) :
    Separated σ i j := by
  have hodd := odd_card_units_of_charTwo K
  obtain ⟨a₀, ha₀, hN₀⟩ := exists_norm_one_ne_one σ hσ hlt
  obtain ⟨b₀, hb₀⟩ := exists_fixedUnit_ne_one σ hk
  obtain ⟨a₁, ha₁⟩ := hN
  have hfb : fu b₀ ≠ 1 := fun h => hb₀ (fu_injective σ (h.trans (map_one _).symm))
  have hsq₀ : a₀ ^ 2 ≠ 1 := sq_ne_one_of_odd hodd ha₀
  have hisq₀ : (a₀ ^ 2)⁻¹ ≠ 1 := inv_ne_one' hsq₀
  have hifb : (fu b₀)⁻¹ ≠ 1 := inv_ne_one' hfb
  have hia₁ : (a₁ * σu a₁ * σu (σu a₁))⁻¹ ≠ 1 := inv_ne_one' ha₁
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := weights_normOne σ hN₀
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := weights_fixed σ b₀
  obtain ⟨d0, d1, d2, d3, d4, d5⟩ := weights_diag σ b₀
  obtain ⟨m1, m4⟩ := weights_norm σ hσ a₁
  obtain ⟨o1, o4, o5⟩ := weights_outer σ a₁
  have key : ∀ i j : Fin 6, i < j → Separated σ i j := by
    intro i j hlt'
    fin_cases i <;> fin_cases j <;> simp at hlt'
    · exact ⟨(a₀, 1), Or.inr ⟨n1, (fun h => hsq₀ (n0.symm.trans h))⟩⟩
    · exact ⟨(fu b₀, b₀), Or.inr ⟨d2, (fun h => hfb (d0.symm.trans h))⟩⟩
    · exact ⟨(1, b₀), Or.inr ⟨f3, (fun h => hifb (f0.symm.trans h))⟩⟩
    · exact ⟨(a₀, 1), Or.inr ⟨n4, (fun h => hsq₀ (n0.symm.trans h))⟩⟩
    · exact ⟨(a₀, 1), Or.inr ⟨n5, (fun h => hsq₀ (n0.symm.trans h))⟩⟩
    · exact ⟨(a₀, 1), Or.inl ⟨n1, (fun h => hsq₀ (n2.symm.trans h))⟩⟩
    · exact ⟨(a₀, 1), Or.inl ⟨n1, (fun h => hisq₀ (n3.symm.trans h))⟩⟩
    · exact ⟨(a₁, trialityNorm σ hσ a₁), Or.inr ⟨m4, (fun h => ha₁ (m1.symm.trans h))⟩⟩
    · exact ⟨(a₁, 1), Or.inr ⟨o5, (fun h => hia₁ (o1.symm.trans h))⟩⟩
    · exact ⟨(1, b₀), Or.inr ⟨f3, (fun h => hfb (f2.symm.trans h))⟩⟩
    · exact ⟨(a₀, 1), Or.inr ⟨n4, (fun h => hsq₀ (n2.symm.trans h))⟩⟩
    · exact ⟨(a₀, 1), Or.inr ⟨n5, (fun h => hsq₀ (n2.symm.trans h))⟩⟩
    · exact ⟨(a₀, 1), Or.inr ⟨n4, (fun h => hisq₀ (n3.symm.trans h))⟩⟩
    · exact ⟨(a₀, 1), Or.inr ⟨n5, (fun h => hisq₀ (n3.symm.trans h))⟩⟩
    · exact ⟨(a₁, 1), Or.inr ⟨o5, (fun h => ha₁ (o4.symm.trans h))⟩⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem posRoot_cartanCoord_cases : ∀ k : Fin 24,
    0 < height (TwistTag.D4.tag.rootCertificate.root k) →
      (cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨2, by decide⟩ = 1 ∨
          cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨2, by decide⟩ = -1 ∨
          cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨2, by decide⟩ = 2 ∨
          cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨2, by decide⟩ = -2) ∨
        (cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨0, by decide⟩ = 1 ∧
          cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨1, by decide⟩ = 1 ∧
          cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨2, by decide⟩ = 0 ∧
          cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨3, by decide⟩ = -1) ∨
        (cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨0, by decide⟩ = 1 ∧
          cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨1, by decide⟩ = -1 ∧
          cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨2, by decide⟩ = 0 ∧
          cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨3, by decide⟩ = 1) ∨
        (cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨0, by decide⟩ = -1 ∧
          cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨1, by decide⟩ = 1 ∧
          cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨2, by decide⟩ = 0 ∧
          cartanCoord (TwistTag.D4.tag.rootCertificate.root k) ⟨3, by decide⟩ = 1) := by
  decide +kernel

theorem rootChar_comp_torusParam_ne_one (hσ : σ ^ 3 = 1)
    (hlt : Nat.card (trialityFixedField K σ.toRingHom) < Nat.card K)
    (hk : 3 ≤ Nat.card (trialityFixedField K σ.toRingHom)) {β : Fin TwistTag.D4.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.D4.tag β) (hpos : 0 < height β) :
    (rootChar K β).comp (torusParam σ) ≠ 1 := by
  have hodd := odd_card_units_of_charTwo K
  obtain ⟨a₀, ha₀, hN₀⟩ := exists_norm_one_ne_one σ hσ hlt
  obtain ⟨b₀, hb₀⟩ := exists_fixedUnit_ne_one σ hk
  have hfb : fu b₀ ≠ 1 := fun h => hb₀ (fu_injective σ (h.trans (map_one _).symm))
  have hs : σu (σu a₀) = (a₀ * σu a₀)⁻¹ := eq_inv_of_mul_eq_one_right hN₀
  have hss : σu (σu a₀) ≠ 1 := unitsSigma_ne_one σ (unitsSigma_ne_one σ ha₀)
  obtain ⟨k, hk', rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hβ
  have hcases := posRoot_cartanCoord_cases ⟨k, hk'⟩ hpos
  intro h1
  have hev : ∀ p, rootChar K (TwistTag.D4.tag.rootCertificate.root k) (torusParam σ p) = 1 :=
    fun p => DFunLike.congr_fun h1 p
  rcases hcases with hc | hc | hc | hc
  ·
    have h := hev (1, b₀)
    rw [rootChar_torusParam] at h
    simp only [map_one, one_zpow, one_mul, mul_one] at h
    rcases hc with hc | hc | hc | hc <;> rw [hc] at h
    · exact hfb (by simpa using h)
    · exact hfb (by simpa using h)
    · exact sq_ne_one_of_odd hodd hfb (by simpa using h)
    · exact sq_ne_one_of_odd hodd hfb (by simpa [zpow_neg] using h)
  all_goals
    have h := hev (a₀, 1)
    rw [rootChar_torusParam, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, map_one, hs] at h
  ·
    refine sq_ne_one_of_odd hodd (x := a₀ * σu a₀) (fun h' => hss (by rw [hs, h', inv_one])) ?_
    rw [← h]
    unit_arith
  ·
    refine sq_ne_one_of_odd hodd (x := (σu a₀)⁻¹) (inv_ne_one' (unitsSigma_ne_one σ ha₀)) ?_
    rw [← h]
    unit_arith
  ·
    refine sq_ne_one_of_odd hodd (x := a₀⁻¹) (inv_ne_one' ha₀) ?_
    rw [← h]
    unit_arith

end Separation

end CFSG.LieType.Chevalley.TrialityCover
