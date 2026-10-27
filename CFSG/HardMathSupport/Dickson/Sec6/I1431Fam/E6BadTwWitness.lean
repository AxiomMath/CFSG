module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTwTorusZ
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTwRoots
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTwRankOne
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Torus
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Simplicity CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Adjoint

section Zeta

variable {K : Type} [Field K]

theorem exists_unit_orderOf_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, orderOf ζ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact h3
  exact exists_prime_orderOf_dvd_card' 3 this

theorem unit_cube_eq_one (ζ : Kˣ) (hζ : orderOf ζ = 3) : (ζ : K) ^ 3 = 1 := by
  have h := congrArg Units.val (pow_orderOf_eq_one ζ)
  rw [hζ, Units.val_pow_eq_pow_val] at h
  simpa using h

theorem unit_ne_one_of_orderOf_three (ζ : Kˣ) (hζ : orderOf ζ = 3) : (ζ : K) ≠ 1 := by
  intro h
  have := orderOf_eq_one_iff.2 (Units.ext h)
  omega

theorem unit_sq_add_add_one (ζ : Kˣ) (hζ : orderOf ζ = 3) : (ζ : K) ^ 2 + ζ + 1 = 0 := by
  have h1 := unit_cube_eq_one ζ hζ
  have h2 := unit_ne_one_of_orderOf_three ζ hζ
  have : ((ζ : K) - 1) * ((ζ : K) ^ 2 + ζ + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · exact h

theorem three_ne_zero_of_orderOf_three (ζ : Kˣ) (hζ : orderOf ζ = 3) : (3 : K) ≠ 0 := by
  intro h3
  have h1 := unit_cube_eq_one ζ hζ
  have h2 := unit_ne_one_of_orderOf_three ζ hζ
  have : ((ζ : K) - 1) ^ 3 = 0 := by linear_combination h1 + ((ζ : K) - (ζ : K) ^ 2) * h3
  exact h2 (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this))

theorem units_map_theta_zeta (θ : K →+* K) {q : ℕ} (hθq : ∀ c, θ c = c ^ q) (h3 : 3 ∣ q + 1)
    (ζ : Kˣ) (hζ : orderOf ζ = 3) : Units.map (θ : K →* K) ζ = ζ⁻¹ := by
  have hpow : Units.map (θ : K →* K) ζ = ζ ^ q := Units.ext (by simp [hθq])
  obtain ⟨m, hm⟩ := h3
  have h1 : ζ ^ (q + 1) = 1 := by
    rw [hm, pow_mul]
    have := pow_orderOf_eq_one ζ
    rw [hζ] at this
    rw [this, one_pow]
  rw [hpow]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h1)

theorem isSymU_zeta3Pi (θ : K →+* K) (ζ : Kˣ) (hζ : orderOf ζ = 3)
    (hθζ : Units.map (θ : K →* K) ζ = ζ⁻¹) (x : Fin Tag.E6.rank → ZMod 3)
    (hx : ∀ a, x (rhoPerm a) = -x a) :
    IsSymU θ (zeta3Pi ζ hζ (Multiplicative.ofAdd x)) := fun a => by
  show zeta3Hom ζ hζ (Multiplicative.ofAdd (x (rhoPerm a))) =
    Units.map (θ : K →* K) (zeta3Hom ζ hζ (Multiplicative.ofAdd (x a)))
  have h1 : zeta3Hom ζ hζ (Multiplicative.ofAdd (-x a)) =
      (zeta3Hom ζ hζ (Multiplicative.ofAdd (x a)))⁻¹ := by
    rw [← map_inv]
    rfl
  rw [hx, h1, zeta3Hom_apply, map_pow, hθζ, inv_pow]

end Zeta

section Abstract

variable {G : Type*} [Group G]

theorem conj_three_left (a b c t : G) (hb : Commute t b) (hc : Commute t c) :
    a * b * c * t * (a * b * c)⁻¹ = a * t * a⁻¹ := by
  have h1 : c * t * c⁻¹ = t := by rw [← hc.eq, mul_inv_cancel_right]
  have h2 : b * t * b⁻¹ = t := by rw [← hb.eq, mul_inv_cancel_right]
  calc a * b * c * t * (a * b * c)⁻¹ = a * (b * (c * t * c⁻¹) * b⁻¹) * a⁻¹ := by group
    _ = a * t * a⁻¹ := by rw [h1, h2]

theorem conj_three_mid (a b c t : G) (hab : Commute a b) (hat : Commute a t) (hc : Commute t c) :
    a * b * c * t * (a * b * c)⁻¹ = b * t * b⁻¹ := by
  have h1 : c * t * c⁻¹ = t := by rw [← hc.eq, mul_inv_cancel_right]
  have h2 : a * (b * t * b⁻¹) * a⁻¹ = b * t * b⁻¹ := by
    have hab' : Commute a (b * t * b⁻¹) := (hab.mul_right hat).mul_right (hab.inv_right)
    rw [hab'.eq, mul_inv_cancel_right]
  calc a * b * c * t * (a * b * c)⁻¹ = a * (b * (c * t * c⁻¹) * b⁻¹) * a⁻¹ := by group
    _ = a * (b * t * b⁻¹) * a⁻¹ := by rw [h1]
    _ = b * t * b⁻¹ := h2

theorem conj_three_right (a b c t : G) (hac : Commute a c) (hbc : Commute b c)
    (hat : Commute a t) (hbt : Commute b t) :
    a * b * c * t * (a * b * c)⁻¹ = c * t * c⁻¹ := by
  have hb : Commute b (c * t * c⁻¹) := (hbc.mul_right hbt).mul_right hbc.inv_right
  have ha : Commute a (c * t * c⁻¹) := (hac.mul_right hat).mul_right hac.inv_right
  have h1 : b * (c * t * c⁻¹) * b⁻¹ = c * t * c⁻¹ := by rw [hb.eq, mul_inv_cancel_right]
  have h2 : a * (c * t * c⁻¹) * a⁻¹ = c * t * c⁻¹ := by rw [ha.eq, mul_inv_cancel_right]
  calc a * b * c * t * (a * b * c)⁻¹ = a * (b * (c * t * c⁻¹) * b⁻¹) * a⁻¹ := by group
    _ = c * t * c⁻¹ := by rw [h1, h2]

theorem conj_three_none (a b c t : G) (ha : Commute t a) (hb : Commute t b) (hc : Commute t c) :
    a * b * c * t * (a * b * c)⁻¹ = t := by
  have h : Commute t (a * b * c) := (ha.mul_right hb).mul_right hc
  rw [← h.eq, mul_inv_cancel_right]

end Abstract

section Main

variable {K : Type} [Field K]

@[expose] def wvec : Fin 5 → (Fin Tag.E6.rank → ZMod 3) := ![vE0a, vE0b, vT1, vT2, vT3]

@[expose] def CC (w : Fin Tag.E6.rank → ZMod 3) (γ : Fin Tag.E6.rank → ℤ) : Prop :=
  (3 : ℤ) ∣ ∑ k, ((w k).val : ℤ) * ExceptionalCover.cartanCoord γ k

instance (w : Fin Tag.E6.rank → ZMod 3) (γ : Fin Tag.E6.rank → ℤ) : Decidable (CC w γ) :=
  inferInstanceAs (Decidable ((3 : ℤ) ∣ _))

theorem cc_vE0a : CC vE0a twB1 ∧ CC vE0a twB2 ∧ CC vE0a twB3 ∧ CC vE0a twTheta := by
  decide +kernel

theorem cc_vE0b : CC vE0b twB1 ∧ CC vE0b twB2 ∧ CC vE0b twB3 ∧ CC vE0b twTheta := by
  decide +kernel

theorem cc_vT1 : CC vT1 twB2 ∧ CC vT1 twB3 ∧ CC vT1 twTheta := by decide +kernel

theorem cc_vT2 : CC vT2 twB1 ∧ CC vT2 twB3 ∧ CC vT2 twTheta := by decide +kernel

theorem cc_vT3 : CC vT3 twB1 ∧ CC vT3 twB2 ∧ CC vT3 twTheta := by decide +kernel

theorem commute_torusZ_cc (ζ : Kˣ) (hζ : orderOf ζ = 3) {w : Fin Tag.E6.rank → ZMod 3}
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) (h : CC w γ) {y : e6Data_valid.minGroup K}
    (hy : y ∈ rootPair K γ) : Commute (torusZ K ζ hζ w) y :=
  commute_torusZ_rootPair ζ hζ hγ h hy

theorem rankOneThree_mem_fixedGroup (θ : K →+* K) :
    rankOneThree K (nd 3) ∈ fixedGroup K θ := by
  rw [mem_fixedGroup]
  unfold rankOneThree
  have hρ : rhoPerm (nd 3) = nd 3 := by decide
  rw [map_mul, sigma_xm_single θ (nd 3) 1, sigma_xm_neg_single θ (nd 3) (-3), hρ, map_one,
    show θ (-3 : K) = -3 by rw [map_neg, map_ofNat]]

theorem torusZ_mem_fixedGroup_of_neg (θ : K →+* K) (ζ : Kˣ) (hζ : orderOf ζ = 3)
    (hθζ : Units.map (θ : K →* K) ζ = ζ⁻¹) (x : Fin Tag.E6.rank → ZMod 3)
    (hx : ∀ a, x (rhoPerm a) = -x a) : torusZ K ζ hζ x ∈ fixedGroup K θ :=
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.minTorus_mem_fixedGroup θ
    (isSymU_zeta3Pi θ ζ hζ hθζ x hx)

theorem vE0a_neg : ∀ a, vE0a (rhoPerm a) = -vE0a a := by decide +kernel
theorem vE0b_neg : ∀ a, vE0b (rhoPerm a) = -vE0b a := by decide +kernel

theorem exists_conj_data (θ : K →+* K) (ζ : Kˣ) (hζ : orderOf ζ = 3)
    (hθζ : Units.map (θ : K →* K) ζ = ζ⁻¹) :
    ∃ g₁ g₂ g₃ : e6Data_valid.minGroup K, g₁ ∈ rootPair K twB1 ∧ g₂ ∈ rootPair K twB2 ∧
      g₃ ∈ rootPair K twB3 ∧
      ∀ j, (g₁ * g₂ * g₃) * torusZ K ζ hζ (wvec j) * (g₁ * g₂ * g₃)⁻¹ ∈ fixedGroup K θ := by
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_orderOf_three ζ hζ
  obtain ⟨g₁, hg₁, hg₁eq⟩ :=
    exists_conj_rankOneThree (K := K) (nd 3) ζ (unit_sq_add_add_one ζ hζ) h3
  have hg₁' : g₁ ∈ rootPair K twB1 := hg₁
  have hn2f : nHatE K (nf 2) ∈ fixedGroup K θ := (mem_fixedGroup θ).2 (sigma_nHatE θ (nf 2))
  have hn3f : nHatE K (nf 3) ∈ fixedGroup K θ := (mem_fixedGroup θ).2 (sigma_nHatE θ (nf 3))
  obtain ⟨g₂, hg₂def⟩ : ∃ g₂, g₂ = nHatE K (nf 2) * g₁ * (nHatE K (nf 2))⁻¹ := ⟨_, rfl⟩
  obtain ⟨g₃, hg₃def⟩ : ∃ g₃, g₃ = nHatE K (nf 3) * g₂ * (nHatE K (nf 3))⁻¹ := ⟨_, rfl⟩
  have hg₂ : g₂ ∈ rootPair K twB2 := by
    rw [hg₂def]
    exact nHat2_conj_rootPair hg₁'
  have hg₃ : g₃ ∈ rootPair K twB3 := by
    rw [hg₃def]
    exact nHat3_conj_rootPair hg₂
  refine ⟨g₁, g₂, g₃, hg₁', hg₂, hg₃, ?_⟩
  have hT1 : torusZ K ζ hζ vT1 = e6Data_valid.hm K (nd 3) ζ := torusZ_vT1 ζ hζ
  have hc₁ : rankOneThree K (nd 3) ∈ fixedGroup K θ := rankOneThree_mem_fixedGroup θ
  have hc₁eq : rankOneThree K (nd 3) = g₁ * torusZ K ζ hζ vT1 * g₁⁻¹ := by
    rw [hT1, hg₁eq]
  have hc₂ : nHatE K (nf 2) * rankOneThree K (nd 3) * (nHatE K (nf 2))⁻¹ ∈ fixedGroup K θ :=
    mul_mem (mul_mem hn2f hc₁) (inv_mem hn2f)
  have hc₂eq : nHatE K (nf 2) * rankOneThree K (nd 3) * (nHatE K (nf 2))⁻¹ =
      g₂ * torusZ K ζ hζ vT2 * g₂⁻¹ := by
    rw [hc₁eq, ← nHat2_conj_torusZ ζ hζ, hg₂def]
    group
  have hc₃ : nHatE K (nf 3) * (nHatE K (nf 2) * rankOneThree K (nd 3) * (nHatE K (nf 2))⁻¹) *
      (nHatE K (nf 3))⁻¹ ∈ fixedGroup K θ :=
    mul_mem (mul_mem hn3f hc₂) (inv_mem hn3f)
  have hc₃eq : nHatE K (nf 3) * (nHatE K (nf 2) * rankOneThree K (nd 3) *
      (nHatE K (nf 2))⁻¹) * (nHatE K (nf 3))⁻¹ = g₃ * torusZ K ζ hζ vT3 * g₃⁻¹ := by
    rw [hc₂eq, ← nHat3_conj_torusZ ζ hζ, hg₃def]
    group
  have g12 : Commute g₁ g₂ := commute_rootPair_B12 hg₁' hg₂
  have g13 : Commute g₁ g₃ := commute_rootPair_B13 hg₁' hg₃
  have g23 : Commute g₂ g₃ := commute_rootPair_B23 hg₂ hg₃
  have r1 : IsRoot .E6 twB1 := isRoot_twB1
  have r2 : IsRoot .E6 twB2 := isRoot_twB2
  have r3 : IsRoot .E6 twB3 := isRoot_twB3
  intro j
  fin_cases j
  ·
    change g₁ * g₂ * g₃ * torusZ K ζ hζ vE0a * (g₁ * g₂ * g₃)⁻¹ ∈ fixedGroup K θ
    rw [conj_three_none g₁ g₂ g₃ _ (commute_torusZ_cc ζ hζ r1 cc_vE0a.1 hg₁')
      (commute_torusZ_cc ζ hζ r2 cc_vE0a.2.1 hg₂) (commute_torusZ_cc ζ hζ r3 cc_vE0a.2.2.1 hg₃)]
    exact torusZ_mem_fixedGroup_of_neg θ ζ hζ hθζ vE0a vE0a_neg
  ·
    change g₁ * g₂ * g₃ * torusZ K ζ hζ vE0b * (g₁ * g₂ * g₃)⁻¹ ∈ fixedGroup K θ
    rw [conj_three_none g₁ g₂ g₃ _ (commute_torusZ_cc ζ hζ r1 cc_vE0b.1 hg₁')
      (commute_torusZ_cc ζ hζ r2 cc_vE0b.2.1 hg₂) (commute_torusZ_cc ζ hζ r3 cc_vE0b.2.2.1 hg₃)]
    exact torusZ_mem_fixedGroup_of_neg θ ζ hζ hθζ vE0b vE0b_neg
  ·
    change g₁ * g₂ * g₃ * torusZ K ζ hζ vT1 * (g₁ * g₂ * g₃)⁻¹ ∈ fixedGroup K θ
    rw [conj_three_left g₁ g₂ g₃ _ (commute_torusZ_cc ζ hζ r2 cc_vT1.1 hg₂)
      (commute_torusZ_cc ζ hζ r3 cc_vT1.2.1 hg₃), ← hc₁eq]
    exact hc₁
  ·
    change g₁ * g₂ * g₃ * torusZ K ζ hζ vT2 * (g₁ * g₂ * g₃)⁻¹ ∈ fixedGroup K θ
    rw [conj_three_mid g₁ g₂ g₃ _ g12 (commute_torusZ_cc ζ hζ r1 cc_vT2.1 hg₁').symm
      (commute_torusZ_cc ζ hζ r3 cc_vT2.2.1 hg₃), ← hc₂eq]
    exact hc₂
  ·
    change g₁ * g₂ * g₃ * torusZ K ζ hζ vT3 * (g₁ * g₂ * g₃)⁻¹ ∈ fixedGroup K θ
    rw [conj_three_right g₁ g₂ g₃ _ g13 g23 (commute_torusZ_cc ζ hζ r1 cc_vT3.1 hg₁').symm
      (commute_torusZ_cc ζ hζ r2 cc_vT3.2.1 hg₂).symm, ← hc₃eq]
    exact hc₃

@[expose] def wsum (x : Fin 5 → ZMod 3) : Fin Tag.E6.rank → ZMod 3 := ∑ j, x j • wvec j

theorem wsum_add (x y : Fin 5 → ZMod 3) : wsum (x + y) = wsum x + wsum y := by
  simp [wsum, add_smul, Finset.sum_add_distrib]

theorem wsum_zero : wsum 0 = 0 := by simp [wsum]

theorem wsum_eq_zero : ∀ x : Fin 5 → ZMod 3, wsum x = 0 → x = 0 := by decide +kernel

theorem wsum_injective : Function.Injective wsum := by
  intro x y h
  have h0 : wsum (x - y) = 0 := by
    have : wsum (x - y) + wsum y = wsum x := by rw [← wsum_add, sub_add_cancel]
    rw [h] at this
    exact add_eq_right.1 this
  exact sub_eq_zero.1 (wsum_eq_zero _ h0)

@[expose] noncomputable def torusHom5 (ζ : Kˣ) (hζ : orderOf ζ = 3) :
    Multiplicative (Fin 5 → ZMod 3) →* e6Data_valid.minGroup K where
  toFun x := torusZ K ζ hζ (wsum (Multiplicative.toAdd x))
  map_one' := by
    show torusZ K ζ hζ (wsum 0) = 1
    rw [wsum_zero, torusZ_zero]
  map_mul' x y := by
    show torusZ K ζ hζ (wsum (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
    rw [wsum_add, torusZ_add]

theorem conj_torusZ_wsum_mem (ζ : Kˣ) (hζ : orderOf ζ = 3) (g : e6Data_valid.minGroup K)
    (S : Subgroup (e6Data_valid.minGroup K))
    (hw : ∀ j, g * torusZ K ζ hζ (wvec j) * g⁻¹ ∈ S) (x : Fin 5 → ZMod 3) :
    g * torusZ K ζ hζ (wsum x) * g⁻¹ ∈ S := by
  let P : AddSubmonoid (Fin Tag.E6.rank → ZMod 3) :=
    { carrier := {v | g * torusZ K ζ hζ v * g⁻¹ ∈ S}
      zero_mem' := by
        show g * torusZ K ζ hζ 0 * g⁻¹ ∈ S
        rw [torusZ_zero, mul_one, mul_inv_cancel]
        exact one_mem S
      add_mem' := fun {a b} (ha : g * torusZ K ζ hζ a * g⁻¹ ∈ S)
          (hb : g * torusZ K ζ hζ b * g⁻¹ ∈ S) => by
        show g * torusZ K ζ hζ (a + b) * g⁻¹ ∈ S
        have := mul_mem ha hb
        rw [torusZ_add]
        convert this using 1
        group }
  have hmem : ∀ j, wvec j ∈ P := hw
  unfold wsum
  refine P.sum_mem fun j _ => ?_
  have h1 : x j • wvec j = (x j).val • wvec j := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [h1]
  exact P.nsmul_mem (hmem j) _

theorem hom_conj_eq_one_iff {G H : Type*} [Group G] [Group H] (f : G →* H) (g t : G) :
    f (g * t * g⁻¹) = 1 ↔ f t = 1 := by
  rw [map_mul, map_mul, map_inv]
  constructor
  · intro h
    have := congrArg (fun y => (f g)⁻¹ * y * f g) h
    simpa [mul_assoc] using this
  · intro h
    rw [h, mul_one, mul_inv_cancel]

theorem card_ker_torusHom5_le [Finite K] (ζ : Kˣ) (hζ : orderOf ζ = 3) :
    Nat.card ((e6Isogeny K).comp (torusHom5 ζ hζ)).ker ≤ 3 := by
  let f : ((e6Isogeny K).comp (torusHom5 ζ hζ)).ker →
      ((e6Isogeny K).comp ((minTorus e6Data_valid K).comp (zeta3Pi ζ hζ))).ker := fun x =>
    ⟨Multiplicative.ofAdd (wsum (Multiplicative.toAdd (x : Multiplicative (Fin 5 → ZMod 3)))),
      x.2⟩
  have hf : Function.Injective f := by
    intro a b h
    have h' : wsum (Multiplicative.toAdd (a : Multiplicative (Fin 5 → ZMod 3))) =
        wsum (Multiplicative.toAdd (b : Multiplicative (Fin 5 → ZMod 3))) :=
      congrArg (fun y : ((e6Isogeny K).comp ((minTorus e6Data_valid K).comp
        (zeta3Pi ζ hζ))).ker => Multiplicative.toAdd (y : Multiplicative (Fin Tag.E6.rank → ZMod 3))) h
    exact Subtype.ext (Multiplicative.toAdd.injective (wsum_injective h'))
  exact (Nat.card_le_card_of_injective f hf).trans (card_ker_torus_zeta_le ζ hζ)

theorem witness_of_involution {P S : Type*} [Group P] [Group S] (iso : P →* S)
    (E : Subgroup P) (u : P) (hu2 : u ^ 2 = 1) (hu1 : iso u ≠ 1) (hEu : ∀ e ∈ E, Commute e u) :
    ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E.map iso ≤ Subgroup.normalizer (U : Set S) := by
  have hX2 : IsPGroup 2 (Subgroup.zpowers u) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    show (g : P) ^ 2 = 1
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu2, one_zpow]
  have hXnorm : E ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup P) : Set P) := by
    refine le_normalizer_of_conj_mem fun e he y hy => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h := ((hEu e he).zpow_right n).eq
    rw [h, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.2 ⟨n, rfl⟩
  refine ⟨(Subgroup.zpowers u).map iso, ?_, hX2.map iso, map_le_normalizer_map iso hXnorm⟩
  intro hbot
  have hmem : iso u ∈ (Subgroup.zpowers u).map iso := ⟨u, Subgroup.mem_zpowers u, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hu1 hmem

@[expose] def uOdd (L : Type) [Field L] : Fin Tag.E6.rank → Lˣ :=
  Pi.mulSingle (nd 0) (-1) * Pi.mulSingle (nd 3) (-1) * Pi.mulSingle (nd 5) (-1)

theorem uOdd_apply (a : Fin Tag.E6.rank) :
    uOdd K a = if (a = nd 0 ∨ a = nd 3 ∨ a = nd 5) then -1 else 1 := by
  fin_cases a <;> simp [uOdd, Pi.mulSingle_apply, Fin.ext_iff]

theorem uOdd_sq : uOdd K ^ 2 = 1 := by
  funext a
  rw [Pi.pow_apply, uOdd_apply]
  split_ifs <;> simp

theorem uOdd_rho (a : Fin Tag.E6.rank) : uOdd K (rhoPerm a) = uOdd K a := by
  have h : (rhoPerm a = nd 0 ∨ rhoPerm a = nd 3 ∨ rhoPerm a = nd 5) ↔
      (a = nd 0 ∨ a = nd 3 ∨ a = nd 5) := by
    revert a
    decide
  rw [uOdd_apply, uOdd_apply]
  by_cases hc : a = nd 0 ∨ a = nd 3 ∨ a = nd 5
  · rw [if_pos hc, if_pos (h.2 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (h.1 h'))]

theorem uOdd_isSymU (θ : K →+* K) : IsSymU θ (uOdd K) := fun a => by
  rw [uOdd_rho, uOdd_apply]
  split_ifs
  · exact Units.ext (by simp)
  · exact (map_one _).symm

theorem rootChar_uOdd (γ : Fin Tag.E6.rank → ℤ) :
    ExceptionalCover.rootChar K γ (uOdd K) =
      (-1) ^ (ExceptionalCover.cartanCoord γ (nd 0) + ExceptionalCover.cartanCoord γ (nd 3) +
        ExceptionalCover.cartanCoord γ (nd 5)) := by
  unfold uOdd
  rw [map_mul, map_mul, ExceptionalCover.rootChar_mulSingle, ExceptionalCover.rootChar_mulSingle,
    ExceptionalCover.rootChar_mulSingle, zpow_add, zpow_add]

@[expose] def EvenSum (γ : Fin Tag.E6.rank → ℤ) : Prop :=
  (2 : ℤ) ∣ ExceptionalCover.cartanCoord γ (nd 0) + ExceptionalCover.cartanCoord γ (nd 3) +
    ExceptionalCover.cartanCoord γ (nd 5)

instance (γ : Fin Tag.E6.rank → ℤ) : Decidable (EvenSum γ) :=
  inferInstanceAs (Decidable ((2 : ℤ) ∣ _))

theorem evenSum_B : EvenSum twB1 ∧ EvenSum twB2 ∧ EvenSum twB3 := by decide +kernel

theorem rootChar_uOdd_eq_one {γ : Fin Tag.E6.rank → ℤ} (h : EvenSum γ) :
    ExceptionalCover.rootChar K γ (uOdd K) = 1 := by
  rw [rootChar_uOdd]
  obtain ⟨m, hm⟩ := h
  rw [hm, zpow_mul]
  simp

theorem rootChar_simple_uOdd :
    ExceptionalCover.rootChar K (Pi.single (nd 1) 1 : Fin Tag.E6.rank → ℤ) (uOdd K) = -1 := by
  rw [rootChar_uOdd]
  have h0 : ExceptionalCover.cartanCoord (Pi.single (nd 1) 1 : Fin Tag.E6.rank → ℤ) (nd 0) +
      ExceptionalCover.cartanCoord (Pi.single (nd 1) 1 : Fin Tag.E6.rank → ℤ) (nd 3) +
      ExceptionalCover.cartanCoord (Pi.single (nd 1) 1 : Fin Tag.E6.rank → ℤ) (nd 5) = -1 := by
    simp [ExceptionalCover.cartanCoord, Pi.single_apply]
    decide +kernel
  rw [h0, zpow_neg_one, inv_neg_one]

theorem commute_minTorus_minTorus (u v : Fin Tag.E6.rank → Kˣ) :
    Commute (minTorus e6Data_valid K u) (minTorus e6Data_valid K v) := by
  show minTorus e6Data_valid K u * minTorus e6Data_valid K v =
    minTorus e6Data_valid K v * minTorus e6Data_valid K u
  rw [← map_mul, ← map_mul, mul_comm]

theorem exists_involution_odd [Finite K] (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c)
    (hK : 4 ≤ Nat.card K) (ζ : Kˣ) (hζ : orderOf ζ = 3) (h2 : (2 : K) ≠ 0)
    {g₁ g₂ g₃ : e6Data_valid.minGroup K} (hg₁ : g₁ ∈ rootPair K twB1)
    (hg₂ : g₂ ∈ rootPair K twB2) (hg₃ : g₃ ∈ rootPair K twB3) :
    ∃ u : fixedGroup K θ, u ^ 2 = 1 ∧ twistedIsogeny θ hθ hK u ≠ 1 ∧
      ∀ x : Multiplicative (Fin 5 → ZMod 3),
        Commute (g₁ * g₂ * g₃ * torusHom5 ζ hζ x * (g₁ * g₂ * g₃)⁻¹)
          (u : e6Data_valid.minGroup K) := by
  refine ⟨⟨minTorus e6Data_valid K (uOdd K),
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.minTorus_mem_fixedGroup θ
      (uOdd_isSymU θ)⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (minTorus e6Data_valid K (uOdd K)) ^ 2 = 1
    rw [← map_pow, uOdd_sq, map_one]
  · intro h
    have h' : e6Isogeny K (minTorus e6Data_valid K (uOdd K)) = 1 := by
      have h1 := congrArg (fun y : ↥⁅twistedFixedGroup TwistTag.E6 K θ,
        twistedFixedGroup TwistTag.E6 K θ⁆ => (y : ModGL TwistTag.E6.tag K)) h
      exact Subtype.ext h1
    have h1 := rootChar_simple_eq_one_of_isogeny_eq_one (uOdd K) h' (nd 1)
    rw [rootChar_simple_uOdd] at h1
    have h4 : (-1 : K) = 1 := by simpa using congrArg Units.val h1
    exact h2 (by linear_combination (-1 : K) * h4)
  · intro x
    have hz1 : Commute (minTorus e6Data_valid K (uOdd K)) g₁ :=
      commute_minTorus_rootPair isRoot_twB1 (rootChar_uOdd_eq_one evenSum_B.1) hg₁
    have hz2 : Commute (minTorus e6Data_valid K (uOdd K)) g₂ :=
      commute_minTorus_rootPair isRoot_twB2 (rootChar_uOdd_eq_one evenSum_B.2.1) hg₂
    have hz3 : Commute (minTorus e6Data_valid K (uOdd K)) g₃ :=
      commute_minTorus_rootPair isRoot_twB3 (rootChar_uOdd_eq_one evenSum_B.2.2) hg₃
    have hzg : Commute (minTorus e6Data_valid K (uOdd K)) (g₁ * g₂ * g₃) :=
      (hz1.mul_right hz2).mul_right hz3
    have hzt : Commute (minTorus e6Data_valid K (uOdd K)) (torusHom5 ζ hζ x) :=
      commute_minTorus_minTorus _ _
    exact ((hzg.mul_right hzt).mul_right hzg.inv_right).symm

theorem exists_involution_even [Finite K] (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c)
    (hK : 4 ≤ Nat.card K) (ζ : Kˣ) (hζ : orderOf ζ = 3) (h2 : (2 : K) = 0)
    {g₁ g₂ g₃ : e6Data_valid.minGroup K} (hg₁ : g₁ ∈ rootPair K twB1)
    (hg₂ : g₂ ∈ rootPair K twB2) (hg₃ : g₃ ∈ rootPair K twB3) :
    ∃ u : fixedGroup K θ, u ^ 2 = 1 ∧ twistedIsogeny θ hθ hK u ≠ 1 ∧
      ∀ x : Multiplicative (Fin 5 → ZMod 3),
        Commute (g₁ * g₂ * g₃ * torusHom5 ζ hζ x * (g₁ * g₂ * g₃)⁻¹)
          (u : e6Data_valid.minGroup K) := by
  have hr : IsRoot .E6 twTheta := isRoot_twTheta
  have hρ : rho twTheta = twTheta := by decide +kernel
  have hfix : e6Data_valid.xm K twTheta 1 ∈ fixedGroup K θ := by
    rw [mem_fixedGroup, sigma_xm θ hr, hρ, twistSign_of_rho_eq hr hρ, Int.cast_one, one_mul,
      map_one]
  have hu : e6Data_valid.xm K twTheta 1 ∈ rootPair K twTheta :=
    Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup K _ _)
  refine ⟨⟨e6Data_valid.xm K twTheta 1, hfix⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show e6Data_valid.xm K twTheta 1 ^ 2 = 1
    rw [pow_two, ← e6Data_valid.xm_add]
    have : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
    rw [this, e6Data_valid.xm_zero]
  · intro h
    have h' : e6Isogeny K (e6Data_valid.xm K twTheta 1) = 1 := by
      have h1 := congrArg (fun y : ↥⁅twistedFixedGroup TwistTag.E6 K θ,
        twistedFixedGroup TwistTag.E6 K θ⁆ => (y : ModGL TwistTag.E6.tag K)) h
      exact Subtype.ext h1
    rw [e6Isogeny_xm K hr] at h'
    unfold yPar at h'
    have h3 := xPar_injective hr (h'.trans (xPar_zero (F := rootOperatorFamily .E6)
      (K := K) twTheta).symm)
    have h4 := relSignOr_mul_self (F := rootOperatorFamily .E6) (hD := e6AdjData_valid)
      (k := K) twTheta
    rw [mul_one] at h3
    rw [h3, zero_mul] at h4
    exact zero_ne_one h4
  · intro x
    have c1 : Commute g₁ (e6Data_valid.xm K twTheta 1) := commute_rootPair_B1T hg₁ hu
    have c2 : Commute g₂ (e6Data_valid.xm K twTheta 1) := commute_rootPair_B2T hg₂ hu
    have c3 : Commute g₃ (e6Data_valid.xm K twTheta 1) := commute_rootPair_B3T hg₃ hu
    have hg : Commute (g₁ * g₂ * g₃) (e6Data_valid.xm K twTheta 1) := (c1.mul_left c2).mul_left c3
    have hw : ∀ j, 1 * torusZ K ζ hζ (wvec j) * (1 : e6Data_valid.minGroup K)⁻¹ ∈
        Subgroup.centralizer {e6Data_valid.xm K twTheta 1} := by
      intro j
      rw [inv_one, one_mul, mul_one]
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      fin_cases j
      · exact commute_torusZ_cc ζ hζ hr cc_vE0a.2.2.2 hu
      · exact commute_torusZ_cc ζ hζ hr cc_vE0b.2.2.2 hu
      · exact commute_torusZ_cc ζ hζ hr cc_vT1.2.2 hu
      · exact commute_torusZ_cc ζ hζ hr cc_vT2.2.2 hu
      · exact commute_torusZ_cc ζ hζ hr cc_vT3.2.2 hu
    have ht : Commute (torusHom5 ζ hζ x) (e6Data_valid.xm K twTheta 1) := by
      have := conj_torusZ_wsum_mem ζ hζ 1 (Subgroup.centralizer {e6Data_valid.xm K twTheta 1}) hw
        (Multiplicative.toAdd x)
      rw [inv_one, one_mul, mul_one] at this
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    exact (hg.mul_left ht).mul_left hg.inv_left

theorem card_multiplicative_fin_five :
    Nat.card (Multiplicative (Fin 5 → ZMod 3)) = 3 ^ 5 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 5 → ZMod 3) ≃ _)]
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_fun, ZMod.card]

theorem tw_exists_torus_witness [Finite K] (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c)
    (hK : 4 ≤ Nat.card K) {q : ℕ} (hKq : Nat.card K = q ^ 2) (hθq : ∀ c, θ c = c ^ q)
    (h3 : 3 ∣ q + 1) :
    ∃ (E : Subgroup (fixedGroup K θ))
      (U : Subgroup ↥⁅twistedFixedGroup TwistTag.E6 K θ, twistedFixedGroup TwistTag.E6 K θ⁆),
      IsElemAbelian 3 E ∧ 3 ^ 4 ≤ Nat.card (E.map (twistedIsogeny θ hθ hK)) ∧ U ≠ ⊥ ∧
        IsPGroup 2 U ∧ E.map (twistedIsogeny θ hθ hK) ≤
          Subgroup.normalizer (U : Set ↥⁅twistedFixedGroup TwistTag.E6 K θ,
            twistedFixedGroup TwistTag.E6 K θ⁆) := by
  classical
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hKq]
    have h := Nat.sq_sub_sq q 1
    rw [one_pow] at h
    rw [h]
    exact Dvd.dvd.mul_right h3 _
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf_three h3K
  have hθζ := units_map_theta_zeta θ hθq h3 ζ hζ
  obtain ⟨g₁, g₂, g₃, hg₁, hg₂, hg₃, hfix⟩ := exists_conj_data θ ζ hζ hθζ
  have hΦ : ∀ x : Multiplicative (Fin 5 → ZMod 3),
      g₁ * g₂ * g₃ * torusHom5 ζ hζ x * (g₁ * g₂ * g₃)⁻¹ ∈ fixedGroup K θ := fun x =>
    conj_torusZ_wsum_mem ζ hζ (g₁ * g₂ * g₃) (fixedGroup K θ) hfix (Multiplicative.toAdd x)
  let ΦM : Multiplicative (Fin 5 → ZMod 3) →* e6Data_valid.minGroup K :=
    (MulAut.conj (g₁ * g₂ * g₃)).toMonoidHom.comp (torusHom5 ζ hζ)
  have hΦM : ∀ x, ΦM x = g₁ * g₂ * g₃ * torusHom5 ζ hζ x * (g₁ * g₂ * g₃)⁻¹ := fun x => rfl
  let ΦG : Multiplicative (Fin 5 → ZMod 3) →* ↥(fixedGroup K θ) :=
    ΦM.codRestrict (fixedGroup K θ) (fun x => by rw [hΦM]; exact hΦ x)
  obtain ⟨u, hu2, hu1, hcomm⟩ : ∃ u : fixedGroup K θ, u ^ 2 = 1 ∧
      twistedIsogeny θ hθ hK u ≠ 1 ∧ ∀ x : Multiplicative (Fin 5 → ZMod 3),
        Commute (g₁ * g₂ * g₃ * torusHom5 ζ hζ x * (g₁ * g₂ * g₃)⁻¹)
          (u : e6Data_valid.minGroup K) := by
    by_cases h2 : (2 : K) = 0
    · exact exists_involution_even θ hθ hK ζ hζ h2 hg₁ hg₂ hg₃
    · exact exists_involution_odd θ hθ hK ζ hζ h2 hg₁ hg₂ hg₃
  obtain ⟨U, hU, hU2, hUn⟩ := witness_of_involution (twistedIsogeny θ hθ hK) ΦG.range u hu2 hu1
    (by
      rintro _ ⟨x, rfl⟩
      exact Subtype.ext (hcomm x).eq)
  refine ⟨ΦG.range, U, ?_, ?_, hU, hU2, hUn⟩
  · exact isElemAbelian_range_of_pow_three ΦG (pow_three_multiplicative_pi 5)
  · have hmap : ΦG.range.map (twistedIsogeny θ hθ hK) =
        ((twistedIsogeny θ hθ hK).comp ΦG).range :=
      (MonoidHom.range_comp (twistedIsogeny θ hθ hK) ΦG).symm
    rw [hmap]
    have hprod := Subgroup.card_ker_mul_card_range ((twistedIsogeny θ hθ hK).comp ΦG)
    have hle : ((twistedIsogeny θ hθ hK).comp ΦG).ker ≤
        ((e6Isogeny K).comp (torusHom5 ζ hζ)).ker := by
      intro x hx
      have h1 : (twistedIsogeny θ hθ hK) (ΦG x) = 1 := hx
      have h2 : e6Isogeny K (g₁ * g₂ * g₃ * torusHom5 ζ hζ x * (g₁ * g₂ * g₃)⁻¹) = 1 := by
        have h3 := congrArg (fun y : ↥⁅twistedFixedGroup TwistTag.E6 K θ,
          twistedFixedGroup TwistTag.E6 K θ⁆ => (y : ModGL TwistTag.E6.tag K)) h1
        exact Subtype.ext h3
      exact (hom_conj_eq_one_iff (e6Isogeny K) _ _).1 h2
    have hker : Nat.card ((twistedIsogeny θ hθ hK).comp ΦG).ker ≤ 3 :=
      (Subgroup.card_le_of_le hle).trans (card_ker_torusHom5_le ζ hζ)
    rw [card_multiplicative_fin_five] at hprod
    have hpos : 0 < Nat.card ((twistedIsogeny θ hθ hK).comp ΦG).range := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card ((twistedIsogeny θ hθ hK).comp ΦG).ker *
        Nat.card ((twistedIsogeny θ hθ hK).comp ΦG).range < 3 ^ 5 := by
      calc Nat.card ((twistedIsogeny θ hθ hK).comp ΦG).ker *
            Nat.card ((twistedIsogeny θ hθ hK).comp ΦG).range
          ≤ 3 * Nat.card ((twistedIsogeny θ hθ hK).comp ΦG).range :=
            Nat.mul_le_mul_right _ hker
        _ < 3 * 3 ^ 4 := by omega
        _ = 3 ^ 5 := by norm_num
    omega

end Main

end CFSG.HardMathSupport.Dickson.Sec6.I1431
