module

public import CFSG.Timmesfeld.Orders.ExceptionalTwisted
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ExceptionalOrders

theorem units_map_eq_pow {K : Type*} [Field K] {q : ℕ} {σ : K →+* K} (hσ : ∀ c, σ c = c ^ q)
    (ζ : Kˣ) : Units.map σ.toMonoidHom ζ = ζ ^ q :=
  Units.ext (by
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_ofClass, hσ,
      Units.val_pow_eq_pow_val])

section D4

theorem eq_one_of_odd_pow_cycle {G : Type*} [CommGroup G] {q : ℕ} (hq : Odd q)
    {x₀ x₁ x₂ x₃ : G} (h₁ : x₁ = x₀ ^ q) (h₃ : x₃ = x₁ ^ q) (h₀ : x₀ = x₃ ^ q)
    (k₀ : x₀ ^ 2 = x₂) (k₁ : x₁ ^ 2 = x₂) (k₃ : x₃ ^ 2 = x₂) (k₂ : x₂ ^ 2 = x₀ * x₁ * x₃) :
    x₀ = 1 ∧ x₁ = 1 ∧ x₂ = 1 ∧ x₃ = 1 := by
  obtain ⟨m, rfl⟩ := hq
  have e₁ : x₁ = x₀ * x₂ ^ m := by rw [h₁, pow_succ, pow_mul, k₀, mul_comm]
  have e₃ : x₃ = x₁ * x₂ ^ m := by rw [h₃, pow_succ, pow_mul, k₁, mul_comm]
  have e₀ : x₀ = x₃ * x₂ ^ m := by rw [h₀, pow_succ, pow_mul, k₃, mul_comm]
  have hbbb : x₂ ^ m * x₂ ^ m * x₂ ^ m = 1 := by
    refine mul_left_cancel (a := x₀) ?_
    calc x₀ * (x₂ ^ m * x₂ ^ m * x₂ ^ m) = x₀ * x₂ ^ m * x₂ ^ m * x₂ ^ m := by ac_rfl
      _ = x₁ * x₂ ^ m * x₂ ^ m := by rw [← e₁]
      _ = x₃ * x₂ ^ m := by rw [← e₃]
      _ = x₀ := e₀.symm
      _ = x₀ * 1 := (mul_one _).symm
  have h4 : x₀ ^ 3 * x₀ = x₀ ^ 3 * 1 := by
    calc x₀ ^ 3 * x₀ = (x₀ ^ 2) ^ 2 := by rw [← pow_succ, ← pow_mul]
      _ = x₂ ^ 2 := by rw [k₀]
      _ = x₀ * x₁ * x₃ := k₂
      _ = x₀ ^ 3 * (x₂ ^ m * x₂ ^ m * x₂ ^ m) := by
        rw [e₃, e₁, pow_three]
        ac_rfl
      _ = x₀ ^ 3 * 1 := by rw [hbbb]
  have hx₀ : x₀ = 1 := mul_left_cancel h4
  have hx₂ : x₂ = 1 := by rw [← k₀, hx₀, one_pow]
  have hx₁ : x₁ = 1 := by rw [e₁, hx₀, hx₂, one_pow, one_mul]
  have hx₃ : x₃ = 1 := by rw [e₃, hx₁, hx₂, one_pow, one_mul]
  exact ⟨hx₀, hx₁, hx₂, hx₃⟩

theorem eq_one_of_cycle_ker_D4 {G : Type*} [CommGroup G] {q : ℕ} (hq : Odd q) {c : Fin 4 → G}
    (h1 : c 1 = c 0 ^ q) (h3 : c 3 = c 1 ^ q) (h0 : c 0 = c 3 ^ q)
    (hk : ∀ j : Fin 4, ∏ i : Fin 4, c i ^ (Tag.D4.cartan i j) = 1) : c = 1 := by
  have k0 := hk 0
  have k1 := hk 1
  have k2 := hk 2
  have k3 := hk 3
  simp only [Tag.cartan, Int.reduceNeg, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.prod_univ_four, zpow_ofNat,
    Matrix.cons_val_one, pow_zero, mul_one, Matrix.cons_val, zpow_neg, pow_one, one_mul]
    at k0 k1 k2 k3
  have k2' : c 2 ^ 2 = c 0 * c 1 * c 3 := by
    refine div_eq_one.1 (Eq.trans ?_ k2)
    simp only [div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  obtain ⟨hx0, hx1, hx2, hx3⟩ := eq_one_of_odd_pow_cycle hq h1 h3 h0 (mul_inv_eq_one.1 k0)
    (mul_inv_eq_one.1 k1) (inv_mul_eq_one.1 k3).symm k2'
  funext i
  fin_cases i <;> first | exact hx0 | exact hx1 | exact hx2 | exact hx3

variable {K : Type} [Field K]

theorem eq_one_of_mem_compat_inf_ker_D4 {q : ℕ} (hq : Odd q) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ q) {c : Fin TwistTag.D4.tag.rank → Kˣ}
    (hc : c ∈ compatSubgroup (t := TwistTag.D4) σ)
    (hk : c ∈ (zpowMatrix (G := Kˣ) TwistTag.D4.tag.cartan).ker) : c = 1 := by
  have hmap := units_map_eq_pow hσ
  rw [mem_compatSubgroup] at hc
  have p0 : TwistTag.D4.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have p1 : TwistTag.D4.perm ⟨1, by decide⟩ = ⟨3, by decide⟩ := by decide
  have p3 : TwistTag.D4.perm ⟨3, by decide⟩ = ⟨0, by decide⟩ := by decide
  have h1 := hc ⟨0, by decide⟩
  have h3 := hc ⟨1, by decide⟩
  have h0 := hc ⟨3, by decide⟩
  rw [p0, hmap] at h1
  rw [p1, hmap] at h3
  rw [p3, hmap] at h0
  exact eq_one_of_cycle_ker_D4 hq h1 h3 h0 fun j => congrFun (MonoidHom.mem_ker.1 hk) j

theorem card_compat_inf_ker_D4_of_odd {q : ℕ} (hq : Odd q) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ q) :
    Nat.card ↥(compatSubgroup (t := TwistTag.D4) σ ⊓
      (zpowMatrix (G := Kˣ) TwistTag.D4.tag.cartan).ker) = 1 := by
  rw [Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
  intro c hc
  obtain ⟨hcompat, hker⟩ := Subgroup.mem_inf.1 hc
  exact eq_one_of_mem_compat_inf_ker_D4 hq hσ hcompat hker

end D4

section E6

variable {K : Type} [Field K] [Finite K]

theorem card_compat_inf_ker_E6_of_card {q : ℕ} (hK : Nat.card K = q ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ q) :
    Nat.card ↥(compatSubgroup (t := TwistTag.E6) σ ⊓
      (zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan).ker) = Nat.gcd 3 (q + 1) := by
  set S := {ζ : Kˣ // ζ ^ 3 = 1 ∧
    ∀ i, ζ ^ e6Exp (TwistTag.E6.perm i) = ζ ^ ((q : ℤ) * e6Exp i)}
  have hmap := units_map_eq_pow hσ
  have hcompat : ∀ ζ : Kˣ, (fun j => ζ ^ e6Exp j) ∈ compatSubgroup (t := TwistTag.E6) σ ↔
      ∀ i, ζ ^ e6Exp (TwistTag.E6.perm i) = ζ ^ ((q : ℤ) * e6Exp i) := fun ζ => by
    refine (mem_compatSubgroup σ).trans (forall_congr' fun i => ?_)
    rw [map_zpow, hmap, ← zpow_natCast, ← zpow_mul]
  have hcard : Nat.card ↥(compatSubgroup (t := TwistTag.E6) σ ⊓
      (zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan).ker) = Nat.card S := by
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun ζ : S => ⟨fun j => ζ.1 ^ e6Exp j,
      Subgroup.mem_inf.2 ⟨(hcompat ζ.1).2 ζ.2.2,
        mem_ker_zpowMatrix_twistedE6.2 ⟨ζ.1, ζ.2.1, rfl⟩⟩⟩) ⟨fun ζ ζ' h => ?_, fun c => ?_⟩)
    · have h1 := congrFun (congrArg Subtype.val h) ⟨5, by decide⟩
      simp only [e6Exp_last, zpow_neg, zpow_one, inv_inj] at h1
      exact Subtype.ext h1
    · obtain ⟨hc, hk⟩ := Subgroup.mem_inf.1 c.2
      obtain ⟨ζ, hζ, hcζ⟩ := mem_ker_zpowMatrix_twistedE6.1 hk
      refine ⟨⟨ζ, hζ, (hcompat ζ).1 (hcζ ▸ hc)⟩, Subtype.ext ?_⟩
      exact hcζ.symm
  rw [hcard]
  have hS1 : (∀ ζ : S, ζ.1 = 1) → Nat.card S = 1 := fun hS => by
    have : Unique S := ⟨⟨⟨1, one_pow 3, fun _ => by rw [one_zpow, one_zpow]⟩⟩,
      fun ζ => Subtype.ext (hS ζ)⟩
    exact Nat.card_unique
  have hq3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hq3 with hq3 | hq3 | hq3
  ·
    have hS : ∀ ζ : S, ζ.1 = 1 := fun ζ => by
      obtain ⟨ζ, h3, hcond⟩ := ζ
      have h0 := hcond ⟨0, by decide⟩
      rw [e6Exp_perm_zero, e6Exp_zero] at h0
      have hdvd : (3 : ℤ) ∣ (q : ℤ) * -5 - 0 := by
        have : (q : ℤ) % 3 = 0 := by exact_mod_cast hq3
        omega
      rw [zpow_eq_zpow_of_dvd h3 hdvd, zpow_zero, zpow_neg_one, inv_eq_one] at h0
      exact h0
    rw [hS1 hS, Nat.gcd_rec, show (q + 1) % 3 = 1 by omega, Nat.gcd_one_left]
  ·
    have hS : ∀ ζ : S, ζ.1 = 1 := fun ζ => by
      obtain ⟨ζ, h3, hcond⟩ := ζ
      have h0 := hcond ⟨0, by decide⟩
      rw [e6Exp_perm_zero, e6Exp_zero] at h0
      have hdvd : (3 : ℤ) ∣ (q : ℤ) * -5 - -2 := by
        have : (q : ℤ) % 3 = 1 := by exact_mod_cast hq3
        omega
      rw [zpow_eq_zpow_of_dvd h3 hdvd] at h0
      change ζ = 1
      calc ζ = ζ ^ (-1 : ℤ) * ζ ^ (2 : ℤ) := by group
        _ = ζ ^ (-2 : ℤ) * ζ ^ (2 : ℤ) := by rw [h0]
        _ = 1 := by group
    rw [hS1 hS, Nat.gcd_rec, show (q + 1) % 3 = 2 by omega]
    rfl
  ·
    have hcond : ∀ ζ : Kˣ, ζ ^ 3 = 1 →
        ∀ i, ζ ^ e6Exp (TwistTag.E6.perm i) = ζ ^ ((q : ℤ) * e6Exp i) := fun ζ h3 i => by
      refine zpow_eq_zpow_of_dvd h3 ?_
      have h1 := dvd_e6Exp i
      have h2 : (3 : ℤ) ∣ (q : ℤ) - 2 := by
        have : (q : ℤ) % 3 = 2 := by exact_mod_cast hq3
        omega
      have h3' : (3 : ℤ) ∣ ((q : ℤ) - 2) * e6Exp i := dvd_mul_of_dvd_left h2 _
      have := dvd_sub h1 h3'
      convert this using 1
      ring
    have hS : Nat.card S = Nat.card (powMonoidHom 3 : Kˣ →* Kˣ).ker :=
      Nat.card_congr ⟨fun ζ => ⟨ζ.1, ζ.2.1⟩, fun ζ => ⟨ζ.1, ζ.2, hcond ζ.1 ζ.2⟩,
        fun _ => rfl, fun _ => rfl⟩
    rw [hS, IsCyclic.card_powMonoidHom_ker, Nat.card_units, hK]
    have h3 : 3 ∣ q ^ 2 - 1 := by
      have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
      omega
    rw [Nat.gcd_eq_right h3, Nat.gcd_rec, show (q + 1) % 3 = 0 by omega, Nat.gcd_zero_left]

end E6

section Orders

variable {K : Type} [Field K] [Finite K]

theorem card_graphFixedRootGroup_E6 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    Nat.card (graphFixedRootGroup TwistTag.E6 K σ) = ordTwistedE6 (p ^ f) := by
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq := CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.E6) hp hf hK hσ
  have : Fintype (WeylGroup TwistTag.E6.tag) := Fintype.ofFinite _
  have hC := card_graphFixedRootGroup hsurj hq
  rw [sum_length_relWeylTwist_E6, ncard_posRoots_twistedE6] at hC
  have hT := card_compatTorus_mul (t := TwistTag.E6) (K := K) σ
  rw [card_compat_inf_ker_E6_of_card hK hσ, card_compatSubgroup] at hT
  simp only [hq] at hT
  rw [prod_orbit_E6] at hT
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  rw [ordTwistedE6, ← ordTwistedE6_mul _ hq1, ← hT, hC]
  refine (Nat.div_eq_of_eq_mul_left (Nat.gcd_pos_of_pos_left _ (by norm_num)) ?_).symm
  ring

theorem card_graphFixedRootGroup_D4_of_ne_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    Nat.card (graphFixedRootGroup TwistTag.D4 K σ) = ordTrialityD4 (p ^ f) := by
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq := CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.D4) hp hf hK hσ
  have : Fintype (WeylGroup TwistTag.D4.tag) := Fintype.ofFinite _
  have hC := card_graphFixedRootGroup hsurj hq
  rw [sum_length_relWeylTwist_D4, ncard_posRoots_twistedD4] at hC
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hT := card_compatTorus_mul (t := TwistTag.D4) (K := K) σ
  rw [card_compat_inf_ker_D4_of_odd hodd hσ, card_compatSubgroup, mul_one] at hT
  simp only [hq] at hT
  rw [prod_orbit_D4] at hT
  rw [hC, hT, ← ordTrialityD4_eq _ (Nat.one_le_pow _ _ hp.pos)]

end Orders

section Models

variable {G : Type} [Group G]

theorem card_of_twistedChevalleyModel_E6 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h : TwistedChevalleyModel G .E6 (p ^ f)) : Nat.card G = ordTwistedE6 (p ^ f) := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_derivedCentralQuotient hp hf hK σ hσ]
  exact card_graphFixedRootGroup_E6 hp hf hK σ hσ

theorem card_of_twistedChevalleyModel_D4_of_ne_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h : TwistedChevalleyModel G .D4 (p ^ f)) :
    Nat.card G = ordTrialityD4 (p ^ f) := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_derivedCentralQuotient hp hf hK σ hσ]
  exact card_graphFixedRootGroup_D4_of_ne_two hp hp2 hf hK σ hσ

theorem card_chevalleyExceptionalModel_of_ne_two {t : StatedLieTag} {p f : ℕ} (hp2 : p ≠ 2)
    (h : ChevalleyExceptionalModel G t p f) :
    Nat.card G = match t with
      | .G2 => ordG2 (p ^ f) | .F4 => ordF4 (p ^ f) | .E6 => ordE6 (p ^ f)
      | .E7 => ordE7 (p ^ f) | .E8 => ordE8 (p ^ f) | .twistedE6 => ordTwistedE6 (p ^ f)
      | .trialityD4 => ordTrialityD4 (p ^ f) | _ => 0 := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  cases t
  case G2 => exact card_of_untwistedChevalleyModel_G2 hm
  case F4 => exact card_of_untwistedChevalleyModel_F4 hm
  case E6 => exact card_of_untwistedChevalleyModel_E6 hm
  case E7 => exact card_of_untwistedChevalleyModel_E7 hm
  case E8 => exact card_of_untwistedChevalleyModel_E8 hm
  case twistedE6 => exact card_of_twistedChevalleyModel_E6 hp hf hm
  case trialityD4 => exact card_of_twistedChevalleyModel_D4_of_ne_two hp hp2 hf hm
  all_goals exact hm.elim

end Models

end CFSG.ClassicalInvolution
