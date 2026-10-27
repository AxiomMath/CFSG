module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSqClass
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsJModel

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup
open scoped commutatorElement

universe u

variable {F : Type u} [Field F] [Finite F]

structure HarrisHyp (F : Type u) [Field F] [Finite F] : Prop where
  char : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F = p ^ f ∧ Even f
  odd : IsOddPrimePower (Nat.card F)
  sq : IsSquare (-1 : F)
  q4 : Nat.card F % 4 = 1
  four_le : 4 ≤ twoVal F

theorem harrisHyp_of {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hfe : Even f) (h16 : 16 ∣ p ^ f - 1) : HarrisHyp F := by
  have hq := Finite.one_lt_card (α := F)
  have hf : 1 ≤ f := by
    by_contra h
    rw [show f = 0 by omega, pow_zero] at hF
    omega
  have hodd := isOddPrimePower_of hp hp2 hf hF
  have hq4 : Nat.card F % 4 = 1 := by rw [hF]; exact pow_mod_four_of_even hp hp2 hfe
  refine ⟨⟨p, f, hp, hp2, hF, hfe⟩, hodd, ?_, hq4, ?_⟩
  · classical
    have : Fintype F := Fintype.ofFinite F
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  · have h16' : 2 ^ 4 ∣ Nat.card F - 1 := by rw [hF]; simpa using h16
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).mp h16'

theorem HarrisHyp.two_ne_zero (hH : HarrisHyp F) : (2 : F) ≠ 0 :=
  two_ne_zero_of_isOddPrimePower hH.odd

omit [Finite F] in
theorem units_eq_one_or_neg_one {u : Fˣ} (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  have h : ((u : F) - 1) * ((u : F) + 1) = 0 := by
    have := congrArg (fun w : Fˣ => (w : F)) hu
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    linear_combination this
  rcases mul_eq_zero.mp h with h | h
  · left
    ext
    simpa [sub_eq_zero] using h
  · right
    ext
    simpa [add_eq_zero_iff_eq_neg] using h

theorem HarrisHyp.neg_one_ne_one (hH : HarrisHyp F) : (-1 : Fˣ) ≠ 1 := by
  intro h
  apply hH.two_ne_zero
  have := congrArg (fun w : Fˣ => (w : F)) h
  simp only [Units.val_neg, Units.val_one] at this
  linear_combination -this

section Psi

variable (F) in
open Classical in
@[expose] def psiF : F ≃+* F :=
  if h : ∃ σ : F ≃+* F, σ ≠ 1 ∧ σ * σ = 1 then h.choose else 1

theorem HarrisHyp.exists_inv (hH : HarrisHyp F) : ∃ σ : F ≃+* F, σ ≠ 1 ∧ σ * σ = 1 := by
  obtain ⟨p, f, hp, hp2, hF, hfe⟩ := hH.char
  have h2f : 2 ∣ Nat.card (F ≃+* F) := by
    rw [card_ringAut F hp hF]
    exact even_iff_two_dvd.mp hfe
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' 2 h2f
  refine ⟨σ, ?_, ?_⟩
  · intro h
    rw [h, orderOf_one] at hσ
    norm_num at hσ
  · rw [← pow_two, ← hσ, pow_orderOf_eq_one]

theorem HarrisHyp.psiF_spec (hH : HarrisHyp F) : psiF F ≠ 1 ∧ psiF F * psiF F = 1 := by
  unfold psiF
  split_ifs with h
  · exact h.choose_spec
  · exact absurd hH.exists_inv h

theorem HarrisHyp.psiF_ne_one (hH : HarrisHyp F) : psiF F ≠ 1 := hH.psiF_spec.1

theorem HarrisHyp.psiF_mul_self (hH : HarrisHyp F) : psiF F * psiF F = 1 := hH.psiF_spec.2

theorem HarrisHyp.orderOf_psiF (hH : HarrisHyp F) : orderOf (psiF F) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hH.psiF_mul_self) hH.psiF_ne_one

theorem HarrisHyp.eq_psiF (hH : HarrisHyp F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσ : σ * σ = 1) :
    σ = psiF F :=
  ringAut_eq_of_sq hσ hH.psiF_mul_self hσ1 hH.psiF_ne_one

theorem HarrisHyp.eq_psiF_of_orderOf (hH : HarrisHyp F) {σ : F ≃+* F} (hσ : orderOf σ = 2) :
    σ = psiF F := by
  refine hH.eq_psiF (fun h => ?_) (by rw [← pow_two, ← hσ, pow_orderOf_eq_one])
  rw [h, orderOf_one] at hσ
  norm_num at hσ

end Psi

section GalTwo

variable (F) in
@[expose] def galTwo : Subgroup (F ≃+* F) where
  carrier := {σ | ∃ k : ℕ, σ ^ 2 ^ k = 1}
  one_mem' := ⟨0, one_pow _⟩
  mul_mem' := by
    rintro σ τ ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    rw [(show Commute σ τ from ringAut_comm σ τ).mul_pow, pow_add, pow_mul, hk, one_pow,
      one_mul, mul_comm, pow_mul, hl, one_pow]
  inv_mem' := by
    rintro σ ⟨k, hk⟩
    exact ⟨k, by rw [inv_pow, hk, inv_one]⟩

theorem HarrisHyp.psiF_mem_galTwo (hH : HarrisHyp F) : psiF F ∈ galTwo F :=
  ⟨1, by rw [pow_one, pow_two, hH.psiF_mul_self]⟩

end GalTwo

theorem fu_mem_zpowers (σ : F ≃+* F) (c : Fˣ) {b : Fˣ} (hb : b ∈ zpowers c) :
    fu F σ b ∈ zpowers c := by
  obtain ⟨j, rfl⟩ := hb
  rw [map_zpow]
  exact zpow_mem (mem_zpowers_of_orderOf_dvd c _ (orderOf_map_dvd _ _)) j

theorem fu_mem_zpowers_iff (σ : F ≃+* F) (c : Fˣ) (b : Fˣ) :
    fu F σ b ∈ zpowers c ↔ b ∈ zpowers c := by
  refine ⟨fun h => ?_, fu_mem_zpowers σ c⟩
  have := fu_mem_zpowers σ⁻¹ c h
  rwa [fu_inv_fu] at this

omit [Finite F] in
theorem twist_mem_iff {U : Subgroup Fˣ} (ε : Bool) (y : Fˣ) : twist F ε y ∈ U ↔ y ∈ U := by
  refine ⟨fun h => ?_, fun h => twist_mem h ε⟩
  have := twist_mem h ε
  rwa [twist_twist_self] at this

omit [Finite F] in
theorem twist_pow (ε : Bool) (x : Fˣ) (j : ℕ) : twist F ε (x ^ j) = twist F ε x ^ j := by
  cases ε
  · rfl
  · simp

section S0

variable (F) in
@[expose] def sylS0 : Subgroup (PGammaL2 F) where
  carrier := {x | ∃ a ∈ zpowers (stdGen F), ∃ ε : Bool, ∃ σ ∈ galTwo F, x = nm F a ε σ}
  one_mem' := ⟨1, one_mem _, false, 1, one_mem _, nm_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, ε, σ, hσ, rfl⟩ ⟨b, hb, ε', τ, hτ, rfl⟩
    exact ⟨_, mul_mem ha (twist_mem (fu_mem_zpowers σ _ hb) ε), _, _, mul_mem hσ hτ,
      nm_mul a b ε ε' σ τ⟩
  inv_mem' := by
    rintro _ ⟨a, ha, ε, σ, hσ, rfl⟩
    rw [nm_inv]
    exact ⟨_, twist_mem (fu_mem_zpowers _ _ (inv_mem ha)) ε, ε, σ⁻¹, inv_mem hσ, rfl⟩

theorem pow_two_pow_twoVal_eq_one {b : Fˣ} (hb : b ∈ zpowers (stdGen F)) :
    b ^ 2 ^ twoVal F = 1 := by
  have := orderOf_dvd_of_mem_zpowers hb
  rw [orderOf_stdGen] at this
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem isPGroup_sylS0 : IsPGroup 2 (sylS0 F) := by
  rintro ⟨x, a, ha, ε, σ, ⟨k, hk⟩, rfl⟩
  have hpow : ∀ j : ℕ, ∃ b ∈ zpowers (stdGen F), ∃ ε' : Bool,
      nm F a ε σ ^ j = nm F b ε' (σ ^ j) := by
    intro j
    induction j with
    | zero => exact ⟨1, one_mem _, false, by rw [pow_zero, pow_zero, nm_one]⟩
    | succ j ih =>
      obtain ⟨b, hb, ε', h⟩ := ih
      rw [pow_succ, h, nm_mul, ← pow_succ]
      exact ⟨_, mul_mem hb (twist_mem (fu_mem_zpowers _ _ ha) _), _, rfl⟩
  obtain ⟨b, hb, ε', h⟩ := hpow (2 ^ k)
  rw [hk] at h
  have h1 : nm F b ε' 1 ^ 2 ^ (twoVal F + 1) = 1 := by
    cases ε'
    · rw [nm_false_pow, pow_succ, pow_mul, pow_two_pow_twoVal_eq_one hb, one_pow, nm_one]
    · rw [pow_succ', pow_mul, pow_two, nm_true_mul_self, one_pow]
  refine ⟨k + (twoVal F + 1), Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [pow_add, pow_mul, h, h1]

theorem nm_mem_sylS0 {a : Fˣ} (ha : a ∈ zpowers (stdGen F)) (ε : Bool) {σ : F ≃+* F}
    (hσ : σ ∈ galTwo F) : nm F a ε σ ∈ sylS0 F :=
  ⟨a, ha, ε, σ, hσ, rfl⟩

theorem zpowers_sq_le : zpowers (stdGen F ^ 2) ≤ zpowers (stdGen F) :=
  (zpowers_le).mpr (pow_mem (mem_zpowers _) 2)

theorem map_stdT_le_sylS0 (hsq : IsSquare (-1 : F)) : (stdT F).map (incl F) ≤ sylS0 F := by
  intro x hx
  obtain ⟨y, hy, ε, rfl⟩ := (mem_map_stdT_iff hsq x).mp hx
  exact nm_mem_sylS0 (zpowers_sq_le hy) ε (one_mem _)

end S0

section Twist

theorem mem_zpowers_sq_or {a : Fˣ} (ha : a ∈ zpowers (stdGen F)) :
    a ∈ zpowers (stdGen F ^ 2) ∨ a * (stdGen F)⁻¹ ∈ zpowers (stdGen F ^ 2) := by
  obtain ⟨j, rfl⟩ := ha
  rcases Int.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    refine ⟨m, ?_⟩
    show (stdGen F ^ 2) ^ m = stdGen F ^ j
    rw [hm, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  · right
    refine ⟨m, ?_⟩
    show (stdGen F ^ 2) ^ m = stdGen F ^ j * (stdGen F)⁻¹
    rw [hm, ← zpow_natCast, ← zpow_mul, ← zpow_neg_one, ← zpow_add]
    congr 1
    push_cast
    ring

theorem pow_half_eq_one_iff (hodd : IsOddPrimePower (Nat.card F)) {a : Fˣ} :
    a ^ 2 ^ (twoVal F - 1) = 1 ↔ a ∈ zpowers (stdGen F ^ 2) := by
  constructor
  · intro h
    apply mem_zpowers_of_orderOf_dvd
    rw [orderOf_stdGen_sq hodd]
    exact orderOf_dvd_of_pow_eq_one h
  · intro h
    have := orderOf_dvd_of_mem_zpowers h
    rw [orderOf_stdGen_sq hodd] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this

theorem pow_half_eq_neg_one (hodd : IsOddPrimePower (Nat.card F)) {a : Fˣ}
    (ha : a ∈ zpowers (stdGen F)) (ha2 : a ∉ zpowers (stdGen F ^ 2)) :
    a ^ 2 ^ (twoVal F - 1) = -1 := by
  have h1 := one_le_twoVal hodd
  rcases units_eq_one_or_neg_one (u := a ^ 2 ^ (twoVal F - 1)) (by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel h1, pow_two_pow_twoVal_eq_one ha]) with h | h
  · exact absurd ((pow_half_eq_one_iff hodd).mp h) ha2
  · exact h

theorem orderOf_of_not_mem (hodd : IsOddPrimePower (Nat.card F)) {a : Fˣ}
    (ha : a ∈ zpowers (stdGen F)) (ha2 : a ∉ zpowers (stdGen F ^ 2)) :
    orderOf a = 2 ^ twoVal F := by
  have hdvd : orderOf a ∣ 2 ^ twoVal F := by
    have := orderOf_dvd_of_mem_zpowers ha
    rwa [orderOf_stdGen] at this
  obtain ⟨i, hi, hia⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  by_contra hne
  apply ha2
  apply mem_zpowers_of_orderOf_dvd
  rw [orderOf_stdGen_sq hodd, hia]
  exact Nat.pow_dvd_pow 2 (by
    rcases Nat.lt_or_ge i (twoVal F) with h | h
    · omega
    · exact absurd (by rw [hia, show i = twoVal F by omega]) hne)

theorem HarrisHyp.stdGen_not_mem (hH : HarrisHyp F) : stdGen F ∉ zpowers (stdGen F ^ 2) := by
  intro h
  have := orderOf_dvd_of_mem_zpowers h
  rw [orderOf_stdGen, orderOf_stdGen_sq hH.odd] at this
  have h4 := hH.four_le
  have := Nat.le_of_dvd (by positivity) this
  have : 2 ^ (twoVal F - 1) < 2 ^ twoVal F := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

omit [Finite F] in
theorem fu_neg_one (σ : F ≃+* F) : fu F σ (-1) = -1 := by
  ext
  simp

omit [Finite F] in
theorem twist_fu_pow_eq {m : ℕ} {b : Fˣ} (hb : (b ^ 2 ^ m) ^ 2 = 1) (ε : Bool)
    (σ : F ≃+* F) : twist F ε (fu F σ b) ^ 2 ^ m = b ^ 2 ^ m := by
  rw [← twist_pow, ← map_pow]
  rcases units_eq_one_or_neg_one hb with h | h
  · rw [h, map_one, twist_one]
  · rw [h, fu_neg_one]
    cases ε
    · rfl
    · simp

variable (F) in
open Classical in
@[expose] def epsR : Bool := decide (fu F (psiF F) (stdGen F ^ 2) ≠ stdGen F ^ 2)

theorem HarrisHyp.twist_epsR_sq (hH : HarrisHyp F) :
    twist F (epsR F) (fu F (psiF F) (stdGen F ^ 2)) = stdGen F ^ 2 := by
  obtain ⟨p, f, hp, hp2, hF, -⟩ := hH.char
  by_cases h : fu F (psiF F) (stdGen F ^ 2) = stdGen F ^ 2
  · have : epsR F = false := by
      classical
      unfold epsR
      exact decide_eq_false (not_not.mpr h)
    rw [this, twist_false, h]
  · have : epsR F = true := by
      classical
      unfold epsR
      exact decide_eq_true h
    rw [this, twist_true]
    rcases fix_or_inv_of_order_two hp hp2 hF (psiF F) (by rw [pow_one]; exact hH.orderOf_psiF)
      (stdGen F ^ 2) (orderOf_stdGen_sq hH.odd) (by have := hH.four_le; omega) with h' | h'
    · exact absurd h' h
    · rw [h', inv_inv]

theorem HarrisHyp.twist_epsR_of_mem (hH : HarrisHyp F) {c : Fˣ}
    (hc : c ∈ zpowers (stdGen F ^ 2)) : twist F (epsR F) (fu F (psiF F) c) = c := by
  obtain ⟨j, rfl⟩ := hc
  rw [map_zpow, twist_zpow, hH.twist_epsR_sq]

theorem HarrisHyp.twist_epsR_gen (hH : HarrisHyp F) :
    twist F (epsR F) (fu F (psiF F) (stdGen F)) = -stdGen F := by
  obtain ⟨p, f, hp, hp2, hF, -⟩ := hH.char
  set w := twist F (epsR F) (fu F (psiF F) (stdGen F)) * (stdGen F)⁻¹
  have hw : w ^ 2 = 1 := by
    simp only [w, mul_pow, ← twist_pow, ← map_pow]
    rw [hH.twist_epsR_of_mem (mem_zpowers _), inv_pow, mul_inv_cancel]
  rcases units_eq_one_or_neg_one hw with h | h
  · exfalso
    have h' : twist F (epsR F) (fu F (psiF F) (stdGen F)) = stdGen F := mul_inv_eq_one.mp h
    have hfix : Units.map (psiF F).toRingHom (stdGen F) = stdGen F ∨
        Units.map (psiF F).toRingHom (stdGen F) = (stdGen F)⁻¹ := by
      cases hε : epsR F
      · rw [hε, twist_false] at h'
        exact Or.inl h'
      · rw [hε, twist_true] at h'
        exact Or.inr (inv_eq_iff_eq_inv.mp h')
    have := two_pow_add_dvd_of_fix_or_inv hp hp2 hF (psiF F) le_rfl
      (by rw [pow_one]; exact hH.orderOf_psiF) (stdGen F) orderOf_stdGen hfix
    exact not_two_pow_twoVal_succ_dvd F Finite.one_lt_card this
  · calc twist F (epsR F) (fu F (psiF F) (stdGen F)) = w * stdGen F := by
          simp [w]
      _ = -stdGen F := by rw [h, neg_one_mul]

theorem HarrisHyp.twist_epsR_of_not_mem (hH : HarrisHyp F) {a : Fˣ}
    (ha : a ∈ zpowers (stdGen F)) (ha2 : a ∉ zpowers (stdGen F ^ 2)) :
    twist F (epsR F) (fu F (psiF F) a) = -a := by
  rcases mem_zpowers_sq_or ha with h | h
  · exact absurd h ha2
  · have ha' : a = a * (stdGen F)⁻¹ * stdGen F := by group
    rw [ha', map_mul, twist_mul, hH.twist_epsR_of_mem h, hH.twist_epsR_gen, mul_neg]

end Twist

section Central

omit [Finite F] in
theorem nm_mul_z (a : Fˣ) (ε : Bool) (σ : F ≃+* F) :
    nm F a ε σ * nm F (-1) false 1 = nm F (-a) ε σ := by
  rw [nm_mul, fu_neg_one]
  cases ε <;> simp

omit [Finite F] in
theorem z_mul_nm (a : Fˣ) (ε : Bool) (σ : F ≃+* F) :
    nm F (-1) false 1 * nm F a ε σ = nm F (-a) ε σ := by
  rw [nm_mul]
  simp [fu_one]

omit [Finite F] in
theorem z_mul_self : nm F (-1) false 1 * nm F (-1) false 1 = 1 := by
  rw [z_mul_nm, neg_neg, nm_one]

theorem HarrisHyp.v₀_mul_nm (hH : HarrisHyp F) {a : Fˣ} (ha : a ∈ zpowers (stdGen F))
    (ε : Bool) (σ : F ≃+* F) :
    (a ∈ zpowers (stdGen F ^ 2) → nm F 1 (epsR F) (psiF F) * nm F a ε σ =
      nm F a ε σ * nm F 1 (epsR F) (psiF F)) ∧
    (a ∉ zpowers (stdGen F ^ 2) → nm F 1 (epsR F) (psiF F) * nm F a ε σ =
      nm F (-1) false 1 * (nm F a ε σ * nm F 1 (epsR F) (psiF F))) := by
  have h1 : nm F a ε σ * nm F 1 (epsR F) (psiF F) = nm F a (xor ε (epsR F)) (σ * psiF F) := by
    rw [nm_mul, map_one, twist_one, mul_one]
  have h2 : nm F 1 (epsR F) (psiF F) * nm F a ε σ =
      nm F (twist F (epsR F) (fu F (psiF F) a)) (xor ε (epsR F)) (σ * psiF F) := by
    rw [nm_mul, one_mul, Bool.xor_comm, ringAut_comm]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h1, h2, hH.twist_epsR_of_mem h]
  · rw [h1, h2, hH.twist_epsR_of_not_mem ha h, z_mul_nm]

end Central

section Formulas

omit [Finite F] in
theorem nm_mul_inv_nm (u w : Fˣ) (ε : Bool) (σ : F ≃+* F) :
    nm F u ε σ * (nm F w ε σ)⁻¹ = nm F (u * w⁻¹) false 1 := by
  rw [mul_inv_eq_iff_eq_mul, nm_mul]
  simp [fu_one]

theorem commutator_nm_eq (a b : Fˣ) (ε ε' : Bool) (σ τ : F ≃+* F) :
    ⁅nm F a ε σ, nm F b ε' τ⁆ = nm F (a * twist F ε (fu F σ b) *
      (b * twist F ε' (fu F τ a))⁻¹) false 1 := by
  have h : ⁅nm F a ε σ, nm F b ε' τ⁆ =
      nm F a ε σ * nm F b ε' τ * (nm F b ε' τ * nm F a ε σ)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h, nm_mul, nm_mul, Bool.xor_comm ε' ε, ringAut_comm τ σ, nm_mul_inv_nm]

omit [Finite F] in
theorem nm_conj_refl (b c : Fˣ) (ε : Bool) (σ : F ≃+* F) :
    nm F b ε σ * nm F c true 1 * (nm F b ε σ)⁻¹ =
      nm F (b * b * twist F ε (fu F σ c)) true 1 := by
  rw [nm_inv, nm_mul, mul_one, nm_mul, fu_twist, fu_fu_inv, twist_twist, mul_inv_cancel]
  have h1 : xor (xor ε true) ε = true := by cases ε <;> rfl
  rw [h1, twist_true, inv_inv]
  congr 1
  rw [mul_right_comm]

end Formulas

end CFSG.ComponentClassification.AutL2Facts
