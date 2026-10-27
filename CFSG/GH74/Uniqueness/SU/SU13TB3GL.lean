module

public import CFSG.RankThree.Asc83Table.GL23
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.GLR

open CFSG.RankThree.Asc83Table

abbrev Q8 : Type := QuaternionGroup 2

@[expose] def evalAut (p : Q8 × Q8) : Q8 → Q8
  | .a i => p.1 ^ i.val
  | .xa i => p.2 * p.1 ^ i.val

@[expose] def IsAutPair (p : Q8 × Q8) : Prop :=
  (∀ g h : Q8, evalAut p (g * h) = evalAut p g * evalAut p h) ∧ Function.Injective (evalAut p)

instance : DecidablePred IsAutPair := fun p => by unfold IsAutPair; infer_instance

@[expose] def tx : Q8 × Q8 := (.xa 0, .xa 3)

@[expose] def ty : Q8 × Q8 := (.a 3, .xa 1)

theorem classify : ∀ px py : Q8 × Q8, IsAutPair px → IsAutPair py →
    (∀ g, evalAut px (evalAut px (evalAut px g)) = g) → (∃ g, evalAut px g ≠ g) →
    (∀ g, evalAut py (evalAut py g) = g) →
    (∀ g, evalAut py (evalAut px (evalAut py g)) = evalAut px (evalAut px g)) →
    ∃ σ : Q8 × Q8, IsAutPair σ ∧ (∀ g, evalAut σ (evalAut tx g) = evalAut px (evalAut σ g)) ∧
      (∀ g, evalAut σ (evalAut ty g) = evalAut py (evalAut σ g)) := by
  decide +kernel

theorem a_eq_pow : ∀ i : ZMod (2 * 2), (QuaternionGroup.a i : Q8) = QuaternionGroup.a 1 ^ i.val := by
  decide

theorem xa_eq_mul : ∀ i : ZMod (2 * 2),
    (QuaternionGroup.xa i : Q8) = QuaternionGroup.xa 0 * QuaternionGroup.a 1 ^ i.val := by
  decide

theorem hom_eq_evalAut (ρ : Q8 →* Q8) (g : Q8) : ρ g = evalAut (ρ (.a 1), ρ (.xa 0)) g := by
  cases g with
  | a i =>
    calc ρ (.a i) = ρ (.a 1 ^ i.val) := by rw [← a_eq_pow i]
      _ = (ρ (.a 1)) ^ i.val := map_pow ρ _ _
      _ = evalAut (ρ (.a 1), ρ (.xa 0)) (.a i) := rfl
  | xa i =>
    calc ρ (.xa i) = ρ (.xa 0 * .a 1 ^ i.val) := by rw [← xa_eq_mul i]
      _ = ρ (.xa 0) * (ρ (.a 1)) ^ i.val := by rw [map_mul, map_pow]
      _ = evalAut (ρ (.a 1), ρ (.xa 0)) (.xa i) := rfl

theorem isAutPair_of_mulEquiv (ρ : Q8 ≃* Q8) : IsAutPair (ρ (.a 1), ρ (.xa 0)) := by
  have h : ∀ g, evalAut (ρ (.a 1), ρ (.xa 0)) g = ρ g := fun g =>
    (hom_eq_evalAut ρ.toMonoidHom g).symm
  refine ⟨fun g k => ?_, fun g k hgk => ?_⟩
  · rw [h, h, h, map_mul]
  · rw [h, h] at hgk
    exact ρ.injective hgk

theorem exists_mulEquiv_of_isAutPair (p : Q8 × Q8) (hp : IsAutPair p) :
    ∃ σ : Q8 ≃* Q8, ∀ g, σ g = evalAut p g := by
  have h1 : evalAut p 1 = 1 := by
    have := hp.1 1 1
    rw [mul_one] at this
    simpa using this
  let f : Q8 →* Q8 := { toFun := evalAut p, map_one' := h1, map_mul' := hp.1 }
  refine ⟨MulEquiv.ofBijective f ((Finite.injective_iff_bijective).mp hp.2), fun g => rfl⟩

@[expose] def IsOrd3 (g : GL23) : Prop := g * g * g = 1 ∧ g ≠ 1

instance : DecidablePred IsOrd3 := fun g => by unfold IsOrd3; infer_instance

theorem gl_conj3 : ∀ g h : GL23, IsOrd3 g → IsOrd3 h → ∃ k : GL23, k * g * k⁻¹ = h := by
  decide +kernel

theorem card_cube_eq_one : Fintype.card {h : GL23 // h * h * h = 1} = 9 := by decide +kernel

theorem pPrimeCore_GL23 : CFSG.pPrimeCore 2 GL23 = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hK hcop
  by_contra hne
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hg1 : (a : GL23) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hodd : Odd (Nat.card K) := Nat.coprime_two_left.mp hcop
  have hdvd48 : Nat.card K ∣ 48 := by
    rw [← card_GL23]; exact Subgroup.card_subgroup_dvd_card K
  have hdvd3 : Nat.card K ∣ 3 := by
    have hc : Nat.Coprime (Nat.card K) 16 := by
      have h2 : Nat.Coprime 2 (Nat.card K) := hcop
      have : Nat.Coprime (2 ^ 4) (Nat.card K) := Nat.Coprime.pow_left 4 h2
      exact this.symm
    exact hc.dvd_of_dvd_mul_left (by simpa using hdvd48)
  have hord : orderOf (a : GL23) = 3 := by
    have h1 : orderOf (a : GL23) ∣ Nat.card K := by
      have := Subgroup.orderOf_dvd_natCard K a.2
      exact this
    have h3 : orderOf (a : GL23) ∣ 3 := h1.trans hdvd3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg1
    · exact h
  have hcube : (a : GL23) * a * a = 1 := by
    have h3 : (a : GL23) ^ (orderOf (a : GL23)) = 1 := pow_orderOf_eq_one _
    rw [hord, pow_three'] at h3
    exact h3
  have hmem : ∀ h : {h : GL23 // h * h * h = 1}, h.1 ∈ K := by
    intro h
    by_cases hh : h.1 = 1
    · rw [hh]; exact K.one_mem
    · obtain ⟨k, hk⟩ := gl_conj3 a h.1 ⟨hcube, hg1⟩ ⟨h.2, hh⟩
      rw [← hk]
      exact hK.conj_mem _ a.2 k
  have hinj : Function.Injective (fun h : {h : GL23 // h * h * h = 1} => (⟨h.1, hmem h⟩ : ↥K)) := by
    intro h h' hh
    exact Subtype.ext (congrArg (fun w : ↥K => (w : GL23)) hh)
  have h9 : 9 ≤ Nat.card K := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card, card_cube_eq_one] at this
  have := Nat.le_of_dvd (by norm_num) hdvd3
  omega

@[expose] def uU : GL23 := gl23 !![1, 1; 0, 1] !![1, 2; 0, 1] (by decide) (by decide)

@[expose] def vV : GL23 := gl23 !![1, 0; 0, 2] !![1, 0; 0, 2] (by decide) (by decide)

@[expose] def g0Fun : DihedralGroup 3 → GL23
  | .r i => uU ^ i.val
  | .sr i => vV * uU ^ i.val

@[expose] def g0 : DihedralGroup 3 →* GL23 where
  toFun := g0Fun
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem quatRange_conj : ∀ (g : GL23) (q : Q8), ∃ q' : Q8, quatHom q' = g * quatHom q * g⁻¹ := by
  decide +kernel

instance quatRange_normal : (quatHom.range).Normal :=
  ⟨fun n hn g => by
    obtain ⟨q, rfl⟩ := hn
    obtain ⟨q', hq'⟩ := quatRange_conj g q
    exact ⟨q', hq'⟩⟩

@[expose] noncomputable def rho' : GL23 →* MulAut Q8 :=
  (MulAut.congr (MonoidHom.ofInjective quatHom_injective).symm).toMonoidHom.comp
    (MulAut.conjNormal (H := quatHom.range))

theorem quatHom_rho' (g : GL23) (q : Q8) : quatHom (rho' g q) = g * quatHom q * g⁻¹ := by
  have h : MonoidHom.ofInjective quatHom_injective (rho' g q) =
      (MulAut.conjNormal (H := quatHom.range) g) (MonoidHom.ofInjective quatHom_injective q) := by
    simp [rho']
  have := congrArg Subtype.val h
  exact this

theorem rho'_u : ∀ q, rho' uU q = evalAut tx q := by
  intro q
  apply quatHom_injective
  rw [quatHom_rho']
  revert q
  decide +kernel

theorem rho'_v : ∀ q, rho' vV q = evalAut ty q := by
  intro q
  apply quatHom_injective
  rw [quatHom_rho']
  revert q
  decide +kernel

@[expose] noncomputable def phi' : DihedralGroup 3 →* MulAut Q8 := rho'.comp g0

@[expose] noncomputable def theta' : Q8 ⋊[phi'] DihedralGroup 3 →* GL23 :=
  SemidirectProduct.lift quatHom g0 (fun d => by
    ext q
    simp [phi', quatHom_rho'])

theorem card_Q8 : Nat.card Q8 = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem card_D3 : Nat.card (DihedralGroup 3) = 6 := by
  rw [Nat.card_eq_fintype_card, DihedralGroup.card]

theorem quat_g0_eq_one : ∀ (q : Q8) (d : DihedralGroup 3), quatHom q * g0 d = 1 → q = 1 ∧ d = 1 := by
  decide +kernel

theorem theta'_bijective : Function.Bijective theta' := by
  have hinj : Function.Injective theta' := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : quatHom x.left * g0 x.right = 1 := hx
    obtain ⟨h1, h2⟩ := quat_g0_eq_one _ _ hx'
    ext
    · exact h1
    · exact h2
  refine hinj.bijective_of_nat_card_le ?_
  rw [SemidirectProduct.card, card_Q8, card_D3, card_GL23]

@[expose] noncomputable def glEquiv : GL23 ≃* Q8 ⋊[phi'] DihedralGroup 3 :=
  (MulEquiv.ofBijective theta' theta'_bijective).symm

section D3

variable {Λ : Type} [Group Λ] (x y : Λ)

@[expose] def xpow (i : ZMod 3) : Λ := x ^ i.val

theorem xpow_add (hx3 : x ^ 3 = 1) (i j : ZMod 3) : xpow x (i + j) = xpow x i * xpow x j := by
  unfold xpow
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ hx3).symm

theorem xpow_zero : xpow x (0 : ZMod 3) = 1 := by simp [xpow]

theorem xpow_neg (hx3 : x ^ 3 = 1) (i : ZMod 3) : xpow x (-i) = (xpow x i)⁻¹ := by
  have h := xpow_add x hx3 i (-i)
  have h0 : ∀ i : ZMod 3, i + -i = 0 := by decide
  rw [h0, xpow_zero] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem xpow_mul_y (hx3 : x ^ 3 = 1) (hy2 : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x⁻¹) (i : ZMod 3) :
    xpow x i * y = y * xpow x (-i) := by
  have hy' : y * y = 1 := by rw [← pow_two]; exact hy2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy'
  have h1 : y * x ^ i.val * y⁻¹ = (x ^ i.val)⁻¹ := by
    rw [← conj_pow, hyx, inv_pow]
  rw [xpow_neg x hx3]
  unfold xpow
  calc x ^ i.val * y = y * (y⁻¹ * x ^ i.val * y) := by group
    _ = y * (y * x ^ i.val * y⁻¹) := by rw [hyinv]
    _ = y * (x ^ i.val)⁻¹ := by rw [h1]

@[expose] def thetaFun : DihedralGroup 3 → Λ
  | .r i => xpow x i
  | .sr i => y * xpow x i

theorem thetaFun_mul (hx3 : x ^ 3 = 1) (hy2 : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x⁻¹)
    (a b : DihedralGroup 3) : thetaFun x y (a * b) = thetaFun x y a * thetaFun x y b := by
  have hy' : y * y = 1 := by rw [← pow_two]; exact hy2
  rcases a with i | i <;> rcases b with j | j
  · simp only [DihedralGroup.r_mul_r, thetaFun, xpow_add x hx3]
  · simp only [DihedralGroup.r_mul_sr, thetaFun]
    have hsub : ∀ i j : ZMod 3, j - i = -i + j := by decide
    calc y * xpow x (j - i) = y * xpow x (-i + j) := by rw [hsub]
      _ = y * (xpow x (-i) * xpow x j) := by rw [xpow_add x hx3]
      _ = (y * xpow x (-i)) * xpow x j := by group
      _ = (xpow x i * y) * xpow x j := by rw [xpow_mul_y x y hx3 hy2 hyx]
      _ = xpow x i * (y * xpow x j) := by group
  · simp only [DihedralGroup.sr_mul_r, thetaFun, xpow_add x hx3, mul_assoc]
  · simp only [DihedralGroup.sr_mul_sr, thetaFun]
    have hsub : ∀ i j : ZMod 3, j - i = -i + j := by decide
    calc xpow x (j - i) = xpow x (-i + j) := by rw [hsub]
      _ = xpow x (-i) * xpow x j := xpow_add x hx3 _ _
      _ = (y * y) * xpow x (-i) * xpow x j := by rw [hy', one_mul]
      _ = y * (y * xpow x (-i)) * xpow x j := by group
      _ = y * (xpow x i * y) * xpow x j := by rw [xpow_mul_y x y hx3 hy2 hyx]
      _ = y * xpow x i * (y * xpow x j) := by group

end D3

theorem val_one3 : (1 : ZMod 3).val = 1 := by decide

theorem val_two3 : (2 : ZMod 3).val = 2 := by decide

section Lam

variable {Λ : Type} [Group Λ] [Finite Λ] (Q : Subgroup Λ) [Q.Normal] (e : Q8 ≃* ↥Q)

@[expose] noncomputable def rho : Λ →* MulAut Q8 :=
  (MulAut.congr e.symm).toMonoidHom.comp (MulAut.conjNormal (H := Q))

omit [Finite Λ] in
theorem coe_rho (l : Λ) (q : Q8) : ((e (rho Q e l q) : ↥Q) : Λ) = l * (e q : Λ) * l⁻¹ := by
  have : e (rho Q e l q) = MulAut.conjNormal l (e q) := by
    simp [rho]
  rw [this, MulAut.conjNormal_apply]

theorem involution_Q8 : ∀ q : Q8, q * q = 1 → q ≠ 1 → q = QuaternionGroup.a 2 := by decide

omit [Finite Λ] in
theorem rho_a2 (l : Λ) : rho Q e l (QuaternionGroup.a 2) = QuaternionGroup.a 2 := by
  apply involution_Q8
  · rw [← map_mul]
    have : (QuaternionGroup.a 2 : Q8) * QuaternionGroup.a 2 = 1 := by decide
    rw [this, map_one]
  · intro h
    have h1 : rho Q e l (QuaternionGroup.a 2) = rho Q e l 1 := by rw [map_one]; exact h
    have := (rho Q e l).injective h1
    exact absurd this (by decide)

omit [Finite Λ] in
theorem z0_central (l : Λ) : l * (e (QuaternionGroup.a 2) : Λ) * l⁻¹ = (e (QuaternionGroup.a 2) : Λ) := by
  rw [← coe_rho Q e l, rho_a2]

section Main

omit [Finite Λ] [Q.Normal] in
theorem x_ne_one {x : Λ} (hxQ : ∃ q ∈ Q, x * q * x⁻¹ ≠ q) : x ≠ 1 := by
  obtain ⟨q, -, hq⟩ := hxQ
  rintro rfl
  exact hq (by group)

omit [Finite Λ] [Q.Normal] in
theorem card_Q' (e : Q8 ≃* ↥Q) : Nat.card ↥Q = 8 := by
  rw [← Nat.card_congr e.toEquiv, card_Q8]

omit [Finite Λ] [Q.Normal] in
theorem x_not_mem_Q (e : Q8 ≃* ↥Q) {x : Λ} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : x ∉ Q := by
  intro hx
  have hord : orderOf x = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hx3 hx1
  have h1 : orderOf x ∣ Nat.card ↥Q := Subgroup.orderOf_dvd_natCard Q hx
  rw [hord, card_Q' Q e] at h1
  exact absurd h1 (by decide)

@[expose] def thetaHom {x y : Λ} (hx3 : x ^ 3 = 1) (hy2 : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x⁻¹) :
    DihedralGroup 3 →* Λ where
  toFun := thetaFun x y
  map_one' := by
    rw [DihedralGroup.one_def]
    simp [thetaFun, xpow_zero]
  map_mul' := thetaFun_mul x y hx3 hy2 hyx

omit [Finite Λ] [Q.Normal] in
theorem y_inv_x {x y : Λ} (hyx : y * x * y⁻¹ = x⁻¹) : y * x⁻¹ = x * y := by
  calc y * x⁻¹ = (y * x⁻¹ * y⁻¹) * y := by group
    _ = (y * x * y⁻¹)⁻¹ * y := by group
    _ = x * y := by rw [hyx, inv_inv]

omit [Finite Λ] in
theorem theta_mem_Q (e : Q8 ≃* ↥Q) {x y : Λ} (hx3 : x ^ 3 = 1) (hy2 : y ^ 2 = 1)
    (hyx : y * x * y⁻¹ = x⁻¹) (hxQ : ∃ q ∈ Q, x * q * x⁻¹ ≠ q) (hy1 : y ≠ 1) (d : DihedralGroup 3)
    (hd : thetaFun x y d ∈ Q) : d = 1 := by
  have hx1 : x ≠ 1 := x_ne_one Q hxQ
  have hxQ' : x ∉ Q := x_not_mem_Q Q e hx3 hx1
  have hy' : y * y = 1 := by rw [← pow_two]; exact hy2
  rcases d with i | i
  · have hi : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hi i with rfl | rfl | rfl
    · exact DihedralGroup.one_def.symm
    · exfalso
      apply hxQ'
      have : thetaFun x y (DihedralGroup.r 1) = x := by simp [thetaFun, xpow, val_one3]
      rwa [this] at hd
    · exfalso
      apply hxQ'
      have h2 : thetaFun x y (DihedralGroup.r 2) = x ^ 2 := by simp [thetaFun, xpow, val_two3]
      rw [h2] at hd
      have : x = (x ^ 2) ^ 2 := by
        calc x = x * (x ^ 3) := by rw [hx3, mul_one]
          _ = (x ^ 2) ^ 2 := by group
      rw [this]
      exact Q.pow_mem hd 2
  · exfalso
    set w : Λ := y * xpow x i with hw
    have hw2 : w * w = 1 := by
      calc w * w = y * (xpow x i * y) * xpow x i := by rw [hw]; group
        _ = y * (y * xpow x (-i)) * xpow x i := by rw [xpow_mul_y x y hx3 hy2 hyx]
        _ = (y * y) * (xpow x (-i) * xpow x i) := by group
        _ = 1 := by
          rw [hy', ← xpow_add x hx3, (show ∀ i : ZMod 3, -i + i = 0 by decide) i, xpow_zero, one_mul]
    have hw1 : w ≠ 1 := by
      intro h1
      apply hy1
      have hyi : y = (xpow x i)⁻¹ := by
        rw [hw] at h1
        exact eq_inv_of_mul_eq_one_left h1
      have hy3 : y ^ 3 = 1 := by
        rw [hyi, inv_pow]
        have : (xpow x i) ^ 3 = 1 := by
          unfold xpow
          rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]
        rw [this, inv_one]
      calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
        _ = 1 := by rw [hy3, hy2]; group
    have hwQ : w ∈ Q := hd
    set q : Q8 := e.symm ⟨w, hwQ⟩ with hq
    have hqe : (e q : Λ) = w := by rw [hq]; simp
    have hq2 : q * q = 1 := by
      apply e.injective
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, hqe, hw2, map_one, Subgroup.coe_one]
    have hq1 : q ≠ 1 := by
      intro h
      apply hw1
      rw [← hqe, h, map_one, Subgroup.coe_one]
    have hqa : q = QuaternionGroup.a 2 := involution_Q8 q hq2 hq1
    have hcentral := z0_central Q e x
    rw [← hqa, hqe] at hcentral
    have hxy : x * y = y * x⁻¹ := (y_inv_x hyx).symm
    have hx3' : x * x * x = 1 := by rw [← pow_three']; exact hx3
    have hinv1 : x⁻¹ = x * x := (eq_inv_of_mul_eq_one_left hx3').symm
    have hinv : x⁻¹ * x⁻¹ = x := by
      rw [hinv1]
      calc x * x * (x * x) = (x * x * x) * x := by group
        _ = x := by rw [hx3', one_mul]
    have hcomm : x⁻¹ * xpow x i = xpow x i * x⁻¹ :=
      (Commute.inv_left (Commute.pow_right (Commute.refl x) _)).eq
    have h2 : x * w * x⁻¹ = w * x := by
      calc x * w * x⁻¹ = (x * y) * xpow x i * x⁻¹ := by rw [hw]; group
        _ = (y * x⁻¹) * xpow x i * x⁻¹ := by rw [hxy]
        _ = y * (x⁻¹ * xpow x i) * x⁻¹ := by group
        _ = y * (xpow x i * x⁻¹) * x⁻¹ := by rw [hcomm]
        _ = y * xpow x i * (x⁻¹ * x⁻¹) := by group
        _ = w * x := by rw [hinv, hw]
    have : w * x = w := by rw [← h2]; exact hcentral
    exact hx1 (mul_eq_left.mp this)

@[expose] noncomputable def phi {x y : Λ} (hx3 : x ^ 3 = 1) (hy2 : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x⁻¹) :
    DihedralGroup 3 →* MulAut Q8 :=
  (rho Q e).comp (thetaHom hx3 hy2 hyx)

@[expose] noncomputable def thetaL {x y : Λ} (hx3 : x ^ 3 = 1) (hy2 : y ^ 2 = 1)
    (hyx : y * x * y⁻¹ = x⁻¹) : Q8 ⋊[phi Q e hx3 hy2 hyx] DihedralGroup 3 →* Λ :=
  SemidirectProduct.lift (Q.subtype.comp e.toMonoidHom) (thetaHom hx3 hy2 hyx) (fun d => by
    ext q
    simp [phi, coe_rho])

theorem thetaL_bijective (hcard : Nat.card Λ = 48) {x y : Λ} (hx3 : x ^ 3 = 1) (hy2 : y ^ 2 = 1)
    (hyx : y * x * y⁻¹ = x⁻¹) (hxQ : ∃ q ∈ Q, x * q * x⁻¹ ≠ q) (hy1 : y ≠ 1) :
    Function.Bijective (thetaL Q e hx3 hy2 hyx) := by
  have hinj : Function.Injective (thetaL Q e hx3 hy2 hyx) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hw' : (e w.left : Λ) * thetaFun x y w.right = 1 := hw
    have hmem : thetaFun x y w.right ∈ Q := by
      have h1 : thetaFun x y w.right = ((e w.left : ↥Q) : Λ)⁻¹ := eq_inv_of_mul_eq_one_right hw'
      rw [h1]
      exact Q.inv_mem (e w.left).2
    have hd : w.right = 1 := theta_mem_Q Q e hx3 hy2 hyx hxQ hy1 _ hmem
    have h1 : thetaFun x y w.right = 1 := by
      rw [hd, DihedralGroup.one_def]; simp [thetaFun, xpow_zero]
    rw [h1, mul_one] at hw'
    have : e w.left = 1 := Subtype.ext hw'
    have hl : w.left = 1 := e.injective (by rw [this, map_one])
    ext
    · exact hl
    · exact hd
  refine hinj.bijective_of_nat_card_le ?_
  rw [SemidirectProduct.card, card_Q8, card_D3, hcard]

end Main

theorem nonempty_mulEquiv_GL23 (hcard : Nat.card Λ = 48) (e : Q8 ≃* ↥Q) (x y : Λ) (hx3 : x ^ 3 = 1) (hy2 : y ^ 2 = 1)
    (hyx : y * x * y⁻¹ = x⁻¹) (hxQ : ∃ q ∈ Q, x * q * x⁻¹ ≠ q) (hy1 : y ≠ 1) :
    Nonempty (Λ ≃* GL23) := by
  have hx3' : x * x * x = 1 := by rw [← pow_three']; exact hx3
  have hy' : y * y = 1 := by rw [← pow_two]; exact hy2
  have hfun : ∀ (l : Λ) (g : Q8), evalAut (rho Q e l (.a 1), rho Q e l (.xa 0)) g = rho Q e l g :=
    fun l g => (hom_eq_evalAut (rho Q e l).toMonoidHom g).symm
  set px : Q8 × Q8 := (rho Q e x (.a 1), rho Q e x (.xa 0)) with hpx
  set py : Q8 × Q8 := (rho Q e y (.a 1), rho Q e y (.xa 0)) with hpy
  have hPx : IsAutPair px := isAutPair_of_mulEquiv (rho Q e x)
  have hPy : IsAutPair py := isAutPair_of_mulEquiv (rho Q e y)
  have hx1 : ∀ g, rho Q e x (rho Q e x (rho Q e x g)) = g := by
    intro g
    have h : rho Q e x * rho Q e x * rho Q e x = 1 := by
      rw [← map_mul, ← map_mul, hx3']; exact map_one _
    simpa using congrArg (fun f : MulAut Q8 => f g) h
  have hy1' : ∀ g, rho Q e y (rho Q e y g) = g := by
    intro g
    have h : rho Q e y * rho Q e y = 1 := by rw [← map_mul, hy']; exact map_one _
    simpa using congrArg (fun f : MulAut Q8 => f g) h
  have hyx' : ∀ g, rho Q e y (rho Q e x (rho Q e y g)) = rho Q e x (rho Q e x g) := by
    intro g
    have hinv : x⁻¹ = x * x := (eq_inv_of_mul_eq_one_left hx3').symm
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy'
    have h : rho Q e y * rho Q e x * rho Q e y = rho Q e x * rho Q e x := by
      rw [← map_mul, ← map_mul, ← map_mul]
      congr 1
      have := hyx
      rw [hyinv, hinv] at this
      exact this
    simpa using congrArg (fun f : MulAut Q8 => f g) h
  have hne : ∃ g, rho Q e x g ≠ g := by
    obtain ⟨q, hq, hqne⟩ := hxQ
    refine ⟨e.symm ⟨q, hq⟩, fun h => hqne ?_⟩
    have := congrArg (fun g => ((e g : ↥Q) : Λ)) h
    simp only [coe_rho] at this
    simpa using this
  have hpxf : ∀ g, evalAut px g = rho Q e x g := hfun x
  have hpyf : ∀ g, evalAut py g = rho Q e y g := hfun y
  obtain ⟨σ, hσ, hσx, hσy⟩ := classify px py hPx hPy
    (by intro g; rw [hpxf, hpxf, hpxf]; exact hx1 g)
    (by obtain ⟨g, hg⟩ := hne; exact ⟨g, by rw [hpxf]; exact hg⟩)
    (by intro g; rw [hpyf, hpyf]; exact hy1' g)
    (by intro g; rw [hpyf, hpxf, hpyf, hpxf, hpxf]; exact hyx' g)
  obtain ⟨σt, hσt⟩ := exists_mulEquiv_of_isAutPair σ hσ
  have hX : ∀ g, σt (rho' uU g) = rho Q e x (σt g) := by
    intro g
    calc σt (rho' uU g) = evalAut σ (rho' uU g) := hσt _
      _ = evalAut σ (evalAut tx g) := by rw [rho'_u]
      _ = evalAut px (evalAut σ g) := hσx g
      _ = rho Q e x (evalAut σ g) := hpxf _
      _ = rho Q e x (σt g) := by rw [hσt]
  have hY : ∀ g, σt (rho' vV g) = rho Q e y (σt g) := by
    intro g
    calc σt (rho' vV g) = evalAut σ (rho' vV g) := hσt _
      _ = evalAut σ (evalAut ty g) := by rw [rho'_v]
      _ = evalAut py (evalAut σ g) := hσy g
      _ = rho Q e y (evalAut σ g) := hpyf _
      _ = rho Q e y (σt g) := by rw [hσt]
  have hpow : ∀ (n : ℕ) (g : Q8), σt ((rho' uU ^ n) g) = (rho Q e x ^ n) (σt g) := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, hX]
  have hD : ∀ (d : DihedralGroup 3) (g : Q8), σt (phi' d g) = phi Q e hx3 hy2 hyx d (σt g) := by
    intro d g
    rcases d with i | i
    · have h1 : phi' (.r i) = rho' uU ^ i.val := by
        simp [phi', g0, g0Fun]
      have h2 : phi Q e hx3 hy2 hyx (.r i) = rho Q e x ^ i.val := by
        simp [phi, thetaHom, thetaFun, xpow]
      rw [h1, h2, hpow]
    · have h1 : phi' (.sr i) = rho' vV * rho' uU ^ i.val := by
        simp [phi', g0, g0Fun]
      have h2 : phi Q e hx3 hy2 hyx (.sr i) = rho Q e y * rho Q e x ^ i.val := by
        simp [phi, thetaHom, thetaFun, xpow]
      rw [h1, h2, MulAut.mul_apply, MulAut.mul_apply, hY, hpow]
  have hcongr : ∀ d : DihedralGroup 3,
      (phi Q e hx3 hy2 hyx d).trans σt.symm = σt.symm.trans (phi' ((MulEquiv.refl _) d)) := by
    intro d
    ext g
    simp only [MulEquiv.trans_apply, MulEquiv.coe_refl, id_eq]
    have := hD d (σt.symm g)
    rw [σt.apply_symm_apply] at this
    rw [← this, σt.symm_apply_apply]
  exact ⟨(MulEquiv.ofBijective (thetaL Q e hx3 hy2 hyx) (thetaL_bijective Q e hcard hx3 hy2 hyx hxQ hy1)).symm.trans
    ((SemidirectProduct.congr σt.symm (MulEquiv.refl _) hcongr).trans glEquiv.symm)⟩

end Lam

end CFSG.GH74.Uniqueness.SU.SU13.GLR
