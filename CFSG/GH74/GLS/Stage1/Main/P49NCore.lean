module

public import CFSG.GH74.GLS.Stage1.Main.P49HMain

public section

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49N

section FourGroup

variable {M : Type} [Group M]

theorem fix_two {U : Subgroup M} (hU : IVK.IsFourSubgroup U) {c : M} {a b : M} (ha : a ∈ U)
    (hb : b ∈ U) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hca : c * a * c⁻¹ = a)
    (hcb : c * b * c⁻¹ = b) : ∀ x ∈ U, c * x * c⁻¹ = x := by
  have hsq : ∀ x ∈ U, x * x = 1 := fun x hx => P49T.sq_of_four hU hx
  intro x hx
  rcases (CFSG.QuasithinUnique.Unc25Small.mem_klein_iff hU.2 hsq ha hb ha1 hb1 hab x).1 hx with
    h | h | h | h
  · rw [h]; simp
  · rw [h]; exact hca
  · rw [h]; exact hcb
  · rw [h]
    calc c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
      _ = a * b := by rw [hca, hcb]

theorem exists_fixed_of_sq {U : Subgroup M} (hU : IVK.IsFourSubgroup U) {t : M}
    (htU : ∀ x ∈ U, t * x * t⁻¹ ∈ U) (ht2 : t * t = 1) (ht : ∃ v ∈ U, t * v * t⁻¹ ≠ v) :
    ∃ w ∈ U, w ≠ 1 ∧ t * w * t⁻¹ = w := by
  have hsq : ∀ x ∈ U, x * x = 1 := fun x hx => P49T.sq_of_four hU hx
  obtain ⟨v, hvU, hv⟩ := ht
  have hv1 : v ≠ 1 := by
    rintro rfl; apply hv; simp
  set v' := t * v * t⁻¹ with hv'
  have hv'U : v' ∈ U := htU v hvU
  have hv'1 : v' ≠ 1 := by
    intro h; apply hv1
    have := congrArg (fun y => t⁻¹ * y * t) h
    simpa [hv', mul_assoc] using this
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hvv' : v ≠ v' := fun h => hv h.symm
  have hback : t * v' * t⁻¹ = v := by
    rw [hv', htinv]
    calc t * (t * v * t) * t = (t * t) * v * (t * t) := by group
      _ = v := by rw [ht2]; simp
  refine ⟨v * v', U.mul_mem hvU hv'U, ?_, ?_⟩
  · intro h
    apply hvv'
    have : v = v'⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right (hsq v' hv'U)]
  · calc t * (v * v') * t⁻¹ = (t * v * t⁻¹) * (t * v' * t⁻¹) := by group
      _ = v' * v := by rw [← hv', hback]
      _ = v * v' := P49T.comm_of_four hU hv'U hvU

end FourGroup

section Sign

variable {M : Type} [Group M] [Finite M]


theorem exists_sgn {U : Subgroup M} (hU : IVK.IsFourSubgroup U)
    (hUn : ∀ m : M, ∀ v ∈ U, m * v * m⁻¹ ∈ U) :
    ∃ sgn : M →* ℤˣ, (∀ m : M, (∀ v ∈ U, m * v * m⁻¹ = v) → sgn m = 1) ∧
      ∀ p : M, (∃ w ∈ U, w ≠ 1 ∧ p * w * p⁻¹ = w) → (∃ v ∈ U, p * v * p⁻¹ ≠ v) → sgn p = -1 := by
  classical
  have : Fintype M := Fintype.ofFinite M
  have hUnorm : U.Normal := ⟨fun v hv m => hUn m v hv⟩
  have hsq : ∀ x ∈ U, x * x = 1 := fun x hx => P49T.sq_of_four hU hx
  refine ⟨(Equiv.Perm.sign).comp ((MulAut.toPerm ↥U).comp MulAut.conjNormal), ?_, ?_⟩
  · intro m hm
    have : (MulAut.toPerm ↥U) (MulAut.conjNormal m) = 1 := by
      ext ⟨v, hv⟩
      change (MulAut.conjNormal m (⟨v, hv⟩ : ↥U) : M) = v
      rw [MulAut.conjNormal_apply]
      exact hm v hv
    simp [this]
  · rintro p ⟨w, hwU, hw1, hpw⟩ ⟨v, hvU, hv⟩
    have hv1 : v ≠ 1 := by rintro rfl; apply hv; simp
    have hvw : v ≠ w := by rintro rfl; exact hv hpw
    have hvU' : p * v * p⁻¹ ∈ U := hUn p v hvU
    have hmem := fun y => CFSG.QuasithinUnique.Unc25Small.mem_klein_iff hU.2 hsq hwU hvU hw1 hv1
      (Ne.symm hvw) y
    have hpv : p * v * p⁻¹ = w * v := by
      rcases (hmem _).1 hvU' with h | h | h | h
      · exfalso; apply hv1
        have := congrArg (fun y => p⁻¹ * y * p) h
        simpa [mul_assoc] using this
      · exfalso; apply hvw
        have h' : p * v * p⁻¹ = p * w * p⁻¹ := h.trans hpw.symm
        exact mul_left_cancel (mul_right_cancel h')
      · exact absurd h hv
      · exact h
    have hpwv : p * (w * v) * p⁻¹ = v := by
      calc p * (w * v) * p⁻¹ = (p * w * p⁻¹) * (p * v * p⁻¹) := by group
        _ = w * (w * v) := by rw [hpw, hpv]
        _ = v := by rw [← mul_assoc, hsq w hwU, one_mul]
    have hwvU : w * v ∈ U := U.mul_mem hwU hvU
    have hne : (⟨v, hvU⟩ : ↥U) ≠ ⟨w * v, hwvU⟩ := by
      intro h
      have h' : v = w * v := congrArg Subtype.val h
      apply hw1
      have : w * v = 1 * v := by rw [one_mul]; exact h'.symm
      exact mul_right_cancel this
    have hwv1 : w * v ≠ 1 := by
      intro h
      apply hvw
      have : v = w⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this, inv_eq_of_mul_eq_one_right (hsq w hwU)]
    have hσ : (MulAut.toPerm ↥U) (MulAut.conjNormal p) = Equiv.swap ⟨v, hvU⟩ ⟨w * v, hwvU⟩ := by
      have hσ1 : (MulAut.toPerm ↥U) (MulAut.conjNormal p) ⟨1, U.one_mem⟩ = ⟨1, U.one_mem⟩ := by
        apply Subtype.ext
        change (MulAut.conjNormal p (⟨1, U.one_mem⟩ : ↥U) : M) = 1
        rw [MulAut.conjNormal_apply]; simp
      have hσw : (MulAut.toPerm ↥U) (MulAut.conjNormal p) ⟨w, hwU⟩ = ⟨w, hwU⟩ := by
        apply Subtype.ext
        change (MulAut.conjNormal p (⟨w, hwU⟩ : ↥U) : M) = w
        rw [MulAut.conjNormal_apply]; exact hpw
      have hσv : (MulAut.toPerm ↥U) (MulAut.conjNormal p) ⟨v, hvU⟩ = ⟨w * v, hwvU⟩ := by
        apply Subtype.ext
        change (MulAut.conjNormal p (⟨v, hvU⟩ : ↥U) : M) = w * v
        rw [MulAut.conjNormal_apply]; exact hpv
      have hσwv : (MulAut.toPerm ↥U) (MulAut.conjNormal p) ⟨w * v, hwvU⟩ = ⟨v, hvU⟩ := by
        apply Subtype.ext
        change (MulAut.conjNormal p (⟨w * v, hwvU⟩ : ↥U) : M) = v
        rw [MulAut.conjNormal_apply]; exact hpwv
      ext ⟨e, he⟩
      rcases (hmem e).1 he with h | h | h | h
      · have h1 : (⟨e, he⟩ : ↥U) = ⟨1, U.one_mem⟩ := Subtype.ext h
        rw [h1, hσ1, Equiv.swap_apply_of_ne_of_ne]
        · intro h'; exact hv1 (congrArg Subtype.val h').symm
        · intro h'; exact hwv1 (congrArg Subtype.val h').symm
      · have h1 : (⟨e, he⟩ : ↥U) = ⟨w, hwU⟩ := Subtype.ext h
        rw [h1, hσw, Equiv.swap_apply_of_ne_of_ne]
        · intro h'; exact hvw (congrArg Subtype.val h').symm
        · intro h'
          apply hv1
          have h'' : w = w * v := congrArg Subtype.val h'
          have : w * v = w * 1 := by rw [mul_one]; exact h''.symm
          exact mul_left_cancel this
      · have h1 : (⟨e, he⟩ : ↥U) = ⟨v, hvU⟩ := Subtype.ext h
        rw [h1, hσv, Equiv.swap_apply_left]
      · have h1 : (⟨e, he⟩ : ↥U) = ⟨w * v, hwvU⟩ := Subtype.ext h
        rw [h1, hσwv, Equiv.swap_apply_right]
    simp [hσ, Equiv.Perm.sign_swap hne]

end Sign

section Abstract

variable {M : Type} [Group M] [Finite M]

theorem abstract_N (A S U : Subgroup M) (u' x p : M)
    (hAn : A.Normal) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : IsPGroup 2 ↥A)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) (hAS : A ≤ S) (hu'S : u' ∈ S)
    (hSsq : ∀ s ∈ S, s * s ∈ A)
    (hu'2 : u' * u' = 1) (hu'A : u' ∉ A) (hu'inv : ∀ a ∈ A, u' * a * u'⁻¹ = a⁻¹)
    (hF : ∀ m : M, ∀ a ∈ A, ∃ a' ∈ A, m * (a * u') * m⁻¹ = a' * u')
    (hU : IVK.IsFourSubgroup U) (hUA : U ≤ A) (hU1 : ∀ a ∈ A, a * a = 1 → a ∈ U)
    (hUn : ∀ m : M, ∀ v ∈ U, m * v * m⁻¹ ∈ U)
    (hx3 : IsPGroup 3 ↥(zpowers x)) (hx : ∃ v ∈ U, x * v * x⁻¹ ≠ v)
    (hpU : ∃ w ∈ U, w ≠ 1 ∧ p * w * p⁻¹ = w) (hp : ∃ v ∈ U, p * v * p⁻¹ ≠ v) :
    ∃ h₀ t t' : M, orderOf h₀ = 2 ∧ orderOf t = 2 ∧ orderOf t' = 2 ∧ h₀ ∈ S ∧
      (∀ w ∈ U, h₀ * w = w * h₀) ∧ h₀ * t = t * h₀ ∧ h₀ * t' = t' * h₀ ∧
      (∀ w ∈ U, t * w * t⁻¹ ∈ U) ∧ (∀ w ∈ U, t' * w * t'⁻¹ ∈ U) ∧
      (∃ w ∈ U, t * w * t⁻¹ ≠ w) ∧ (∃ w ∈ U, t' * w * t'⁻¹ ≠ w) ∧
      (∃ w ∈ U, t * w * t⁻¹ = w ∧ t' * w * t'⁻¹ ≠ w) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  classical
  have hUnorm : U.Normal := ⟨fun v hv m => hUn m v hv⟩
  have hsq : ∀ v ∈ U, v * v = 1 := fun v hv => P49T.sq_of_four hU hv
  obtain ⟨sgn, hsgn1, hsgnp⟩ := exists_sgn hU hUn
  obtain ⟨k₃, hk₃⟩ := hx3 ⟨x, mem_zpowers x⟩
  have hxk : x ^ (3 ^ k₃) = 1 := by simpa using congrArg Subtype.val hk₃
  have hxfix : ∀ w ∈ U, w ≠ 1 → x * w * x⁻¹ ≠ w := by
    intro w hw hw1 hfix
    obtain ⟨v, hvU, hv⟩ := hx
    exact hv (P49H.trivial_of_fixed hU (fun y hy => hUn x y hy) hxk hw hw1 hfix v hvU)
  have hCA : ∀ a ∈ A, x * a * x⁻¹ = a → a = 1 := by
    intro a ha hxa
    by_contra ha1
    obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.mp hA2 ⟨a, ha⟩
    rw [Subgroup.orderOf_mk] at hi
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply ha1
      simpa using hi
    have hdvd : 2 ^ (i - 1) ∣ orderOf a := by rw [hi]; exact pow_dvd_pow 2 (Nat.sub_le i 1)
    have hb := orderOf_pow_of_dvd (by positivity : 2 ^ (i - 1) ≠ 0) hdvd
    rw [hi, Nat.pow_div (Nat.sub_le i 1) (by norm_num)] at hb
    have hb2 : orderOf (a ^ 2 ^ (i - 1)) = 2 := by
      rw [hb]
      have : i - (i - 1) = 1 := by omega
      rw [this]
    have hbb : a ^ 2 ^ (i - 1) * a ^ 2 ^ (i - 1) = 1 := by
      have := pow_orderOf_eq_one (a ^ 2 ^ (i - 1))
      rw [hb2, pow_two] at this
      exact this
    have hb1 : a ^ 2 ^ (i - 1) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hb2
      exact absurd hb2 (by norm_num)
    have hbA : a ^ 2 ^ (i - 1) ∈ A := A.pow_mem ha _
    have hbU : a ^ 2 ^ (i - 1) ∈ U := hU1 _ hbA hbb
    refine hxfix _ hbU hb1 ?_
    rw [← conj_pow, hxa]
  obtain ⟨Y, hxY⟩ : ∃ Y : Sylow 3 M, x ∈ (Y : Subgroup M) := by
    obtain ⟨Y, hY⟩ := hx3.exists_le_sylow
    exact ⟨Y, hY (mem_zpowers x)⟩
  set F : Set M := {f | ∃ a ∈ A, f = a * u'} with hFdef
  have hFinv : ∀ m : M, ∀ f ∈ F, m * f * m⁻¹ ∈ F := by
    rintro m f ⟨a, ha, rfl⟩
    obtain ⟨a', ha', h'⟩ := hF m a ha
    exact ⟨a', ha', h'⟩
  let smulF : SMul ↥(Y : Subgroup M) ↥F := ⟨fun y f => ⟨(y : M) * f * (y : M)⁻¹, hFinv _ _ f.2⟩⟩
  let actF : MulAction ↥(Y : Subgroup M) ↥F :=
    { toSMul := smulF
      one_smul := fun f => Subtype.ext (by
        change ((1 : ↥(Y : Subgroup M)) : M) * (f : M) * ((1 : ↥(Y : Subgroup M)) : M)⁻¹ = f
        simp)
      mul_smul := fun y₁ y₂ f => Subtype.ext (by
        change ((y₁ * y₂ : ↥(Y : Subgroup M)) : M) * (f : M) * ((y₁ * y₂ : ↥(Y : Subgroup M)) : M)⁻¹ =
          (y₁ : M) * ((y₂ : M) * (f : M) * (y₂ : M)⁻¹) * (y₁ : M)⁻¹
        simp [mul_assoc]) }
  let _inst := actF
  have hFcard : Nat.card ↥F = Nat.card ↥A := by
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun a : ↥A => (⟨(a : M) * u', a, a.2, rfl⟩ : ↥F)) ⟨?_, ?_⟩)
    · intro a b hab
      have : (a : M) * u' = b * u' := congrArg Subtype.val hab
      exact Subtype.ext (mul_right_cancel this)
    · rintro ⟨f, a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨m, hm⟩ := hA2.exists_card_eq
  have h3F : ¬ 3 ∣ Nat.card ↥F := by
    rw [hFcard, hm]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  obtain ⟨f₀, hf₀⟩ := (Y.isPGroup' : IsPGroup 3 ↥(Y : Subgroup M)).nonempty_fixed_point_of_prime_not_dvd_card
    ↥F h3F
  have hf₀y : ∀ y ∈ (Y : Subgroup M), y * (f₀ : M) * y⁻¹ = f₀ := fun y hy =>
    congrArg Subtype.val (MulAction.mem_fixedPoints.1 hf₀ ⟨y, hy⟩)
  obtain ⟨a₀, ha₀, hh₀⟩ := f₀.2
  set h₀ : M := (f₀ : M) with hh₀def
  have hinvh : ∀ a ∈ A, h₀ * a * h₀⁻¹ = a⁻¹ := by
    intro a ha
    have e : h₀ * a * h₀⁻¹ = a₀ * (u' * a * u'⁻¹) * a₀⁻¹ := by rw [hh₀]; group
    rw [e, hu'inv a ha, hAc a₀ ha₀ a⁻¹ (A.inv_mem ha)]
    group
  have hh₀2 : h₀ * h₀ = 1 := by
    have e1 : u' * a₀ = a₀⁻¹ * u' := by
      have := hu'inv a₀ ha₀
      calc u' * a₀ = (u' * a₀ * u'⁻¹) * u' := by group
        _ = a₀⁻¹ * u' := by rw [this]
    calc h₀ * h₀ = a₀ * (u' * a₀) * u' := by rw [hh₀]; group
      _ = a₀ * (a₀⁻¹ * u') * u' := by rw [e1]
      _ = u' * u' := by group
      _ = 1 := hu'2
  have hh₀A : h₀ ∉ A := by
    intro h
    apply hu'A
    have : u' = a₀⁻¹ * h₀ := by rw [hh₀]; group
    rw [this]
    exact A.mul_mem (A.inv_mem ha₀) h
  have hh₀S : h₀ ∈ S := by rw [hh₀]; exact S.mul_mem (hAS ha₀) hu'S
  have hh₀U : ∀ w ∈ U, h₀ * w = w * h₀ := by
    intro w hw
    have h1 := hinvh w (hUA hw)
    have h2 : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hsq w hw)
    rw [h2] at h1
    calc h₀ * w = (h₀ * w * h₀⁻¹) * h₀ := by group
      _ = w * h₀ := by rw [h1]
  have huniq : ∀ f ∈ F, (∀ y ∈ (Y : Subgroup M), y * f * y⁻¹ = f) → f = h₀ := by
    rintro f ⟨a, ha, rfl⟩ hfy
    have hx1 := hfy x hxY
    have hx2 : x * h₀ * x⁻¹ = h₀ := hf₀y x hxY
    have hc : x * (a * a₀⁻¹) * x⁻¹ = a * a₀⁻¹ := by
      have e : a * a₀⁻¹ = (a * u') * h₀⁻¹ := by rw [hh₀]; group
      have e2 : x * ((a * u') * h₀⁻¹) * x⁻¹ = (x * (a * u') * x⁻¹) * (x * h₀ * x⁻¹)⁻¹ := by group
      rw [e, e2, hx1, hx2]
    have := hCA _ (A.mul_mem ha (A.inv_mem ha₀)) hc
    rw [hh₀, mul_inv_eq_one.1 this]
  have hnorm_comm : ∀ n ∈ Subgroup.normalizer (Y : Subgroup M), n * h₀ * n⁻¹ = h₀ := by
    intro n hn
    apply huniq (n * h₀ * n⁻¹) (hFinv n _ f₀.2)
    intro y hy
    have hy' : n⁻¹ * y * n ∈ (Y : Subgroup M) := by
      refine (Subgroup.mem_normalizer_iff.1 hn (n⁻¹ * y * n)).2 ?_
      have e : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
      rw [e]; exact hy
    calc y * (n * h₀ * n⁻¹) * y⁻¹ = n * ((n⁻¹ * y * n) * h₀ * (n⁻¹ * y * n)⁻¹) * n⁻¹ := by group
      _ = n * h₀ * n⁻¹ := by rw [hf₀y _ hy']
  have hYker : (Y : Subgroup M) ≤ sgn.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    obtain ⟨j, hj⟩ := (Y.isPGroup' : IsPGroup 3 ↥(Y : Subgroup M)) ⟨y, hy⟩
    have h1 : sgn y ^ (3 ^ j) = 1 := by
      have := congrArg (fun z : ↥(Y : Subgroup M) => sgn (z : M)) hj
      simpa [← map_pow] using this
    rcases Int.units_eq_one_or (sgn y) with h | h
    · exact h
    · exfalso
      rw [h] at h1
      have hodd : Odd (3 ^ j) := Odd.pow (by decide)
      rw [hodd.neg_one_pow] at h1
      exact absurd h1 (by decide)
  have hfr := Sylow.normalizer_sup_eq_top' Y hYker
  obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_right.1 (hfr ▸ Subgroup.mem_top p)
  have hsgnn : sgn n = -1 := by
    have h1 : sgn p = -1 := hsgnp p hpU hp
    have h2 : sgn n * sgn k = sgn p := by rw [← map_mul, hnk]
    have h3 : sgn k = 1 := MonoidHom.mem_ker.1 hk
    rw [h3, mul_one] at h2
    rw [h2, h1]
  have hn0 : orderOf n ≠ 0 := (orderOf_pos n).ne'
  obtain ⟨j, o, ho, hno⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 2 (by norm_num)
  set n₂ := n ^ o with hn₂
  have hn₂2 : n₂ ^ (2 ^ j) = 1 := by
    rw [hn₂, ← pow_mul, mul_comm, ← hno]
    exact pow_orderOf_eq_one n
  have hsgn₂ : sgn n₂ = -1 := by
    rw [hn₂, map_pow, hsgnn]
    have : Odd o := Nat.odd_iff.2 (by omega)
    exact this.neg_one_pow
  have hn₂move : ∃ v ∈ U, n₂ * v * n₂⁻¹ ≠ v := by
    by_contra hcon
    push Not at hcon
    have := hsgn1 n₂ hcon
    rw [hsgn₂] at this
    exact absurd this (by decide)
  have hn₂h : n₂ * h₀ * n₂⁻¹ = h₀ := hnorm_comm n₂ (Subgroup.pow_mem _ hn o)
  have hn₂U : ∀ v ∈ U, n₂ * v * n₂⁻¹ ∈ U := fun v hv => hUn n₂ v hv
  obtain ⟨g, hg⟩ := P49H.exists_conj_mem_sylow hS hn₂2
  have hc_A : n₂ * n₂ ∈ A := by
    have h1 := hSsq _ hg
    have h2 : g * (n₂ * n₂) * g⁻¹ ∈ A := by
      have e : g * (n₂ * n₂) * g⁻¹ = (g * n₂ * g⁻¹) * (g * n₂ * g⁻¹) := by group
      rw [e]; exact h1
    have h3 := hAn.conj_mem _ h2 g⁻¹
    have e : g⁻¹ * (g * (n₂ * n₂) * g⁻¹) * g⁻¹⁻¹ = n₂ * n₂ := by group
    rwa [e] at h3
  have hn₂h' : n₂ * h₀ = h₀ * n₂ := by
    calc n₂ * h₀ = (n₂ * h₀ * n₂⁻¹) * n₂ := by group
      _ = h₀ * n₂ := by rw [hn₂h]
  have hcsq : (n₂ * n₂) * (n₂ * n₂) = 1 := by
    have h1 : h₀ * (n₂ * n₂) * h₀⁻¹ = (n₂ * n₂)⁻¹ := hinvh _ hc_A
    have h2 : h₀ * (n₂ * n₂) * h₀⁻¹ = n₂ * n₂ := by
      have e : h₀ * n₂ * h₀⁻¹ = n₂ := by rw [← hn₂h']; group
      calc h₀ * (n₂ * n₂) * h₀⁻¹ = (h₀ * n₂ * h₀⁻¹) * (h₀ * n₂ * h₀⁻¹) := by group
        _ = n₂ * n₂ := by rw [e]
    have h3 : n₂ * n₂ = (n₂ * n₂)⁻¹ := h2.symm.trans h1
    calc (n₂ * n₂) * (n₂ * n₂) = (n₂ * n₂) * (n₂ * n₂)⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel _
  have hcU : n₂ * n₂ ∈ U := hU1 _ hc_A hcsq
  have hcfix : n₂ * (n₂ * n₂) * n₂⁻¹ = n₂ * n₂ := by group
  obtain ⟨t, ht2, hth, hteq⟩ : ∃ t : M, t * t = 1 ∧ t * h₀ = h₀ * t ∧
      ∀ w ∈ U, t * w * t⁻¹ = n₂ * w * n₂⁻¹ := by
    by_cases hc1 : n₂ * n₂ = 1
    · exact ⟨n₂, hc1, hn₂h', fun w _ => rfl⟩
    · obtain ⟨v, hvU, hv⟩ := hn₂move
      have hv1 : v ≠ 1 := by rintro rfl; apply hv; simp
      have hvc : v ≠ n₂ * n₂ := by rintro rfl; exact hv hcfix
      have hv'U : n₂ * v * n₂⁻¹ ∈ U := hn₂U v hvU
      have hmem := fun y => CFSG.QuasithinUnique.Unc25Small.mem_klein_iff hU.2 hsq hcU hvU hc1 hv1
        (Ne.symm hvc) y
      have hv' : n₂ * v * n₂⁻¹ = (n₂ * n₂) * v := by
        rcases (hmem _).1 hv'U with h | h | h | h
        · exfalso; apply hv1
          have := congrArg (fun y => n₂⁻¹ * y * n₂) h
          simpa [mul_assoc] using this
        · exfalso; apply hvc
          have h' : n₂ * v * n₂⁻¹ = n₂ * (n₂ * n₂) * n₂⁻¹ := h.trans hcfix.symm
          exact mul_left_cancel (mul_right_cancel h')
        · exact absurd h hv
        · exact h
      have hback : n₂⁻¹ * v * n₂ = (n₂ * n₂) * v := by
        have h1 : n₂ * ((n₂ * n₂) * v) * n₂⁻¹ = v := by
          calc n₂ * ((n₂ * n₂) * v) * n₂⁻¹
              = (n₂ * (n₂ * n₂) * n₂⁻¹) * (n₂ * v * n₂⁻¹) := by group
            _ = (n₂ * n₂) * ((n₂ * n₂) * v) := by rw [hcfix, hv']
            _ = v := by rw [← mul_assoc, hcsq, one_mul]
        calc n₂⁻¹ * v * n₂ = n₂⁻¹ * (n₂ * ((n₂ * n₂) * v) * n₂⁻¹) * n₂ := by rw [h1]
          _ = (n₂ * n₂) * v := by group
      have hvw : ∀ w ∈ U, v * w * v⁻¹ = w := by
        intro w hw
        calc v * w * v⁻¹ = (w * v) * v⁻¹ := by rw [P49T.comm_of_four hU hvU hw]
          _ = w := by group
      refine ⟨n₂ * v, ?_, ?_, ?_⟩
      · calc n₂ * v * (n₂ * v) = (n₂ * n₂) * (n₂⁻¹ * v * n₂) * v := by group
          _ = (n₂ * n₂) * ((n₂ * n₂) * v) * v := by rw [hback]
          _ = ((n₂ * n₂) * (n₂ * n₂)) * (v * v) := by group
          _ = 1 := by rw [hcsq, hsq v hvU, mul_one]
      · calc n₂ * v * h₀ = n₂ * (v * h₀) := by group
          _ = n₂ * (h₀ * v) := by rw [(hh₀U v hvU).symm]
          _ = (n₂ * h₀) * v := by group
          _ = (h₀ * n₂) * v := by rw [hn₂h']
          _ = h₀ * (n₂ * v) := by group
      · intro w hw
        calc n₂ * v * w * (n₂ * v)⁻¹ = n₂ * (v * w * v⁻¹) * n₂⁻¹ := by group
          _ = n₂ * w * n₂⁻¹ := by rw [hvw w hw]
  have htU : ∀ w ∈ U, t * w * t⁻¹ ∈ U := fun w hw => by rw [hteq w hw]; exact hn₂U w hw
  have htmove : ∃ w ∈ U, t * w * t⁻¹ ≠ w := by
    obtain ⟨v, hvU, hv⟩ := hn₂move
    exact ⟨v, hvU, by rw [hteq v hvU]; exact hv⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    obtain ⟨v, hvU, hv⟩ := htmove
    apply hv; simp
  have hord_t : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  obtain ⟨w₁, hw₁U, hw₁1, htw₁⟩ := exists_fixed_of_sq hU htU ht2 htmove
  have hxh : x * h₀ * x⁻¹ = h₀ := hf₀y x hxY
  have hxh' : x * h₀ = h₀ * x := by
    calc x * h₀ = (x * h₀ * x⁻¹) * x := by group
      _ = h₀ * x := by rw [hxh]
  have ht'2 : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
    calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have ht'1 : x * t * x⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  have ht'h : (x * t * x⁻¹) * h₀ = h₀ * (x * t * x⁻¹) := by
    calc (x * t * x⁻¹) * h₀ = x * t * (x⁻¹ * h₀) := by group
      _ = x * t * (h₀ * x⁻¹) := by
          have : x⁻¹ * h₀ = h₀ * x⁻¹ := by
            calc x⁻¹ * h₀ = x⁻¹ * (h₀ * x) * x⁻¹ := by group
              _ = x⁻¹ * (x * h₀) * x⁻¹ := by rw [hxh']
              _ = h₀ * x⁻¹ := by group
          rw [this]
      _ = x * (t * h₀) * x⁻¹ := by group
      _ = x * (h₀ * t) * x⁻¹ := by rw [hth]
      _ = (x * h₀) * t * x⁻¹ := by group
      _ = (h₀ * x) * t * x⁻¹ := by rw [hxh']
      _ = h₀ * (x * t * x⁻¹) := by group
  have ht'U : ∀ w ∈ U, (x * t * x⁻¹) * w * (x * t * x⁻¹)⁻¹ ∈ U := fun w hw => hUn _ w hw
  have ht'move : ∃ w ∈ U, (x * t * x⁻¹) * w * (x * t * x⁻¹)⁻¹ ≠ w := by
    obtain ⟨v, hvU, hv⟩ := htmove
    refine ⟨x * v * x⁻¹, hUn x v hvU, ?_⟩
    intro h
    apply hv
    have e : (x * t * x⁻¹) * (x * v * x⁻¹) * (x * t * x⁻¹)⁻¹ = x * (t * v * t⁻¹) * x⁻¹ := by group
    rw [e] at h
    exact mul_left_cancel (mul_right_cancel h)
  have hlast : (x * t * x⁻¹) * w₁ * (x * t * x⁻¹)⁻¹ ≠ w₁ := by
    intro h
    have hw₁' : x * w₁ * x⁻¹ ∈ U := hUn x w₁ hw₁U
    have hw₁'1 : x * w₁ * x⁻¹ ≠ 1 := by
      intro h1
      apply hw₁1
      have := congrArg (fun y => x⁻¹ * y * x) h1
      simpa [mul_assoc] using this
    have hfix' : (x * t * x⁻¹) * (x * w₁ * x⁻¹) * (x * t * x⁻¹)⁻¹ = x * w₁ * x⁻¹ := by
      have e : (x * t * x⁻¹) * (x * w₁ * x⁻¹) * (x * t * x⁻¹)⁻¹ = x * (t * w₁ * t⁻¹) * x⁻¹ := by group
      rw [e, htw₁]
    have hall := fix_two hU hw₁U hw₁' hw₁1 hw₁'1 (fun e => hxfix w₁ hw₁U hw₁1 e.symm) h hfix'
    obtain ⟨y, hyU, hy⟩ := ht'move
    exact hy (hall y hyU)
  refine ⟨h₀, t, x * t * x⁻¹, ?_, hord_t, orderOf_eq_prime (by rw [pow_two]; exact ht'2) ht'1, hh₀S,
    hh₀U, hth.symm, ht'h.symm, htU, ht'U, htmove, ht'move, ⟨w₁, hw₁U, htw₁, hlast⟩⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact hh₀2) (fun h => hh₀A (h ▸ A.one_mem))

end Abstract

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49N
