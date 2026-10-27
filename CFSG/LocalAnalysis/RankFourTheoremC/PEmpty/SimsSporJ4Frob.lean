module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigOrd

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

private theorem zmod_add_neg_mul (p : ℕ) (x y : ZMod p) : x + -x * y = x * (1 - y) := by ring

theorem exists_fixed_ne_one_of_frobenius {E : Type*} [CommGroup E] (h2 : ∀ a : E, a * a = 1)
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (Z U : Monoid.End E) {m n : ℕ} (hn : 0 < n)
    (hZp : Z ^ p = 1) (hUZ : U * Z = Z ^ m * U) (hUn : U ^ n = 1)
    (hm : ∀ k, 0 < k → k < n → (m : ZMod p) ^ k ≠ 1) (hfix : ∀ a, Z a = a → a = 1)
    {a : E} (ha : a ≠ 1) : ∃ f, f ≠ 1 ∧ U f = f := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hZmod : ∀ k : ℕ, Z ^ k = Z ^ (k % p) := fun k => by
    conv_lhs => rw [← Nat.mod_add_div k p, pow_add, pow_mul, hZp, one_pow, mul_one]
  obtain ⟨Zp, hZpdef⟩ : ∃ f : ZMod p → Monoid.End E, ∀ x, f x = Z ^ x.val := ⟨_, fun _ => rfl⟩
  have hZcast : ∀ k : ℕ, Zp (k : ZMod p) = Z ^ k := fun k => by
    rw [hZpdef, ZMod.val_natCast, ← hZmod]
  have hZadd : ∀ x y : ZMod p, Zp (x + y) = Zp x * Zp y := fun x y => by
    rw [hZpdef, hZpdef, hZpdef, ← pow_add, ZMod.val_add, ← hZmod]
  have hZzero : Zp 0 = 1 := by rw [hZpdef, ZMod.val_zero, pow_zero]
  have hZ1 : Zp 1 = Z := by
    have h := hZcast 1
    rwa [Nat.cast_one, pow_one] at h
  have hZnegl : ∀ x, Zp (-x) * Zp x = 1 := fun x => by
    rw [← hZadd, show -x + x = 0 from neg_add_cancel x, hZzero]
  have hZnegr : ∀ x, Zp x * Zp (-x) = 1 := fun x => by
    rw [← hZadd, show x + -x = 0 from add_neg_cancel x, hZzero]
  have hUZj : ∀ j : ℕ, U * Z ^ j = Z ^ (j * m) * U := by
    intro j
    induction j with
    | zero => rw [pow_zero, zero_mul, pow_zero, mul_one, one_mul]
    | succ j ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hUZ, ← mul_assoc, ← pow_add,
        show j * m + m = (j + 1) * m by ring]
  have hUkZj : ∀ k j : ℕ, U ^ k * Z ^ j = Z ^ (j * m ^ k) * U ^ k := by
    intro k
    induction k with
    | zero => intro j; rw [pow_zero, pow_zero, mul_one, one_mul, mul_one]
    | succ k ih =>
      intro j
      rw [pow_succ, mul_assoc, hUZj, ← mul_assoc, ih, mul_assoc, ← pow_succ,
        show j * m * m ^ k = j * m ^ (k + 1) by ring]
  have hUkZp : ∀ (k : ℕ) (x : ZMod p), U ^ k * Zp x = Zp (x * (m : ZMod p) ^ k) * U ^ k := by
    intro k x
    have hcast : x * (m : ZMod p) ^ k = ((x.val * m ^ k : ℕ) : ZMod p) := by
      rw [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]
    rw [hcast, hZcast, hZpdef]
    exact hUkZj k x.val
  have hσ : ∀ b : E, ∏ x : ZMod p, Zp x b = 1 := by
    intro b
    apply hfix
    rw [map_prod]
    have h1 : ∀ x : ZMod p, Z (Zp x b) = Zp (1 + x) b := fun x => by
      rw [hZadd, hZ1]
      rfl
    rw [Fintype.prod_congr _ _ h1]
    exact Fintype.prod_equiv (Equiv.addLeft 1) _ _ (fun x => rfl)
  have hterm : ∀ k, 0 < k → k < n → ∏ x : ZMod p, (Zp x * U ^ k * Zp (-x)) a = 1 := by
    intro k hk0 hkn
    have hc : (1 - (m : ZMod p) ^ k) ≠ 0 := sub_ne_zero.mpr (Ne.symm (hm k hk0 hkn))
    have h1 : ∀ x : ZMod p,
        (Zp x * U ^ k * Zp (-x)) a = Zp (x * (1 - (m : ZMod p) ^ k)) ((U ^ k) a) := by
      intro x
      rw [mul_assoc, hUkZp, ← mul_assoc, ← hZadd]
      have e : x + -x * (m : ZMod p) ^ k = x * (1 - (m : ZMod p) ^ k) := zmod_add_neg_mul p x _
      rw [e]
      rfl
    rw [Fintype.prod_congr _ _ h1,
      show (∏ x : ZMod p, Zp (x * (1 - (m : ZMod p) ^ k)) ((U ^ k) a)) =
        ∏ y : ZMod p, Zp y ((U ^ k) a) from
        Fintype.prod_equiv (Equiv.mulRight₀ _ hc) _ _ (fun x => rfl)]
    exact hσ _
  have h0 : ∏ x : ZMod p, (Zp x * U ^ 0 * Zp (-x)) a = a := by
    have h1 : ∀ x : ZMod p, (Zp x * U ^ 0 * Zp (-x)) a = a := fun x => by
      rw [pow_zero, mul_one, hZnegr]
      rfl
    rw [Fintype.prod_congr _ _ h1, Finset.prod_const, Finset.card_univ, ZMod.card]
    obtain ⟨q, hq⟩ := hp.out.odd_of_ne_two hp2
    rw [hq, pow_succ, pow_mul, sq, h2, one_pow, one_mul]
  have hVpow : ∀ (x : ZMod p) (k : ℕ), (Zp x * U * Zp (-x)) ^ k = Zp x * U ^ k * Zp (-x) := by
    intro x k
    induction k with
    | zero => rw [pow_zero, pow_zero, mul_one, hZnegr]
    | succ k ih =>
      rw [pow_succ, ih]
      calc Zp x * U ^ k * Zp (-x) * (Zp x * U * Zp (-x))
          = Zp x * U ^ k * (Zp (-x) * Zp x) * U * Zp (-x) := by simp only [mul_assoc]
        _ = Zp x * U ^ (k + 1) * Zp (-x) := by
          rw [hZnegl, mul_one, mul_assoc (Zp x), ← pow_succ]
  set N : ZMod p → E := fun x => ∏ k ∈ Finset.range n, ((Zp x * U * Zp (-x)) ^ k) a with hN
  have hdecomp : ∏ x : ZMod p, N x = a := by
    simp only [hN, hVpow]
    rw [Finset.prod_comm]
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [Finset.prod_range_succ', h0, Finset.prod_eq_one, one_mul]
    intro k hk
    exact hterm (k + 1) (Nat.succ_pos k) (Nat.succ_lt_succ (Finset.mem_range.mp hk))
  obtain ⟨x, hx⟩ : ∃ x, N x ≠ 1 :=
    not_forall.mp fun hcon => ha (hdecomp.symm.trans (Finset.prod_eq_one fun x _ => hcon x))
  have hVN : (Zp x * U * Zp (-x)) (N x) = N x := by
    simp only [hN]
    rw [map_prod]
    have h1 : ∀ k, (Zp x * U * Zp (-x)) (((Zp x * U * Zp (-x)) ^ k) a) =
        ((Zp x * U * Zp (-x)) ^ (k + 1)) a := fun k => by
      rw [pow_succ']
      rfl
    rw [Finset.prod_congr rfl (fun k _ => h1 k)]
    have hVn : ((Zp x * U * Zp (-x)) ^ n) a = a := by
      rw [hVpow, hUn, mul_one, hZnegr]
      rfl
    have e1 := Finset.prod_range_succ (fun k => ((Zp x * U * Zp (-x)) ^ k) a) n
    have e2 := Finset.prod_range_succ' (fun k => ((Zp x * U * Zp (-x)) ^ k) a) n
    rw [e1, hVn, pow_zero] at e2
    exact (mul_right_cancel e2).symm
  refine ⟨Zp (-x) (N x), fun hf => hx ?_, ?_⟩
  · have h : (Zp x * Zp (-x)) (N x) = Zp x 1 := by
      change Zp x (Zp (-x) (N x)) = Zp x 1
      rw [hf]
    rw [hZnegr, map_one] at h
    exact h
  · have hUZ' : U * Zp (-x) = Zp (-x) * (Zp x * U * Zp (-x)) := by
      rw [← mul_assoc, ← mul_assoc, hZnegl, one_mul]
    calc U (Zp (-x) (N x)) = (U * Zp (-x)) (N x) := rfl
      _ = (Zp (-x) * (Zp x * U * Zp (-x))) (N x) := by rw [hUZ']
      _ = Zp (-x) ((Zp x * U * Zp (-x)) (N x)) := rfl
      _ = Zp (-x) (N x) := by rw [hVN]

theorem exists_ne_one_mem_centralizer_of_frobenius {G : Type*} [Group G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {z u : G} (hz : z ^ p = 1) {m n : ℕ} (hn : 0 < n)
    (hu : u * z * u⁻¹ = z ^ m) (hun : u ^ n = 1)
    (hm : ∀ k, 0 < k → k < n → (m : ZMod p) ^ k ≠ 1) {E : Subgroup G}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1)
    (hzE : z ∈ normalizer (E : Set G)) (huE : u ∈ normalizer (E : Set G))
    (hCz : ∀ x ∈ E, x * z = z * x → x = 1) (hE : E ≠ ⊥) :
    ∃ f ∈ E, f ≠ 1 ∧ f * u = u * f := by
  classical
  letI : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun a b => Subtype.ext (hEab a a.2 b b.2) }
  let c : normalizer (E : Set G) →* Monoid.End E :=
    { toFun := fun g =>
        { toFun := fun e => ⟨(g : G) * e * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 e).mp e.2⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
      map_one' := DFunLike.ext _ _ fun e => Subtype.ext (by
        show ((1 : normalizer (E : Set G)) : G) * e * ((1 : normalizer (E : Set G)) : G)⁻¹ = e
        simp)
      map_mul' := fun g h => DFunLike.ext _ _ fun e => Subtype.ext (by
        show ((g * h : normalizer (E : Set G)) : G) * e * ((g * h : normalizer (E : Set G)) : G)⁻¹ =
          (g : G) * ((h : G) * e * (h : G)⁻¹) * (g : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hc : ∀ g (e : E), ((c g e : E) : G) = (g : G) * e * (g : G)⁻¹ := fun _ _ => rfl
  set Zn : normalizer (E : Set G) := ⟨z, hzE⟩ with hZn
  set Un : normalizer (E : Set G) := ⟨u, huE⟩ with hUn
  have huz : u * z = z ^ m * u := by
    calc u * z = u * z * u⁻¹ * u := by group
      _ = z ^ m * u := by rw [hu]
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hE
  have hZp : Zn ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hz)
  have hUZ : Un * Zn = Zn ^ m * Un :=
    Subtype.ext (by simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]; exact huz)
  have hUp : Un ^ n = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hun)
  obtain ⟨f, hf1, hfu⟩ := exists_fixed_ne_one_of_frobenius (fun a => Subtype.ext (hE2 a a.2))
    hp2 (c Zn) (c Un) hn
    (by rw [← map_pow, hZp, map_one])
    (by rw [← map_mul, ← map_pow, ← map_mul, hUZ])
    (by rw [← map_pow, hUp, map_one])
    hm
    (fun e he => Subtype.ext (hCz e e.2 (by
      have h := congrArg Subtype.val he
      rw [hc] at h
      calc (e : G) * z = z * e * z⁻¹ * z := by rw [h]
        _ = z * e := by group)))
    ha
  refine ⟨f, f.2, fun h => hf1 (Subtype.ext h), ?_⟩
  have h := congrArg Subtype.val hfu
  rw [hc] at h
  calc (f : G) * u = u * f * u⁻¹ * u := by rw [h]
    _ = u * f := by group

theorem eq_bot_of_normalizes {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {z u : G} (hz : z ^ p = 1) {m n : ℕ} (hn : 0 < n) (hu : u * z * u⁻¹ = z ^ m)
    (hun : u ^ n = 1) (hm : ∀ k, 0 < k → k < n → (m : ZMod p) ^ k ≠ 1)
    (hinv : ∀ t : G, orderOf t = 2 → t * z ≠ z * t)
    (hbad : ∀ e : G, e * u = u * e → orderOf e = 2 →
      ∃ i : ℕ, e * (z ^ i * e * z⁻¹ ^ i) ≠ (z ^ i * e * z⁻¹ ^ i) * e)
    {Y : Subgroup G} (hY : IsPGroup 2 Y) (hzY : z ∈ normalizer (Y : Set G))
    (huY : u ∈ normalizer (Y : Set G)) : Y = ⊥ := by
  classical
  by_contra hY1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ (∀ w ∈ Y, y * w = w * y) ∧ y * y = 1}
      mul_mem' := fun {a b} ha hb => ⟨Y.mul_mem ha.1 hb.1, fun w hw => by
          rw [mul_assoc, hb.2.1 w hw, ← mul_assoc, ha.2.1 w hw, mul_assoc], by
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hb.2.1 a ha.1]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha.2.2, hb.2.2, one_mul]⟩
      one_mem' := ⟨Y.one_mem, fun w _ => by rw [one_mul, mul_one], by rw [one_mul]⟩
      inv_mem' := fun {a} ha => by
        rw [inv_eq_of_mul_eq_one_right ha.2.2]
        exact ha }
  have hmemE : ∀ y, y ∈ E ↔ y ∈ Y ∧ (∀ w ∈ Y, y * w = w * y) ∧ y * y = 1 := fun _ => Iff.rfl
  have hconjE : ∀ g ∈ normalizer (Y : Set G), ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg e he
    rw [hmemE] at he ⊢
    have hg' : g⁻¹ ∈ normalizer (Y : Set G) := inv_mem hg
    refine ⟨(mem_normalizer_iff.mp hg e).mp he.1, fun w hw => ?_, ?_⟩
    · have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ Y := (mem_normalizer_iff.mp hg' w).mp hw
      rw [inv_inv] at hw'
      have hc := he.2.1 _ hw'
      calc g * e * g⁻¹ * w = g * (e * (g⁻¹ * w * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * w * g) * e) * g⁻¹ := by rw [hc]
        _ = w * (g * e * g⁻¹) := by group
    · calc g * e * g⁻¹ * (g * e * g⁻¹) = g * (e * e) * g⁻¹ := by group
        _ = 1 := by rw [he.2.2, mul_one, mul_inv_cancel]
  have hnormE : ∀ g ∈ normalizer (Y : Set G), g ∈ normalizer (E : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro e
    refine ⟨fun he => hconjE g hg e he, fun he => ?_⟩
    have h := hconjE g⁻¹ (inv_mem hg) _ he
    rwa [show g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e by group] at h
  have hEne : E ≠ ⊥ := by
    haveI : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY1
    have hZ : Nontrivial (center Y) := hY.center_nontrivial
    obtain ⟨k, hk0, hk⟩ := (hY.to_subgroup (center Y)).nontrivial_iff_card.mp hZ
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := center Y) 2
      (hk ▸ dvd_pow_self 2 hk0.ne')
    have hyo : orderOf ((y : Y) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨((y : Y) : G), (y : Y).2, fun w hw => ?_, ?_⟩, fun h => ?_⟩
    · have h := Subgroup.mem_center_iff.mp y.2 ⟨w, hw⟩
      exact (congrArg Subtype.val h).symm
    · rw [← sq, ← hyo, pow_orderOf_eq_one]
    · have h' : ((y : Y) : G) = 1 := congrArg Subtype.val h
      rw [h', orderOf_one] at hyo
      exact absurd hyo (by norm_num)
  have hCz : ∀ x ∈ E, x * z = z * x → x = 1 := by
    intro x hx hxz
    by_contra hx1
    exact hinv x (orderOf_eq_prime (by rw [sq]; exact ((hmemE x).mp hx).2.2) hx1) hxz
  obtain ⟨f, hfE, hf1, hfu⟩ := exists_ne_one_mem_centralizer_of_frobenius hp2 hz hn hu hun hm
    (fun x hx y hy => ((hmemE x).mp hx).2.1 y ((hmemE y).mp hy).1)
    (fun x hx => ((hmemE x).mp hx).2.2) (hnormE z hzY) (hnormE u huY) hCz hEne
  obtain ⟨i, hi⟩ := hbad f hfu (orderOf_eq_prime (by rw [sq]; exact ((hmemE f).mp hfE).2.2) hf1)
  apply hi
  have hzi : z ^ i ∈ normalizer (E : Set G) := pow_mem (hnormE z hzY) i
  have hmem : z ^ i * f * z⁻¹ ^ i ∈ E := by
    rw [inv_pow]
    exact (mem_normalizer_iff.mp hzi f).mp hfE
  exact ((hmemE f).mp hfE).2.1 _ ((hmemE _).mp hmem).1

theorem row_of_orbitU {s : TauCeti.SporadicName} {p : ℕ} (X : Type) [Group X] [Finite X]
    (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hsyl : ¬ p ^ 2 ∣ Nat.card X) {z₀ u₀ : X} (hz₀ : orderOf z₀ = p) {m n : ℕ} (hn : 0 < n)
    (hu : u₀ * z₀ * u₀⁻¹ = z₀ ^ m) (hun : u₀ ^ n = 1)
    (hm : ∀ k, 0 < k → k < n → (m : ZMod p) ^ k ≠ 1)
    (hinv : ∀ t : X, orderOf t = 2 → t * z₀ ≠ z₀ * t)
    (hbad : ∀ e : X, e * u₀ = u₀ * e → orderOf e = 2 →
      ∃ i : ℕ, e * (z₀ ^ i * e * z₀⁻¹ ^ i) ≠ (z₀ ^ i * e * z₀⁻¹ ^ i) * e) :
    KFactSporLocalRow s p := by
  apply row_of_model
  intro G _ _ ⟨e'⟩ _ _ K z hz _ hzK hN _ hy _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ξ⟩ := hX
  set φ : G ≃* X := e'.trans ξ.symm with hφ
  have hz' : orderOf (φ z) = p := by rw [MulEquiv.orderOf_eq]; exact hz
  obtain ⟨c, hc⟩ := exists_mulEquiv_zpowers hp hsyl hz' hz₀
  set ψ : X ≃* G := c.trans φ.symm with hψ
  have hψz : zpowers (ψ z₀) = zpowers z := by
    have h := congrArg (Subgroup.map φ.symm.toMonoidHom) hc
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h
    simpa [hψ] using h
  have hz₁p : ψ z₀ ^ p = 1 := by rw [← map_pow, ← hz₀, pow_orderOf_eq_one, map_one]
  have hu₁z : ψ u₀ * ψ z₀ * (ψ u₀)⁻¹ = ψ z₀ ^ m := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, hu]
  have hu₁n : ψ u₀ ^ n = 1 := by rw [← map_pow, hun, map_one]
  have hinv₁ : ∀ t : G, orderOf t = 2 → t * ψ z₀ ≠ ψ z₀ * t := by
    intro t ht htz
    refine hinv (ψ.symm t) (by rw [MulEquiv.orderOf_eq]; exact ht) (ψ.injective ?_)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact htz
  have hbad₁ : ∀ e : G, e * ψ u₀ = ψ u₀ * e → orderOf e = 2 →
      ∃ i : ℕ, e * (ψ z₀ ^ i * e * (ψ z₀)⁻¹ ^ i) ≠ (ψ z₀ ^ i * e * (ψ z₀)⁻¹ ^ i) * e := by
    intro e heu he
    obtain ⟨i, hi⟩ := hbad (ψ.symm e)
      (ψ.injective (by rw [map_mul, map_mul, MulEquiv.apply_symm_apply]; exact heu))
      (by rw [MulEquiv.orderOf_eq]; exact he)
    refine ⟨i, fun h => hi (ψ.injective ?_)⟩
    simp only [map_mul, map_pow, map_inv, MulEquiv.apply_symm_apply]
    exact h
  have hz₁K : ψ z₀ ∈ K := hN (by rw [← hψz]; exact le_normalizer (mem_zpowers _))
  have hu₁K : ψ u₀ ∈ K := hN (by rw [← hψz]; exact mem_normalizer_zpowers_of_conj_pow hu₁z)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot := eq_bot_of_normalizes hp2 hz₁p hn hu₁z hu₁n hm hinv₁ hbad₁ (pCoreOf_isPGroup 2 K)
    (localGroup_le_normalizer_pCoreOf 2 K hz₁K) (localGroup_le_normalizer_pCoreOf 2 K hu₁K)
  obtain ⟨y, hyY, hyz⟩ := hy
  rw [hbot, Subgroup.mem_bot] at hyY
  exact absurd (by rw [hyY, mul_one, one_mul]) hyz

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
