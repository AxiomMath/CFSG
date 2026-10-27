module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim

public section

namespace CFSG.QuasithinUnique.Bridge.J2Excl

open CFSG.QuasithinUnique.Setup.X1

abbrev Q5 : Type := Multiplicative (ZMod 5) × Multiplicative (ZMod 5)

@[expose] def q5 (a b : ZMod 5) : Q5 := (Multiplicative.ofAdd a, Multiplicative.ofAdd b)

@[expose] def Indep5 (q r : Q5) : Prop :=
  Function.Injective fun ij : Fin 5 × Fin 5 => q ^ (ij.1 : ℕ) * r ^ (ij.2 : ℕ)

instance (q r : Q5) : Decidable (Indep5 q r) := by unfold Indep5; infer_instance

@[expose] def gQ (p : Q5) : Q5 :=
  q5 (-(Multiplicative.toAdd p.2)) (Multiplicative.toAdd p.1 - Multiplicative.toAdd p.2)

theorem q5_pow_five : ∀ q : Q5, q ^ 5 = 1 := by decide

theorem gQ_bijective : Function.Bijective gQ := by decide

theorem Indep5.symm {q r : Q5} (h : Indep5 q r) : Indep5 r q := by
  have e : (fun ij : Fin 5 × Fin 5 => r ^ (ij.1 : ℕ) * q ^ (ij.2 : ℕ)) =
      (fun ij : Fin 5 × Fin 5 => q ^ (ij.1 : ℕ) * r ^ (ij.2 : ℕ)) ∘ Prod.swap := by
    funext ij
    simp [mul_comm]
  unfold Indep5
  rw [e]
  exact h.comp Prod.swap_injective

theorem indep5_x_line : ∀ j : Fin 5, Indep5 (q5 1 0) (q5 (j : ℕ) 1) := by decide

theorem indep5_triple : ∀ j : Fin 5, Indep5 (q5 (j : ℕ) 1) (gQ (q5 (j : ℕ) 1)) ∧
    Indep5 (gQ (q5 (j : ℕ) 1)) (gQ (gQ (q5 (j : ℕ) 1))) ∧
    Indep5 (gQ (gQ (q5 (j : ℕ) 1))) (q5 (j : ℕ) 1) := by decide

section Hom

variable {W : Type} [CommGroup W]

@[expose] def zp5 (x : MulAut W) (a : ZMod 5) : MulAut W := x ^ a.val

theorem zp5_zero (x : MulAut W) : zp5 x 0 = 1 := by simp [zp5]

theorem zp5_add {x : MulAut W} (hx : x ^ 5 = 1) (a b : ZMod 5) :
    zp5 x (a + b) = zp5 x a * zp5 x b := by
  unfold zp5
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

theorem zp5_neg {x : MulAut W} (hx : x ^ 5 = 1) (a : ZMod 5) : zp5 x (-a) = (zp5 x a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← zp5_add hx, neg_add_cancel, zp5_zero]

theorem zp5_sub {x : MulAut W} (hx : x ^ 5 = 1) (a b : ZMod 5) :
    zp5 x (a - b) = zp5 x a * (zp5 x b)⁻¹ := by
  rw [sub_eq_add_neg, zp5_add hx, zp5_neg hx]

@[expose] def qhom (x y : MulAut W) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hxy : Commute x y) :
    Q5 →* MulAut W where
  toFun p := zp5 x (Multiplicative.toAdd p.1) * zp5 y (Multiplicative.toAdd p.2)
  map_one' := by simp [zp5]
  map_mul' p r := by
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, zp5_add hx, zp5_add hy]
    exact (Commute.mul_mul_mul_comm (by unfold zp5; exact (hxy.pow_pow _ _).symm) _ _).symm

theorem qhom_q5 (x y : MulAut W) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hxy : Commute x y)
    (a b : ZMod 5) : qhom x y hx hy hxy (q5 a b) = zp5 x a * zp5 y b := rfl

theorem qhom_conj {x y g : MulAut W} (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hxy : Commute x y)
    (hgx : g * x * g⁻¹ = y) (hgy : g * y * g⁻¹ = (x * y)⁻¹) (p : Q5) :
    g * qhom x y hx hy hxy p * g⁻¹ = qhom x y hx hy hxy (gQ p) := by
  obtain ⟨pa, pb⟩ := p
  set A : ZMod 5 := Multiplicative.toAdd pa with hA
  set B : ZMod 5 := Multiplicative.toAdd pb with hB
  show g * (zp5 x A * zp5 y B) * g⁻¹ = zp5 x (-B) * zp5 y (A - B)
  have h1 : g * (zp5 x A * zp5 y B) * g⁻¹ = (g * zp5 x A * g⁻¹) * (g * zp5 y B * g⁻¹) := by
    group
  have h2 : g * zp5 x A * g⁻¹ = zp5 y A := by
    unfold zp5
    rw [← hgx, conj_pow]
  have h3 : g * zp5 y B * g⁻¹ = (zp5 y B)⁻¹ * (zp5 x B)⁻¹ := by
    unfold zp5
    rw [← conj_pow, hgy, inv_pow, hxy.mul_pow, mul_inv_rev]
  have hXU : Commute (zp5 x B)⁻¹ (zp5 y A) := (hxy.pow_pow B.val A.val).inv_left
  have hXY : Commute (zp5 x B)⁻¹ (zp5 y B)⁻¹ := (hxy.pow_pow B.val B.val).inv_inv
  rw [h1, h2, h3, zp5_neg hx, zp5_sub hy, ← hXY.eq, ← mul_assoc, ← mul_assoc, hXU.eq]

end Hom

section Norm

variable {W : Type} [CommGroup W]

@[expose] def NQ (φ : Q5 →* MulAut W) (v : W) : W := ∏ p : Q5, φ p v

theorem NQ_mul (φ : Q5 →* MulAut W) (u v : W) : NQ φ (u * v) = NQ φ u * NQ φ v := by
  unfold NQ
  simp only [map_mul]
  exact Finset.prod_mul_distrib

theorem NQ_one (φ : Q5 →* MulAut W) : NQ φ 1 = 1 := by simp [NQ]

theorem NQ_inv (φ : Q5 →* MulAut W) (v : W) : NQ φ v⁻¹ = (NQ φ v)⁻¹ := by
  unfold NQ
  simp only [map_inv, Finset.prod_inv_distrib]

theorem nrmW_nrmW (φ : Q5 →* MulAut W) {q r : Q5} (h : Indep5 q r) (v : W) :
    nrmW 5 (φ q) (nrmW 5 (φ r) v) = NQ φ v := by
  have hbij : Function.Bijective
      (fun ij : Fin 5 × Fin 5 => q ^ (ij.1 : ℕ) * r ^ (ij.2 : ℕ)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨h, ?_⟩
    simp [Fintype.card_prod, ZMod.card]
  unfold nrmW NQ
  have e1 : ∀ i : ℕ, (φ q ^ i) (∏ j ∈ Finset.range 5, (φ r ^ j) v) =
      ∏ j ∈ Finset.range 5, φ (q ^ i * r ^ j) v := by
    intro i
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_mul, MulAut.mul_apply, ← map_pow, ← map_pow]
  simp only [e1]
  rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ Finset.range 5, φ (q ^ i * r ^ j) v) 5]
  simp only [← Fin.prod_univ_eq_prod_range (fun j => φ (q ^ _ * r ^ j) v) 5]
  rw [← Fintype.prod_prod_type
    (fun ij : Fin 5 × Fin 5 => φ (q ^ (ij.1 : ℕ) * r ^ (ij.2 : ℕ)) v)]
  exact Fintype.prod_bijective _ hbij _ _ (fun _ => rfl)

theorem NQ_shift (φ : Q5 →* MulAut W) (r : Q5) (v : W) : NQ φ (φ r v) = NQ φ v := by
  unfold NQ
  have e : ∀ p : Q5, φ p (φ r v) = φ (p * r) v := fun p => by rw [map_mul, MulAut.mul_apply]
  simp only [e]
  exact Fintype.prod_equiv (Equiv.mulRight r) _ _ (fun _ => rfl)

theorem NQ_conj (φ : Q5 →* MulAut W) {g : MulAut W} (hg : ∀ p, g * φ p * g⁻¹ = φ (gQ p))
    (v : W) : NQ φ (g v) = g (NQ φ v) := by
  unfold NQ
  rw [map_prod]
  have e : ∀ p : Q5, g (φ p v) = φ (gQ p) (g v) := fun p => by
    rw [← hg p]
    simp [MulAut.mul_apply]
  simp only [e]
  exact (Fintype.prod_equiv (Equiv.ofBijective gQ gQ_bijective) _ _ (fun _ => rfl)).symm

@[expose] def Wsp (φ : Q5 →* MulAut W) (a : Q5) : Subgroup W where
  carrier := {v | φ a v = v ∧ NQ φ v = 1}
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    exact ⟨by rw [map_mul, hu1, hv1], by rw [NQ_mul, hu2, hv2, mul_one]⟩
  one_mem' := ⟨map_one _, NQ_one φ⟩
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    exact ⟨by rw [map_inv, hu1], by rw [NQ_inv, hu2, inv_one]⟩

theorem nrmW_of_fixed (hW : ∀ w : W, w * w = 1) {g : MulAut W} {v : W} (hv : g v = v) :
    nrmW 5 g v = v := by
  have hfix : ∀ i : ℕ, (g ^ i) v = v := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', MulAut.mul_apply, ih]; exact hv
  unfold nrmW
  simp only [hfix, Finset.prod_const, Finset.card_range]
  exact pow_odd_eq_self_W hW (by decide) v

theorem nrmW_eq_one_of_mem_Wsp (hW : ∀ w : W, w * w = 1) {φ : Q5 →* MulAut W} {a b : Q5}
    (hab : Indep5 a b) {v : W} (hv : v ∈ Wsp φ b) : nrmW 5 (φ a) v = 1 := by
  have h1 := nrmW_nrmW φ hab v
  rw [nrmW_of_fixed hW hv.1, hv.2] at h1
  exact h1

theorem apply_mem_Wsp {φ : Q5 →* MulAut W} {g : MulAut W} (hg : ∀ p, g * φ p * g⁻¹ = φ (gQ p))
    {p : Q5} {v : W} (hv : v ∈ Wsp φ p) : g v ∈ Wsp φ (gQ p) := by
  refine ⟨?_, ?_⟩
  · rw [← hg p]
    simp [MulAut.mul_apply, hv.1]
  · rw [NQ_conj φ hg, hv.2, map_one]

theorem Wsp_indep (hW : ∀ w : W, w * w = 1) {φ : Q5 →* MulAut W} {a b c : Q5}
    (hab : Indep5 a b) (hac : Indep5 a c) (hbc : Indep5 b c) {u v w : W} (hu : u ∈ Wsp φ a)
    (hv : v ∈ Wsp φ b) (hw : w ∈ Wsp φ c) (h : u * v * w = 1) : u = 1 ∧ v = 1 ∧ w = 1 := by
  have hu1 : u = 1 := by
    have h1 := congrArg (nrmW 5 (φ a)) h
    rw [nrmW_mul, nrmW_mul, nrmW_one, nrmW_of_fixed hW hu.1, nrmW_eq_one_of_mem_Wsp hW hab hv,
      nrmW_eq_one_of_mem_Wsp hW hac hw, mul_one, mul_one] at h1
    exact h1
  subst hu1
  rw [one_mul] at h
  have hv1 : v = 1 := by
    have h1 := congrArg (nrmW 5 (φ b)) h
    rw [nrmW_mul, nrmW_one, nrmW_of_fixed hW hv.1, nrmW_eq_one_of_mem_Wsp hW hbc hw,
      mul_one] at h1
    exact h1
  subst hv1
  rw [one_mul] at h
  exact ⟨rfl, rfl, h⟩

theorem orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem card_Wsp_modEq [Finite W] (hW : ∀ w : W, w * w = 1) {φ : Q5 →* MulAut W} {a b : Q5}
    (hab : Indep5 a b) : Nat.card (Wsp φ a) ≡ 1 [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcomm : φ a * φ b = φ b * φ a := by rw [← map_mul, ← map_mul, mul_comm]
  have hmem : ∀ v ∈ Wsp φ a, φ b v ∈ Wsp φ a := by
    rintro v ⟨h1, h2⟩
    refine ⟨?_, by rw [NQ_shift, h2]⟩
    have := congrArg (fun m : MulAut W => m v) hcomm
    simp only [MulAut.mul_apply] at this
    rw [this, h1]
  let f : Wsp φ a → Wsp φ a := fun v => ⟨φ b v, hmem v v.2⟩
  have hiter : ∀ (n : ℕ) (v : Wsp φ a), ((f^[n] v : Wsp φ a) : W) = (φ b ^ n) v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [Function.iterate_succ_apply, ih, pow_succ, MulAut.mul_apply]
  have hf : ∀ v, f^[5] v = v := by
    intro v
    apply Subtype.ext
    rw [hiter, ← map_pow, q5_pow_five, map_one]
    rfl
  have hmod := card_modEq_fix_prime 5 f hf
  have hfix : Nat.card {v : Wsp φ a | f v = v} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun u w => ?_⟩, ⟨⟨1, Subtype.ext (map_one (φ b))⟩⟩⟩
    have hone : ∀ c : {v : Wsp φ a | f v = v}, (c.1 : W) = 1 := by
      intro c
      have hc : φ b (c.1 : W) = c.1 := congrArg Subtype.val c.2
      have hn := nrmW_nrmW φ hab (c.1 : W)
      rw [nrmW_of_fixed hW hc, nrmW_of_fixed hW c.1.2.1, c.1.2.2] at hn
      exact hn
    apply Subtype.ext
    apply Subtype.ext
    rw [hone u, hone w]
  rwa [hfix] at hmod

theorem sixteen_le_card_Wsp [Finite W] (hW : ∀ w : W, w * w = 1) {φ : Q5 →* MulAut W}
    {a b : Q5} (hab : Indep5 a b) (hne : Wsp φ a ≠ ⊥) : 16 ≤ Nat.card (Wsp φ a) := by
  obtain ⟨m, hm⟩ := card_eq_two_pow_W hW (Wsp φ a)
  have hmod := card_Wsp_modEq hW (φ := φ) hab
  have hm0 : m ≠ 0 := by
    intro h0
    apply hne
    have : Nat.card (Wsp φ a) = 1 := by rw [hm, h0, pow_zero]
    exact Subgroup.card_eq_one.1 this
  rw [hm] at hmod ⊢
  have h2 : ((2 ^ m : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  push_cast at h2
  have h3 : orderOf (2 : ZMod 5) ∣ m := orderOf_dvd_of_pow_eq_one h2
  rw [orderOf_two_zmod_five] at h3
  have h4 : 4 ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h3
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h4

theorem card_pow_three_le_card [Finite W] (hW : ∀ w : W, w * w = 1) {φ : Q5 →* MulAut W}
    {g : MulAut W} (hg : ∀ p, g * φ p * g⁻¹ = φ (gQ p)) {a : Q5} (hab : Indep5 a (gQ a))
    (hbc : Indep5 (gQ a) (gQ (gQ a))) (hca : Indep5 (gQ (gQ a)) a) :
    Nat.card (Wsp φ a) ^ 3 ≤ Nat.card W := by
  have hac : Indep5 a (gQ (gQ a)) := hca.symm
  have hmono : ∀ p : Q5, Nat.card (Wsp φ p) ≤ Nat.card (Wsp φ (gQ p)) := by
    intro p
    refine Nat.card_le_card_of_injective (fun v => ⟨g v.1, apply_mem_Wsp hg v.2⟩) ?_
    intro u w h
    exact Subtype.ext (g.injective (congrArg Subtype.val h))
  have h1 := hmono a
  have h2 := hmono (gQ a)
  let F : ↥(Wsp φ a) × (↥(Wsp φ (gQ a)) × ↥(Wsp φ (gQ (gQ a)))) →* W :=
    (Wsp φ a).subtype.coprod ((Wsp φ (gQ a)).subtype.coprod (Wsp φ (gQ (gQ a))).subtype)
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, v, w⟩ h
    have h' : (u : W) * ((v : W) * (w : W)) = 1 := by simpa [F] using h
    rw [← mul_assoc] at h'
    obtain ⟨hu, hv, hw⟩ := Wsp_indep hW hab hac hbc u.2 v.2 w.2 h'
    exact Prod.ext (Subtype.ext hu) (Prod.ext (Subtype.ext hv) (Subtype.ext hw))
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Nat.card_prod] at hcard
  calc Nat.card (Wsp φ a) ^ 3
      = Nat.card (Wsp φ a) * (Nat.card (Wsp φ a) * Nat.card (Wsp φ a)) := by ring
    _ ≤ Nat.card (Wsp φ a) * (Nat.card (Wsp φ (gQ a)) * Nat.card (Wsp φ (gQ (gQ a)))) :=
        Nat.mul_le_mul le_rfl (Nat.mul_le_mul h1 (h1.trans h2))
    _ ≤ Nat.card W := hcard

theorem prod_nrmW' {p : ℕ} [Fact p.Prime] (hW : ∀ w : W, w * w = 1) (hodd : Odd p)
    {x z : MulAut W} (hxz : x * z = z * x) (hzp : z ^ p = 1) {t : W} (ht : t ∈ imgT z) :
    ∏ j ∈ Finset.range p, nrmW p (x * z ^ j) t = t := by
  have h1 : Commute x z := hxz
  have hterm : ∀ j i : ℕ, ((x * z ^ j) ^ i) t = (x ^ i) (((z ^ i) ^ j) t) := by
    intro j i
    rw [(h1.pow_right j).mul_pow, MulAut.mul_apply, pow_right_comm]
  have hswap : ∏ j ∈ Finset.range p, nrmW p (x * z ^ j) t =
      ∏ i ∈ Finset.range p, (x ^ i) (nrmW p (z ^ i) t) := by
    unfold nrmW
    simp only [hterm]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod]
  rw [hswap]
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by have := (Fact.out : Nat.Prime p).pos; omega⟩
  rw [Finset.prod_range_succ']
  have hrest : ∏ i ∈ Finset.range p', (x ^ (i + 1)) (nrmW (p' + 1) (z ^ (i + 1)) t) = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    have hi' : i < p' := Finset.mem_range.1 hi
    have hnd : ¬ (p' + 1) ∣ i + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rw [nrmW_pow_of_mem_imgT hzp hnd ht, map_one]
  rw [hrest, one_mul]
  simp only [pow_zero, MulAut.one_apply, nrmW, Finset.prod_const, Finset.card_range, one_pow]
  exact pow_odd_eq_self_W hW hodd t

theorem exists_Wsp_ne_bot (hW : ∀ w : W, w * w = 1) {x y : MulAut W} (hx : x ^ 5 = 1)
    (hy : y ^ 5 = 1) (hxy : Commute x y) (hx1 : x ≠ 1) :
    ∃ j : Fin 5, Wsp (qhom x y hx hy hxy) (q5 (j : ℕ) 1) ≠ ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_contra H
  push Not at H
  set φ := qhom x y hx hy hxy with hφ
  apply hx1
  have hv1 : (1 : ZMod 5).val = 1 := rfl
  have hφx : φ (q5 1 0) = x := by
    rw [hφ, qhom_q5]
    simp [zp5, hv1]
  have hT : ∀ t ∈ imgT x, t = 1 := by
    intro t ht
    obtain ⟨v, hv⟩ := mem_imgT.1 ht
    have hxt : nrmW 5 x t = 1 := by rw [← hv]; exact nrmW_comm_image 5 hx v
    have h1 := prod_nrmW' hW (p := 5) (by decide) (x := y) (z := x) hxy.symm.eq hx ht
    have hfac : ∀ j ∈ Finset.range 5, nrmW 5 (y * x ^ j) t = 1 := by
      intro j hj
      have hj5 : j < 5 := Finset.mem_range.1 hj
      set jj : Fin 5 := ⟨j, hj5⟩ with hjj
      have hφpj : φ (q5 (jj : ℕ) 1) = y * x ^ j := by
        rw [hφ, qhom_q5]
        have e1 : zp5 x ((jj : ℕ) : ZMod 5) = x ^ j := by
          unfold zp5
          rw [hjj, ZMod.val_natCast_of_lt hj5]
        have e2 : zp5 y 1 = y := by simp [zp5, hv1]
        rw [e1, e2]
        exact ((hxy.pow_left j).eq)
      have hpow : (y * x ^ j) ^ 5 = 1 := by
        rw [(hxy.symm.pow_right j).mul_pow, hy, ← pow_mul, mul_comm, pow_mul, hx, one_pow,
          one_mul]
      have hfix : φ (q5 (jj : ℕ) 1) (nrmW 5 (y * x ^ j) t) = nrmW 5 (y * x ^ j) t := by
        rw [hφpj]
        exact apply_nrmW 5 hpow t
      have hxj : Indep5 (q5 1 0) (q5 (jj : ℕ) 1) := indep5_x_line jj
      have hA := nrmW_nrmW φ hxj t
      have hB := nrmW_nrmW φ hxj.symm t
      rw [hφx] at hA hB
      have hNQt : NQ φ t = 1 := by
        rw [← hB, hxt, nrmW_one]
      have hmem : nrmW 5 (y * x ^ j) t ∈ Wsp φ (q5 (jj : ℕ) 1) := by
        refine ⟨hfix, ?_⟩
        have hC := nrmW_nrmW φ hxj (nrmW 5 (y * x ^ j) t)
        rw [hφx, nrmW_of_fixed hW hfix] at hC
        rw [← hC, ← hφpj, hA, hNQt]
      rw [H jj] at hmem
      exact Subgroup.mem_bot.1 hmem
    rw [Finset.prod_eq_one hfac] at h1
    exact h1.symm
  ext v
  have := hT (x v * v⁻¹) (mem_imgT.2 ⟨v, rfl⟩)
  rw [mul_inv_eq_one] at this
  simpa using this

end Norm

section Main

variable {W : Type} [CommGroup W]

theorem two_pow_twelve_le_card [Finite W] (hW : ∀ w : W, w * w = 1) {x g : MulAut W}
    (hx : x ^ 5 = 1) (hcomm : Commute x (g * x * g⁻¹))
    (hrel : g * (g * x * g⁻¹) * g⁻¹ = (x * (g * x * g⁻¹))⁻¹) (hx1 : x ≠ 1) :
    2 ^ 12 ≤ Nat.card W := by
  have hy5 : (g * x * g⁻¹) ^ 5 = 1 := by rw [conj_pow, hx]; group
  have hg : ∀ p, g * qhom x (g * x * g⁻¹) hx hy5 hcomm p * g⁻¹ =
      qhom x (g * x * g⁻¹) hx hy5 hcomm (gQ p) := qhom_conj hx hy5 hcomm rfl hrel
  obtain ⟨j, hj⟩ := exists_Wsp_ne_bot hW hx hy5 hcomm hx1
  obtain ⟨h1, h2, h3⟩ := indep5_triple j
  have h16 := sixteen_le_card_Wsp hW h1 hj
  have h3le := card_pow_three_le_card hW hg h1 h2 h3
  calc 2 ^ 12 = 16 ^ 3 := by norm_num
    _ ≤ Nat.card (Wsp (qhom x (g * x * g⁻¹) hx hy5 hcomm) (q5 (j : ℕ) 1)) ^ 3 :=
        Nat.pow_le_pow_left h16 3
    _ ≤ Nat.card W := h3le

end Main

end CFSG.QuasithinUnique.Bridge.J2Excl
