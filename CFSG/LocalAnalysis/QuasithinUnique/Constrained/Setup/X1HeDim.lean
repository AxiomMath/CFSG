module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TNum

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin

section Norm

variable {W : Type} [CommGroup W]

@[expose] def nrmW (p : ℕ) (g : MulAut W) (t : W) : W := ∏ i ∈ Finset.range p, (g ^ i) t

theorem nrmW_mul (p : ℕ) (g : MulAut W) (a b : W) :
    nrmW p g (a * b) = nrmW p g a * nrmW p g b := by
  simp only [nrmW, map_mul, Finset.prod_mul_distrib]

theorem nrmW_one (p : ℕ) (g : MulAut W) : nrmW p g 1 = 1 := by
  simp [nrmW]

@[expose] def nrmHom (p : ℕ) (g : MulAut W) : W →* W where
  toFun := nrmW p g
  map_one' := nrmW_one p g
  map_mul' := nrmW_mul p g

theorem nrmHom_apply (p : ℕ) (g : MulAut W) (t : W) : nrmHom p g t = nrmW p g t := rfl

theorem apply_nrmW (p : ℕ) {g : MulAut W} (hg : g ^ p = 1) (t : W) :
    g (nrmW p g t) = nrmW p g t := by
  unfold nrmW
  rw [map_prod]
  have h1 : ∀ i : ℕ, g ((g ^ i) t) = (g ^ (i + 1)) t := fun i => by
    rw [pow_succ', MulAut.mul_apply]
  simp only [h1]
  have h2 := Finset.prod_range_succ' (fun i => (g ^ i) t) p
  have h3 := Finset.prod_range_succ (fun i => (g ^ i) t) p
  have h4 : (g ^ p) t = (g ^ 0) t := by rw [hg, pow_zero]
  have h5 := h2.symm.trans h3
  simp only [h4] at h5
  exact mul_right_cancel h5

theorem pow_apply_div (g : MulAut W) (n : ℕ) (v : W) :
    (g ^ n) v * v⁻¹ = g (∏ k ∈ Finset.range n, (g ^ k) v) *
      (∏ k ∈ Finset.range n, (g ^ k) v)⁻¹ := by
  rw [map_prod]
  have h1 : ∀ i : ℕ, g ((g ^ i) v) = (g ^ (i + 1)) v := fun i => by
    rw [pow_succ', MulAut.mul_apply]
  simp only [h1]
  have h2 := Finset.prod_range_div (fun i => (g ^ i) v) n
  simp only [pow_zero, MulAut.one_apply] at h2
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← Finset.prod_div_distrib, h2]

theorem nrmW_comm_image (p : ℕ) {g : MulAut W} (hg : g ^ p = 1) (v : W) :
    nrmW p g (g v * v⁻¹) = 1 := by
  unfold nrmW
  have h1 : ∀ i : ℕ, (g ^ i) (g v * v⁻¹) = (g ^ (i + 1)) v / (g ^ i) v := fun i => by
    have h : (g ^ i) (g v) = (g ^ (i + 1)) v := by rw [pow_succ, MulAut.mul_apply]
    rw [map_mul, map_inv, h, ← div_eq_mul_inv]
  simp only [h1]
  rw [Finset.prod_range_div (fun i => (g ^ i) v) p]
  rw [hg, pow_zero]
  simp

end Norm

section Struct

variable {W : Type} [CommGroup W]

theorem pow_odd_eq_self_W (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : Odd p) (w : W) :
    w ^ p = w := by
  obtain ⟨k, rfl⟩ := hp
  rw [pow_succ, pow_mul, sq, hW w, one_pow, one_mul]

theorem exists_pow_pow_eq_self_W {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Monoid G] {g : G}
    (hg : g ^ p = 1) {m : ℕ} (hm : ¬ p ∣ m) : ∃ n : ℕ, (g ^ m) ^ n = g := by
  have hcop : Nat.Coprime m p :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
  obtain ⟨n, -, hn⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  refine ⟨n, ?_⟩
  rw [← pow_mul, ← Nat.div_add_mod (m * n) p, hn, pow_add, pow_mul, hg, one_pow, one_mul,
    pow_one]

@[expose] def cHom (z : MulAut W) : W →* W where
  toFun v := z v * v⁻¹
  map_one' := by simp
  map_mul' a b := by simp only [map_mul, mul_inv_rev]; ac_rfl

@[expose] def imgT (z : MulAut W) : Subgroup W := (cHom z).range

theorem mem_imgT {z : MulAut W} {t : W} : t ∈ imgT z ↔ ∃ v, z v * v⁻¹ = t := by
  simp only [imgT, MonoidHom.mem_range]
  exact Iff.rfl

theorem apply_mem_imgT {z g : MulAut W} (hg : g * z = z * g) {t : W} (ht : t ∈ imgT z) :
    g t ∈ imgT z := by
  obtain ⟨v, rfl⟩ := mem_imgT.1 ht
  refine mem_imgT.2 ⟨g v, ?_⟩
  have h : g (z v) = z (g v) := by
    have := congrArg (fun h : MulAut W => h v) hg
    simpa only [MulAut.mul_apply] using this
  rw [map_mul, map_inv, h]

theorem pow_apply_mem_imgT {z g : MulAut W} (hg : g * z = z * g) {t : W} (ht : t ∈ imgT z)
    (i : ℕ) : (g ^ i) t ∈ imgT z := by
  induction i with
  | zero => simpa using ht
  | succ i ih => rw [pow_succ', MulAut.mul_apply]; exact apply_mem_imgT hg ih

theorem nrmW_mem_imgT {p : ℕ} {z g : MulAut W} (hg : g * z = z * g) {t : W} (ht : t ∈ imgT z) :
    nrmW p g t ∈ imgT z :=
  Subgroup.prod_mem _ fun i _ => pow_apply_mem_imgT hg ht i

theorem eq_one_of_mem_imgT_fixed (hW : ∀ w : W, w * w = 1) {p : ℕ} (hodd : Odd p) {z : MulAut W}
    (hz : z ^ p = 1) {t : W} (ht : t ∈ imgT z) (hzt : z t = t) : t = 1 := by
  obtain ⟨v, rfl⟩ := mem_imgT.1 ht
  have h1 := nrmW_comm_image p hz v
  have hfix : ∀ i : ℕ, (z ^ i) (z v * v⁻¹) = z v * v⁻¹ := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', MulAut.mul_apply, ih]; exact hzt
  have h2 : nrmW p z (z v * v⁻¹) = (z v * v⁻¹) ^ p := by
    unfold nrmW
    simp [hfix]
  rw [h2, pow_odd_eq_self_W hW hodd] at h1
  exact h1

theorem nrmW_pow_of_mem_imgT {p : ℕ} [Fact p.Prime] {z : MulAut W} (hz : z ^ p = 1) {m : ℕ}
    (hm : ¬ p ∣ m) {t : W} (ht : t ∈ imgT z) : nrmW p (z ^ m) t = 1 := by
  obtain ⟨v, rfl⟩ := mem_imgT.1 ht
  obtain ⟨n, hn⟩ := exists_pow_pow_eq_self_W hz hm
  have hg : (z ^ m) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  have h := pow_apply_div (z ^ m) n v
  rw [hn] at h
  rw [h]
  exact nrmW_comm_image p hg _

end Struct

section Eigen

variable {W : Type} [CommGroup W]

structure ExtraCfg (p : ℕ) (x y z : MulAut W) : Prop where
  xp : x ^ p = 1
  zp : z ^ p = 1
  zx : x * z = z * x
  zy : y * z = z * y
  yx : y⁻¹ * x * y = x * z
  z1 : z ≠ 1

@[expose] def eigE (x z : MulAut W) (j : ℕ) : Subgroup W :=
  imgT z ⊓ fixV (Subgroup.zpowers (x * z ^ j))

theorem mem_eigE {x z : MulAut W} {j : ℕ} {t : W} :
    t ∈ eigE x z j ↔ t ∈ imgT z ∧ (x * z ^ j) t = t := by
  rw [eigE, Subgroup.mem_inf, mem_fixV_zpowers]

variable {p : ℕ} {x y z : MulAut W}

theorem ExtraCfg.comm_xz (h : ExtraCfg p x y z) (j : ℕ) : (x * z ^ j) * z = z * (x * z ^ j) := by
  have h1 : Commute x z := h.zx
  have h2 : Commute (x * z ^ j) z := h1.mul_left ((Commute.refl z).pow_left j)
  exact h2.eq

theorem ExtraCfg.pow_xz (h : ExtraCfg p x y z) (j : ℕ) : (x * z ^ j) ^ p = 1 := by
  have h0 : Commute x z := h.zx
  have h1 : Commute x (z ^ j) := h0.pow_right j
  rw [h1.mul_pow, h.xp, ← pow_mul, mul_comm, pow_mul, h.zp, one_pow, one_mul]

theorem ExtraCfg.nrmW_mem_eigE (h : ExtraCfg p x y z) {t : W} (ht : t ∈ imgT z) (j : ℕ) :
    nrmW p (x * z ^ j) t ∈ eigE x z j :=
  mem_eigE.2 ⟨nrmW_mem_imgT (h.comm_xz j) ht, apply_nrmW p (h.pow_xz j) t⟩

theorem nrmW_eigE_self (hW : ∀ w : W, w * w = 1) (hodd : Odd p)
    {j : ℕ} {e : W} (he : e ∈ eigE x z j) : nrmW p (x * z ^ j) e = e := by
  have hfix : ∀ i : ℕ, ((x * z ^ j) ^ i) e = e := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', MulAut.mul_apply, ih]; exact (mem_eigE.1 he).2
  unfold nrmW
  simp only [hfix, Finset.prod_const, Finset.card_range]
  exact pow_odd_eq_self_W hW hodd e

theorem ExtraCfg.nrmW_eigE_ne [Fact p.Prime] (h : ExtraCfg p x y z) {j k : ℕ} (hj : j < p)
    (hk : k < p) (hjk : j ≠ k) {e : W} (he : e ∈ eigE x z k) : nrmW p (x * z ^ j) e = 1 := by
  have hm : ¬ p ∣ j + p - k := by
    rintro ⟨c, hc⟩
    have h1 : c ≤ 1 := by
      by_contra hcon
      have : p * 2 ≤ p * c := Nat.mul_le_mul_left p (by omega)
      omega
    interval_cases c <;> omega
  have h1 : Commute x z := h.zx
  have hxz : x * z ^ j = z ^ (j + p - k) * (x * z ^ k) := by
    have hc : Commute (z ^ (j + p - k)) x := (h1.pow_right (j + p - k)).symm
    calc x * z ^ j = x * z ^ (j + p) := by rw [pow_add, h.zp, mul_one]
      _ = x * (z ^ (j + p - k) * z ^ k) := by
          rw [← pow_add, show j + p - k + k = j + p by omega]
      _ = z ^ (j + p - k) * (x * z ^ k) := by rw [← mul_assoc, hc.eq.symm, mul_assoc]
  have hfixk : ∀ i : ℕ, ((x * z ^ k) ^ i) e = e := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', MulAut.mul_apply, ih]; exact (mem_eigE.1 he).2
  have hpow : ∀ i : ℕ, ((x * z ^ j) ^ i) e = ((z ^ (j + p - k)) ^ i) e := by
    intro i
    have hcom : Commute (z ^ (j + p - k)) (x * z ^ k) :=
      (h1.pow_right (j + p - k)).symm.mul_right ((Commute.refl z).pow_pow _ _)
    rw [hxz, hcom.mul_pow, MulAut.mul_apply, hfixk]
  unfold nrmW
  simp only [hpow]
  exact nrmW_pow_of_mem_imgT h.zp hm (mem_eigE.1 he).1

theorem ExtraCfg.prod_nrmW [Fact p.Prime] (h : ExtraCfg p x y z) (hW : ∀ w : W, w * w = 1)
    (hodd : Odd p) {t : W} (ht : t ∈ imgT z) :
    ∏ j ∈ Finset.range p, nrmW p (x * z ^ j) t = t := by
  have h1 : Commute x z := h.zx
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
    rw [nrmW_pow_of_mem_imgT h.zp hnd ht, map_one]
  rw [hrest, one_mul]
  simp only [pow_zero, MulAut.one_apply, nrmW, Finset.prod_const, Finset.card_range, one_pow]
  exact pow_odd_eq_self_W hW hodd t

end Eigen

section Count

variable {W : Type} [CommGroup W] [Finite W] {p : ℕ} {x y z : MulAut W}

@[expose] noncomputable def prodE (x z : MulAut W) (p : ℕ) :
    (∀ j : Fin p, ↥(eigE x z j)) →* W :=
  ∏ j : Fin p, (eigE x z j).subtype.comp
    (Pi.evalMonoidHom (fun j : Fin p => ↥(eigE x z j)) j)

omit [Finite W] in
theorem prodE_apply (e : ∀ j : Fin p, ↥(eigE x z j)) :
    prodE x z p e = ∏ j : Fin p, (e j : W) := by
  simp [prodE]

omit [Finite W] in
theorem prodE_injective [Fact p.Prime] (h : ExtraCfg p x y z) (hW : ∀ w : W, w * w = 1)
    (hodd : Odd p) : Function.Injective (prodE x z p) := by
  rw [injective_iff_map_eq_one]
  intro e he
  rw [prodE_apply] at he
  funext k
  apply Subtype.ext
  have h1 := congrArg (nrmHom p (x * z ^ (k : ℕ))) he
  rw [map_prod, map_one] at h1
  rw [Finset.prod_eq_single k] at h1
  · rw [nrmHom_apply, nrmW_eigE_self hW hodd (e k).2] at h1
    simpa using h1
  · intro j _ hjk
    rw [nrmHom_apply]
    exact h.nrmW_eigE_ne k.2 j.2 (fun hkj => hjk (Fin.ext hkj.symm)) (e j).2
  · intro hk
    exact absurd (Finset.mem_univ k) hk

omit [Finite W] in
theorem ExtraCfg.yInv_mem_eigE (h : ExtraCfg p x y z) {j : ℕ} {e : W} (he : e ∈ eigE x z j) :
    y⁻¹ e ∈ eigE x z (j + 1) := by
  have hyz : Commute y z := h.zy
  refine mem_eigE.2 ⟨?_, ?_⟩
  · have hy : y⁻¹ * z = z * y⁻¹ := (hyz.inv_left).eq
    exact apply_mem_imgT hy (mem_eigE.1 he).1
  · have hzj : y * z ^ j * y⁻¹ = z ^ j := by
      have : Commute y (z ^ j) := hyz.pow_right j
      rw [this.eq, mul_inv_cancel_right]
    have hconj : x * z ^ (j + 1) * y⁻¹ = y⁻¹ * (x * z ^ j) := by
      calc x * z ^ (j + 1) * y⁻¹ = x * z * z ^ j * y⁻¹ := by rw [pow_succ', ← mul_assoc]
        _ = y⁻¹ * x * y * z ^ j * y⁻¹ := by rw [← h.yx]
        _ = y⁻¹ * x * (y * z ^ j * y⁻¹) := by group
        _ = y⁻¹ * (x * z ^ j) := by rw [hzj, mul_assoc]
    rw [← MulAut.mul_apply, hconj, MulAut.mul_apply, (mem_eigE.1 he).2]

theorem ExtraCfg.card_eigE_le_succ (h : ExtraCfg p x y z) (j : ℕ) :
    Nat.card (eigE x z j) ≤ Nat.card (eigE x z (j + 1)) := by
  have hle : (eigE x z j).map (y⁻¹ : W ≃* W).toMonoidHom ≤ eigE x z (j + 1) := by
    rintro _ ⟨e, he, rfl⟩
    exact h.yInv_mem_eigE he
  have h1 := Subgroup.card_le_of_le hle
  rwa [Subgroup.card_map_of_injective (y⁻¹ : W ≃* W).injective] at h1

omit [Finite W] in
theorem ExtraCfg.eigE_add_p (h : ExtraCfg p x y z) (j : ℕ) :
    eigE x z (j + p) = eigE x z j := by
  unfold eigE
  rw [pow_add, h.zp, mul_one]

theorem ExtraCfg.card_eigE_eq (h : ExtraCfg p x y z) {j : ℕ} (hj : j ≤ p) :
    Nat.card (eigE x z j) = Nat.card (eigE x z 0) := by
  have hmono : ∀ m j : ℕ, Nat.card (eigE x z j) ≤ Nat.card (eigE x z (j + m)) := by
    intro m
    induction m with
    | zero => intro j; exact le_rfl
    | succ m ih => intro j; exact (ih j).trans (h.card_eigE_le_succ (j + m))
  apply le_antisymm
  · have h1 := hmono (p - j) j
    rw [show j + (p - j) = 0 + p by omega, h.eigE_add_p] at h1
    exact h1
  · have h1 := hmono j 0
    rwa [zero_add] at h1

omit [Finite W] in
theorem ExtraCfg.exists_eigE_ne_bot [Fact p.Prime] (h : ExtraCfg p x y z)
    (hW : ∀ w : W, w * w = 1) (hodd : Odd p) : ∃ j < p, eigE x z j ≠ ⊥ := by
  have hT : ∃ t ∈ imgT z, t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply h.z1
    ext v
    have := hcon (z v * v⁻¹) (mem_imgT.2 ⟨v, rfl⟩)
    rw [mul_inv_eq_one] at this
    simpa using this
  obtain ⟨t, ht, ht1⟩ := hT
  by_contra hall
  push Not at hall
  apply ht1
  rw [← h.prod_nrmW hW hodd ht]
  refine Finset.prod_eq_one fun j hj => ?_
  have hmem := h.nrmW_mem_eigE ht j
  rw [hall j (Finset.mem_range.1 hj), Subgroup.mem_bot] at hmem
  exact hmem

theorem ExtraCfg.card_eigE_zero_modEq [Fact p.Prime] (h : ExtraCfg p x y z)
    (hW : ∀ w : W, w * w = 1) (hodd : Odd p) : Nat.card (eigE x z 0) ≡ 1 [MOD p] := by
  have hx : Commute x z := h.zx
  have hz : ∀ a : W, a ∈ eigE x z 0 → z a ∈ eigE x z 0 := by
    intro a ha
    obtain ⟨haT, hax⟩ := mem_eigE.1 ha
    refine mem_eigE.2 ⟨apply_mem_imgT rfl haT, ?_⟩
    have hax' : x a = a := by simpa using hax
    have hxa : x (z a) = z (x a) := by
      have := congrArg (fun g : MulAut W => g a) h.zx
      simpa only [MulAut.mul_apply] using this
    simp [hxa, hax']
  let f : eigE x z 0 → eigE x z 0 := fun a => ⟨z a, hz a a.2⟩
  have hiter : ∀ (n : ℕ) (a : eigE x z 0), ((f^[n] a : eigE x z 0) : W) = (z ^ n) a := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply, ih, pow_succ, MulAut.mul_apply]
  have hf : ∀ a, f^[p] a = a := by
    intro a
    apply Subtype.ext
    rw [hiter, h.zp]
    rfl
  have hmod := card_modEq_fix_prime p f hf
  have hfix : Nat.card {a : eigE x z 0 | f a = a} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, Subtype.ext (map_one z)⟩⟩⟩
    have hone : ∀ c : {a : eigE x z 0 | f a = a}, (c.1 : W) = 1 := by
      intro c
      have h1 : z (c.1 : W) = c.1 := congrArg Subtype.val c.2
      exact eq_one_of_mem_imgT_fixed hW hodd h.zp (mem_eigE.1 c.1.2).1 h1
    apply Subtype.ext
    apply Subtype.ext
    rw [hone a, hone b]
  rwa [hfix] at hmod

theorem card_eq_two_pow_W (hW : ∀ w : W, w * w = 1) (H : Subgroup W) :
    ∃ m : ℕ, Nat.card H = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 H := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [sq] using hW g
  exact (IsPGroup.iff_card).1 hp

theorem ExtraCfg.two_pow_le_card_eigE [Fact p.Prime] (h : ExtraCfg p x y z)
    (hW : ∀ w : W, w * w = 1) (hodd : Odd p) :
    2 ^ orderOf (2 : ZMod p) ≤ Nat.card (eigE x z 0) := by
  obtain ⟨m, hm⟩ := card_eq_two_pow_W hW (eigE x z 0)
  have hne : m ≠ 0 := by
    intro hm0
    obtain ⟨j, hj, hjne⟩ := h.exists_eigE_ne_bot hW hodd
    have h1 : Nat.card (eigE x z j) = 1 := by
      rw [h.card_eigE_eq hj.le, hm, hm0, pow_zero]
    exact hjne (Subgroup.card_eq_one.1 h1)
  have hmod := h.card_eigE_zero_modEq hW hodd
  rw [hm] at hmod
  have h2 : ((2 ^ m : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  push_cast at h2
  have h3 : orderOf (2 : ZMod p) ∣ m := orderOf_dvd_of_pow_eq_one h2
  rw [hm]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h3)

theorem ExtraCfg.two_pow_mul_le_card [Fact p.Prime] (h : ExtraCfg p x y z)
    (hW : ∀ w : W, w * w = 1) (hodd : Odd p) :
    2 ^ (p * orderOf (2 : ZMod p)) ≤ Nat.card W := by
  have h1 := Nat.card_le_card_of_injective _ (prodE_injective h hW hodd)
  rw [Nat.card_pi] at h1
  have h2 : ∏ j : Fin p, Nat.card (eigE x z j) = Nat.card (eigE x z 0) ^ p := by
    rw [Finset.prod_congr rfl (fun j _ => h.card_eigE_eq (le_of_lt j.2))]
    simp
  rw [h2] at h1
  calc 2 ^ (p * orderOf (2 : ZMod p)) = (2 ^ orderOf (2 : ZMod p)) ^ p := by
        rw [mul_comm, pow_mul]
    _ ≤ Nat.card (eigE x z 0) ^ p := Nat.pow_le_pow_left (h.two_pow_le_card_eigE hW hodd) p
    _ ≤ Nat.card W := h1

end Count

section Extraspecial

open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_mul_le_card_of_extraspecial (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {x y : MulAut W} (hx : x ^ p = 1) (hz1 : ⁅x, y⁆ ≠ 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) :
    2 ^ (p * orderOf (2 : ZMod p)) ≤ Nat.card W := by
  set z : MulAut W := ⁅x, y⁆ with hz
  have hyz : y * z = z * y := hzy.symm.eq
  have hxz : x * z = z * x := hzx.symm.eq
  have hyx : y⁻¹ * x * y = x * z := by
    have key : x * y = y * z * x := by
      calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
        _ = z * y * x := by rw [hz, commutatorElement_def]
        _ = y * z * x := by rw [hyz]
    calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
      _ = y⁻¹ * (y * z * x) := by rw [key]
      _ = z * x := by group
      _ = x * z := hxz.symm
  have hzp : z ^ p = 1 := by
    have h1 : (x * z) ^ p = 1 := by
      rw [← hyx, show y⁻¹ * x * y = y⁻¹ * x * y⁻¹⁻¹ by rw [inv_inv], conj_pow, hx]
      group
    have h2 : Commute x z := hxz
    rw [h2.mul_pow, hx, one_mul] at h1
    exact h1
  have hcfg : ExtraCfg p x y z := ⟨hx, hzp, hxz, hyz, hyx, hz1⟩
  exact hcfg.two_pow_mul_le_card hW ((Fact.out : Nat.Prime p).odd_of_ne_two hp2)

end Extraspecial

end CFSG.QuasithinUnique.Setup.X1
