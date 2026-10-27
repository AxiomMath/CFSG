module

public import CFSG.GH74.Uniqueness.Section126Dihedral
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

namespace NormDvd

open Subgroup

variable {G : Type} [Group G]

theorem eight_dvd_closure_pair {H : Type*} [Group H] [Finite H] {a w : H}
    (ha : a * a = 1) (hw : w * w = 1) (h2 : a * w * (a * w) ≠ 1)
    (h4 : a * w * (a * w) * (a * w * (a * w)) = 1) :
    8 ∣ Nat.card ↥(closure ({a, w} : Set H)) := by
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact h2 (by simpa using hw)
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact h2 (by simpa using ha)
  have hoa : orderOf a = 2 := orderOf_eq_prime (by rwa [pow_two]) ha1
  have how : orderOf w = 2 := orderOf_eq_prime (by rwa [pow_two]) hw1
  have hoaw : orderOf (a * w) = 4 := by
    have h4'' : (a * w) ^ 4 = 1 := by
      have e : (a * w) ^ 4 = (a * w) ^ 2 * (a * w) ^ 2 := by rw [← pow_add]
      rw [pow_two] at e
      exact e.trans h4
    have h4' : (a * w) ^ 2 ^ (1 + 1) = 1 := h4''
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a * w) (by simpa [pow_two] using h2) h4'
    simpa using this
  rw [CFSG.GH74.Uniqueness.card_closure_pair_involutions hoa how, hoaw]

def bsel (b d : ℕ) : ℕ := if b = 1 then d else 0

def lin (cu cf cz cs c : ℕ) : ℕ :=
  bsel (c % 2) cu ^^^ (bsel (c / 2 % 2) cf ^^^ (bsel (c / 4 % 2) cz ^^^ bsel (c / 8 % 2) cs))

def elt (u f z s : G) (c : ℕ) : G :=
  u ^ (c % 2) * (f ^ (c / 2 % 2) * (z ^ (c / 4 % 2) * s ^ (c / 8 % 2)))

def Acts (u f z s x : G) (L : ℕ → ℕ) : Prop :=
  ∀ c < 16, L c < 16 ∧ x * elt u f z s c * x⁻¹ = elt u f z s (L c)

theorem xor_lt {a b : ℕ} (ha : a < 16) (hb : b < 16) : a ^^^ b < 16 :=
  (by decide : ∀ a < 16, ∀ b < 16, a ^^^ b < 16) a ha b hb

theorem bsel_lt {b d : ℕ} (hd : d < 16) : bsel b d < 16 := by
  unfold bsel
  split_ifs <;> omega

theorem lin_lt {cu cf cz cs : ℕ} (hu : cu < 16) (hf : cf < 16) (hz : cz < 16) (hs : cs < 16)
    (c : ℕ) : lin cu cf cz cs c < 16 :=
  xor_lt (bsel_lt hu) (xor_lt (bsel_lt hf) (xor_lt (bsel_lt hz) (bsel_lt hs)))

theorem xor_bits : ∀ a < 16, ∀ b < 16,
    (a ^^^ b) % 2 = (a % 2 + b % 2) % 2 ∧ (a ^^^ b) / 2 % 2 = (a / 2 % 2 + b / 2 % 2) % 2 ∧
    (a ^^^ b) / 4 % 2 = (a / 4 % 2 + b / 4 % 2) % 2 ∧
    (a ^^^ b) / 8 % 2 = (a / 8 % 2 + b / 8 % 2) % 2 := by
  decide

theorem pow_mod_two_add {x : G} (hx : x ^ 2 = 1) (m n : ℕ) :
    x ^ ((m + n) % 2) = x ^ m * x ^ n := by
  rw [← pow_eq_pow_mod _ hx, pow_add]

theorem elt_zero {u f z s : G} : elt u f z s 0 = 1 := by simp [elt]

theorem pow_bsel {u f z s : G} {b : ℕ} (hb : b < 2) (d : ℕ) :
    elt u f z s d ^ b = elt u f z s (bsel b d) := by
  interval_cases b
  · simp [bsel, elt_zero]
  · simp [bsel]

theorem Acts.mul {u f z s x y : G} {Lx Ly : ℕ → ℕ} (hx : Acts u f z s x Lx)
    (hy : Acts u f z s y Ly) : Acts u f z s (x * y) (fun c => Lx (Ly c)) := by
  intro c hc
  obtain ⟨hlt, hy'⟩ := hy c hc
  obtain ⟨hlt', hx'⟩ := hx _ hlt
  refine ⟨hlt', ?_⟩
  calc (x * y) * elt u f z s c * (x * y)⁻¹ = x * (y * elt u f z s c * y⁻¹) * x⁻¹ := by group
    _ = elt u f z s (Lx (Ly c)) := by rw [hy', hx']

structure E16 (A : Subgroup G) (u f z s : G) : Prop where
  mem : ∀ y : G, y ∈ A ↔ ∃ i j k l : ℕ, y = u ^ i * f ^ j * z ^ k * s ^ l
  card : Nat.card ↥A = 16
  u2 : u ^ 2 = 1
  f2 : f ^ 2 = 1
  z2 : z ^ 2 = 1
  s2 : s ^ 2 = 1
  uf : Commute u f
  uz : Commute u z
  us : Commute u s
  fz : Commute f z
  fs : Commute f s
  zs : Commute z s

namespace E16

variable {A : Subgroup G} {u f z s : G}

theorem elt_mul (h : E16 A u f z s) {a b : ℕ} (ha : a < 16) (hb : b < 16) :
    elt u f z s a * elt u f z s b = elt u f z s (a ^^^ b) := by
  obtain ⟨e1, e2, e3, e4⟩ := xor_bits a ha b hb
  unfold elt
  rw [e1, e2, e3, e4, pow_mod_two_add h.u2, pow_mod_two_add h.f2, pow_mod_two_add h.z2,
    pow_mod_two_add h.s2]
  have c1 : Commute (f ^ (a / 2 % 2) * (z ^ (a / 4 % 2) * s ^ (a / 8 % 2))) (u ^ (b % 2)) :=
    ((h.uf.symm.pow_pow _ _).mul_left ((h.uz.symm.pow_pow _ _).mul_left (h.us.symm.pow_pow _ _)))
  have c2 : Commute (z ^ (a / 4 % 2) * s ^ (a / 8 % 2)) (f ^ (b / 2 % 2)) :=
    ((h.fz.symm.pow_pow _ _).mul_left (h.fs.symm.pow_pow _ _))
  have c3 : Commute (s ^ (a / 8 % 2)) (z ^ (b / 4 % 2)) := h.zs.symm.pow_pow _ _
  rw [c1.mul_mul_mul_comm, c2.mul_mul_mul_comm, c3.mul_mul_mul_comm]

theorem elt_mem (h : E16 A u f z s) (c : ℕ) : elt u f z s c ∈ A :=
  (h.mem _).2 ⟨c % 2, c / 2 % 2, c / 4 % 2, c / 8 % 2, by simp only [elt, mul_assoc]⟩

theorem mem_iff (h : E16 A u f z s) (y : G) : y ∈ A ↔ ∃ c < 16, y = elt u f z s c := by
  refine ⟨fun hy => ?_, fun ⟨c, _, hc⟩ => hc ▸ h.elt_mem c⟩
  obtain ⟨i, j, k, l, rfl⟩ := (h.mem y).1 hy
  refine ⟨i % 2 + 2 * (j % 2) + 4 * (k % 2) + 8 * (l % 2), by omega, ?_⟩
  have e1 : (i % 2 + 2 * (j % 2) + 4 * (k % 2) + 8 * (l % 2)) % 2 = i % 2 := by omega
  have e2 : (i % 2 + 2 * (j % 2) + 4 * (k % 2) + 8 * (l % 2)) / 2 % 2 = j % 2 := by omega
  have e3 : (i % 2 + 2 * (j % 2) + 4 * (k % 2) + 8 * (l % 2)) / 4 % 2 = k % 2 := by omega
  have e4 : (i % 2 + 2 * (j % 2) + 4 * (k % 2) + 8 * (l % 2)) / 8 % 2 = l % 2 := by omega
  simp only [elt, e1, e2, e3, e4, ← pow_eq_pow_mod _ h.u2, ← pow_eq_pow_mod _ h.f2,
    ← pow_eq_pow_mod _ h.z2, ← pow_eq_pow_mod _ h.s2, mul_assoc]

theorem elt_inj (h : E16 A u f z s) {c d : ℕ} (hc : c < 16) (hd : d < 16)
    (e : elt u f z s c = elt u f z s d) : c = d := by
  let F : Fin 16 → ↥A := fun c => ⟨elt u f z s c.1, h.elt_mem c.1⟩
  have hsurj : Function.Surjective F := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc, rfl⟩ := (h.mem_iff y).1 hy
    exact ⟨⟨c, hc⟩, rfl⟩
  have hbij : Function.Bijective F :=
    hsurj.bijective_of_nat_card_le (by rw [h.card, Nat.card_eq_fintype_card, Fintype.card_fin])
  have := hbij.1 (a₁ := ⟨c, hc⟩) (a₂ := ⟨d, hd⟩) (Subtype.ext e)
  simpa using this

theorem exists_code (h : E16 A u f z s) (t : ↥A) :
    ∃ c < 16, t = ⟨elt u f z s c, h.elt_mem c⟩ := by
  obtain ⟨y, hy⟩ := t
  obtain ⟨c, hc, rfl⟩ := (h.mem_iff y).1 hy
  exact ⟨c, hc, rfl⟩

theorem comm (h : E16 A u f z s) {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x := by
  obtain ⟨a, ha, rfl⟩ := (h.mem_iff x).1 hx
  obtain ⟨b, hb, rfl⟩ := (h.mem_iff y).1 hy
  rw [h.elt_mul ha hb, h.elt_mul hb ha, Nat.xor_comm]

theorem acts_lin (h : E16 A u f z s) {x : G} {cu cf cz cs : ℕ} (hcu : cu < 16) (hcf : cf < 16)
    (hcz : cz < 16) (hcs : cs < 16) (hxu : x * u * x⁻¹ = elt u f z s cu)
    (hxf : x * f * x⁻¹ = elt u f z s cf) (hxz : x * z * x⁻¹ = elt u f z s cz)
    (hxs : x * s * x⁻¹ = elt u f z s cs) : Acts u f z s x (lin cu cf cz cs) := by
  intro c hc
  refine ⟨lin_lt hcu hcf hcz hcs c, ?_⟩
  have e : MulAut.conj x (elt u f z s c) = (MulAut.conj x u) ^ (c % 2) *
      ((MulAut.conj x f) ^ (c / 2 % 2) * ((MulAut.conj x z) ^ (c / 4 % 2) *
        (MulAut.conj x s) ^ (c / 8 % 2))) := by
    simp only [elt, map_mul, map_pow]
  simp only [MulAut.conj_apply] at e
  rw [e, hxu, hxf, hxz, hxs, pow_bsel (Nat.mod_lt _ two_pos), pow_bsel (Nat.mod_lt _ two_pos),
    pow_bsel (Nat.mod_lt _ two_pos), pow_bsel (Nat.mod_lt _ two_pos)]
  unfold lin
  rw [h.elt_mul (bsel_lt hcz) (bsel_lt hcs),
    h.elt_mul (bsel_lt hcf) (xor_lt (bsel_lt hcz) (bsel_lt hcs)),
    h.elt_mul (bsel_lt hcu) (xor_lt (bsel_lt hcf) (xor_lt (bsel_lt hcz) (bsel_lt hcs)))]

theorem mem_normalizer (h : E16 A u f z s) {x : G} {L : ℕ → ℕ} (hx : Acts u f z s x L) :
    x ∈ normalizer (A : Set G) := by
  have : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
  refine mem_normalizer_fintype fun n hn => ?_
  obtain ⟨c, hc, rfl⟩ := (h.mem_iff n).1 hn
  rw [SetLike.mem_coe, (hx c hc).2]
  exact h.elt_mem _

theorem phi_elt (h : E16 A u f z s) (W : ↥(normalizer (A : Set G))) {L : ℕ → ℕ}
    (hW : Acts u f z s (W : G) L) {c : ℕ} (hc : c < 16) :
    A.normalizerMonoidHom W ⟨elt u f z s c, h.elt_mem c⟩ = ⟨elt u f z s (L c), h.elt_mem _⟩ := by
  apply Subtype.ext
  simpa using (hW c hc).2

theorem phi_eq_one (h : E16 A u f z s) (W : ↥(normalizer (A : Set G))) {L : ℕ → ℕ}
    (hW : Acts u f z s (W : G) L) (hL : ∀ c < 16, L c = c) : A.normalizerMonoidHom W = 1 := by
  refine MulEquiv.ext fun t => ?_
  obtain ⟨c, hc, rfl⟩ := h.exists_code t
  rw [h.phi_elt W hW hc, hL c hc]
  rfl

theorem phi_ne_one (h : E16 A u f z s) (W : ↥(normalizer (A : Set G))) {L : ℕ → ℕ}
    (hW : Acts u f z s (W : G) L) {c : ℕ} (hc : c < 16) (hne : L c ≠ c) :
    A.normalizerMonoidHom W ≠ 1 := by
  intro h1
  have e := h.phi_elt W hW hc
  rw [h1] at e
  exact hne (h.elt_inj (hW c hc).1 hc (congrArg Subtype.val e).symm)

theorem ker_dvd (h : E16 A u f z s) : 16 ∣ Nat.card ↥(A.normalizerMonoidHom.ker) := by
  have hle : A.subgroupOf (normalizer (A : Set G)) ≤ A.normalizerMonoidHom.ker := by
    intro X hX
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun t => Subtype.ext ?_
    have hc := h.comm (mem_subgroupOf.1 hX) t.2
    simp [hc]
  have := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv, h.card] at this

end E16

def La : ℕ → ℕ := lin 1 2 8 4

def Lb : ℕ → ℕ := lin 1 2 4 12

def Lg (bi bj bk bl bm : ℕ) : ℕ → ℕ := lin 5 (2 + bi + 4 * bj) 4 (8 + bk + 2 * bl + 4 * bm)

abbrev Bad (L : ℕ → ℕ) : Prop := L 1 = 4 ∨ L 1 = 8 ∨ L 1 = 12

abbrev Good (a w : ℕ → ℕ) : Prop :=
  (∀ c < 16, a (a c) = c) ∧ (∀ c < 16, w (w c) = c) ∧
  (∀ c < 16, a (w (a (w (a (w (a (w c))))))) = c) ∧ ∃ c < 16, a (w (a (w c))) ≠ c

@[expose] def Case (g : ℕ → ℕ) : Prop :=
  Bad (fun c => g (La (g c))) ∨ Bad (fun c => g (g (La (g c)))) ∨ Good La g ∨
    Good La (fun c => Lb (g c)) ∨ Good La (fun c => g (La (g (g (g c))))) ∨
    Good La (fun c => g (g c))

instance (g : ℕ → ℕ) : Decidable (Case g) := by unfold Case; infer_instance

theorem table : ∀ bi < 2, ∀ bj < 2, ∀ bk < 2, ∀ bl < 2, ∀ bm < 2, Case (Lg bi bj bk bl bm) := by
  decide

namespace E16

variable {A : Subgroup G} {u f z s : G}

theorem good_step (h : E16 A u f z s) {x y : G} {Lx Ly : ℕ → ℕ} (hx : Acts u f z s x Lx)
    (hy : Acts u f z s y Ly) (hg : Good Lx Ly) :
    8 ∣ Nat.card ↥(A.normalizerMonoidHom.range) := by
  obtain ⟨hxx, hyy, h4, c0, hc0, h2⟩ := hg
  have : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
  let X : ↥(normalizer (A : Set G)) := ⟨x, h.mem_normalizer hx⟩
  let Y : ↥(normalizer (A : Set G)) := ⟨y, h.mem_normalizer hy⟩
  have hXX : A.normalizerMonoidHom (X * X) = 1 := h.phi_eq_one (X * X) (hx.mul hx) hxx
  have hYY : A.normalizerMonoidHom (Y * Y) = 1 := h.phi_eq_one (Y * Y) (hy.mul hy) hyy
  have hP : Acts u f z s ((X * Y : ↥(normalizer (A : Set G))) : G) (fun c => Lx (Ly c)) :=
    hx.mul hy
  have e2 : A.normalizerMonoidHom (X * Y * (X * Y)) ≠ 1 := h.phi_ne_one _ (hP.mul hP) hc0 h2
  have e4 : A.normalizerMonoidHom (X * Y * (X * Y) * (X * Y * (X * Y))) = 1 :=
    h.phi_eq_one _ ((hP.mul hP).mul (hP.mul hP)) h4
  have key := eight_dvd_closure_pair (a := A.normalizerMonoidHom X) (w := A.normalizerMonoidHom Y)
    (by rw [← map_mul]; exact hXX) (by rw [← map_mul]; exact hYY)
    (by simpa only [map_mul] using e2) (by simpa only [map_mul] using e4)
  refine key.trans (Subgroup.card_dvd_of_le ?_)
  rw [closure_le]
  rintro t (rfl | rfl)
  · exact ⟨X, rfl⟩
  · exact ⟨Y, rfl⟩

end E16

theorem bad_step {u f z s w n1 n2 : G} {L : ℕ → ℕ} (hw : Acts u f z s w L) (hL : Bad L)
    (hn1z : n1 * z * n1⁻¹ = s) (hn2s : n2 * s * n2⁻¹ = z * s)
    (hnc : ∀ w : G, w * u * w⁻¹ ≠ z) : False := by
  have hw1 := (hw 1 (by norm_num)).2
  have e1 : elt u f z s 1 = u := by simp [elt]
  have e4 : elt u f z s 4 = z := by simp [elt]
  have e8 : elt u f z s 8 = s := by simp [elt]
  have e12 : elt u f z s 12 = z * s := by simp [elt]
  rw [e1] at hw1
  rcases hL with hL | hL | hL
  · rw [hL, e4] at hw1
    exact hnc w hw1
  · rw [hL, e8] at hw1
    refine hnc (n1⁻¹ * w) ?_
    calc n1⁻¹ * w * u * (n1⁻¹ * w)⁻¹ = n1⁻¹ * (w * u * w⁻¹) * n1 := by group
      _ = n1⁻¹ * s * n1 := by rw [hw1]
      _ = z := by rw [← hn1z]; group
  · rw [hL, e12] at hw1
    refine hnc (n1⁻¹ * (n2⁻¹ * w)) ?_
    calc n1⁻¹ * (n2⁻¹ * w) * u * (n1⁻¹ * (n2⁻¹ * w))⁻¹
        = n1⁻¹ * (n2⁻¹ * (w * u * w⁻¹) * n2) * n1 := by group
      _ = n1⁻¹ * (n2⁻¹ * (z * s) * n2) * n1 := by rw [hw1]
      _ = z := by rw [← hn2s, ← hn1z]; group

namespace E16

variable {A : Subgroup G} {u f z s : G}

theorem range_dvd (h : E16 A u f z s) {n1 n2 g : G} {bi bj bk bl bm : ℕ} (hbi : bi < 2)
    (hbj : bj < 2) (hbk : bk < 2) (hbl : bl < 2) (hbm : bm < 2)
    (hn1 : Acts u f z s n1 La) (hn2 : Acts u f z s n2 Lb)
    (hg : Acts u f z s g (Lg bi bj bk bl bm)) (hn1z : n1 * z * n1⁻¹ = s)
    (hn2s : n2 * s * n2⁻¹ = z * s) (hnc : ∀ w : G, w * u * w⁻¹ ≠ z) :
    8 ∣ Nat.card ↥(A.normalizerMonoidHom.range) := by
  rcases table bi hbi bj hbj bk hbk bl hbl bm hbm with hb | hb | hgd | hgd | hgd | hgd
  · exact (bad_step (hg.mul (hn1.mul hg)) hb hn1z hn2s hnc).elim
  · exact (bad_step (hg.mul (hg.mul (hn1.mul hg))) hb hn1z hn2s hnc).elim
  · exact good_step h hn1 hg hgd
  · exact good_step h hn1 (hn2.mul hg) hgd
  · exact good_step h hn1 (hg.mul (hn1.mul (hg.mul (hg.mul hg)))) hgd
  · exact good_step h hn1 (hg.mul hg) hgd

end E16

end NormDvd

open NormDvd

theorem normalizer_dvd
    {G : Type} [Group G] [Finite G] (A : Subgroup G) (u f z s n1 n2 g : G)
    (hA : ∀ y : G, y ∈ A ↔ ∃ i j k l : ℕ, y = u ^ i * f ^ j * z ^ k * s ^ l)
    (hcard : Nat.card ↥A = 16)
    (hu2 : u ^ 2 = 1) (hf2 : f ^ 2 = 1) (hz2 : z ^ 2 = 1) (hs2 : s ^ 2 = 1)
    (huf : u * f = f * u) (huz : u * z = z * u) (hus : u * s = s * u)
    (hfz : f * z = z * f) (hfs : f * s = s * f) (hzs : z * s = s * z)
    (n1_u : n1 * u * n1⁻¹ = u) (n1_f : n1 * f * n1⁻¹ = f)
    (n1_z : n1 * z * n1⁻¹ = s) (n1_s : n1 * s * n1⁻¹ = z)
    (n2_u : n2 * u * n2⁻¹ = u) (n2_f : n2 * f * n2⁻¹ = f)
    (n2_z : n2 * z * n2⁻¹ = z) (n2_s : n2 * s * n2⁻¹ = z * s)
    (g_u : g * u * g⁻¹ = u * z) (g_z : g * z * g⁻¹ = z)
    (g_f : ∃ i j : ℕ, g * f * g⁻¹ = f * u ^ i * z ^ j)
    (g_s : ∃ i j k : ℕ, g * s * g⁻¹ = s * u ^ i * f ^ j * z ^ k)
    (hnc : ∀ w : G, w * u * w⁻¹ ≠ z) :
    2 ^ 7 ∣ Nat.card ↥(Subgroup.normalizer (A : Set G)) := by
  have h : E16 A u f z s := ⟨hA, hcard, hu2, hf2, hz2, hs2, huf, huz, hus, hfz, hfs, hzs⟩
  have e1 : elt u f z s 1 = u := by simp [elt]
  have e2 : elt u f z s 2 = f := by simp [elt]
  have e4 : elt u f z s 4 = z := by simp [elt]
  have e5 : elt u f z s 5 = u * z := by simp [elt]
  have e8 : elt u f z s 8 = s := by simp [elt]
  have e12 : elt u f z s 12 = z * s := by simp [elt]
  have hn1 : Acts u f z s n1 La :=
    h.acts_lin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (n1_u.trans e1.symm)
      (n1_f.trans e2.symm) (n1_z.trans e8.symm) (n1_s.trans e4.symm)
  have hn2 : Acts u f z s n2 Lb :=
    h.acts_lin (by norm_num) (by norm_num) (by norm_num) (by norm_num) (n2_u.trans e1.symm)
      (n2_f.trans e2.symm) (n2_z.trans e4.symm) (n2_s.trans e12.symm)
  obtain ⟨p, q, hgf⟩ := g_f
  obtain ⟨r, t, v, hgs⟩ := g_s
  have hgf' : g * f * g⁻¹ = elt u f z s (2 + p % 2 + 4 * (q % 2)) := by
    rw [hgf]
    have c1 : (2 + p % 2 + 4 * (q % 2)) % 2 = p % 2 := by omega
    have c2 : (2 + p % 2 + 4 * (q % 2)) / 2 % 2 = 1 := by omega
    have c3 : (2 + p % 2 + 4 * (q % 2)) / 4 % 2 = q % 2 := by omega
    have c4 : (2 + p % 2 + 4 * (q % 2)) / 8 % 2 = 0 := by omega
    simp only [elt, c1, c2, c3, c4, pow_one, pow_zero, mul_one]
    rw [← pow_eq_pow_mod p hu2, ← pow_eq_pow_mod q hz2, (h.uf.symm.pow_right p).eq, mul_assoc]
  have hgs' : g * s * g⁻¹ = elt u f z s (8 + r % 2 + 2 * (t % 2) + 4 * (v % 2)) := by
    rw [hgs]
    have c1 : (8 + r % 2 + 2 * (t % 2) + 4 * (v % 2)) % 2 = r % 2 := by omega
    have c2 : (8 + r % 2 + 2 * (t % 2) + 4 * (v % 2)) / 2 % 2 = t % 2 := by omega
    have c3 : (8 + r % 2 + 2 * (t % 2) + 4 * (v % 2)) / 4 % 2 = v % 2 := by omega
    have c4 : (8 + r % 2 + 2 * (t % 2) + 4 * (v % 2)) / 8 % 2 = 1 := by omega
    simp only [elt, c1, c2, c3, c4, pow_one]
    rw [← pow_eq_pow_mod r hu2, ← pow_eq_pow_mod t hf2, ← pow_eq_pow_mod v hz2]
    have hc : Commute s (u ^ r * (f ^ t * z ^ v)) :=
      (h.us.symm.pow_right r).mul_right ((h.fs.symm.pow_right t).mul_right (h.zs.symm.pow_right v))
    calc s * u ^ r * f ^ t * z ^ v = s * (u ^ r * (f ^ t * z ^ v)) := by simp only [mul_assoc]
      _ = u ^ r * (f ^ t * z ^ v) * s := hc.eq
      _ = u ^ r * (f ^ t * (z ^ v * s)) := by simp only [mul_assoc]
  have hg : Acts u f z s g (Lg (p % 2) (q % 2) (r % 2) (t % 2) (v % 2)) :=
    h.acts_lin (by omega) (by omega) (by norm_num) (by omega) (g_u.trans e5.symm)
      (hgf') (g_z.trans e4.symm) hgs'
  have hrange := h.range_dvd (Nat.mod_lt _ two_pos) (Nat.mod_lt _ two_pos) (Nat.mod_lt _ two_pos)
    (Nat.mod_lt _ two_pos) (Nat.mod_lt _ two_pos) hn1 hn2 hg n1_z n2_s hnc
  have hker := h.ker_dvd
  rw [← Subgroup.card_ker_mul_card_range A.normalizerMonoidHom,
    show (2 : ℕ) ^ 7 = 16 * 8 by norm_num]
  exact Nat.mul_dvd_mul hker hrange

end CFSG.GH74.GLS.C3.Layer1.P89
