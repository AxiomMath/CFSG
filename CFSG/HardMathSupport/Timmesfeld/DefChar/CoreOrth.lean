module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterOrth
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreC

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open QuadraticMap

namespace Orth
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

@[expose] def eich (a b : V) : V →ₗ[K] V where
  toFun x := x + polar Q x a • b - (polar Q x b + Q b * polar Q x a) • a
  map_add' x y := by
    simp only [polar_add_left, add_smul, smul_sub]
    module
  map_smul' c x := by
    simp only [polar_smul_left, smul_eq_mul, RingHom.id_apply, smul_add, smul_sub, mul_add]
    module

theorem eich_apply (a b x : V) :
    eich Q a b x = x + polar Q x a • b - (polar Q x b + Q b * polar Q x a) • a := rfl

theorem eich_zero_right (a x : V) : eich Q a 0 x = x := by
  simp [eich_apply]



variable {Q}

theorem Qadd (x y : V) : Q (x + y) = Q x + Q y + polar Q x y := QuadraticMap.map_add _ _ _

theorem Qsmul (c : K) (x : V) : Q (c • x) = c ^ 2 * Q x := by
  rw [QuadraticMap.map_smul, smul_eq_mul, _root_.sq]

theorem polar_aa (a : V) (ha : Q a = 0) : polar Q a a = 0 := by
  rw [polar_self, ha]; simp

theorem map_eich (a b : V) (ha : Q a = 0) (hab : polar Q a b = 0) (x : V) :
    Q (eich Q a b x) = Q x := by
  rw [eich_apply]
  set s := polar Q x a
  set t := polar Q x b + Q b * s
  have hba : polar Q b a = 0 := by rw [polar_comm]; exact hab
  have e1 : x + s • b - t • a = (x + s • b) + (-t) • a := by rw [neg_smul, sub_eq_add_neg]
  rw [e1, Qadd, Qadd, Qsmul, Qsmul, ha]
  simp only [polar_add_left, polar_smul_left, polar_smul_right, polar_comm Q b x, polar_comm Q a x, hab, hba,
    smul_eq_mul]
  have hs : polar Q x a = s := rfl
  rw [hs]
  have ht : t = polar Q x b + Q b * s := rfl
  simp only [ht]
  ring

theorem eich_comp (a b b' : V) (ha : Q a = 0) (hab : polar Q a b = 0) (hab' : polar Q a b' = 0) (x : V) :
    eich Q a b (eich Q a b' x) = eich Q a (b + b') x := by
  have hba : polar Q b a = 0 := by rw [polar_comm]; exact hab
  have hba' : polar Q b' a = 0 := by rw [polar_comm]; exact hab'
  have haa := polar_aa a ha
  simp only [eich_apply, polar_add_left, polar_add_right, polar_sub_left, polar_sub_right, polar_smul_left, polar_smul_right,
    hab, hab', hba, hba', haa, smul_eq_mul, Qadd]
  rw [polar_comm Q b b']
  module

section Skew
variable (Z : Module.End K V)

@[expose] def IsSkew : Prop := ∀ x y, polar Q (Z x) y = - polar Q x (Z y)

variable {Z}

theorem polar_zero_of_ker_range (hZ : IsSkew (Q := Q) Z) {x a : V} (hx : Z x = 0) (ha : a ∈ LinearMap.range Z) :
    polar Q x a = 0 := by
  obtain ⟨u, rfl⟩ := ha
  have := hZ x u
  rw [hx, polar_zero_left] at this
  simpa using this.symm

theorem polar_zero_of_ker_range' (hZ : IsSkew (Q := Q) Z) {x a : V} (hx : Z x = 0) (ha : a ∈ LinearMap.range Z) :
    polar Q a x = 0 := by
  rw [polar_comm]; exact polar_zero_of_ker_range hZ hx ha

theorem Q_eq_zero_of_mem_W (h2 : (2 : K) ≠ 0) (hZ : IsSkew (Q := Q) Z) {a : V} (ha : Z a = 0)
    (ha' : a ∈ LinearMap.range Z) : Q a = 0 := by
  have := polar_zero_of_ker_range hZ ha ha'
  rw [polar_self] at this
  simpa [h2] using this

theorem eich_comm (hZ : IsSkew (Q := Q) Z) {a b : V} (ha : Z a = 0) (hb : Z b = 0) (x : V) :
    Z (eich Q a b x) = eich Q a b (Z x) := by
  have h1 : polar Q (Z x) a = 0 := by
    have := hZ x a; rw [ha, polar_zero_right] at this; simpa using this
  have h2 : polar Q (Z x) b = 0 := by
    have := hZ x b; rw [hb, polar_zero_right] at this; simpa using this
  simp only [eich_apply, map_add, map_sub, map_smul, ha, hb, h1, h2]
  simp

@[expose] def InFlag (Z : Module.End K V) (f : Module.End K V) : Prop :=
  (∀ x, f (Z x) = Z (f x)) ∧
  (∀ x ∈ LinearMap.ker Z, f x - x ∈ LinearMap.ker Z ⊓ LinearMap.range Z) ∧
  (∀ x ∈ LinearMap.ker Z ⊓ LinearMap.range Z, f x = x)

theorem InFlag.mul {f g : Module.End K V} (hf : InFlag Z f) (hg : InFlag Z g) : InFlag Z (f * g) := by
  obtain ⟨f0, f2, f3⟩ := hf
  obtain ⟨g0, g2, g3⟩ := hg
  have pres : ∀ {h : Module.End K V}, (∀ x, h (Z x) = Z (h x)) → ∀ x ∈ LinearMap.ker Z,
      h x ∈ LinearMap.ker Z := fun {h} h0 x hx => by
    simp only [LinearMap.mem_ker] at hx ⊢
    rw [← h0, hx, map_zero]
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · show f (g (Z x)) = Z (f (g x))
    rw [g0, f0]
  · have : (f * g) x - x = (f (g x) - g x) + (g x - x) := by simp
    rw [this]
    exact Submodule.add_mem _ (f2 _ (pres g0 x hx)) (g2 _ hx)
  · have h := g3 x hx
    show f (g x) = x
    rw [h]; exact f3 x hx

theorem InFlag.one : InFlag Z (1 : Module.End K V) := by
  refine ⟨fun x => rfl, fun x _ => ?_, fun x _ => rfl⟩
  simp

theorem InFlag.sq_apply {f : Module.End K V} (hf : InFlag Z f) {x : V} (hx : Z x = 0) :
    (f - 1) ((f - 1) x) = 0 := by
  obtain ⟨f0, f2, f3⟩ := hf
  have h1 : (f - 1) x ∈ LinearMap.ker Z ⊓ LinearMap.range Z := by
    simpa using f2 x hx
  have := f3 _ h1
  simp only [LinearMap.sub_apply, Module.End.one_apply] at this ⊢
  rw [this, sub_self]

theorem eich_inFlag (hZ : IsSkew (Q := Q) Z) {a b : V} (ha : Z a = 0) (ha' : a ∈ LinearMap.range Z)
    (hb : Z b = 0) : InFlag Z (eich Q a b) := by
  have hKa : ∀ x, Z x = 0 → polar Q x a = 0 := fun x hx => polar_zero_of_ker_range hZ hx ha'
  have hKb : ∀ x, x ∈ LinearMap.range Z → polar Q x b = 0 := fun x hx =>
    polar_zero_of_ker_range' hZ hb hx
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact (eich_comm hZ ha hb x).symm
  · have : eich Q a b x - x = - (polar Q x b) • a := by
      simp [eich_apply, hKa x hx]
    rw [this]
    exact Submodule.smul_mem _ _ ⟨by simpa using ha, ha'⟩
  · have h1 : polar Q x a = 0 := hKa x hx.1
    have h2 : polar Q x b = 0 := hKb x hx.2
    simp [eich_apply, h1, h2]

theorem eich_comm₂ (hZ : IsSkew (Q := Q) Z) {a b : V} {c : K} (ha : Z a = 0) (hb : Z b = c • a)
    (x : V) : Z (eich Q a b x) = eich Q a b (Z x) := by
  have h1 : polar Q (Z x) a = 0 := by
    have := hZ x a; rw [ha, polar_zero_right] at this; simpa using this
  have h2 : polar Q (Z x) b = - (c * polar Q x a) := by
    have := hZ x b; rw [hb, polar_smul_right, smul_eq_mul] at this; exact this
  simp only [eich_apply, map_add, map_sub, map_smul, ha, hb, h1, h2]
  simp only [smul_zero, sub_zero, smul_smul]
  module

theorem eich_inFlag₂ (hZ : IsSkew (Q := Q) Z) {a b : V} {c : K} (ha : Z a = 0)
    (ha' : a ∈ LinearMap.range Z) (hb : Z b = c • a)
    (hbW : ∀ w, Z w = 0 → w ∈ LinearMap.range Z → polar Q w b = 0) :
    InFlag Z (eich Q a b) := by
  have hKa : ∀ x, Z x = 0 → polar Q x a = 0 := fun x hx => polar_zero_of_ker_range hZ hx ha'
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact (eich_comm₂ hZ ha hb x).symm
  · have : eich Q a b x - x = - (polar Q x b) • a := by
      simp [eich_apply, hKa x hx]
    rw [this]
    exact Submodule.smul_mem _ _ ⟨by simpa using ha, ha'⟩
  · have h1 : polar Q x a = 0 := hKa x hx.1
    have h2 : polar Q x b = 0 := hbW x hx.1 hx.2
    simp [eich_apply, h1, h2]

theorem isNilpotent_of_ker {B : Module.End K V} {n : ℕ} (hn : Z ^ n = 0) (hBZ : B * Z = Z * B)
    (hB : ∀ x, Z x = 0 → B (B x) = 0) : IsNilpotent B := by
  have key : ∀ j : ℕ, ∀ x, (Z ^ j) x = 0 → (B ^ (2 * j)) x = 0 := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      have h1 : (Z ^ j) (Z x) = 0 := by
        have : (Z ^ (j + 1)) x = (Z ^ j) (Z x) := by rw [pow_succ]; rfl
        rw [← this]; exact hx
      have h2 := ih _ h1
      have h3 : Z ((B ^ (2 * j)) x) = 0 := by
        have hc : ∀ k, Z * B ^ k = B ^ k * Z := fun k =>
          ((show Commute B Z from hBZ).symm.pow_right k).eq
        have := congrArg (fun f => f x) (hc (2 * j))
        simp only [Module.End.mul_apply] at this
        rw [this]; exact h2
      have h4 := hB _ h3
      have : (B ^ (2 * (j + 1))) x = B (B ((B ^ (2 * j)) x)) := by
        rw [show 2 * (j + 1) = 2 + 2 * j by ring, pow_add]
        simp [pow_two, Module.End.mul_apply]
      rw [this]; exact h4
  refine ⟨2 * n, ?_⟩
  ext x
  apply key
  rw [hn]; rfl

end Skew




theorem pow_prime_pow_eq_one {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p] {f : R} {n k : ℕ}
    (h : (f - 1) ^ n = 0) (hn : n ≤ p ^ k) : f ^ (p ^ k) = 1 := by
  have h1 : f = (f - 1) + 1 := by abel
  have h2 : (f - 1) ^ (p ^ k) = 0 := by
    have : p ^ k = n + (p ^ k - n) := by omega
    rw [this, pow_add, h, zero_mul]
  conv_lhs => rw [h1]
  rw [add_pow_char_pow_of_commute (R := R) p k (Commute.one_right _), h2]; simp

section Cayley
variable (Z : Module.End K V) (n : ℕ)

@[expose] def cay (t : K) : Module.End K V := (1 + t • Z) * ∑ i ∈ Finset.range n, (t • Z) ^ i

variable {Z n}

theorem geom_mul (hn : Z ^ n = 0) (t : K) :
    (∑ i ∈ Finset.range n, (t • Z) ^ i) * (1 - t • Z) = 1 := by
  rw [geom_sum_mul_neg, smul_pow, hn]; simp

theorem geom_mul' (hn : Z ^ n = 0) (t : K) :
    (1 - t • Z) * (∑ i ∈ Finset.range n, (t • Z) ^ i) = 1 := by
  rw [mul_neg_geom_sum, smul_pow, hn]; simp

theorem commute_geom (t : K) : Commute Z (∑ i ∈ Finset.range n, (t • Z) ^ i) := by
  refine Commute.sum_right _ _ _ fun i _ => ?_
  exact ((Commute.refl Z).smul_right t).pow_right i

theorem cay_comm {s : Module.End K V} (hs : s * Z = Z * s) (t : K) : s * cay Z n t = cay Z n t * s := by
  have hc : Commute s Z := hs
  have h1 : Commute s (1 + t • Z) := (Commute.one_right s).add_right (hc.smul_right t)
  have h2 : Commute s (∑ i ∈ Finset.range n, (t • Z) ^ i) :=
    Commute.sum_right _ _ _ fun i _ => (hc.smul_right t).pow_right i
  exact (h1.mul_right h2).eq

theorem cay_mul_one_sub (hn : Z ^ n = 0) (t : K) : cay Z n t * (1 - t • Z) = 1 + t • Z := by
  rw [cay, mul_assoc, geom_mul hn, mul_one]

theorem cay_sub_one (hn : Z ^ n = 0) (t : K) :
    cay Z n t - 1 = (2 * t) • Z * ∑ i ∈ Finset.range n, (t • Z) ^ i := by
  have h := geom_mul' hn t
  calc cay Z n t - 1 = (1 + t • Z) * (∑ i ∈ Finset.range n, (t • Z) ^ i) -
        (1 - t • Z) * (∑ i ∈ Finset.range n, (t • Z) ^ i) := by rw [h]; rfl
    _ = _ := by rw [← sub_mul]; congr 1; rw [mul_smul]; module

theorem isNilpotent_cay_sub_one (hn : Z ^ n = 0) (t : K) : IsNilpotent (cay Z n t - 1) := by
  rw [cay_sub_one hn]
  have hc : Commute ((2 * t) • Z) (∑ i ∈ Finset.range n, (t • Z) ^ i) :=
    (commute_geom (Z := Z) (n := n) t).smul_left (2 * t)
  exact hc.isNilpotent_mul_right ⟨n, by rw [smul_pow, hn, smul_zero]⟩

theorem polar_cay (hZ : IsSkew (Q := Q) Z) (hn : Z ^ n = 0) (t : K) (x y : V) :
    polar Q (cay Z n t x) (cay Z n t y) = polar Q x y := by
  set S := ∑ i ∈ Finset.range n, (t • Z) ^ i
  have h1 : ∀ w, (1 - t • Z) (S w) = w := fun w => by
    have h : ((1 - t • Z) * S) w = w := by rw [geom_mul' hn t]; rfl
    exact h
  have hx := h1 x
  have hy := h1 y
  have e1 : cay Z n t x = (1 + t • Z) (S x) := rfl
  have e2 : cay Z n t y = (1 + t • Z) (S y) := rfl
  set u := S x
  set v := S y
  rw [e1, e2, ← hx, ← hy]
  have hs : polar Q (Z u) v = - polar Q u (Z v) := hZ u v
  have hs' : polar Q (Z v) u = - polar Q v (Z u) := hZ v u
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply,
    polar_add_left, polar_add_right, polar_sub_left, polar_sub_right, polar_smul_left, polar_smul_right,
    smul_eq_mul]
  linear_combination (2 * t) * hs

theorem cay_neg_mul (hn : Z ^ n = 0) (t : K) : cay Z n t * cay Z n (-t) = 1 := by
  have hu : IsUnit (1 + t • Z) := IsNilpotent.isUnit_one_add ⟨n, by rw [smul_pow, hn, smul_zero]⟩
  have h1 := cay_mul_one_sub hn t
  have h2 := cay_mul_one_sub hn (-t)
  rw [neg_smul, sub_neg_eq_add] at h2
  rw [← sub_eq_add_neg] at h2
  have h3 : (cay Z n t * cay Z n (-t) - 1) * (1 + t • Z) = 0 := by
    rw [sub_mul, mul_assoc, h2, h1]; simp
  have := hu.mul_left_eq_zero.1 h3
  exact sub_eq_zero.1 this

theorem cay_inj (h2 : (2 : K) ≠ 0) (hn : Z ^ n = 0) {s t : K}
    (h : cay Z n s = cay Z n t) : (s - t) • Z = 0 := by
  have e1 := cay_mul_one_sub hn s
  have e2 := cay_mul_one_sub hn t
  rw [← h] at e2
  set C := cay Z n s
  set x := s • Z
  set y := t • Z
  have hCZ : C * Z = Z * C := (cay_comm (Z := Z) (n := n) (s := Z) rfl s).symm
  have a1 : x + C * x = C - 1 := by
    rw [mul_sub, mul_one] at e1
    calc x + C * x = (1 + x) - 1 + C * x := by abel
      _ = (C - C * x) - 1 + C * x := by rw [← e1]
      _ = C - 1 := by abel
  have a2 : y + C * y = C - 1 := by
    rw [mul_sub, mul_one] at e2
    calc y + C * y = (1 + y) - 1 + C * y := by abel
      _ = (C - C * y) - 1 + C * y := by rw [← e2]
      _ = C - 1 := by abel
  have a3 : (1 + C) * (x - y) = 0 := by
    have : (x + C * x) - (y + C * y) = 0 := by rw [a1, a2]; simp
    calc (1 + C) * (x - y) = (x + C * x) - (y + C * y) := by noncomm_ring
      _ = 0 := this
  have hxC : (x - y) * C = C * (x - y) := by
    simp only [x, y, ← sub_smul, mul_smul_comm, smul_mul_assoc, hCZ]
  have a4 : (x - y) * ((1 + C) * (1 - x)) = 0 := by
    calc (x - y) * ((1 + C) * (1 - x)) = ((x - y) * (1 + C)) * (1 - x) := by rw [mul_assoc]
      _ = 0 := by
        have : (x - y) * (1 + C) = (1 + C) * (x - y) := by
          rw [mul_add, add_mul, mul_one, one_mul, hxC]
        rw [this, a3, zero_mul]
  have a5 : (1 + C) * (1 - x) = 2 := by
    calc (1 + C) * (1 - x) = (1 - x) + C * (1 - x) := by rw [add_mul, one_mul]
      _ = 2 := by rw [e1]; norm_num
  rw [a5] at a4
  have : (x - y) * 2 = 0 := a4
  have h2' : (x - y) = 0 := by
    rw [mul_two, ← two_smul K] at this
    exact (smul_eq_zero.1 this).resolve_left h2
  simpa [x, y, sub_smul] using h2'

end Cayley




section Gen
variable (p : ℕ) (G : Module.End K V)

@[expose] def invS : Module.End K V := (2 : K)⁻¹ • ∑ i ∈ Finset.range p, ((-1 : K) • G) ^ i

@[expose] def zOf : Module.End K V := (G - 1) * invS p G

variable {p G}

theorem add_one_mul_geom (hp : Odd p) (hG : G ^ p = 1) :
    (G + 1) * ∑ i ∈ Finset.range p, ((-1 : K) • G) ^ i = 1 + 1 := by
  have h1 : (G + 1) = 1 - (-1 : K) • G := by simp [sub_eq_add_neg, add_comm]
  rw [h1, mul_neg_geom_sum, smul_pow, hp.neg_pow, one_pow, hG]
  simp [sub_neg_eq_add]

theorem commute_invS : Commute G (invS p G) := by
  unfold invS
  refine Commute.smul_right (Commute.sum_right _ _ _ fun i _ => ?_) _
  exact ((Commute.refl G).smul_right (-1 : K)).pow_right i

theorem add_one_mul_invS (h2 : (2 : K) ≠ 0) (hp : Odd p) (hG : G ^ p = 1) :
    (G + 1) * invS p G = 1 := by
  rw [invS, mul_smul_comm (2 : K)⁻¹, add_one_mul_geom hp hG, ← two_smul K (1 : Module.End K V), smul_smul,
    inv_mul_cancel₀ h2, one_smul]

theorem invS_mul_add_one (h2 : (2 : K) ≠ 0) (hp : Odd p) (hG : G ^ p = 1) :
    invS p G * (G + 1) = 1 := by
  have hc : Commute (G + 1) (invS p G) := (commute_invS (p := p) (G := G)).add_left (Commute.one_left _)
  rw [← hc.eq]
  exact add_one_mul_invS h2 hp hG

theorem zOf_mul_add_one (h2 : (2 : K) ≠ 0) (hp : Odd p) (hG : G ^ p = 1) :
    zOf p G * (G + 1) = G - 1 := by
  rw [zOf, mul_assoc, invS_mul_add_one h2 hp hG, mul_one]

theorem commute_zOf {s : Module.End K V} (hs : s * G = G * s) : s * zOf p G = zOf p G * s := by
  have hc : Commute s G := hs
  have h1 : Commute s (invS p G) := by
    unfold invS
    refine Commute.smul_right (Commute.sum_right _ _ _ fun i _ => ?_) _
    exact (hc.smul_right (-1 : K)).pow_right i
  exact (((hc.sub_right (Commute.one_right s))).mul_right h1).eq

theorem isSkew_zOf (h2 : (2 : K) ≠ 0) (hp : Odd p) (hG : G ^ p = 1)
    (hiso : ∀ x y, polar Q (G x) (G y) = polar Q x y) : IsSkew (Q := Q) (zOf p G) := by
  intro x y
  have hs1 : ∀ w, (G + 1) (invS p G w) = w := fun w => by
    have h : ((G + 1) * invS p G) w = w := by rw [add_one_mul_invS h2 hp hG]; rfl
    exact h
  obtain ⟨u, rfl⟩ : ∃ u, x = (G + 1) u := ⟨invS p G x, (hs1 x).symm⟩
  obtain ⟨v, rfl⟩ : ∃ v, y = (G + 1) v := ⟨invS p G y, (hs1 y).symm⟩
  have e : ∀ w, zOf p G ((G + 1) w) = (G - 1) w := fun w => by
    have h : (zOf p G * (G + 1)) w = (G - 1) w := by rw [zOf_mul_add_one h2 hp hG]
    exact h
  rw [e, e]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply, polar_add_left,
    polar_add_right, polar_sub_left, polar_sub_right, hiso]
  rw [polar_comm Q (G u) v]
  ring

variable [Fact p.Prime] [CharP (Module.End K V) p]

theorem zOf_pow (hG : G ^ p = 1) : zOf p G ^ p = 0 := by
  have hc : Commute (G - 1) (invS p G) :=
    (commute_invS (p := p) (G := G)).sub_left (Commute.one_left _)
  have h1 : (G - 1) ^ p = 0 := by
    rw [sub_pow_char_of_commute p (Commute.one_right G), hG]; simp
  rw [zOf, hc.mul_pow, h1, zero_mul]

theorem cay_zOf (h2 : (2 : K) ≠ 0) (hp : Odd p) (hG : G ^ p = 1) :
    cay (zOf p G) p 1 = G := by
  set Z := zOf p G
  have hn : Z ^ p = 0 := zOf_pow hG
  have hZG : Z * G = G * Z := (commute_zOf (p := p) (G := G) (s := G) rfl).symm
  have h1 := zOf_mul_add_one h2 hp hG
  have h3 : G * (1 - Z) = 1 + Z := by
    rw [mul_sub, mul_one, ← hZG]
    rw [mul_add, mul_one] at h1
    calc G - Z * G = G - (G - 1 - Z) := by rw [← h1]; abel
      _ = 1 + Z := by abel
  have h4 := cay_mul_one_sub hn (1 : K)
  rw [one_smul] at h4
  have hu : IsUnit (1 - Z) := IsNilpotent.isUnit_one_sub ⟨p, hn⟩
  have : (cay Z p 1 - G) * (1 - Z) = 0 := by rw [sub_mul, h4, h3]; simp
  exact sub_eq_zero.1 (hu.mul_left_eq_zero.1 this)

theorem zOf_ne_zero (h2 : (2 : K) ≠ 0) (hp : Odd p) (hG : G ^ p = 1) (hG1 : G ≠ 1) :
    zOf p G ≠ 0 := by
  intro h
  have := zOf_mul_add_one h2 hp hG
  rw [h, zero_mul] at this
  exact hG1 (sub_eq_zero.1 this.symm)

end Gen



theorem eich_sub_neg (a b x : V) :
    eich Q a b x - eich Q a (-b) x = (2 : K) • (polar Q x a • b - polar Q x b • a) := by
  simp only [eich_apply, polar_neg_right, QuadraticMap.map_neg]
  module

theorem eich_add_neg (a b x : V) :
    eich Q a b x + eich Q a (-b) x = (2 : K) • x - (2 * Q b * polar Q x a) • a := by
  simp only [eich_apply, polar_neg_right, QuadraticMap.map_neg]
  module

section Comm
variable {A : Module.End K V}

theorem comm_X (h2 : (2 : K) ≠ 0) {a b : V}
    (h1 : A * eich Q a b = eich Q a b * A) (h1' : A * eich Q a (-b) = eich Q a (-b) * A) (x : V) :
    A (polar Q x a • b - polar Q x b • a) = polar Q (A x) a • b - polar Q (A x) b • a := by
  have e1 := congrArg (fun f => f x) h1
  have e2 := congrArg (fun f => f x) h1'
  simp only [Module.End.mul_apply] at e1 e2
  have e3 : A ((2 : K) • (polar Q x a • b - polar Q x b • a)) =
      (2 : K) • (polar Q (A x) a • b - polar Q (A x) b • a) := by
    rw [← eich_sub_neg, ← eich_sub_neg, map_sub, e1, e2]
  rw [map_smul] at e3
  exact smul_right_injective V h2 e3

theorem comm_P (h2 : (2 : K) ≠ 0) {a b : V}
    (h1 : A * eich Q a b = eich Q a b * A) (h1' : A * eich Q a (-b) = eich Q a (-b) * A) (x : V) :
    (Q b * polar Q x a) • A a = (Q b * polar Q (A x) a) • a := by
  have e1 := congrArg (fun f => f x) h1
  have e2 := congrArg (fun f => f x) h1'
  simp only [Module.End.mul_apply] at e1 e2
  have e3 : A ((2 : K) • x - (2 * Q b * polar Q x a) • a) =
      (2 : K) • A x - (2 * Q b * polar Q (A x) a) • a := by
    rw [← eich_add_neg, ← eich_add_neg, map_add, e1, e2]
  rw [map_sub, map_smul, map_smul] at e3
  have e4 : (2 * Q b * polar Q x a) • A a = (2 * Q b * polar Q (A x) a) • a := by
    have := sub_right_inj.1 e3
    exact this
  have e5 : (2 : K) • ((Q b * polar Q x a) • A a) = (2 : K) • ((Q b * polar Q (A x) a) • a) := by
    simpa [smul_smul, mul_assoc] using e4
  exact smul_right_injective V h2 e5

end Comm

theorem exists_vec_pow {Z : Module.End K V} {n : ℕ} (hn : Z ^ n = 0) (k : ℕ) (hk : Z ^ k ≠ 0) :
    ∃ u, (Z ^ k) u ≠ 0 ∧ (Z ^ (k + 1)) u = 0 := by
  classical
  have hex : ∃ j : ℕ, Z ^ (k + j + 1) = 0 := by
    refine ⟨n, ?_⟩
    have : n ≤ k + n + 1 := by omega
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le this
    rw [hr, pow_add, hn, zero_mul]
  set j := Nat.find hex with hj
  have hjs : Z ^ (k + j + 1) = 0 := Nat.find_spec hex
  have hjn : Z ^ (k + j) ≠ 0 := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0]; simpa using hk
    · have := Nat.find_min hex (show j - 1 < j by omega)
      have e : k + (j - 1) + 1 = k + j := by omega
      rwa [e] at this
  obtain ⟨c, hc⟩ : ∃ c, (Z ^ (k + j)) c ≠ 0 := by
    by_contra! h
    exact hjn (LinearMap.ext h)
  refine ⟨(Z ^ j) c, ?_, ?_⟩
  · rw [← Module.End.mul_apply, ← pow_add]; exact hc
  · rw [← Module.End.mul_apply, ← pow_add, show k + 1 + j = k + j + 1 by ring, hjs]; rfl

theorem exists_W {Z : Module.End K V} {n : ℕ} (hn : Z ^ n = 0) (hZ0 : Z ≠ 0) :
    ∃ a, a ≠ 0 ∧ Z a = 0 ∧ a ∈ LinearMap.range Z := by
  obtain ⟨u, hu, hu'⟩ := exists_vec_pow hn 1 (by simpa using hZ0)
  refine ⟨Z u, by simpa using hu, ?_, ⟨u, rfl⟩⟩
  simpa [pow_succ] using hu'

section Uniq
variable [FiniteDimensional K V]

theorem exists_dual_vec (hnd : (polarBilin Q).Nondegenerate) {a b : V}
    (hab : ∀ c : K, c • a ≠ b) : ∃ y, polar Q y a = 0 ∧ polar Q y b = 1 := by
  have hb : b ∉ Submodule.span K {a} := by
    rw [Submodule.mem_span_singleton]; exact fun ⟨c, hc⟩ => hab c hc
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hb inferInstance
  have hfa : f a = 0 := by
    have : f a ∈ Submodule.map f (Submodule.span K {a}) :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self a)
    rw [hmap] at this; simpa using this
  set y₀ := (LinearMap.BilinForm.toDual (polarBilin Q) hnd).symm f with hy₀
  have hy : ∀ z, polar Q y₀ z = f z := fun z => by
    have := LinearMap.BilinForm.toDual_def hnd (m := y₀) (n := z)
    rw [hy₀, LinearEquiv.apply_symm_apply] at this
    rw [this]; rfl
  refine ⟨(f b)⁻¹ • y₀, ?_, ?_⟩
  · rw [polar_smul_left, hy, hfa]; simp
  · rw [polar_smul_left, hy, smul_eq_mul, inv_mul_cancel₀ hf]

theorem exists_polar_ne (hnd : (polarBilin Q).Nondegenerate) {a : V} (ha : a ≠ 0) :
    ∃ x, polar Q x a ≠ 0 := by
  by_contra! h
  apply ha
  refine hnd.1 a fun y => ?_
  have := h y
  rw [polar_comm] at this
  simpa using this

section Eig
variable {A : Module.End K V} {μ : K}

theorem eigen_of_comm_P (hnd : (polarBilin Q).Nondegenerate) (hμ : μ ≠ 0)
    (hsim : ∀ x y, polar Q (A x) (A y) = μ * polar Q x y) {a : V} (ha : a ≠ 0) {c : K} (hc : c ≠ 0)
    (hP : ∀ x, (c * polar Q x a) • A a = (c * polar Q (A x) a) • a) :
    ∃ l : K, l ≠ 0 ∧ A a = l • a ∧ μ = l ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := exists_polar_ne hnd ha
  set u := polar Q x₀ a with hu
  set p := polar Q (A x₀) a with hp
  have h1 : (c * u) • A a = (c * p) • a := hP x₀
  have hcu : c * u ≠ 0 := mul_ne_zero hc hx₀
  have hAa : A a = (p / u) • a := by
    have : A a = (c * u)⁻¹ • ((c * p) • a) := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hcu, one_smul]
    rw [this, smul_smul]
    congr 1
    field_simp
  set l := p / u with hl
  have hpl : p = l * u := by rw [hl]; field_simp
  have hs := hsim x₀ a
  rw [hAa, polar_smul_right, smul_eq_mul] at hs
  have hμl : μ = l ^ 2 := by
    apply mul_right_cancel₀ hx₀
    rw [← hu] at *
    calc μ * u = l * p := hs.symm
      _ = l ^ 2 * u := by rw [hpl]; ring
  refine ⟨l, ?_, hAa, hμl⟩
  intro hl0
  exact hμ (by rw [hμl, hl0]; ring)

theorem polar_A_left (hμ : μ ≠ 0) (hsim : ∀ x y, polar Q (A x) (A y) = μ * polar Q x y) {a : V}
    {l : K} (hl : l ≠ 0) (hAa : A a = l • a) (x : V) : polar Q (A x) a = l⁻¹ * μ * polar Q x a := by
  have := hsim x a
  rw [hAa, polar_smul_right, smul_eq_mul] at this
  field_simp
  linear_combination this

theorem eigen_b (hnd : (polarBilin Q).Nondegenerate) (hμ : μ ≠ 0)
    (hsim : ∀ x y, polar Q (A x) (A y) = μ * polar Q x y) {a b : V} (ha : a ≠ 0) {l : K}
    (hl : l ≠ 0) (hAa : A a = l • a) (hab : ∀ c : K, c • a ≠ b)
    (hX : ∀ x, A (polar Q x a • b - polar Q x b • a) = polar Q (A x) a • b - polar Q (A x) b • a) :
    ∃ t : K, A b = (l⁻¹ * μ) • b + t • a := by
  have hba : ∀ c : K, c • b ≠ a := by
    intro c hc
    have hc0 : c ≠ 0 := by rintro rfl; exact ha (by simpa using hc.symm)
    exact hab c⁻¹ (by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
  obtain ⟨y, hy1, hy2⟩ := exists_dual_vec hnd hba
  have h := hX y
  rw [hy2, hy1] at h
  rw [polar_A_left hμ hsim hl hAa y, hy2] at h
  refine ⟨- polar Q (A y) b, ?_⟩
  simpa [sub_eq_add_neg] using h

theorem eigen_of_type2 (hnd : (polarBilin Q).Nondegenerate) (hμ : μ ≠ 0)
    (hsim : ∀ x y, polar Q (A x) (A y) = μ * polar Q x y) {Z : Module.End K V} (hAZ : A * Z = Z * A)
    {a b : V} (ha : a ≠ 0) (haZ : Z a = 0) (hbZ : Z b = a)
    (hX : ∀ x, A (polar Q x a • b - polar Q x b • a) = polar Q (A x) a • b - polar Q (A x) b • a) :
    ∃ l : K, l ≠ 0 ∧ A a = l • a ∧ μ = l ^ 2 := by
  have hAZ' : ∀ x, A (Z x) = Z (A x) := fun x => by
    have := congrArg (fun f => f x) hAZ
    simpa using this
  have hab : ∀ c : K, c • a ≠ b := by
    intro c hc
    have : Z b = 0 := by rw [← hc, map_smul, haZ, smul_zero]
    exact ha (by rw [← hbZ, this])
  have hba : ∀ c : K, c • b ≠ a := by
    intro c hc
    have hc0 : c ≠ 0 := by rintro rfl; exact ha (by simpa using hc.symm)
    exact hab c⁻¹ (by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
  obtain ⟨y, hy1, hy2⟩ := exists_dual_vec hnd hab
  have h := hX y
  rw [hy1, hy2] at h
  have hZa : Z (A a) = 0 := by rw [← hAZ', haZ, map_zero]
  have h' := congrArg Z h
  simp only [zero_smul, one_smul, zero_sub, map_neg, hZa, neg_zero, map_sub, map_smul, hbZ, haZ,
    smul_zero, sub_zero] at h'
  have hp1 : polar Q (A y) a = 0 := by
    have : polar Q (A y) a • a = 0 := by rw [← h']
    exact (smul_eq_zero.1 this).resolve_right ha
  set l := polar Q (A y) b with hl
  have hAa : A a = l • a := by
    have h' : -(A a) = -(l • a) := by simpa [hp1, map_neg, sub_eq_add_neg] using h
    exact neg_inj.1 h'
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hAa
    obtain ⟨x, hx⟩ := exists_polar_ne hnd ha
    have := hsim x a
    rw [hAa, polar_zero_right] at this
    exact mul_ne_zero hμ hx (by rw [← this])
  obtain ⟨y', hy1', hy2'⟩ := exists_dual_vec hnd hba
  have h2 := hX y'
  rw [hy2', hy1'] at h2
  rw [polar_A_left hμ hsim hl0 hAa y', hy2'] at h2
  have h3 := congrArg Z h2
  have h4 : Z (A b) = A a := by rw [← hbZ, ← hAZ']
  simp only [one_smul, zero_smul, sub_zero, map_sub, map_smul, hbZ, haZ, smul_zero] at h3
  rw [h4, hAa] at h3
  have h5 : (l⁻¹ * μ * 1) • a = l • a := by
    simpa using h3.symm
  have h6 : l⁻¹ * μ * 1 = l := smul_left_injective K ha h5
  refine ⟨l, hl0, hAa, ?_⟩
  field_simp at h6
  exact h6

theorem line_pair (hnd : (polarBilin Q).Nondegenerate) {a c : V} (hac : ∀ s : K, s • a ≠ c)
    (hX : ∀ x, A (polar Q x a • c - polar Q x c • a) = polar Q (A x) a • c - polar Q (A x) c • a) :
    ∃ α β : K, A a = α • c + β • a := by
  obtain ⟨y, hy1, hy2⟩ := exists_dual_vec hnd hac
  have h := hX y
  rw [hy1, hy2] at h
  refine ⟨- polar Q (A y) a, polar Q (A y) c, ?_⟩
  have h' : -(A a) = polar Q (A y) a • c + -(polar Q (A y) c • a) := by
    simpa [map_neg, sub_eq_add_neg] using h
  calc A a = -(-(A a)) := (neg_neg _).symm
    _ = (- polar Q (A y) a) • c + polar Q (A y) c • a := by rw [h']; module

theorem eigen_of_two_partners (hnd : (polarBilin Q).Nondegenerate) {a c₁ c₂ : V}
    (h1 : c₁ ∉ Submodule.span K {a}) (h2 : c₂ ∉ Submodule.span K {a, c₁})
    (hX₁ : ∀ x, A (polar Q x a • c₁ - polar Q x c₁ • a) = polar Q (A x) a • c₁ - polar Q (A x) c₁ • a)
    (hX₂ : ∀ x, A (polar Q x a • c₂ - polar Q x c₂ • a) = polar Q (A x) a • c₂ - polar Q (A x) c₂ • a) :
    ∃ l : K, A a = l • a := by
  have hac₁ : ∀ s : K, s • a ≠ c₁ := fun s hs => h1 (hs ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a))
  have hac₂ : ∀ s : K, s • a ≠ c₂ := fun s hs => h2 (hs ▸ Submodule.smul_mem _ _
    (Submodule.subset_span (by simp)))
  obtain ⟨α₁, β₁, e₁⟩ := line_pair hnd hac₁ hX₁
  obtain ⟨α₂, β₂, e₂⟩ := line_pair hnd hac₂ hX₂
  have e : α₂ • c₂ = α₁ • c₁ + (β₁ - β₂) • a := by
    rw [e₁] at e₂
    have : α₁ • c₁ + β₁ • a = α₂ • c₂ + β₂ • a := e₂
    calc α₂ • c₂ = (α₁ • c₁ + β₁ • a) - β₂ • a := by rw [this]; abel
      _ = _ := by module
  have hα₂ : α₂ = 0 := by
    by_contra hne
    apply h2
    have : c₂ = α₂⁻¹ • (α₁ • c₁ + (β₁ - β₂) • a) := by
      rw [← e, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ ?_))
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  have hα₁ : α₁ = 0 := by
    by_contra hne
    apply h1
    rw [hα₂, zero_smul] at e
    have : c₁ = α₁⁻¹ • ((β₂ - β₁) • a) := by
      have e' : α₁ • c₁ = (β₂ - β₁) • a := by
        have : α₁ • c₁ + (β₁ - β₂) • a = 0 := by rw [← e]
        have h3 : α₁ • c₁ = -((β₁ - β₂) • a) := eq_neg_of_add_eq_zero_left this
        rw [h3, ← neg_smul, neg_sub]
      rw [← e', smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a))
  exact ⟨β₁, by rw [e₁, hα₁, zero_smul, zero_add]⟩

end Eig

theorem mem_range_of_orth (hnd : (polarBilin Q).Nondegenerate) {Z : Module.End K V}
    (hZ : IsSkew (Q := Q) Z) {b : V} (hb : ∀ k, Z k = 0 → polar Q b k = 0) :
    b ∈ LinearMap.range Z := by
  by_contra hnot
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hfZ : ∀ x, f (Z x) = 0 := fun x => by
    have : f (Z x) ∈ Submodule.map f (LinearMap.range Z) :=
      Submodule.mem_map_of_mem ⟨x, rfl⟩
    rw [hmap] at this; simpa using this
  set y := (LinearMap.BilinForm.toDual (polarBilin Q) hnd).symm f with hy₀
  have hy : ∀ z, polar Q y z = f z := fun z => by
    have := LinearMap.BilinForm.toDual_def hnd (m := y) (n := z)
    rw [hy₀, LinearEquiv.apply_symm_apply] at this
    rw [this]; rfl
  have hZy : Z y = 0 := by
    refine hnd.1 (Z y) fun x => ?_
    have := hZ y x
    rw [hy] at this
    have h2 : polar Q (Z y) x = 0 := by rw [this, hfZ]; simp
    simpa using h2
  apply hf
  rw [← hy, polar_comm]
  exact hb y hZy

theorem exists_partners (W : Submodule K V) (hW : 3 ≤ Module.finrank K W) {a : V} (haW : a ∈ W)
    (ha : a ≠ 0) :
    ∃ c₁ ∈ W, ∃ c₂ ∈ W, c₁ ∉ Submodule.span K {a} ∧ c₂ ∉ Submodule.span K {a, c₁} := by
  have h1 : ∃ c₁ ∈ W, c₁ ∉ Submodule.span K {a} := by
    by_contra! h
    have : W ≤ Submodule.span K {a} := h
    have := Submodule.finrank_mono this
    rw [finrank_span_singleton ha] at this
    omega
  obtain ⟨c₁, hc₁, hc₁'⟩ := h1
  have h2 : ∃ c₂ ∈ W, c₂ ∉ Submodule.span K {a, c₁} := by
    by_contra! h
    have : W ≤ Submodule.span K {a, c₁} := h
    have h3 := Submodule.finrank_mono this
    classical
    have h4 := finrank_span_finset_le_card (R := K) ({a, c₁} : Finset V)
    have h5 : ({a, c₁} : Finset V).card ≤ 2 := Finset.card_le_two
    have h6 : Submodule.span K (↑({a, c₁} : Finset V) : Set V) = Submodule.span K {a, c₁} := by
      simp
    have h7 : Module.finrank K (Submodule.span K (↑({a, c₁} : Finset V) : Set V)) ≤ 2 :=
      h4.trans h5
    rw [h6] at h7
    omega
  obtain ⟨c₂, hc₂, hc₂'⟩ := h2
  exact ⟨c₁, hc₁, c₂, hc₂, hc₁', hc₂'⟩

theorem exists_common_eigen {A : Module.End K V} (W : Submodule K V)
    (h : ∀ a ∈ W, a ≠ 0 → ∃ l : K, A a = l • a) {a₀ : V} (ha₀ : a₀ ∈ W) (hne : a₀ ≠ 0) :
    ∃ l : K, ∀ a ∈ W, A a = l • a := by
  obtain ⟨l₀, hl₀⟩ := h a₀ ha₀ hne
  refine ⟨l₀, fun a haW => ?_⟩
  by_cases hdep : ∃ c : K, a = c • a₀
  · obtain ⟨c, rfl⟩ := hdep
    rw [map_smul, hl₀, smul_comm]
  · push Not at hdep
    have hane : a ≠ 0 := fun h0 => hdep 0 (by simp [h0])
    obtain ⟨l₁, hl₁⟩ := h a haW hane
    have hsum : a + a₀ ≠ 0 := by
      intro h0
      exact hdep (-1) (by rw [neg_one_smul]; exact eq_neg_of_add_eq_zero_left h0)
    obtain ⟨l₂, hl₂⟩ := h (a + a₀) (Submodule.add_mem _ haW ha₀) hsum
    rw [map_add, hl₁, hl₀, smul_add] at hl₂
    have h3 : (l₂ - l₁) • a = (l₀ - l₂) • a₀ := by
      calc (l₂ - l₁) • a = l₂ • a - l₁ • a := sub_smul _ _ _
        _ = l₀ • a₀ - l₂ • a₀ := by
          rw [sub_eq_sub_iff_add_eq_add, add_comm (l₀ • a₀)]
          exact hl₂.symm
        _ = (l₀ - l₂) • a₀ := (sub_smul _ _ _).symm
    have h4 : l₂ - l₁ = 0 := by
      by_contra hne'
      apply hdep (((l₂ - l₁)⁻¹ * (l₀ - l₂)))
      rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hne', one_smul]
    have h5 : l₂ = l₁ := sub_eq_zero.1 h4
    have h6 : (l₀ - l₂) • a₀ = 0 := by rw [← h3, h4, zero_smul]
    have h7 : l₀ - l₂ = 0 := (smul_eq_zero.1 h6).resolve_right hne
    rw [hl₁, ← h5, ← sub_eq_zero.1 h7]

theorem eigen_ne_zero (hnd : (polarBilin Q).Nondegenerate) {A : Module.End K V} {μ : K}
    (hμ : μ ≠ 0) (hsim : ∀ x y, polar Q (A x) (A y) = μ * polar Q x y) {a : V} (ha : a ≠ 0)
    {l : K} (hAa : A a = l • a) : l ≠ 0 := by
  rintro rfl
  rw [zero_smul] at hAa
  obtain ⟨x, hx⟩ := exists_polar_ne hnd ha
  have := hsim x a
  rw [hAa, polar_zero_right] at this
  exact mul_ne_zero hμ hx (by rw [← this])

theorem exists_nilpotent_sub_smul (h2 : (2 : K) ≠ 0) (hnd : (polarBilin Q).Nondegenerate)
    {Z : Module.End K V} (hZ : IsSkew (Q := Q) Z) {n : ℕ} (hn : Z ^ n = 0) (hZ0 : Z ≠ 0)
    (hd : 5 ≤ Module.finrank K V) {A : Module.End K V} {μ : K} (hμ : μ ≠ 0)
    (hsim : ∀ x y, polar Q (A x) (A y) = μ * polar Q x y) (hAZ : A * Z = Z * A)
    (h₁ : ∀ a b, Z a = 0 → a ∈ LinearMap.range Z → Z b = 0 →
      A * eich Q a b = eich Q a b * A)
    (h₂ : ∀ a b (c : K), Z a = 0 → a ∈ LinearMap.range Z → Z b = c • a →
      (∀ w, Z w = 0 → w ∈ LinearMap.range Z → polar Q w b = 0) →
      A * eich Q a b = eich Q a b * A) :
    ∃ l : K, IsNilpotent (A - l • (1 : Module.End K V)) := by
  have hX₁ : ∀ a b, Z a = 0 → a ∈ LinearMap.range Z → Z b = 0 → ∀ x,
      A (polar Q x a • b - polar Q x b • a) = polar Q (A x) a • b - polar Q (A x) b • a := by
    intro a b ha ha' hb x
    exact comm_X h2 (h₁ a b ha ha' hb) (h₁ a (-b) ha ha' (by rw [map_neg, hb, neg_zero])) x
  obtain ⟨a₀, ha₀, ha₀Z, ha₀R⟩ := exists_W hn hZ0
  have key : ∃ a₀ : V, a₀ ≠ 0 ∧ Z a₀ = 0 ∧ a₀ ∈ LinearMap.range Z ∧
      ∃ l : K, l ≠ 0 ∧ A a₀ = l • a₀ ∧ μ = l ^ 2 := by
    by_cases hA : ∃ b₀, Z b₀ = 0 ∧ Q b₀ ≠ 0
    · obtain ⟨b₀, hb₀, hQ⟩ := hA
      refine ⟨a₀, ha₀, ha₀Z, ha₀R, ?_⟩
      have hP := comm_P h2 (h₁ a₀ b₀ ha₀Z ha₀R hb₀)
        (h₁ a₀ (-b₀) ha₀Z ha₀R (by rw [map_neg, hb₀, neg_zero]))
      obtain ⟨l, hl, hAa, hμl⟩ := eigen_of_comm_P hnd hμ hsim ha₀ hQ hP
      exact ⟨l, hl, hAa, hμl⟩
    · push Not at hA
      by_cases hZ2 : Z ^ 2 = 0
      ·
        have hZZ : ∀ x, Z (Z x) = 0 := fun x => by
          have := congrArg (fun f => f x) hZ2
          simpa [pow_two] using this
        have hKR : ∀ b, Z b = 0 → b ∈ LinearMap.range Z := by
          intro b hb
          refine mem_range_of_orth hnd hZ fun k hk => ?_
          have h3 : polar Q b k = Q (b + k) - Q b - Q k := rfl
          rw [h3, hA (b + k) (by rw [map_add, hb, hk, add_zero]), hA b hb, hA k hk]; simp
        have hRK : ∀ b, b ∈ LinearMap.range Z → Z b = 0 := by
          rintro b ⟨x, rfl⟩; exact hZZ x
        have hker : LinearMap.ker Z = LinearMap.range Z := by
          ext b; simp only [LinearMap.mem_ker]
          exact ⟨hKR b, hRK b⟩
        have hrn := LinearMap.finrank_range_add_finrank_ker Z
        rw [← hker] at hrn
        have hr3 : 3 ≤ Module.finrank K (LinearMap.ker Z) := by omega
        have eig : ∀ a ∈ LinearMap.ker Z, a ≠ 0 → ∃ l : K, A a = l • a := by
          intro a ha hane
          have haZ : Z a = 0 := ha
          obtain ⟨c₁, hc₁, c₂, hc₂, h1, h2'⟩ := exists_partners (LinearMap.ker Z) hr3 ha hane
          exact eigen_of_two_partners hnd h1 h2' (hX₁ a c₁ haZ (hKR a haZ) hc₁)
            (hX₁ a c₂ haZ (hKR a haZ) hc₂)
        obtain ⟨l, hl⟩ := exists_common_eigen (LinearMap.ker Z) eig (a₀ := a₀) ha₀Z ha₀
        have hAa : A a₀ = l • a₀ := hl a₀ ha₀Z
        have hl0 : l ≠ 0 := eigen_ne_zero hnd hμ hsim ha₀ hAa
        obtain ⟨c₁, hc₁, c₂, hc₂, h1, -⟩ := exists_partners (LinearMap.ker Z) hr3 ha₀Z ha₀
        have hab : ∀ c : K, c • a₀ ≠ c₁ := fun c hc =>
          h1 (hc ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a₀))
        obtain ⟨t, ht⟩ := eigen_b hnd hμ hsim ha₀ hl0 hAa hab (hX₁ a₀ c₁ ha₀Z ha₀R hc₁)
        have hAc : A c₁ = l • c₁ := hl c₁ hc₁
        have hμl : μ = l ^ 2 := by
          by_contra hne
          apply h1
          have h3 : (l - l⁻¹ * μ) • c₁ = t • a₀ := by
            rw [sub_smul, ← hAc, ht]; abel
          have hne' : l - l⁻¹ * μ ≠ 0 := by
            intro h0
            apply hne
            field_simp at h0
            linear_combination -h0
          have : c₁ = (l - l⁻¹ * μ)⁻¹ • (t • a₀) := by
            rw [← h3, smul_smul, inv_mul_cancel₀ hne', one_smul]
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a₀))
        exact ⟨a₀, ha₀, ha₀Z, ha₀R, l, hl0, hAa, hμl⟩
      ·
        obtain ⟨u, hu, hu'⟩ := exists_vec_pow hn 2 hZ2
        have e2 : (Z ^ 2) u = Z (Z u) := by rw [pow_two]; rfl
        have e3 : (Z ^ (2 + 1)) u = Z (Z (Z u)) := by rw [pow_succ, pow_two]; rfl
        rw [e3] at hu'
        rw [e2] at hu
        have haZ : Z (Z (Z u)) = 0 := hu'
        have hbW : ∀ w, Z w = 0 → w ∈ LinearMap.range Z → polar Q w (Z u) = 0 := by
          intro w hw _
          have := hZ w u
          rw [hw, polar_zero_left] at this
          simpa using this.symm
        have hE₁ := h₂ (Z (Z u)) (Z u) 1 haZ ⟨Z u, rfl⟩ (by rw [one_smul]) hbW
        have hE₂ := h₂ (Z (Z u)) (-(Z u)) (-1) haZ ⟨Z u, rfl⟩
          (by rw [map_neg, neg_smul, one_smul]) (fun w hw hw' => by rw [polar_neg_right, hbW w hw hw', neg_zero])
        have hX := comm_X h2 hE₁ hE₂
        obtain ⟨l, hl, hAa, hμl⟩ := eigen_of_type2 hnd hμ hsim hAZ hu haZ rfl hX
        exact ⟨Z (Z u), hu, haZ, ⟨Z u, rfl⟩, l, hl, hAa, hμl⟩
  obtain ⟨a₀, ha₀, ha₀Z, ha₀R, l, hl, hAa, hμl⟩ := key
  refine ⟨l, ?_⟩
  have hBZ : (A - l • (1 : Module.End K V)) * Z = Z * (A - l • (1 : Module.End K V)) := by
    rw [sub_mul, mul_sub, hAZ]; simp
  refine isNilpotent_of_ker hn hBZ fun x hx => ?_
  have hBa : (A - l • (1 : Module.End K V)) a₀ = 0 := by simp [hAa]
  by_cases hdep : ∃ c : K, c • a₀ = x
  · obtain ⟨c, rfl⟩ := hdep
    simp [hAa, map_smul]
  · push Not at hdep
    obtain ⟨t, ht⟩ := eigen_b hnd hμ hsim ha₀ hl hAa hdep (hX₁ a₀ x ha₀Z ha₀R hx)
    have : l⁻¹ * μ = l := by rw [hμl]; field_simp
    rw [this] at ht
    have hBx : (A - l • (1 : Module.End K V)) x = t • a₀ := by simp [ht]
    rw [hBx, map_smul, hBa, smul_zero]

end Uniq

section Semi
variable {σ : K →+* K} {Φ : V →+ V}

@[expose] def CommWith (Φ : V →+ V) (f : Module.End K V) : Prop := ∀ v, Φ (f v) = f (Φ v)

theorem CommWith.one : CommWith Φ (1 : Module.End K V) := fun v => rfl

theorem CommWith.add {f g : Module.End K V} (hf : CommWith Φ f) (hg : CommWith Φ g) :
    CommWith Φ (f + g) := fun v => by
  simp [map_add, hf v, hg v]

theorem CommWith.mul {f g : Module.End K V} (hf : CommWith Φ f) (hg : CommWith Φ g) :
    CommWith Φ (f * g) := fun v => by
  simp only [Module.End.mul_apply]; rw [hf, hg]

theorem CommWith.sub {f g : Module.End K V} (hf : CommWith Φ f) (hg : CommWith Φ g) :
    CommWith Φ (f - g) := fun v => by
  simp [map_sub, hf v, hg v]

theorem CommWith.pow {f : Module.End K V} (hf : CommWith Φ f) (k : ℕ) : CommWith Φ (f ^ k) := by
  induction k with
  | zero => simpa using CommWith.one
  | succ k ih => rw [pow_succ]; exact ih.mul hf

theorem CommWith.sum {ι : Type*} (s : Finset ι) {f : ι → Module.End K V}
    (hf : ∀ i ∈ s, CommWith Φ (f i)) : CommWith Φ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro v; simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (by simp)).add (ih fun j hj => hf j (by simp [hj]))

theorem CommWith.smul_fixed (hΦ : ∀ c v, Φ (c • v) = σ c • Φ v) {f : Module.End K V}
    (hf : CommWith Φ f) {c : K} (hc : σ c = c) : CommWith Φ (c • f) := fun v => by
  simp [hΦ, hc, hf v]

theorem commWith_zOf (hΦ : ∀ c v, Φ (c • v) = σ c • Φ v) {p : ℕ} {G : Module.End K V}
    (hG : CommWith Φ G) : CommWith Φ (zOf p G) := by
  have h2 : σ (2 : K)⁻¹ = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
  have hm1 : σ (-1 : K) = (-1 : K) := by rw [map_neg, map_one]
  unfold zOf invS
  refine (hG.sub CommWith.one).mul ?_
  refine CommWith.smul_fixed hΦ (CommWith.sum _ fun i _ => ?_) h2
  exact (CommWith.smul_fixed hΦ hG hm1).pow i

theorem phi_smul_pow (hΦ : ∀ c v, Φ (c • v) = σ c • Φ v) {Z : Module.End K V} (hZ : CommWith Φ Z)
    (t : K) (i : ℕ) (v : V) : Φ (((t • Z) ^ i) v) = (((σ t) • Z) ^ i) (Φ v) := by
  induction i generalizing v with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, pow_succ (σ t • Z), Module.End.mul_apply, Module.End.mul_apply, ih]
    simp only [LinearMap.smul_apply, hΦ, hZ v]

theorem phi_cay (hΦ : ∀ c v, Φ (c • v) = σ c • Φ v) {Z : Module.End K V} (hZ : CommWith Φ Z)
    (n : ℕ) (t : K) (v : V) : Φ (cay Z n t v) = cay Z n (σ t) (Φ v) := by
  unfold cay
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, map_add,
    LinearMap.smul_apply, hΦ, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hZ, phi_smul_pow hΦ hZ t x v]

theorem sigma_eq_self (h2 : (2 : K) ≠ 0) {p : ℕ} [Fact p.Prime] [CharP (Module.End K V) p]
    (hp : Odd p) {G : Module.End K V} (hG : G ^ p = 1) (hG1 : G ≠ 1)
    (hΦ : ∀ c v, Φ (c • v) = σ c • Φ v) (hsurj : Function.Surjective Φ)
    (hcomm : ∀ t v, Φ (cay (zOf p G) p t v) = cay (zOf p G) p t (Φ v)) (t : K) : σ t = t := by
  have hn : zOf p G ^ p = 0 := zOf_pow hG
  have hGc : CommWith Φ G := fun v => by
    have := hcomm 1 v
    rwa [cay_zOf h2 hp hG] at this
  have hZc := commWith_zOf hΦ (p := p) hGc
  have h1 : cay (zOf p G) p (σ t) = cay (zOf p G) p t := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := hsurj w
    rw [← phi_cay hΦ hZc, hcomm]
  have h3 := cay_inj h2 hn h1
  have hne := zOf_ne_zero h2 hp hG hG1
  have : σ t - t = 0 := by
    by_contra hne'
    apply hne
    have := congrArg (fun f => (σ t - t)⁻¹ • f) h3
    simpa [smul_smul, inv_mul_cancel₀ hne'] using this
  exact sub_eq_zero.1 this

end Semi

end Orth

namespace Orth

section Model

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Matrix

variable {K : Type} [Field K] {d : ℕ}

@[expose] noncomputable def toE (A : GL (Fin d) K) : Module.End K (Fin d → K) :=
  (matrixLinearEquiv A : (Fin d → K) →ₗ[K] (Fin d → K))

theorem toE_apply (A : GL (Fin d) K) (v : Fin d → K) : toE A v = A.val *ᵥ v := rfl

theorem toE_mul (A B : GL (Fin d) K) : toE (A * B) = toE A * toE B := by
  ext v
  simp [toE, matrixLinearEquiv_mul]

theorem toE_one : toE (1 : GL (Fin d) K) = 1 := by
  refine LinearMap.ext fun v => ?_
  rw [toE_apply]; simp

theorem toE_injective : Function.Injective (toE : GL (Fin d) K → Module.End K (Fin d → K)) := by
  intro A B h
  have : matrixLinearEquiv A = matrixLinearEquiv B := LinearEquiv.ext fun v => by
    have := congrArg (fun f => f v) h
    exact this
  exact matrixLinearIso.injective this

theorem toE_inv_mul (A : GL (Fin d) K) : toE A⁻¹ * toE A = 1 := by
  rw [← toE_mul, inv_mul_cancel, toE_one]

theorem toE_mul_inv (A : GL (Fin d) K) : toE A * toE A⁻¹ = 1 := by
  rw [← toE_mul, mul_inv_cancel, toE_one]

theorem toE_scalar (c : Kˣ) : toE (GeneralLinearGroup.scalar (Fin d) c) = (c : K) • 1 := by
  refine LinearMap.ext fun v => ?_
  rw [toE_apply]
  simp [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal, smul_mulVec]

@[expose] noncomputable def glOfEnd (f f' : Module.End K (Fin d → K)) (h1 : f * f' = 1) (h2 : f' * f = 1) :
    GL (Fin d) K :=
  matrixLinearIso.symm (LinearEquiv.ofLinearMap f f' (by exact h1) (by exact h2))

theorem toE_glOfEnd (f f' : Module.End K (Fin d → K)) (h1 : f * f' = 1) (h2 : f' * f = 1) :
    toE (glOfEnd f f' h1 h2) = f := by
  refine LinearMap.ext fun v => ?_
  have : matrixLinearIso (glOfEnd f f' h1 h2) = LinearEquiv.ofLinearMap f f' (by exact h1) (by exact h2) :=
    matrixLinearIso.apply_symm_apply _
  have h := congrArg (fun e => e v) this
  exact h

theorem mem_matrixIsometries_iff' (Q : QuadraticForm K (Fin d → K)) (A : GL (Fin d) K) :
    A ∈ matrixIsometries Q ↔ ∀ v, Q (toE A v) = Q v := mem_matrixIsometries_iff Q A

theorem mem_matrixDerivedScalars_iff' (Q : QuadraticForm K (Fin d → K)) (A : matrixDerived Q) :
    A ∈ matrixDerivedScalars Q ↔ ∃ c : Kˣ, A.val = GeneralLinearGroup.scalar (Fin d) c := by
  rw [mem_matrixDerivedScalars_iff]
  exact exists_congr fun c => eq_comm

theorem proj_eq_iff (Q : QuadraticForm K (Fin d → K)) (a b : matrixDerived Q) :
    matrixProjectiveProjection Q a = matrixProjectiveProjection Q b ↔
      ∃ c : Kˣ, b.val = a.val * GeneralLinearGroup.scalar (Fin d) c := by
  change (QuotientGroup.mk a : matrixDerived Q ⧸ matrixDerivedScalars Q) = QuotientGroup.mk b ↔ _
  rw [QuotientGroup.eq, mem_matrixDerivedScalars_iff']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have : (a⁻¹ * b).val = a.val⁻¹ * b.val := rfl
    rw [this] at hc
    rw [← hc]; group
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    show a.val⁻¹ * b.val = _
    rw [hc]; group

theorem toE_pow (A : GL (Fin d) K) (n : ℕ) : toE (A ^ n) = toE A ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, toE_one]
  | succ n ih => rw [pow_succ, pow_succ, toE_mul, ih]

theorem mem_matrixDerived_of_pow_eq_one {Q : QuadraticForm K (Fin d → K)} {p k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    {A : GL (Fin d) K} (hA : A ∈ matrixIsometries Q) (hk : A ^ p ^ k = 1) :
    A ∈ matrixDerived Q := by
  obtain ⟨m, hm⟩ := hab
  set a : matrixIsometries Q := ⟨A, hA⟩ with ha
  have hak : a ^ p ^ k = 1 := Subtype.ext (by simpa using hk)
  have h1 : (Abelianization.of a) ^ p ^ k = 1 := by rw [← map_pow, hak, map_one]
  have h2 : orderOf (Abelianization.of a) ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (Abelianization.of a) ∣ 2 ^ m := hm ▸ orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) (2 ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).2 hp2)
  have h4 : orderOf (Abelianization.of a) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h3
  have h5 : Abelianization.of a = 1 := orderOf_eq_one_iff.1 h4
  have h6 : a ∈ commutator (matrixIsometries Q) := (QuotientGroup.eq_one_iff a).1 h5
  rw [matrixDerived_eq_map_commutator]
  exact ⟨a, h6, rfl⟩

section End

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem isNilpotent_smul_one_iff' [Nontrivial V] {c : K} :
    IsNilpotent (c • (1 : Module.End K V)) ↔ c = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h2 : (c • (1 : Module.End K V)) ^ k = (c ^ k) • (1 : Module.End K V) := by
      rw [smul_pow, one_pow]
    rw [h2] at hk
    have h3 := congrArg (fun f => f v) hk
    simp only [LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply] at h3
    have h4 : c ^ k = 0 := (smul_eq_zero.1 h3).resolve_right hv
    exact pow_eq_zero_iff'.1 h4 |>.1
  · rintro rfl
    exact ⟨1, by simp⟩

theorem eq_one_of_smul_one_add_nilpotent' [Nontrivial V] {z y : Module.End K V} {ζ : K}
    (hz : IsNilpotent z) (hy : IsNilpotent y) (h : ζ • (1 + z) = 1 + y) : ζ = 1 := by
  have hy' : y = (ζ - 1) • (1 : Module.End K V) + ζ • z := by
    have : y = ζ • (1 + z) - 1 := by rw [h]; abel
    rw [this, smul_add, sub_smul, one_smul]; abel
  have hc : Commute y (ζ • z) := by
    rw [hy']
    refine Commute.add_left ?_ (Commute.refl _)
    exact (Commute.one_left _).smul_left _
  have hn : IsNilpotent (y - ζ • z) := hc.isNilpotent_sub hy (hz.smul ζ)
  have : y - ζ • z = (ζ - 1) • (1 : Module.End K V) := by rw [hy']; abel
  rw [this, isNilpotent_smul_one_iff'] at hn
  exact sub_eq_zero.1 hn

theorem isNilpotent_conj_end {A A' X : Module.End K V} (h : A * A' = 1) (h' : A' * A = 1)
    (hX : IsNilpotent X) : IsNilpotent (A * X * A') := by
  obtain ⟨m, hm⟩ := hX
  refine ⟨m, ?_⟩
  have : ∀ k : ℕ, (A * X * A') ^ k = A * X ^ k * A' := by
    intro k
    induction k with
    | zero => simp [h]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      calc A * X ^ k * A' * (A * X * A') = A * X ^ k * (A' * A) * X * A' := by
            simp only [mul_assoc]
        _ = A * (X ^ k * X) * A' := by rw [h', mul_one]; simp only [mul_assoc]
  rw [this, hm]; simp

end End

theorem exists_lift {Q : QuadraticForm K (Fin d → K)} (hQ : ∃ v, Q v ≠ 0) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (g : matrixProjectiveDerived Q) (hg : orderOf g = p) :
    ∃ (s0 : matrixDerived Q) (c : K), c * c = 1 ∧ g = matrixProjectiveProjection Q s0 ∧
      (c • toE s0.val) ^ p = 1 ∧ c • toE s0.val ≠ 1 := by
  obtain ⟨s0, rfl⟩ := matrixProjectiveProjection_surjective Q g
  have hpow : matrixProjectiveProjection Q (s0 ^ p) = 1 := by
    rw [map_pow, ← hg]; exact pow_orderOf_eq_one _
  have hmem : s0 ^ p ∈ matrixDerivedScalars Q := by
    change (QuotientGroup.mk (s0 ^ p) : matrixDerived Q ⧸ matrixDerivedScalars Q) = 1 at hpow
    exact (QuotientGroup.eq_one_iff _).1 hpow
  obtain ⟨c0, hc0⟩ := (mem_matrixDerivedScalars_iff' Q _).1 hmem
  have hiso : ∀ A : matrixDerived Q, ∀ v, Q (toE A.val v) = Q v := fun A =>
    (mem_matrixIsometries_iff' Q A.val).1 (matrixDerived_le_isometries Q A.2)
  have hE : toE s0.val ^ p = (c0 : K) • 1 := by
    rw [← toE_pow]
    have : s0.val ^ p = (s0 ^ p).val := by simp
    rw [this, hc0, toE_scalar]
  obtain ⟨v, hv⟩ := hQ
  have hcc : (c0 : K) * c0 = 1 := by
    have h1 := hiso (s0 ^ p) v
    have : toE (s0 ^ p).val = (c0 : K) • 1 := by rw [hc0, toE_scalar]
    rw [this] at h1
    simp only [LinearMap.smul_apply, Module.End.one_apply, QuadraticMap.map_smul, smul_eq_mul] at h1
    have h2 : ((c0 : K) * c0 - 1) * Q v = 0 := by linear_combination h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hv)
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  refine ⟨s0, c0, hcc, rfl, ?_, ?_⟩
  · rw [smul_pow, hE, smul_smul]
    obtain ⟨k, hk⟩ := hodd
    have : (c0 : K) ^ p * c0 = 1 := by
      rw [← pow_succ, hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, pow_two, hcc, one_pow]
    rw [this, one_smul]
  · intro h1
    have h2 : toE s0.val = (c0 : K) • 1 := by
      have : toE s0.val = (c0 : K) • ((c0 : K) • toE s0.val) := by
        rw [smul_smul, hcc, one_smul]
      rw [this, h1]
    have h3 : toE s0.val = toE (GeneralLinearGroup.scalar (Fin d) c0) := by rw [toE_scalar, h2]
    have h4 := toE_injective h3
    have : s0 ∈ matrixDerivedScalars Q := (mem_matrixDerivedScalars_iff' Q s0).2 ⟨c0, h4⟩
    have h5 : matrixProjectiveProjection Q s0 = 1 := by
      change (QuotientGroup.mk s0 : matrixDerived Q ⧸ matrixDerivedScalars Q) = 1
      exact (QuotientGroup.eq_one_iff _).2 this
    rw [h5, orderOf_one] at hg
    exact (Fact.out : p.Prime).one_lt.ne hg

end Model

end Orth

section Framework

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type*} [Group G] [Finite G]

theorem gLAPPrimeCoreOf_eq_bot_of_framework_pp (hZ : Subgroup.center G = ⊥) {p : ℕ} (hp : p.Prime)
    (g : G) (Gen T : Set G)
    (h1 : ∀ q ∈ Gen ∪ T, g * q = q * g)
    (hT : ∀ s q, s * g = g * s → q ∈ T → s * q = q * s)
    (hGen : ∀ s q, s * g = g * s → q ∈ Gen → s * q * s⁻¹ ∈ Gen)
    (hp3 : ∀ q ∈ Gen, ∀ q' ∈ Gen, ∃ k : ℕ, (q' * q⁻¹) ^ p ^ k = 1)
    (huniq : ∀ α : MulAut G, (orderOf α).Coprime p → (∀ q ∈ Gen ∪ T, α q = q) → α = 1)
    (H : Subgroup (MulAut G)) (hH : innerAut G ≤ H) (x : MulAut G) (hx : x = MulAut.conj g) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut G))) = ⊥ := by
  have hinj := conj_injective_of_center_eq_bot hZ
  set X := H ⊓ Subgroup.centralizer ({x} : Set (MulAut G)) with hX
  have hmemX : ∀ q ∈ Gen ∪ T, (MulAut.conj q : MulAut G) ∈ X := by
    intro q hq
    refine ⟨hH ⟨q, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [hx, ← map_mul, ← map_mul, h1 q hq]
  have hcop : ∀ d ∈ GLAPPrimeCoreOf p X, (orderOf d).Coprime p := fun d hd =>
    CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf hp hd
  have stageA : ∀ s : G, (MulAut.conj s : MulAut G) ∈ GLAPPrimeCoreOf p X →
      (MulAut.conj s : MulAut G) = 1 := by
    intro s hs
    have hsX : (MulAut.conj s : MulAut G) ∈ X := by
      obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 hs
      rw [← hy]; exact y.2
    have hsg : s * g = g * s := by
      have h := (Subgroup.mem_centralizer_singleton_iff.1 hsX.2)
      rw [hx, ← map_mul, ← map_mul] at h
      exact hinj h
    have hfix : ∀ q ∈ Gen, s * q = q * s := by
      intro q hq
      have hq' : s * q * s⁻¹ ∈ Gen := hGen s q hsg hq
      have hcq := hmemX q (Or.inl hq)
      have h2 : (MulAut.conj q : MulAut G) * (MulAut.conj s)⁻¹ * (MulAut.conj q)⁻¹ ∈
          GLAPPrimeCoreOf p X := by
        have := conj_mem_gLAPPrimeCoreOf (inv_mem hs) hcq
        simpa [mul_assoc] using this
      have h3 := mul_mem hs h2
      have he : (MulAut.conj s : MulAut G) * ((MulAut.conj q : MulAut G) *
          (MulAut.conj s)⁻¹ * (MulAut.conj q)⁻¹) = MulAut.conj ((s * q * s⁻¹) * q⁻¹) := by
        simp only [map_mul, map_inv, mul_assoc]
      rw [he] at h3
      have hord := hcop _ h3
      obtain ⟨k, hk⟩ := hp3 q hq _ hq'
      have hpow : ((MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G)) ^ p ^ k = 1 := by
        rw [← map_pow, hk, map_one]
      have hdvd : orderOf (MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G) ∣ p ^ k :=
        orderOf_dvd_of_pow_eq_one hpow
      have h1' : orderOf (MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hord) hdvd
      have h4 : (MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G) = 1 := orderOf_eq_one_iff.1 h1'
      have h5 : (s * q * s⁻¹) * q⁻¹ = 1 := hinj (by rw [h4, map_one])
      have h6 : s * q * s⁻¹ = q := by simpa [mul_inv_eq_one] using h5
      rw [mul_inv_eq_iff_eq_mul] at h6
      exact h6
    refine huniq _ (hcop _ hs) ?_
    rintro q (hq | hq)
    · simp [MulAut.conj_apply, hfix q hq]
    · simp [MulAut.conj_apply, hT s q hsg hq]
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  refine huniq α (hcop α hα) ?_
  intro q hq
  have hcq := hmemX q hq
  have h2 : (MulAut.conj q : MulAut G) * α⁻¹ * (MulAut.conj q)⁻¹ ∈ GLAPPrimeCoreOf p X := by
    have := conj_mem_gLAPPrimeCoreOf (inv_mem hα) hcq
    simpa [mul_assoc] using this
  have h3 := mul_mem hα h2
  have he : α * ((MulAut.conj q : MulAut G) * α⁻¹ * (MulAut.conj q)⁻¹) =
      MulAut.conj (α q * q⁻¹) := by
    have := mul_conj_mul_inv_eq α q
    rw [map_mul, map_inv, ← this]
    group
  rw [he] at h3
  have h4 := stageA _ h3
  have h5 : α q * q⁻¹ = 1 := hinj (by rw [h4, map_one])
  simpa [mul_inv_eq_one] using h5

end Framework

namespace Orth

section FlagMore

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Z : Module.End K V}

theorem InFlag.inv_of_mul {f f' : Module.End K V} (hf : InFlag Z f) (h1 : f * f' = 1)
    (h2 : f' * f = 1) : InFlag Z f' := by
  obtain ⟨f0, f2, f3⟩ := hf
  have happ1 : ∀ y, f (f' y) = y := fun y => by
    simpa [Module.End.mul_apply] using LinearMap.congr_fun h1 y
  have happ2 : ∀ y, f' (f y) = y := fun y => by
    simpa [Module.End.mul_apply] using LinearMap.congr_fun h2 y
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have h : Z x = f (Z (f' x)) := by rw [f0, happ1]
    rw [h, happ2]
  · have hw := f2 x hx
    have hfw := f3 _ hw
    have hh : f (x - (f x - x)) = x := by rw [map_sub, hfw]; abel
    have : f' x - x = -(f x - x) := by
      calc f' x - x = f' (f (x - (f x - x))) - x := by rw [hh]
        _ = (x - (f x - x)) - x := by rw [happ2]
        _ = -(f x - x) := by abel
    rw [this]
    exact Submodule.neg_mem _ hw
  · have := f3 x hx
    calc f' x = f' (f x) := by rw [this]
      _ = x := happ2 x

theorem InFlag.conj {f t t' : Module.End K V} (hf : InFlag Z f) (htZ : t * Z = Z * t)
    (h1 : t * t' = 1) (h2 : t' * t = 1) : InFlag Z (t * f * t') := by
  obtain ⟨f0, f2, f3⟩ := hf
  have happ1 : ∀ y, t (t' y) = y := fun y => by
    simpa [Module.End.mul_apply] using LinearMap.congr_fun h1 y
  have happ2 : ∀ y, t' (t y) = y := fun y => by
    simpa [Module.End.mul_apply] using LinearMap.congr_fun h2 y
  have htz : ∀ y, t (Z y) = Z (t y) := fun y => by
    simpa [Module.End.mul_apply] using LinearMap.congr_fun htZ y
  have ht'z : ∀ y, t' (Z y) = Z (t' y) := fun y => by
    have h : Z y = t (Z (t' y)) := by rw [htz, happ1]
    rw [h, happ2]
  have hker : ∀ y, Z y = 0 → Z (t' y) = 0 := fun y hy => by rw [← ht'z, hy, map_zero]
  have hW : ∀ w ∈ LinearMap.ker Z ⊓ LinearMap.range Z, t w ∈ LinearMap.ker Z ⊓ LinearMap.range Z := by
    rintro w ⟨hw1, ⟨y, rfl⟩⟩
    refine ⟨?_, ⟨t y, (htz y).symm⟩⟩
    show Z (t (Z y)) = 0
    have h' : Z (Z y) = 0 := hw1
    rw [← htz, h', map_zero]
  have hW' : ∀ w ∈ LinearMap.ker Z ⊓ LinearMap.range Z, t' w ∈ LinearMap.ker Z ⊓ LinearMap.range Z := by
    rintro w ⟨hw1, ⟨y, rfl⟩⟩
    refine ⟨?_, ⟨t' y, (ht'z y).symm⟩⟩
    show Z (t' (Z y)) = 0
    have h' : Z (Z y) = 0 := hw1
    rw [← ht'z, h', map_zero]
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · show t (f (t' (Z x))) = Z (t (f (t' x)))
    rw [ht'z, f0, htz]
  · have hx' : Z x = 0 := hx
    have h3 := f2 (t' x) (hker x hx')
    have h4 := hW _ h3
    have : (t * f * t') x - x = t (f (t' x) - t' x) := by
      rw [map_sub, happ1]; rfl
    rw [this]; exact h4
  · have h3 := hW' x hx
    have := f3 _ h3
    show t (f (t' x)) = x
    rw [this, happ1]

end FlagMore

section EichMore

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eich_pow_apply {a b : V} (ha : Q a = 0) (hab : polar Q a b = 0) (n : ℕ) (x : V) :
    ((eich Q a b) ^ n) x = eich Q a ((n : K) • b) x := by
  induction n generalizing x with
  | zero => simp [eich_zero_right]
  | succ n ih =>
    have hn : polar Q a ((n : K) • b) = 0 := by rw [polar_smul_right, hab, smul_zero]
    rw [pow_succ', Module.End.mul_apply, ih, eich_comp a b ((n : K) • b) ha hab hn]
    congr 2
    rw [Nat.cast_succ, add_smul, one_smul, add_comm]

end EichMore

end Orth

namespace Orth

section ModelGrp

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Matrix

variable {K : Type} [Field K] {d : ℕ} [NeZero d] {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  [Fact p.Prime] [CharP K p]

instance charP_end_pi : CharP (Module.End K (Fin d → K)) p :=
  charP_of_injective_algebraMap (algebraMap K (Module.End K (Fin d → K))).injective p

theorem polar_toE_of_mem {A : GL (Fin d) K} (hA : A ∈ matrixIsometries Q) (x y : Fin d → K) :
    polar Q (toE A x) (toE A y) = polar Q x y := by
  have h := (mem_matrixIsometries_iff' Q A).1 hA
  have h1 : polar Q (toE A x) (toE A y) = Q (toE A x + toE A y) - Q (toE A x) - Q (toE A y) := rfl
  have h2 : polar Q x y = Q (x + y) - Q x - Q y := rfl
  rw [h1, h2, ← map_add, h, h, h]

theorem exists_eich_mem (hp2 : p ≠ 2)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m) {a b : Fin d → K}
    (ha : Q a = 0) (hab' : polar Q a b = 0) : ∃ f : matrixDerived Q, toE f.val = eich Q a b := by
  have hba : polar Q a (-b) = 0 := by rw [polar_neg_right, hab', neg_zero]
  have h1 : eich Q a b * eich Q a (-b) = 1 := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, eich_comp a b (-b) ha hab' hba x, add_neg_cancel, eich_zero_right]
    rfl
  have h2 : eich Q a (-b) * eich Q a b = 1 := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, eich_comp a (-b) b ha hba hab' x, neg_add_cancel, eich_zero_right]
    rfl
  set A : GL (Fin d) K := glOfEnd (eich Q a b) (eich Q a (-b)) h1 h2 with hA
  have hAE : toE A = eich Q a b := toE_glOfEnd _ _ h1 h2
  have hiso : A ∈ matrixIsometries Q := (mem_matrixIsometries_iff' Q A).2 fun v => by
    rw [hAE]; exact map_eich a b ha hab' v
  have hpow : A ^ p ^ 1 = 1 := by
    apply toE_injective
    rw [toE_pow, hAE, toE_one, pow_one]
    refine LinearMap.ext fun x => ?_
    rw [eich_pow_apply ha hab' p x, CharP.cast_eq_zero, zero_smul, eich_zero_right]
    rfl
  exact ⟨⟨A, mem_matrixDerived_of_pow_eq_one hp2 hab hiso hpow⟩, hAE⟩

theorem exists_cay_mem (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    {Z : Module.End K (Fin d → K)} (hZ : IsSkew (Q := Q) Z) (hn : Z ^ p = 0) (t : K) :
    ∃ f : matrixDerived Q, toE f.val = cay Z p t := by
  have h1 := cay_neg_mul hn t
  have h2' : cay Z p (-t) * cay Z p t = 1 := by
    have := cay_neg_mul hn (-t); rwa [neg_neg] at this
  set A : GL (Fin d) K := glOfEnd (cay Z p t) (cay Z p (-t)) h1 h2' with hA
  have hAE : toE A = cay Z p t := toE_glOfEnd _ _ h1 h2'
  have hiso : A ∈ matrixIsometries Q := by
    rw [mem_matrixIsometries_iff']
    intro v
    rw [hAE]
    have h := polar_cay hZ hn t v v
    rw [polar_self, polar_self, two_nsmul, two_nsmul] at h
    have h' : (2 : K) * Q (cay Z p t v) = 2 * Q v := by rw [two_mul, two_mul]; exact h
    exact mul_left_cancel₀ h2 h'
  obtain ⟨m, hm⟩ := isNilpotent_cay_sub_one hn t
  obtain ⟨e, he⟩ := exists_pow_prime_pow_ge (p := p) (m := m) (Fact.out : p.Prime).one_lt
  have hpow : A ^ p ^ e = 1 := by
    apply toE_injective
    rw [toE_pow, hAE, toE_one]
    exact pow_prime_pow_eq_one hm he
  exact ⟨⟨A, mem_matrixDerived_of_pow_eq_one hp2 hab hiso hpow⟩, hAE⟩

@[expose] noncomputable def gEnd (s0 : matrixDerived Q) (c : K) : Module.End K (Fin d → K) := c • toE s0.val

@[expose] noncomputable def zEnd (p : ℕ) (s0 : matrixDerived Q) (c : K) : Module.End K (Fin d → K) :=
  zOf p (gEnd s0 c)

variable (Q) in
@[expose] noncomputable def genSet (p : ℕ) (s0 : matrixDerived Q) (c : K) : Set (matrixProjectiveDerived Q) :=
  {q | ∃ f : matrixDerived Q, InFlag (zEnd p s0 c) (toE f.val) ∧
    q = matrixProjectiveProjection Q f}

variable (Q) in
@[expose] noncomputable def tSet (p : ℕ) (s0 : matrixDerived Q) (c : K) : Set (matrixProjectiveDerived Q) :=
  {q | ∃ (f : matrixDerived Q) (t : K), toE f.val = cay (zEnd p s0 c) p t ∧
    q = matrixProjectiveProjection Q f}

theorem gEnd_iso (s0 : matrixDerived Q) {c : K} (hcc : c * c = 1) (x y : Fin d → K) :
    polar Q (gEnd s0 c x) (gEnd s0 c y) = polar Q x y := by
  have := polar_toE_of_mem (matrixDerived_le_isometries Q s0.2) x y
  simp only [gEnd, LinearMap.smul_apply, polar_smul_left, polar_smul_right, smul_eq_mul]
  rw [this, ← mul_assoc, hcc, one_mul]

theorem gEnd_nilpotent (s0 : matrixDerived Q) {c : K} (hG : gEnd s0 c ^ p = 1) :
    IsNilpotent (gEnd s0 c - 1) :=
  ⟨p, by rw [sub_pow_char_of_commute p (Commute.one_right _), hG]; simp⟩

theorem zEnd_pow (s0 : matrixDerived Q) {c : K} (hG : gEnd s0 c ^ p = 1) :
    zEnd p s0 c ^ p = 0 := zOf_pow hG

theorem zEnd_skew (s0 : matrixDerived Q) {c : K} (h2 : (2 : K) ≠ 0) (hp : Odd p)
    (hG : gEnd s0 c ^ p = 1) (hcc : c * c = 1) : IsSkew (Q := Q) (zEnd p s0 c) :=
  isSkew_zOf h2 hp hG (gEnd_iso s0 hcc)

theorem cay_zEnd_one (s0 : matrixDerived Q) {c : K} (h2 : (2 : K) ≠ 0) (hp : Odd p)
    (hG : gEnd s0 c ^ p = 1) : cay (zEnd p s0 c) p 1 = gEnd s0 c := cay_zOf h2 hp hG

theorem comm_g_of_comm_z (s0 : matrixDerived Q) {c : K} (h2 : (2 : K) ≠ 0) (hp : Odd p)
    (hG : gEnd s0 c ^ p = 1) {f : Module.End K (Fin d → K)}
    (hf : f * zEnd p s0 c = zEnd p s0 c * f) : f * gEnd s0 c = gEnd s0 c * f := by
  have := cay_comm (n := p) hf (1 : K)
  rwa [cay_zEnd_one s0 h2 hp hG] at this

theorem comm_z_of_comm_g (s0 : matrixDerived Q) {c : K} {f : Module.End K (Fin d → K)}
    (hf : f * gEnd s0 c = gEnd s0 c * f) : f * zEnd p s0 c = zEnd p s0 c * f :=
  commute_zOf hf

theorem comm_g_cay (s0 : matrixDerived Q) {c : K} (t : K) (hG : gEnd s0 c ^ p = 1) :
    cay (zEnd p s0 c) p t * gEnd s0 c = gEnd s0 c * cay (zEnd p s0 c) p t := by
  have h : gEnd s0 c * zEnd p s0 c = zEnd p s0 c * gEnd s0 c :=
    commute_zOf (p := p) (G := gEnd s0 c) (s := gEnd s0 c) rfl
  exact (cay_comm h t).symm

end ModelGrp

end Orth

namespace Orth

section ModelGrp2

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Matrix

variable {K : Type} [Field K] {d : ℕ} [NeZero d] {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  [Fact p.Prime] [CharP K p] {s0 : matrixDerived Q} {c : K}

theorem flag_comm_z {V : Type*} [AddCommGroup V] [Module K V] {Z f : Module.End K V}
    (hf : InFlag Z f) : f * Z = Z * f := LinearMap.ext fun x => hf.1 x

theorem commute_proj_iff (hcc : c * c = 1) (hG : gEnd s0 c ^ p = 1) (t : matrixDerived Q) :
    matrixProjectiveProjection Q t * matrixProjectiveProjection Q s0 =
        matrixProjectiveProjection Q s0 * matrixProjectiveProjection Q t ↔
      toE t.val * gEnd s0 c = gEnd s0 c * toE t.val := by
  have hc0 : c ≠ 0 := fun h => by rw [h, mul_zero] at hcc; exact zero_ne_one hcc
  constructor
  · intro h
    rw [← map_mul, ← map_mul] at h
    obtain ⟨c', hc'⟩ := (proj_eq_iff Q _ _).1 h
    have h1 : toE s0.val * toE t.val = (c' : K) • (toE t.val * toE s0.val) := by
      have := congrArg toE hc'
      have e1 : ((s0 * t : matrixDerived Q) : GL (Fin d) K) = s0.val * t.val := rfl
      have e2 : ((t * s0 : matrixDerived Q) : GL (Fin d) K) = t.val * s0.val := rfl
      rw [e1, e2, toE_mul, toE_mul, toE_mul, toE_scalar] at this
      rw [this, mul_smul_comm, mul_one]
    have hEE : toE t.val * toE (t.val⁻¹) = 1 := toE_mul_inv t.val
    have hEE' : toE (t.val⁻¹) * toE t.val = 1 := toE_inv_mul t.val
    have h3 : gEnd s0 c * toE t.val = (c' : K) • (toE t.val * gEnd s0 c) := by
      unfold gEnd
      calc (c • toE s0.val) * toE t.val = c • (toE s0.val * toE t.val) := smul_mul_assoc _ _ _
        _ = c • ((c' : K) • (toE t.val * toE s0.val)) := by rw [h1]
        _ = (c' : K) • (toE t.val * (c • toE s0.val)) := by rw [smul_comm, mul_smul_comm]
    have h4 : toE (t.val⁻¹) * gEnd s0 c * toE t.val = (c' : K) • gEnd s0 c := by
      calc toE (t.val⁻¹) * gEnd s0 c * toE t.val
          = toE (t.val⁻¹) * (gEnd s0 c * toE t.val) := by rw [mul_assoc]
        _ = toE (t.val⁻¹) * ((c' : K) • (toE t.val * gEnd s0 c)) := by rw [h3]
        _ = (c' : K) • (toE (t.val⁻¹) * toE t.val * gEnd s0 c) := by
            rw [mul_smul_comm, ← mul_assoc]
        _ = (c' : K) • gEnd s0 c := by rw [hEE', one_mul]
    have hN := gEnd_nilpotent s0 hG
    have hy := isNilpotent_conj_end hEE' hEE hN
    have h5 : (c' : K) • (1 + (gEnd s0 c - 1)) =
        1 + toE (t.val⁻¹) * (gEnd s0 c - 1) * toE t.val := by
      have e : (1 + (gEnd s0 c - 1)) = gEnd s0 c := by abel
      have e' : toE (t.val⁻¹) * (gEnd s0 c - 1) * toE t.val =
          toE (t.val⁻¹) * gEnd s0 c * toE t.val - 1 := by
        rw [mul_sub, sub_mul, mul_one, hEE']
      rw [e, ← h4, e']; abel
    have hc1 : (c' : K) = 1 := eq_one_of_smul_one_add_nilpotent' hN hy h5
    rw [hc1, one_smul] at h3
    exact h3.symm
  · intro h
    have h1 : toE t.val * toE s0.val = toE s0.val * toE t.val := by
      have : c • (toE t.val * toE s0.val) = c • (toE s0.val * toE t.val) := by
        simpa [gEnd, mul_smul_comm, smul_mul_assoc] using h
      exact smul_right_injective _ hc0 this
    have h2 : t.val * s0.val = s0.val * t.val := toE_injective (by rw [toE_mul, toE_mul, h1])
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h2

end ModelGrp2

end Orth

namespace Orth

section ModelGrp3

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Matrix

variable {K : Type} [Field K] {d : ℕ} [NeZero d] {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  [Fact p.Prime] [CharP K p] {s0 : matrixDerived Q} {c : K}

theorem genSet_commute (h2 : (2 : K) ≠ 0) (hp : Odd p) (hcc : c * c = 1)
    (hG : gEnd s0 c ^ p = 1) {q : matrixProjectiveDerived Q} (hq : q ∈ genSet Q p s0 c) :
    matrixProjectiveProjection Q s0 * q = q * matrixProjectiveProjection Q s0 := by
  obtain ⟨f, hf, rfl⟩ := hq
  exact ((commute_proj_iff hcc hG f).2
    (comm_g_of_comm_z s0 h2 hp hG (flag_comm_z hf))).symm

theorem tSet_commute (hcc : c * c = 1) (hG : gEnd s0 c ^ p = 1)
    {q : matrixProjectiveDerived Q} (hq : q ∈ tSet Q p s0 c) :
    matrixProjectiveProjection Q s0 * q = q * matrixProjectiveProjection Q s0 := by
  obtain ⟨f, t, hf, rfl⟩ := hq
  refine ((commute_proj_iff hcc hG f).2 ?_).symm
  rw [hf]
  exact comm_g_cay s0 t hG

theorem tSet_central (hcc : c * c = 1) (hG : gEnd s0 c ^ p = 1) {s q : matrixProjectiveDerived Q}
    (hs : s * matrixProjectiveProjection Q s0 = matrixProjectiveProjection Q s0 * s)
    (hq : q ∈ tSet Q p s0 c) : s * q = q * s := by
  obtain ⟨t, rfl⟩ := matrixProjectiveProjection_surjective Q s
  obtain ⟨f, t', hf, rfl⟩ := hq
  have h1 := (commute_proj_iff hcc hG t).1 hs
  have h2 : toE t.val * zEnd p s0 c = zEnd p s0 c * toE t.val := comm_z_of_comm_g s0 h1
  have h3 : toE t.val * toE f.val = toE f.val * toE t.val := by
    rw [hf]; exact cay_comm h2 t'
  have h4 : t.val * f.val = f.val * t.val := toE_injective (by rw [toE_mul, toE_mul, h3])
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h4

theorem genSet_conj (hcc : c * c = 1) (hG : gEnd s0 c ^ p = 1) {s q : matrixProjectiveDerived Q}
    (hs : s * matrixProjectiveProjection Q s0 = matrixProjectiveProjection Q s0 * s)
    (hq : q ∈ genSet Q p s0 c) : s * q * s⁻¹ ∈ genSet Q p s0 c := by
  obtain ⟨t, rfl⟩ := matrixProjectiveProjection_surjective Q s
  obtain ⟨f, hf, rfl⟩ := hq
  have h1 := (commute_proj_iff hcc hG t).1 hs
  have h2 : toE t.val * zEnd p s0 c = zEnd p s0 c * toE t.val := comm_z_of_comm_g s0 h1
  refine ⟨t * f * t⁻¹, ?_, by simp⟩
  have e : toE ((t * f * t⁻¹ : matrixDerived Q).val) =
      toE t.val * toE f.val * toE (t.val⁻¹) := by
    show toE (t.val * f.val * t.val⁻¹) = _
    rw [toE_mul, toE_mul]
  rw [e]
  exact InFlag.conj hf h2 (toE_mul_inv t.val) (toE_inv_mul t.val)

theorem genSet_pow (h2 : (2 : K) ≠ 0) (hp : Odd p) (hcc : c * c = 1) (hG : gEnd s0 c ^ p = 1)
    {q q' : matrixProjectiveDerived Q} (hq : q ∈ genSet Q p s0 c) (hq' : q' ∈ genSet Q p s0 c) :
    ∃ k : ℕ, (q' * q⁻¹) ^ p ^ k = 1 := by
  obtain ⟨f, hf, rfl⟩ := hq
  obtain ⟨f', hf', rfl⟩ := hq'
  have hfi : InFlag (zEnd p s0 c) (toE (f⁻¹ : matrixDerived Q).val) :=
    InFlag.inv_of_mul hf (toE_mul_inv f.val) (toE_inv_mul f.val)
  set X : Module.End K (Fin d → K) := toE f'.val * toE (f⁻¹ : matrixDerived Q).val with hX
  have hXf : InFlag (zEnd p s0 c) X := InFlag.mul hf' hfi
  have hnil : IsNilpotent (X - 1) := by
    refine isNilpotent_of_ker (Z := zEnd p s0 c) (n := p) (zEnd_pow s0 hG) ?_ ?_
    · have := flag_comm_z hXf
      rw [sub_mul, mul_sub, this]; simp
    · intro x hx
      exact InFlag.sq_apply hXf hx
  obtain ⟨m, hm⟩ := hnil
  obtain ⟨e, he⟩ := exists_pow_prime_pow_ge (p := p) (m := m) (Fact.out : p.Prime).one_lt
  refine ⟨e, ?_⟩
  have h1 : X ^ p ^ e = 1 := pow_prime_pow_eq_one hm he
  rw [← map_inv, ← map_mul, ← map_pow]
  have h2 : (f' * f⁻¹) ^ p ^ e = 1 := by
    apply Subtype.ext
    apply toE_injective
    have : (((f' * f⁻¹) ^ p ^ e : matrixDerived Q) : GL (Fin d) K) =
        ((f' * f⁻¹ : matrixDerived Q) : GL (Fin d) K) ^ p ^ e := rfl
    have e1 : toE ((f' * f⁻¹ : matrixDerived Q) : GL (Fin d) K) = X := toE_mul _ _
    have e2 : toE ((1 : matrixDerived Q) : GL (Fin d) K) = 1 := toE_one
    rw [this, toE_pow, e1, e2]; exact h1
  rw [h2, map_one]

end ModelGrp3

end Orth

namespace Orth

section Semi2

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem semilin_conj_nilpotent {Φ : V ≃+ V} {z Y : Module.End K V} (hz : IsNilpotent z)
    (hY : ∀ v, Y v = Φ (z (Φ.symm v))) : IsNilpotent Y := by
  obtain ⟨m, hm⟩ := hz
  have key : ∀ k : ℕ, ∀ v, (Y ^ k) v = Φ ((z ^ k) (Φ.symm v)) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, ih, hY, AddEquiv.symm_apply_apply, pow_succ',
        Module.End.mul_apply]
  refine ⟨m, LinearMap.ext fun v => ?_⟩
  rw [key, hm]; simp

end Semi2

section Uniq2

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Matrix

variable {K : Type} [Field K] {d : ℕ} [NeZero d] {Q : QuadraticForm K (Fin d → K)}

theorem comm_of_fix {gp : similarityPairs Q} {f : matrixDerived Q} {c0 : K}
    (hc0 : gp.val.right c0 = c0) (hnil : IsNilpotent (c0 • toE f.val - 1))
    (hfix : matrixProjectiveConjugation Q gp (matrixProjectiveProjection Q f) =
      matrixProjectiveProjection Q f) :
    CommWith (coordinateSemilinearMap gp.val).toAddMonoidHom (toE f.val) := by
  set Φ := coordinateSemilinearMap gp.val with hΦdef
  have hconj : ∀ v, toE (matrixDerivedConjugation Q gp f).val v = Φ (toE f.val (Φ.symm v)) :=
    fun v => matrixConjugation_vector gp.val f.val v
  rw [matrixProjectiveConjugation_mk] at hfix
  obtain ⟨c1, hc1⟩ := (proj_eq_iff Q _ _).1 hfix.symm
  have hE : toE (matrixDerivedConjugation Q gp f).val = (c1 : K) • toE f.val := by
    rw [hc1, toE_mul, toE_scalar, mul_smul_comm, mul_one]
  have hrel : ∀ v, Φ (toE f.val (Φ.symm v)) = (c1 : K) • toE f.val v := fun v => by
    rw [← hconj, hE]; rfl
  set Y : Module.End K (Fin d → K) := (c1 : K) • (c0 • toE f.val) - 1 with hY
  have hYv : ∀ v, Y v = Φ ((c0 • toE f.val - 1) (Φ.symm v)) := by
    intro v
    have e1 : Φ ((c0 • toE f.val - 1) (Φ.symm v)) =
        Φ (c0 • toE f.val (Φ.symm v)) - v := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        AddEquiv.apply_symm_apply]
    have e2 : Φ (c0 • toE f.val (Φ.symm v)) = c0 • Φ (toE f.val (Φ.symm v)) := by
      have := coordinateSemilinearMap_smul gp.val c0 (toE f.val (Φ.symm v))
      rw [hc0] at this
      exact this
    rw [e1, e2, hrel, hY]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [smul_comm]
  have hYn : IsNilpotent Y := semilin_conj_nilpotent hnil hYv
  have h1 : (c1 : K) • (1 + (c0 • toE f.val - 1)) = 1 + Y := by
    rw [hY]
    have : (1 + (c0 • toE f.val - 1)) = c0 • toE f.val := by abel
    rw [this]; abel
  have hc11 : (c1 : K) = 1 := eq_one_of_smul_one_add_nilpotent' hnil hYn h1
  intro v
  have := hrel (Φ v)
  rw [hc11, one_smul, AddEquiv.symm_apply_apply] at this
  exact this

end Uniq2

end Orth

namespace Orth

section Uniq3

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField Matrix

variable {K : Type} [Field K] {d : ℕ} [NeZero d] {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  [Fact p.Prime] [CharP K p]

theorem add_smul_one_pow_end {V : Type*} [AddCommGroup V] [Module K V]
    [CharP (Module.End K V) p] {B : Module.End K V} {m : ℕ} (hB : B ^ m = 0) (c : K) :
    ∃ e : ℕ, (c • (1 : Module.End K V) + B) ^ p ^ e = (c ^ p ^ e) • (1 : Module.End K V) := by
  obtain ⟨e, he⟩ := exists_pow_prime_pow_ge (p := p) (m := m) (Fact.out : p.Prime).one_lt
  refine ⟨e, ?_⟩
  rw [add_pow_char_pow_of_commute (R := Module.End K V) p e
    ((Commute.one_left _).smul_left c), pow_eq_zero_of_le he hB, add_zero, smul_pow, one_pow]

theorem eich_pow_eq_one {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {a b : V} (ha : Q a = 0) (hab : polar Q a b = 0) : eich Q a b ^ p = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [eich_pow_apply ha hab p x, CharP.cast_eq_zero, zero_smul, eich_zero_right]
  rfl

theorem pow_conj_eq_one {gp : similarityPairs Q} (hσ : gp.val.right = 1) (k : ℕ) (u : Kˣ)
    (hk : gp.val.left ^ k = GeneralLinearGroup.scalar (Fin d) u) :
    matrixProjectiveConjugation Q gp ^ k = 1 := by
  have hpow : ∀ n : ℕ, (gp.val ^ n).right = 1 ∧ (gp.val ^ n).left = gp.val.left ^ n := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
      constructor
      · rw [pow_succ', coordinateSemilinearGroup_mul_field, hσ, ih.1, mul_one]
      · rw [pow_succ', coordinateSemilinearGroup_mul_matrix, hσ, map_one, ih.2, pow_succ']
        rfl
  have h1 : matrixProjectiveConjugation Q gp ^ k = matrixProjectiveConjugation Q (gp ^ k) :=
    (map_pow (matrixProjectiveConjugationHom Q) gp k).symm
  rw [h1]
  refine MulEquiv.ext fun x => ?_
  obtain ⟨a, rfl⟩ := matrixProjectiveProjection_surjective Q x
  rw [matrixProjectiveConjugation_mk]
  rw [MulAut.one_apply]
  congr 1
  apply Subtype.ext
  have hv : (gp ^ k).val = gp.val ^ k := rfl
  show (gp ^ k).val.left * glFieldAut (Fin d) K (gp ^ k).val.right a.val * (gp ^ k).val.left⁻¹ =
    a.val
  rw [hv, (hpow k).1, (hpow k).2, hk, map_one]
  have hc : GeneralLinearGroup.scalar (Fin d) u ∈ Subgroup.center (GL (Fin d) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  have := Subgroup.mem_center_iff.mp hc a.val
  show GeneralLinearGroup.scalar (Fin d) u * a.val * (GeneralLinearGroup.scalar (Fin d) u)⁻¹ = a.val
  rw [← this, mul_assoc, mul_inv_cancel, mul_one]

end Uniq3

end Orth

namespace Orth

section Uniq4

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField Matrix

variable {K : Type} [Field K] {d : ℕ} [NeZero d] {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  [Fact p.Prime] [CharP K p]

theorem uniq_orth (hnd : (polarBilin Q).Nondegenerate) (hd : 5 ≤ d) (h2 : (2 : K) ≠ 0)
    (hp2 : p ≠ 2)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    {s0 : matrixDerived Q} {c : K} (hcc : c * c = 1) (hG : gEnd s0 c ^ p = 1)
    (hG1 : gEnd s0 c ≠ 1) {α : MulAut (matrixProjectiveDerived Q)}
    (hα : α ∈ matrixProjectiveImage Q) (hcop : (orderOf α).Coprime p)
    (hfixg : α (matrixProjectiveProjection Q s0) = matrixProjectiveProjection Q s0)
    (hfixG : ∀ q ∈ genSet Q p s0 c, α q = q) (hfixT : ∀ q ∈ tSet Q p s0 c, α q = q) :
    α = 1 := by
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨gp, hgp⟩ := (mem_matrixProjectiveImage_iff Q α).1 hα
  have hZ := zEnd_skew s0 h2 hp hG hcc
  have hn := zEnd_pow s0 hG
  have hZ0 : zEnd p s0 c ≠ 0 := zOf_ne_zero h2 hp hG hG1
  set Φ : (Fin d → K) →+ (Fin d → K) := (coordinateSemilinearMap gp.val).toAddMonoidHom with hΦdef
  set σ : K →+* K := (gp.val.right : K →+* K) with hσdef
  have hΦ : ∀ (a : K) (v : Fin d → K), Φ (a • v) = σ a • Φ v := fun a v =>
    coordinateSemilinearMap_smul gp.val a v
  have hsurj : Function.Surjective Φ := (coordinateSemilinearMap gp.val).surjective
  have hcommT : ∀ (t : K) (v : Fin d → K),
      Φ (cay (zOf p (gEnd s0 c)) p t v) = cay (zOf p (gEnd s0 c)) p t (Φ v) := by
    intro t v
    obtain ⟨f, hf⟩ := exists_cay_mem hp2 h2 hab hZ hn t
    have hq : matrixProjectiveProjection Q f ∈ tSet Q p s0 c := ⟨f, t, hf, rfl⟩
    have hfix := hfixT _ hq
    rw [← hgp] at hfix
    have hnil : IsNilpotent ((1 : K) • toE f.val - 1) := by
      rw [one_smul, hf]; exact isNilpotent_cay_sub_one hn t
    have := comm_of_fix (gp := gp) (f := f) (c0 := 1) (map_one _) hnil hfix v
    rw [hf] at this
    exact this
  have hσ : ∀ t, σ t = t :=
    sigma_eq_self h2 hp hG hG1 hΦ hsurj hcommT
  have hσ1 : gp.val.right = 1 := RingEquiv.ext fun t => hσ t
  have hGc : CommWith Φ (gEnd s0 c) := by
    have hfix := hfixg
    rw [← hgp] at hfix
    have hnil : IsNilpotent (c • toE s0.val - 1) := gEnd_nilpotent s0 hG
    have := comm_of_fix (gp := gp) (f := s0) (c0 := c) (hσ c) hnil hfix
    exact CommWith.smul_fixed hΦ this (hσ c)
  have hZc : CommWith Φ (zOf p (gEnd s0 c)) := commWith_zOf hΦ hGc
  let A : Module.End K (Fin d → K) :=
    { toFun := Φ
      map_add' := Φ.map_add
      map_smul' := fun a v => by
        have := hΦ a v
        rw [hσ a] at this
        exact this }
  have hAv : ∀ v, A v = Φ v := fun _ => rfl
  have hAZ : A * zEnd p s0 c = zEnd p s0 c * A := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hAv, hAv]
    exact hZc v
  set μ : K := (multiplier Q gp : K) with hμdef
  have hμ : μ ≠ 0 := (multiplier Q gp).ne_zero
  have hQA : ∀ v, Q (A v) = μ * Q v := by
    intro v
    have := multiplier_spec Q gp v
    rw [hσ1] at this
    exact this
  have hsimA : ∀ x y, polar Q (A x) (A y) = μ * polar Q x y := by
    intro x y
    have h1 : polar Q (A x) (A y) = Q (A x + A y) - Q (A x) - Q (A y) := rfl
    have h3 : polar Q x y = Q (x + y) - Q x - Q y := rfl
    rw [h1, h3, ← map_add, hQA, hQA, hQA]
    ring
  have hd' : 5 ≤ Module.finrank K (Fin d → K) := by simpa using hd
  have hcommA : ∀ f : matrixDerived Q, CommWith Φ (toE f.val) →
      A * toE f.val = toE f.val * A := by
    intro f hf
    refine LinearMap.ext fun v => ?_
    exact hf v
  have h₁ : ∀ a b, zEnd p s0 c a = 0 → a ∈ LinearMap.range (zEnd p s0 c) →
      zEnd p s0 c b = 0 → A * eich Q a b = eich Q a b * A := by
    intro a b ha ha' hb
    have hQa : Q a = 0 := Q_eq_zero_of_mem_W h2 hZ ha ha'
    have hpab : polar Q a b = 0 := polar_zero_of_ker_range' hZ hb ha'
    obtain ⟨f, hf⟩ := exists_eich_mem hp2 hab hQa hpab
    have hflag : InFlag (zEnd p s0 c) (toE f.val) := by
      rw [hf]; exact eich_inFlag hZ ha ha' hb
    have hq : matrixProjectiveProjection Q f ∈ genSet Q p s0 c := ⟨f, hflag, rfl⟩
    have hfix := hfixG _ hq
    rw [← hgp] at hfix
    have hnil : IsNilpotent ((1 : K) • toE f.val - 1) := by
      rw [one_smul, hf]
      exact ⟨p, by
        rw [sub_pow_char_of_commute p (Commute.one_right _), eich_pow_eq_one hQa hpab]; simp⟩
    have hcomm := hcommA f (comm_of_fix (gp := gp) (f := f) (c0 := 1) (map_one _) hnil hfix)
    rw [hf] at hcomm
    exact hcomm
  have h₂ : ∀ a b (cc : K), zEnd p s0 c a = 0 → a ∈ LinearMap.range (zEnd p s0 c) →
      zEnd p s0 c b = cc • a →
      (∀ w, zEnd p s0 c w = 0 → w ∈ LinearMap.range (zEnd p s0 c) → polar Q w b = 0) →
      A * eich Q a b = eich Q a b * A := by
    intro a b cc ha ha' hb hbW
    have hQa : Q a = 0 := Q_eq_zero_of_mem_W h2 hZ ha ha'
    have hpab : polar Q a b = 0 := hbW a ha ha'
    obtain ⟨f, hf⟩ := exists_eich_mem hp2 hab hQa hpab
    have hflag : InFlag (zEnd p s0 c) (toE f.val) := by
      rw [hf]; exact eich_inFlag₂ hZ ha ha' hb hbW
    have hq : matrixProjectiveProjection Q f ∈ genSet Q p s0 c := ⟨f, hflag, rfl⟩
    have hfix := hfixG _ hq
    rw [← hgp] at hfix
    have hnil : IsNilpotent ((1 : K) • toE f.val - 1) := by
      rw [one_smul, hf]
      exact ⟨p, by
        rw [sub_pow_char_of_commute p (Commute.one_right _), eich_pow_eq_one hQa hpab]; simp⟩
    have hcomm := hcommA f (comm_of_fix (gp := gp) (f := f) (c0 := 1) (map_one _) hnil hfix)
    rw [hf] at hcomm
    exact hcomm
  obtain ⟨l, hl⟩ := exists_nilpotent_sub_smul h2 hnd hZ hn hZ0 hd' hμ hsimA hAZ h₁ h₂
  obtain ⟨m, hm⟩ := hl
  obtain ⟨e, he⟩ := add_smul_one_pow_end (p := p) hm l
  have hApow : A ^ p ^ e = (l ^ p ^ e) • (1 : Module.End K (Fin d → K)) := by
    calc A ^ p ^ e = (l • (1 : Module.End K (Fin d → K)) + (A - l • 1)) ^ p ^ e := by
          congr 1; abel
      _ = _ := he
  have htoE : toE gp.val.left = A := by
    refine LinearMap.ext fun v => ?_
    rw [toE_apply, hAv]
    show _ = coordinateSemilinearMap gp.val v
    rw [coordinateSemilinearMap_apply]
    have : (fun i => gp.val.right (v i)) = v := funext fun i => by rw [hσ1]; rfl
    rw [this]
  have hl0 : l ≠ 0 := by
    intro hl0
    have h0 : toE (gp.val.left ^ p ^ e) = 0 := by
      rw [toE_pow, htoE, hApow, hl0, zero_pow (pow_pos (Fact.out : p.Prime).pos e).ne', zero_smul]
    have h1 := toE_mul_inv (gp.val.left ^ p ^ e)
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  set u : Kˣ := Units.mk0 (l ^ p ^ e) (pow_ne_zero _ hl0) with hu
  have hk : gp.val.left ^ p ^ e = GeneralLinearGroup.scalar (Fin d) u := by
    apply toE_injective
    rw [toE_pow, htoE, hApow, toE_scalar]
    rfl
  have hpow := pow_conj_eq_one hσ1 (p ^ e) u hk
  rw [hgp] at hpow
  have hdvd : orderOf α ∣ p ^ e := orderOf_dvd_of_pow_eq_one hpow
  have h1' : orderOf α = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right e hcop) hdvd
  exact orderOf_eq_one_iff.1 h1'

end Uniq4

end Orth

section ModelThm

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Orth

theorem innerCoreFree_of_orthModel {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) {d : ℕ} (hd : 5 ≤ d) (Q : QuadraticForm K (Fin d → K))
    (hnd : (polarBilin Q).Nondegenerate) (hQ : ∃ v, Q v ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    (hE : matrixProjectiveImage Q = ⊤) (e : S ≃* matrixProjectiveDerived Q) :
    ∀ x ∈ innerAut S, orderOf x = p → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  intro x hx hxo H hH
  have : NeZero d := ⟨by omega⟩
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple hS hnab
  obtain ⟨g, rfl⟩ := hx
  have hord : orderOf g = p := by
    rw [← orderOf_injective (MulAut.conj : S →* MulAut S) (conj_injective_of_center_eq_bot hZ) g]
    exact hxo
  have hord0 : orderOf (e g) = p := by rw [MulEquiv.orderOf_eq e g]; exact hord
  obtain ⟨s0, c, hcc, hg0, hG, hG1⟩ := exists_lift hQ hp2 (e g) hord0
  have hodd : Odd p := hp.odd_of_ne_two hp2
  refine gLAPPrimeCoreOf_eq_bot_of_framework_pp hZ hp g
    {q' | e q' ∈ genSet Q p s0 c} {q' | e q' ∈ tSet Q p s0 c ∨ q' = g} ?_ ?_ ?_ ?_ ?_ H hH _ rfl
  · rintro q' (hq' | hq')
    · apply e.injective
      rw [map_mul, map_mul, hg0]
      exact genSet_commute h2 hodd hcc hG hq'
    · rcases hq' with hq' | hq'
      · apply e.injective
        rw [map_mul, map_mul, hg0]
        exact tSet_commute hcc hG hq'
      · rw [hq']
  · intro s q' hs hq'
    have hs' : e s * matrixProjectiveProjection Q s0 = matrixProjectiveProjection Q s0 * e s := by
      rw [← hg0, ← map_mul, ← map_mul, hs]
    rcases hq' with hq' | hq'
    · apply e.injective
      rw [map_mul, map_mul]
      exact tSet_central hcc hG hs' hq'
    · rw [hq']; exact hs
  · intro s q' hs hq'
    have hs' : e s * matrixProjectiveProjection Q s0 = matrixProjectiveProjection Q s0 * e s := by
      rw [← hg0, ← map_mul, ← map_mul, hs]
    have := genSet_conj hcc hG hs' hq'
    show e (s * q' * s⁻¹) ∈ genSet Q p s0 c
    rw [map_mul, map_mul, map_inv]
    exact this
  · intro q' hq' q'' hq''
    obtain ⟨k, hk⟩ := genSet_pow h2 hodd hcc hG hq' hq''
    refine ⟨k, e.injective ?_⟩
    rw [map_pow, map_mul, map_inv, map_one]
    exact hk
  · intro α hα hfix
    have hcop : (orderOf (MulAut.congr e α)).Coprime p := by
      rw [MulEquiv.orderOf_eq (MulAut.congr e) α]; exact hα
    have hαg : α g = g := hfix g (Or.inr (Or.inr rfl))
    have h1 : MulAut.congr e α = 1 := by
      refine uniq_orth hnd hd h2 hp2 hab hcc hG hG1 (by rw [hE]; exact Subgroup.mem_top _) hcop
        ?_ ?_ ?_
      · rw [← hg0, MulAut.congr_apply]
        simp [hαg]
      · intro q0 hq0
        have hmem : e.symm q0 ∈ {q' | e q' ∈ genSet Q p s0 c} := by simpa using hq0
        have := hfix _ (Or.inl hmem)
        change e (α (e.symm q0)) = q0
        rw [this]; simp
      · intro q0 hq0
        have hmem : e.symm q0 ∈ {q' | e q' ∈ tSet Q p s0 c ∨ q' = g} := Or.inl (by simpa using hq0)
        have := hfix _ (Or.inr hmem)
        change e (α (e.symm q0)) = q0
        rw [this]; simp
    exact (MulAut.congr e).injective (by rw [h1, map_one])

end ModelThm

section Families

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedProj StatedOmega
  StatedQuadOdd StatedQuadPlus StatedQuadMinus)
open Matrix Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)
open CFSG.HardMathSupport.Solomon.LocalBalance

theorem innerCoreFree_POmegaOdd {T : Type} [Group T] [Finite T] (hS : IsSimpleGroup T)
    (hnab : ∃ a b : T, a * b ≠ b * a) {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaOdd n ℓ f) :
    ∀ x ∈ innerAut T, orderOf x = ℓ → ∀ H : Subgroup (MulAut T), innerAut T ≤ H →
      CFSG.Open.GLAPPrimeCoreOf ℓ (H ⊓ Subgroup.centralizer ({x} : Set (MulAut T))) = ⊥ := by
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hn : 3 ≤ n := hm.1.2.2.1
  have hℓ2 : ℓ ≠ 2 := hm.1.2.2.2
  have : Fact ℓ.Prime := ⟨hm.1.1⟩
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaOdd (.inl rfl)
    n ℓ f hm K hK (quadOdd n K) (coe_quadOdd n K) e
  have hE : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ := by
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaOdd (.inl rfl) n ℓ
      f hm) K hK e).1]
    exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T .POmegaOdd
      (.inl rfl) n ℓ f hm) K hK).2
  obtain ⟨hchar, hnd, -⟩ := coordinate_model_witness_odd hm K hK e
  have : CharP K ℓ := by
    have := ringChar.charP K
    rw [hchar] at this
    exact this
  exact innerCoreFree_of_orthModel hS hnab hℓ2 (d := 2 * n + 1) (by omega) _ hnd
    (exists_nonzero_value _ (coordinate_model_intrinsic_odd hm K hK e).1)
    (exists_two_pow_card_abelianization (oddIndexEquiv n) (quadOdd n K) hab) hE
    (coordinateOddWitnessEquiv K e)

theorem innerCoreFree_POmegaPlus {T : Type} [Group T] [Finite T] (hS : IsSimpleGroup T)
    (hnab : ∃ a b : T, a * b ≠ b * a) {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaPlus n ℓ f) (hn5 : 5 ≤ n) (hℓ2 : ℓ ≠ 2) :
    ∀ x ∈ innerAut T, orderOf x = ℓ → ∀ H : Subgroup (MulAut T), innerAut T ≤ H →
      CFSG.Open.GLAPPrimeCoreOf ℓ (H ⊓ Subgroup.centralizer ({x} : Set (MulAut T))) = ⊥ := by
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fact ℓ.Prime := ⟨hm.1.1⟩
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
    (.inr (.inl rfl)) n ℓ f hm K hK (quadPlus n K) (coe_quadPlus n K) e
  have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
    (.inr (.inl rfl)) n ℓ f hm) K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit hm hK e
  have hE : matrixProjectiveImage (coordinateQuadPlus n K) = ⊤ := by
    rw [← hEA]
    exact horbit.2.2.2.2.1 hn5
  obtain ⟨hchar, hnd, -⟩ := coordinate_model_witness_plus hm K hK e
  have : CharP K ℓ := by
    have := ringChar.charP K
    rw [hchar] at this
    exact this
  exact innerCoreFree_of_orthModel hS hnab hℓ2 (d := 2 * n) (by omega) _ hnd
    (exists_nonzero_value _ (coordinate_model_intrinsic_plus hm K hK e).1)
    (exists_two_pow_card_abelianization (plusIndexEquiv n) (quadPlus n K) hab) hE
    (coordinatePlusWitnessEquiv K e)

theorem innerCoreFree_POmegaMinus {T : Type} [Group T] [Finite T] (hS : IsSimpleGroup T)
    (hnab : ∃ a b : T, a * b ≠ b * a) {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaMinus n ℓ f) (hℓ2 : ℓ ≠ 2) :
    ∀ x ∈ innerAut T, orderOf x = ℓ → ∀ H : Subgroup (MulAut T), innerAut T ≤ H →
      CFSG.Open.GLAPPrimeCoreOf ℓ (H ⊓ Subgroup.centralizer ({x} : Set (MulAut T))) = ⊥ := by
  have hn4 : 4 ≤ n := hm.1.2.2
  have hn1 : 1 ≤ n := by omega
  have h0 := hm
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have : Fact ℓ.Prime := ⟨hm.1.1⟩
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaMinus
    (.inr (.inr rfl)) n ℓ f hm K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hE : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ := by
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaMinus
      (.inr (.inr rfl)) n ℓ f hm) hn1 K hK b c hirr e).1]
    exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T
      .POmegaMinus (.inr rfl) n ℓ f hm) hn1 K hK b c hirr).2
  obtain ⟨hchar, hnd, -⟩ := coordinate_model_witness_minus hm K hK b c hirr e
  have : CharP K ℓ := by
    have := ringChar.charP K
    rw [hchar] at this
    exact this
  exact innerCoreFree_of_orthModel hS hnab hℓ2 (d := 2 * n) (by omega) _ hnd
    (exists_nonzero_value _ (coordinate_model_intrinsic_minus hm K hK b c hirr e).1)
    (exists_two_pow_card_abelianization (minusIndexEquiv n hn1) (quadMinus n K b c) hab) hE
    (coordinateMinusWitnessEquiv K hn1 b c e)

end Families

section FamilyStatements

open CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def DefCharInnerCoreFreeFamOn (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, P idx.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p →
        ∀ x ∈ innerAut S, orderOf x = p → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
          CFSG.Open.GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥

theorem defCharInnerCoreFreeFamOn_B :
    DefCharInnerCoreFreeFamOn (fun d => ∃ (r : ℕ) (q : TauCeti.PrimePower), d = .B r q ∧ 3 ≤ r) := by
  intro S _ _ hS hnab idx hidx hSe p hp hp2 hch x hx hxo H hH
  obtain ⟨r, q, hr, hr3⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr hch
  subst hr
  obtain ⟨e⟩ := hSe
  have hpq : p = q.p := by simpa using hch.symm
  have hqp2 : q.p ≠ 2 := hpq ▸ hp2
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hqp2 hr3 e
  subst hpq
  exact innerCoreFree_POmegaOdd hS hnab hm x hx hxo H hH

theorem defCharInnerCoreFreeFamOn_D :
    DefCharInnerCoreFreeFamOn (fun d => ∃ (r : ℕ) (q : TauCeti.PrimePower), d = .D r q ∧ 5 ≤ r) := by
  intro S _ _ hS hnab idx hidx hSe p hp hp2 hch x hx hxo H hH
  obtain ⟨r, q, hr, hr5⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr hch
  subst hr
  obtain ⟨e⟩ := hSe
  have hpq : p = q.p := by simpa using hch.symm
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
  subst hpq
  exact innerCoreFree_POmegaPlus hS hnab hm hr5 hp2 x hx hxo H hH

theorem defCharInnerCoreFreeFamOn_twistedD :
    DefCharInnerCoreFreeFamOn (fun d => ∃ (r : ℕ) (q : TauCeti.PrimePower), d = .twistedD r q) := by
  intro S _ _ hS hnab idx hidx hSe p hp hp2 hch x hx hxo H hH
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr hch
  subst hr
  obtain ⟨e⟩ := hSe
  have hpq : p = q.p := by simpa using hch.symm
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
  subst hpq
  exact innerCoreFree_POmegaMinus hS hnab hm hp2 x hx hxo H hH

end FamilyStatements

section SpTwo

open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedProj StatedSp)
open CFSG.HardMathSupport.Solomon.LocalBalance

variable {r : ℕ} {K : Type} [Field K]

theorem uniq_modelC_of_gen {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K] (hp2 : p ≠ 2) [NeZero r]
    (hgen : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ (A : gsp r K) (σ : K ≃+* K),
      α = conjAut r K A * fieldAut r K σ)
    {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hN : IsNilpotent N) (hN0 : N ≠ 0)
    (sg : StatedSp r K)
    (hsg : ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + N)
    (α : MulAut (StatedProj (StatedSp r K))) (hcop : (orderOf α).Coprime p)
    (hfixg : α (proj r K sg) = proj r K sg)
    (hfix : ∀ q ∈ modelGenC r K N, α q = q) : α = 1 := by
  have hne : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, Nat.pos_of_neZero r⟩⟩
  have hs := sp_hs sg hsg
  obtain ⟨A, σ, hα⟩ := hgen α
  obtain ⟨μu, hAμ⟩ := mem_gsp.1 A.2
  set μ : K := (μu : K) with hμdef
  have hμ0 : μ ≠ 0 := μu.ne_zero
  set Am : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAm
  set Ai : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAi
  have h1 : Am * Ai = 1 := (A : GL (Fin r ⊕ Fin r) K).mul_inv
  have h2 : Ai * Am = 1 := (A : GL (Fin r ⊕ Fin r) K).inv_mul
  have hαfix : ∀ q ∈ modelGenC r K N, (conjAut r K A * fieldAut r K σ) q = q := fun q hq => by
    rw [← hα]; exact hfix q hq
  have hαg : (conjAut r K A * fieldAut r K σ) (proj r K sg) = proj r K sg := by
    rw [← hα]; exact hfixg
  obtain ⟨w0, hw0, hw0W⟩ := sp_exists_ne_zero_mem_Wm hN hN0
  have hw0k : w0 ∈ kerN N := Wm_le_kerN N hw0W
  have hpair : ∀ w ∈ Wm N, ∀ w' ∈ kerN N,
      symX (Am *ᵥ (σ ∘ w)) (Am *ᵥ (σ ∘ w')) = μ • symX w w' := by
    intro w hw w' hw'
    exact spPair_rel A σ hAμ w w' (spDot_W_J_ker hs hw hw')
      (hαfix _ ⟨w, w', spDot_W_J_ker hs hw hw', hw, hw', rfl⟩)
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this)
  have hJw0 : formJ r K *ᵥ w0 ≠ 0 := fun h => hw0 (spFormJ_mulVec_eq_zero h)
  set u : Fin r ⊕ Fin r → K := Am *ᵥ (σ ∘ w0) with hu
  have hsymuu : ∀ z : Fin r ⊕ Fin r → K,
      symX z z = (2 : K) • vecMulVec z (formJ r K *ᵥ z) := by
    intro z; rw [symX, two_smul]
  have hA2 : vecMulVec u (formJ r K *ᵥ u) = vecMulVec w0 (μ • (formJ r K *ᵥ w0)) := by
    have hA1 := hpair w0 hw0W w0 hw0k
    rw [hsymuu, hsymuu] at hA1
    have h5 : (2 : K) • vecMulVec u (formJ r K *ᵥ u) =
        (2 : K) • vecMulVec w0 (μ • (formJ r K *ᵥ w0)) := by
      rw [vecMulVec_smul, smul_comm (2 : K) μ]; exact hA1
    exact smul_right_injective _ h2K h5
  have hune : u ≠ 0 := by
    intro h0
    rw [h0, mulVec_zero, zero_vecMulVec] at hA2
    exact sp_vecMulVec_ne_zero hw0 (smul_ne_zero hμ0 hJw0) hA2.symm
  have hJune : formJ r K *ᵥ u ≠ 0 := fun h => hune (spFormJ_mulVec_eq_zero h)
  obtain ⟨c, huc, hμc⟩ := sp_rank_one_eq hw0 hJune hA2
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hune; rw [huc, zero_smul]
  have hμ : μ = c * c := by
    rw [huc, mulVec_smul, smul_smul] at hμc
    exact smul_left_injective K hJw0 hμc
  have hB : ∀ w' ∈ kerN N, Am *ᵥ (σ ∘ w') = c • w' := by
    intro w' hw'
    have h := hpair w0 hw0W w' hw'
    set u' : Fin r ⊕ Fin r → K := Am *ᵥ (σ ∘ w') with hu'
    have e1 : symX u u' = c • (vecMulVec u' (formJ r K *ᵥ w0) +
        vecMulVec w0 (formJ r K *ᵥ u')) := by
      rw [symX, huc, mulVec_smul, vecMulVec_smul, smul_vecMulVec, smul_add]
    have e2 : μ • symX w0 w' = c • (c • (vecMulVec w' (formJ r K *ᵥ w0) +
        vecMulVec w0 (formJ r K *ᵥ w'))) := by
      rw [hμ, smul_smul, symX]
    rw [e1, e2] at h
    have hS := smul_right_injective _ hc0 h
    have key : vecMulVec (u' - c • w') (formJ r K *ᵥ w0) =
        vecMulVec w0 (-(formJ r K *ᵥ (u' - c • w'))) := by
      ext i j
      have := congrFun (congrFun hS i) j
      simp [vecMulVec_apply, mulVec_sub, mulVec_smul] at this ⊢
      linear_combination this
    obtain ⟨d, hzd, hzJ⟩ := sp_rank_one_eq hw0 hJw0 key
    rw [hzd, mulVec_smul] at hzJ
    have hd : d = 0 := by
      have h3 : d • (formJ r K *ᵥ w0) + d • (formJ r K *ᵥ w0) = 0 :=
        add_eq_zero_iff_eq_neg.2 hzJ.symm
      rw [← add_smul] at h3
      rcases smul_eq_zero.1 h3 with h4 | h4
      · have : (2 : K) * d = 0 := by rw [two_mul]; exact h4
        exact (mul_eq_zero.1 this).resolve_left h2K
      · exact absurd h4 hJw0
    rw [hd, zero_smul] at hzd
    exact sub_eq_zero.1 hzd
  have hσ : ∀ t, σ t = t := by
    intro t
    have h := hB (t • w0) (Submodule.smul_mem _ t hw0k)
    have e : σ ∘ (t • w0) = σ t • (σ ∘ w0) := by funext i; simp
    rw [e, mulVec_smul, ← hu, huc, smul_smul, smul_smul] at h
    have h' := smul_left_injective K hw0 h
    rw [mul_comm c t] at h'
    exact mul_right_cancel₀ hc0 h'
  have hσ1 : σ = 1 := RingEquiv.ext hσ
  have hB' : ∀ w' ∈ kerN N, Am *ᵥ w' = c • w' := by
    intro w' hw'
    have := hB w' hw'
    have e : σ ∘ w' = w' := funext fun i => hσ _
    rwa [e] at this
  have hmap : ∀ M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, σ.toRingHom.mapMatrix M = M :=
    fun M => by ext i j; simp [hσ]
  have hAN : Am * N = N * Am := by
    obtain ⟨ζ, hζ⟩ := spFixed_matrix A σ sg hαg
    rw [hsg, map_add, map_one, hmap, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1] at hζ
    have hy : IsNilpotent (Am * N * Ai) := spIsNilpotent_conj h1 h2 hN
    have hζ1 : ζ = 1 := spEq_one_of_smul_one_add_nilpotent hN hy hζ.symm
    rw [hζ1, one_smul] at hζ
    have h3 := add_left_cancel hζ
    calc Am * N = (Am * N * Ai) * Am := by rw [Matrix.mul_assoc _ Ai, h2, Matrix.mul_one]
      _ = N * Am := by rw [h3]
  set B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := Am - c • 1 with hBdef
  have hBN : Commute B N := by
    show B * N = N * B
    rw [hBdef, sub_mul, mul_sub, hAN]
    simp
  have hBk : ∀ w' ∈ kerN N, B *ᵥ w' = 0 := by
    intro w' hw'
    rw [hBdef, sub_mulVec, smul_mulVec, one_mulVec, hB' w' hw', sub_self]
  obtain ⟨m, hm⟩ := hN
  have hBm : B ^ m = 0 := by
    apply sp_matrix_eq_zero_of_mulVec
    have key : ∀ k : ℕ, ∀ x, N ^ k *ᵥ x = 0 → B ^ k *ᵥ x = 0 := by
      intro k
      induction k with
      | zero => intro x hx; rw [pow_zero, one_mulVec] at hx ⊢; exact hx
      | succ k ih =>
        intro x hx
        rw [pow_succ, ← mulVec_mulVec] at hx
        have h1 := ih _ hx
        have hcomm : B ^ k * N = N * B ^ k := (hBN.pow_left k).eq
        have h2 : N *ᵥ (B ^ k *ᵥ x) = 0 := by
          rw [mulVec_mulVec, ← hcomm, ← mulVec_mulVec, h1]
        rw [pow_succ', ← mulVec_mulVec]
        exact hBk _ (mem_kerN.2 h2)
    intro x
    exact key m x (by rw [hm, zero_mulVec])
  obtain ⟨e, he⟩ := sp_add_smul_one_pow_prime_pow (p := p) hBm c
  have hAmB : Am = c • 1 + B := by rw [hBdef]; abel
  have hα' : α = conjAut r K A := by rw [hα, hσ1, map_one, mul_one]
  have hpow : α ^ p ^ e = 1 := by
    rw [hα', ← map_pow]
    apply conjAut_eq_one_of_scalarC _ (c := c ^ p ^ e)
    show (((A : GL (Fin r ⊕ Fin r) K) ^ p ^ e : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = _
    rw [Units.val_pow_eq_pow_val, ← hAm, hAmB]
    exact he
  have hdvd : orderOf α ∣ p ^ e := orderOf_dvd_of_pow_eq_one hpow
  have h1' : orderOf α = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right e hcop) hdvd
  exact orderOf_eq_one_iff.1 h1'


theorem innerCoreFree_PSp_two {T : Type} [Group T] [Finite T] (hS : IsSimpleGroup T)
    (hnab : ∃ a b : T, a * b ≠ b * a) {ℓ f : ℕ} (hm : StatedClassicalModel T .PSp 2 ℓ f)
    (hℓ2 : ℓ ≠ 2) :
    ∀ x ∈ innerAut T, orderOf x = ℓ → ∀ H : Subgroup (MulAut T), innerAut T ≤ H →
      CFSG.Open.GLAPPrimeCoreOf ℓ (H ⊓ Subgroup.centralizer ({x} : Set (MulAut T))) = ⊥ := by
  have h0 := hm
  obtain ⟨hprime, K, _, hfin, hK, ⟨e⟩⟩ := h0
  intro x hx hxo H hH
  have : Fact ℓ.Prime := ⟨hprime.1⟩
  have hchar : CharP K ℓ := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K ℓ] at this
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hprime.1 Nat.prime_two).1 this)
  have hZ : Subgroup.center T = ⊥ := center_eq_bot_of_simple hS hnab
  obtain ⟨g, rfl⟩ := hx
  have hord : orderOf g = ℓ := by
    rw [← orderOf_injective (MulAut.conj : T →* MulAut T) (conj_injective_of_center_eq_bot hZ) g]
    exact hxo
  have hord0 : orderOf (e g) = ℓ := by rw [MulEquiv.orderOf_eq e g]; exact hord
  haveI : NeZero 2 := ⟨by norm_num⟩
  obtain ⟨sg, N, hsg, hN, hN0, hg0⟩ := sp_exists_nilpotent_of_orderOf_eq (r := 2) hℓ2 (e g) hord0
  have hs := sp_hs sg hsg
  have hgen := (CFSG.RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two h2K).2
  refine gLAPPrimeCoreOf_eq_bot_of_framework hZ hprime.1 g
    {q' | e q' ∈ modelGenC 2 K N} {g} ?_ ?_ ?_ ?_ ?_ H hH _ rfl
  · rintro q' (hq' | hq')
    · apply e.injective
      rw [map_mul, map_mul, hg0]
      exact model_h1C sg hsg (e q') hq'
    · rw [Set.mem_singleton_iff.1 hq']
  · intro s q' hs' hq'
    rw [Set.mem_singleton_iff.1 hq']
    exact hs'
  · intro s q' hs' hq'
    have ht : e s * proj 2 K sg = proj 2 K sg * e s := by
      rw [← hg0, ← map_mul, ← map_mul, hs']
    have := model_hGenC hN sg hsg (e s) ht (e q') hq'
    show e (s * q' * s⁻¹) ∈ modelGenC 2 K N
    rw [map_mul, map_mul, map_inv]
    exact this
  · intro q' hq' q'' hq''
    apply e.injective
    rw [map_pow, map_mul, map_inv, map_one]
    exact model_hp3C hℓ2 hs (e q') hq' (e q'') hq''
  · intro α hα hfix
    have hcop : (orderOf (MulAut.congr e α)).Coprime ℓ := by
      rw [MulEquiv.orderOf_eq (MulAut.congr e) α]; exact hα
    have hαg : α g = g := hfix g (Or.inr rfl)
    have h1 : MulAut.congr e α = 1 := by
      refine uniq_modelC_of_gen hℓ2 hgen hN hN0 sg hsg _ hcop ?_ ?_
      · rw [← hg0, MulAut.congr_apply]
        simp [hαg]
      · intro q0 hq0
        have hmem : e.symm q0 ∈ {q' | e q' ∈ modelGenC 2 K N} := by simpa using hq0
        have := hfix _ (Or.inl hmem)
        change e (α (e.symm q0)) = q0
        rw [this]; simp
    exact (MulAut.congr e).injective (by rw [h1, map_one])

end SpTwo

section FamilyStatements2

open CFSG.HardMathSupport.Solomon.LocalBalance

theorem defCharInnerCoreFreeFamOn_B2 :
    DefCharInnerCoreFreeFamOn (fun d => ∃ (q : TauCeti.PrimePower), d = .B 2 q) := by
  intro S _ _ hS hnab idx hidx hSe p hp hp2 hch x hx hxo H hH
  obtain ⟨q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr hch
  subst hr
  obtain ⟨e⟩ := hSe
  have hpq : p = q.p := by simpa using hch.symm
  have hqp2 : q.p ≠ 2 := hpq ▸ hp2
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  subst hpq
  exact innerCoreFree_PSp_two hS hnab hm hqp2 x hx hxo H hH

theorem defCharInnerCoreFreeFamB : DefCharInnerCoreFreeFam .B := by
  intro S _ _ hS hnab idx hidx hSe p hp hp2 hch x hx hxo H hH
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr hch
  subst hr
  have hr2 : 2 ≤ r :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
  rcases Nat.eq_or_lt_of_le hr2 with h2 | h3
  · subst h2
    exact defCharInnerCoreFreeFamOn_B2 S hS hnab ⟨.B 2 q, hv⟩ ⟨q, rfl⟩ hSe p hp hp2 hch x hx hxo
      H hH
  · exact defCharInnerCoreFreeFamOn_B S hS hnab ⟨.B r q, hv⟩ ⟨r, q, rfl, h3⟩ hSe p hp hp2 hch x
      hx hxo H hH

theorem defCharInnerCoreFreeFamTwistedD : DefCharInnerCoreFreeFam .twistedD := by
  intro S _ _ hS hnab idx hidx hSe p hp hp2 hch x hx hxo H hH
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  exact defCharInnerCoreFreeFamOn_twistedD S hS hnab ⟨.twistedD r q, hv⟩ ⟨r, q, rfl⟩ hSe p hp hp2
    hch x hx hxo H hH

@[expose] def DefCharInnerCoreFreeFamDFour : Prop :=
  DefCharInnerCoreFreeFamOn (fun d => ∃ (q : TauCeti.PrimePower), d = .D 4 q)

theorem defCharInnerCoreFreeFamD_of_four (h4 : DefCharInnerCoreFreeFamDFour) :
    DefCharInnerCoreFreeFam .D := by
  intro S _ _ hS hnab idx hidx hSe p hp hp2 hch x hx hxo H hH
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr hch
  subst hr
  have hr4 : 4 ≤ r :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  rcases Nat.eq_or_lt_of_le hr4 with h4' | h5
  · subst h4'
    exact h4 S hS hnab ⟨.D 4 q, hv⟩ ⟨q, rfl⟩ hSe p hp hp2 hch x hx hxo H hH
  · exact defCharInnerCoreFreeFamOn_D S hS hnab ⟨.D r q, hv⟩ ⟨r, q, rfl, h5⟩ hSe p hp hp2 hch x
      hx hxo H hH

end FamilyStatements2

end CFSG.HardMathSupport.Timmesfeld.DefChar
