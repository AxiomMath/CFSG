module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L32Insp

open Subgroup CFSG.QuasithinUnique.Setup.Family

private structure M9 where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  e : Bool
  f : Bool
  g : Bool
  h : Bool
  i : Bool
  deriving DecidableEq

private def M9.mul (x y : M9) : M9 :=
  ⟨(x.a && y.a) ^^ (x.b && y.d) ^^ (x.c && y.g), (x.a && y.b) ^^ (x.b && y.e) ^^ (x.c && y.h),
    (x.a && y.c) ^^ (x.b && y.f) ^^ (x.c && y.i), (x.d && y.a) ^^ (x.e && y.d) ^^ (x.f && y.g),
    (x.d && y.b) ^^ (x.e && y.e) ^^ (x.f && y.h), (x.d && y.c) ^^ (x.e && y.f) ^^ (x.f && y.i),
    (x.g && y.a) ^^ (x.h && y.d) ^^ (x.i && y.g), (x.g && y.b) ^^ (x.h && y.e) ^^ (x.i && y.h),
    (x.g && y.c) ^^ (x.h && y.f) ^^ (x.i && y.i)⟩

private def M9.tr (x : M9) : M9 := ⟨x.a, x.d, x.g, x.b, x.e, x.h, x.c, x.f, x.i⟩

private def M9.p7 (w : M9) : M9 :=
  let w2 := w.mul w
  (w.mul w2).mul (w2.mul w2)

private def one9 : M9 := ⟨true, false, false, false, true, false, false, false, true⟩

private def zb (x : ZMod 2) : Bool := decide (x = 1)

private theorem zb_injective : Function.Injective zb := by decide

private theorem zb_dot (a b c d e f : ZMod 2) :
    zb (a * b + c * d + e * f) = ((zb a && zb b) ^^ (zb c && zb d) ^^ (zb e && zb f)) := by
  revert a b c d e f
  decide

private def enc (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : M9 :=
  ⟨zb (A 0 0), zb (A 0 1), zb (A 0 2), zb (A 1 0), zb (A 1 1), zb (A 1 2), zb (A 2 0),
    zb (A 2 1), zb (A 2 2)⟩

private theorem enc_mul (A B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    enc (A * B) = (enc A).mul (enc B) := by
  simp only [enc, M9.mul, Matrix.mul_apply, Fin.sum_univ_three, zb_dot]

private theorem enc_injective : Function.Injective enc := by
  intro A B h
  simp only [enc, M9.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  ext i j
  fin_cases i <;> fin_cases j
  exacts [zb_injective h1, zb_injective h2, zb_injective h3, zb_injective h4, zb_injective h5,
    zb_injective h6, zb_injective h7, zb_injective h8, zb_injective h9]

private def sh (g : GL32) : M9 := enc (g : Matrix (Fin 3) (Fin 3) (ZMod 2))

private theorem sh_mul (g h : GL32) : sh (g * h) = (sh g).mul (sh h) := by
  simp only [sh, Units.val_mul, enc_mul]

private theorem sh_injective : Function.Injective sh := fun _ _ h => Units.ext (enc_injective h)

private theorem sh_one : sh 1 = one9 := by decide

private theorem sh_pow_seven (g : GL32) : sh (g ^ 7) = (sh g).p7 := by
  rw [show g ^ 7 = g * (g * g) * (g * g * (g * g)) by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
  simp only [sh_mul]
  rfl

private theorem sh_τ (g : GL32) : sh (τ g) = (sh g⁻¹).tr := by
  rw [sh, CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut_matrix]
  rfl

private def good7 (G Gi K : M9) : Bool :=
  let w := ((G.mul K.tr).mul Gi).mul K
  w.p7 == one9 && !(w == one9)

private def k1B : M9 := ⟨false, false, true, false, true, false, true, false, true⟩
private def k2B : M9 := ⟨false, true, false, true, true, false, false, false, true⟩
private def k3B : M9 := ⟨false, false, true, false, true, true, true, true, false⟩

private theorem check_seven : ∀ a b c e f i : Bool, ∀ a' b' c' e' f' i' : Bool,
    M9.mul ⟨a, b, c, b, e, f, c, f, i⟩ ⟨a', b', c', b', e', f', c', f', i'⟩ = one9 →
    (good7 ⟨a, b, c, b, e, f, c, f, i⟩ ⟨a', b', c', b', e', f', c', f', i'⟩ k1B ||
      good7 ⟨a, b, c, b, e, f, c, f, i⟩ ⟨a', b', c', b', e', f', c', f', i'⟩ k2B ||
      good7 ⟨a, b, c, b, e, f, c, f, i⟩ ⟨a', b', c', b', e', f', c', f', i'⟩ k3B) = true := by
  decide +kernel

private theorem check_seven' {G Gi : M9} (hG : G.tr = G) (hGi : Gi.tr = Gi)
    (h : G.mul Gi = one9) : (good7 G Gi k1B || good7 G Gi k2B || good7 G Gi k3B) = true := by
  obtain ⟨a, b, c, d, e, f, g, h', i⟩ := G
  obtain ⟨a', b', c', d', e', f', g', h'', i'⟩ := Gi
  simp only [M9.tr, M9.mk.injEq] at hG hGi
  obtain ⟨-, rfl, rfl, -, -, rfl, -, -, -⟩ := hG
  obtain ⟨-, rfl, rfl, -, -, rfl, -, -, -⟩ := hGi
  exact check_seven _ _ _ _ _ _ _ _ _ _ _ _ h

private def wk1 : GL32 :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 1], !![1, 0, 1; 0, 1, 0; 1, 0, 0], by decide, by decide⟩
private def wk2 : GL32 :=
  ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], !![1, 1, 0; 1, 0, 0; 0, 0, 1], by decide, by decide⟩
private def wk3 : GL32 :=
  ⟨!![0, 0, 1; 0, 1, 1; 1, 1, 0], !![1, 1, 1; 1, 1, 0; 1, 0, 0], by decide, by decide⟩

private theorem sh_wk1 : sh wk1 = k1B := by decide
private theorem sh_wk2 : sh wk2 = k2B := by decide
private theorem sh_wk3 : sh wk3 = k3B := by decide

private theorem sh_witness (g k : GL32) :
    sh (((MulAut.conj g * τ) k)⁻¹ * k) = (((sh g).mul (sh k).tr).mul (sh g⁻¹)).mul (sh k) := by
  have h1 : ((MulAut.conj g * τ) k)⁻¹ * k = g * τ k⁻¹ * g⁻¹ * k := by
    simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
  rw [h1, sh_mul, sh_mul, sh_mul, sh_τ, inv_inv]

private theorem orderOf_witness {g k : GL32} (hk : good7 (sh g) (sh g⁻¹) (sh k) = true) :
    orderOf (((MulAut.conj g * τ) k)⁻¹ * k) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  simp only [good7, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    ne_eq] at hk
  obtain ⟨h7, h1⟩ := hk
  refine orderOf_eq_prime (sh_injective ?_) fun h => h1 ?_
  · rw [sh_pow_seven, sh_witness, sh_one]
    exact h7
  · rw [← sh_witness, h, sh_one]

private theorem outer_involution_form {φ : MulAut GL32} (hφ : φ ∉ Inn) (hφ2 : φ * φ = 1) :
    ∃ g : GL32, φ = MulAut.conj g * τ ∧ τ g = g⁻¹ := by
  rcases mem_Inn_or φ with h | ⟨g, hg⟩
  · exact absurd h hφ
  · have hφ' : φ = MulAut.conj g * τ := by rw [hg, mul_assoc, τ_mul_τ, mul_one]
    refine ⟨g, hφ', ?_⟩
    have h1 : MulAut.conj (g * τ g) = φ * φ := by
      rw [map_mul, ← aut_mul_conj, inv_eq_of_mul_eq_one_right τ_mul_τ, hφ']
      simp only [mul_assoc]
    have h2 : g * τ g = 1 := innConj_injective (by rw [h1, hφ2, map_one])
    exact eq_inv_of_mul_eq_one_right h2

theorem exists_orderOf_eq_seven_of_not_mem_Inn {φ : MulAut GL32} (hφ : φ ∉ Inn)
    (hφ2 : φ * φ = 1) : ∃ k : GL32, orderOf ((φ k)⁻¹ * k) = 7 := by
  obtain ⟨g, rfl, hg⟩ := outer_involution_form hφ hφ2
  have hG : (sh g).tr = sh g := by
    have := sh_τ g⁻¹
    rw [inv_inv, map_inv, hg, inv_inv] at this
    exact this.symm
  have hGi : (sh g⁻¹).tr = sh g⁻¹ := by
    have := sh_τ g
    rw [hg] at this
    exact this.symm
  have h1 : (sh g).mul (sh g⁻¹) = one9 := by rw [← sh_mul, mul_inv_cancel, sh_one]
  have := check_seven' hG hGi h1
  simp only [Bool.or_eq_true] at this
  rcases this with (h | h) | h
  · exact ⟨wk1, orderOf_witness (by rw [sh_wk1]; exact h)⟩
  · exact ⟨wk2, orderOf_witness (by rw [sh_wk2]; exact h)⟩
  · exact ⟨wk3, orderOf_witness (by rw [sh_wk3]; exact h)⟩

private theorem card_modEq_three {α : Type*} [Finite α] (f : α → α) (hf : ∀ a, f (f (f a)) = a) :
    Nat.card α ≡ Nat.card {a // f a = a} [MOD 3] := by
  classical
  have := Fintype.ofFinite α
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) (by
    funext a
    exact hf a)
  rw [Nat.card_eq_fintype_card]
  have h : Nat.card {a // f a = a} = Fintype.card (Function.fixedPoints f) :=
    (Nat.card_eq_fintype_card (α := Function.fixedPoints f))
  rw [h]
  exact key

private theorem eq_one_of_commute_of_isPGroup {V : Subgroup GL32} (hV : IsPGroup 2 V) {v : GL32}
    (hv : v ∈ V) (hc : v * l₀ = l₀ * v) : v = 1 := by
  by_contra h1
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hV ⟨v, hv⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := fun h => h1 (orderOf_eq_one_iff.1 (by rw [hk, h, pow_zero]))
  have hdvd : 2 ∣ orderOf v := hk ▸ dvd_pow_self 2 hk0
  have hs := orderOf_pow_orderOf_div (x := v) (n := 2) (by rw [hk]; exact pow_ne_zero _ two_ne_zero)
    hdvd
  have hs2 : (v ^ (orderOf v / 2)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (v ^ (orderOf v / 2))
    rwa [hs] at this
  have hs1 := eq_one_of_commute_l₀ ((Commute.pow_left (show Commute v l₀ from hc) _)) hs2
  rw [hs1, orderOf_one] at hs
  exact absurd hs (by norm_num)

private theorem card_eq_four_aux {V : Subgroup GL32} (hV : IsPGroup 2 V) (hne : V ≠ ⊥)
    (hl : l₀ ∈ normalizer (V : Set GL32)) : Nat.card V = 4 := by
  have h3 : l₀ * l₀ * l₀ = 1 := by rw [← pow_three']; exact l₀_pow_three
  let f : V → V := fun v => ⟨l₀ * v * l₀⁻¹, (mem_normalizer_iff.1 hl v).1 v.2⟩
  have hf : ∀ v, f (f (f v)) = v := fun v => by
    apply Subtype.ext
    show l₀ * (l₀ * (l₀ * v * l₀⁻¹) * l₀⁻¹) * l₀⁻¹ = v
    calc _ = (l₀ * l₀ * l₀) * v * (l₀ * l₀ * l₀)⁻¹ := by group
      _ = v := by rw [h3]; simp
  have hfix1 : ∀ a : V, f a = a → a = 1 := fun a ha =>
    Subtype.ext (eq_one_of_commute_of_isPGroup hV a.2 (by
      have := congrArg Subtype.val ha
      calc (a : GL32) * l₀ = (l₀ * a * l₀⁻¹) * l₀ := by rw [show l₀ * a * l₀⁻¹ = a from this]
        _ = l₀ * a := by group))
  have hcard : Nat.card {a // f a = a} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ((hfix1 x x.2).trans (hfix1 y y.2).symm)⟩, ⟨⟨1, ?_⟩⟩⟩
    exact Subtype.ext (by show l₀ * 1 * l₀⁻¹ = 1; group)
  have hmod := card_modEq_three f hf
  rw [hcard] at hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hV
  have hdvd : Nat.card V ∣ 168 := card_GL ▸ card_subgroup_dvd_card V
  have hn3 : n ≤ 3 := by
    by_contra hn3
    have : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 (by omega)).trans (hn ▸ hdvd)
    norm_num at this
  have hne1 : Nat.card V ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  rw [hn] at hmod hne1 ⊢
  interval_cases n
  · exact absurd (pow_zero 2) hne1
  · exact absurd hmod (by decide)
  · norm_num
  · exact absurd hmod (by decide)

private def conjSub (g : GL32) (V : Subgroup GL32) : Subgroup GL32 :=
  V.map (MulAut.conj g).toMonoidHom

private theorem mem_conjSub {g : GL32} {V : Subgroup GL32} {y : GL32} :
    y ∈ conjSub g V ↔ g⁻¹ * y * g ∈ V := by
  rw [conjSub, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

private theorem card_conjSub (g : GL32) (V : Subgroup GL32) :
    Nat.card (conjSub g V) = Nat.card V :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem isPGroup_conjSub {g : GL32} {V : Subgroup GL32} (hV : IsPGroup 2 V) :
    IsPGroup 2 (conjSub g V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hV
  exact IsPGroup.iff_card.2 ⟨n, by rw [card_conjSub, hn]⟩

private theorem conjSub_ne_bot {g : GL32} {V : Subgroup GL32} (hne : V ≠ ⊥) :
    conjSub g V ≠ ⊥ :=
  fun h => hne (Subgroup.card_eq_one.1 (by rw [← card_conjSub g V, h, Subgroup.card_bot]))

private theorem exists_conj_normalized {V : Subgroup GL32} {l : GL32} (hl : orderOf l = 3)
    (hlV : l ∈ normalizer (V : Set GL32)) :
    ∃ g : GL32, l₀ ∈ normalizer (conjSub g V : Set GL32) := by
  have hl3 : l ^ 3 = 1 := by
    have := pow_orderOf_eq_one l
    rwa [hl] at this
  obtain ⟨g, hg⟩ := exists_conj_mem_zpowers hl3
  refine ⟨g, ?_⟩
  have h1 : g * l * g⁻¹ ∈ normalizer (conjSub g V : Set GL32) := by
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_conjSub]
    have := mem_normalizer_iff.1 hlV (g⁻¹ * y * g)
    rw [this, show g⁻¹ * ((g * l * g⁻¹) * y * (g * l * g⁻¹)⁻¹) * g = l * (g⁻¹ * y * g) * l⁻¹ by
      group]
  have hord : orderOf (g * l * g⁻¹) = 3 :=
    (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective l).trans hl
  have hz : zpowers (g * l * g⁻¹) = zpowers l₀ := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hg)
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_l₀, hord]
  exact (zpowers_le.2 h1) (hz ▸ mem_zpowers l₀)

theorem card_eq_four_of_normalized_two_subgroup {V : Subgroup GL32} {l : GL32}
    (hl : orderOf l = 3) (hV : IsPGroup 2 V) (hne : V ≠ ⊥)
    (hlV : l ∈ normalizer (V : Set GL32)) : Nat.card V = 4 := by
  obtain ⟨g, hg⟩ := exists_conj_normalized hl hlV
  have h4 := card_eq_four_aux (isPGroup_conjSub (g := g) hV) (conjSub_ne_bot hne) hg
  rwa [card_conjSub] at h4

private def sqSub (V : Subgroup GL32) (hc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) : Subgroup GL32 where
  carrier := {x | x ∈ V ∧ x ^ 2 = 1}
  one_mem' := ⟨one_mem V, one_pow 2⟩
  mul_mem' {a b} ha hb :=
    ⟨mul_mem ha.1 hb.1, by
      rw [(show Commute a b from hc a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

private theorem sq_eq_one_aux {V : Subgroup GL32} (hV : IsPGroup 2 V) (hne : V ≠ ⊥)
    (hl : l₀ ∈ normalizer (V : Set GL32)) : ∀ g ∈ V, g ^ 2 = 1 := by
  have h4 := card_eq_four_aux hV hne hl
  have h22 : Nat.card V = 2 ^ 2 := by rw [h4]; norm_num
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsPGroup.isMulCommutative_of_card_eq_prime_sq h22).is_comm.comm
      ⟨a, ha⟩ ⟨b, hb⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (show 2 ∣ Nat.card V by rw [h4]; norm_num)
  have hx2 : (x : GL32) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have hx1 : (x : GL32) ≠ 1 := fun h => by
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hA : l₀ ∈ normalizer (sqSub V hcomm : Set GL32) := by
    have hconj : ∀ m ∈ normalizer (V : Set GL32), ∀ z ∈ sqSub V hcomm,
        m * z * m⁻¹ ∈ sqSub V hcomm := fun m hm z hz =>
      ⟨(mem_normalizer_iff.1 hm z).1 hz.1, by rw [conj_pow, hz.2]; group⟩
    refine mem_normalizer_iff.2 fun y => ⟨hconj l₀ hl y, fun hy => ?_⟩
    have := hconj l₀⁻¹ (inv_mem hl) _ hy
    rwa [show l₀⁻¹ * (l₀ * y * l₀⁻¹) * l₀⁻¹⁻¹ = y by group] at this
  have hA4 := card_eq_four_aux (V := sqSub V hcomm)
    (fun a => ⟨1, Subtype.ext (by simpa using a.2.2)⟩)
    (fun h => hx1 (by
      have : (x : GL32) ∈ sqSub V hcomm := ⟨x.2, hx2⟩
      rw [h] at this
      exact this)) hA
  have hle : sqSub V hcomm ≤ V := fun y hy => hy.1
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hA4, h4])
  intro y hy
  have hy' : y ∈ sqSub V hcomm := by rw [heq]; exact hy
  exact hy'.2

private theorem sq_eq_one_of_conj {x y : GL32} (h : (x⁻¹ * y * x) ^ 2 = 1) : y ^ 2 = 1 := by
  have h2 : y ^ 2 = x * (x⁻¹ * y * x) ^ 2 * x⁻¹ := by
    rw [← conj_pow, show x * (x⁻¹ * y * x) * x⁻¹ = y by group]
  rw [h2, h]
  group

private theorem not_conj_of_pair {V Q : Subgroup GL32} (hP : Pair V Q)
    (hl : l₀ ∈ normalizer (V : Set GL32)) (hsq : ∀ g ∈ V, g ^ 2 = 1) (hV4 : Nat.card V = 4)
    {h : GL32} (hQ : ∀ q, q ∈ Q ↔ h * q * h⁻¹ ∈ V) : False := by
  have h3 : l₀ * l₀ * l₀ = 1 := by rw [← pow_three']; exact l₀_pow_three
  let N : Subgroup GL32 := normalizer (V : Set GL32)
  let f : GL32 ⧸ N → GL32 ⧸ N := fun c => l₀ • c
  have hf : ∀ c, f (f (f c)) = c := fun c => by
    show l₀ • l₀ • l₀ • c = c
    rw [← mul_smul, ← mul_smul, h3, one_smul]
  have hmod := card_modEq_three f hf
  have hc7 : Nat.card (GL32 ⧸ N) = 7 := hP.index
  have hfix : ∀ x : GL32, f (x : GL32 ⧸ N) = x ↔ x⁻¹ * l₀ * x ∈ N := fun x => by
    show l₀ • (x : GL32 ⧸ N) = x ↔ _
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul,
      show (l₀ * x)⁻¹ * x = (x⁻¹ * l₀ * x)⁻¹ by group, inv_mem_iff]
  have hm : h * l₀ * h⁻¹ ∈ N := by
    refine mem_normalizer_iff.2 fun y => ?_
    have e1 : y ∈ V ↔ h⁻¹ * y * h ∈ Q := by
      rw [hQ, show h * (h⁻¹ * y * h) * h⁻¹ = y by group]
    have e2 := mem_normalizer_iff.1 hP.l₀_mem (h⁻¹ * y * h)
    have e3 : l₀ * (h⁻¹ * y * h) * l₀⁻¹ ∈ Q ↔ (h * l₀ * h⁻¹) * y * (h * l₀ * h⁻¹)⁻¹ ∈ V := by
      rw [hQ, show h * (l₀ * (h⁻¹ * y * h) * l₀⁻¹) * h⁻¹ = (h * l₀ * h⁻¹) * y * (h * l₀ * h⁻¹)⁻¹
        by group]
    rw [e1, e2, e3]
  have hab : ((1 : GL32) : GL32 ⧸ N) ≠ ((h⁻¹ : GL32) : GL32 ⧸ N) := fun hab => by
    rw [QuotientGroup.eq, inv_one, one_mul] at hab
    have hhN : h ∈ N := by simpa using inv_mem hab
    refine hP.not_le fun q hq => ?_
    exact le_normalizer ((mem_normalizer_iff.1 hhN q).2 ((hQ q).1 hq))
  have hS : {c : GL32 ⧸ N | f c = c} = {((1 : GL32) : GL32 ⧸ N), ((h⁻¹ : GL32) : GL32 ⧸ N)} := by
    ext c
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hfix x]
    constructor
    · intro hx
      have hlW : l₀ ∈ normalizer (conjSub x V : Set GL32) := by
        refine mem_normalizer_iff.2 fun y => ?_
        simp only [mem_conjSub]
        have := mem_normalizer_iff.1 hx (x⁻¹ * y * x)
        rw [this, show (x⁻¹ * l₀ * x) * (x⁻¹ * y * x) * (x⁻¹ * l₀ * x)⁻¹
          = x⁻¹ * (l₀ * y * l₀⁻¹) * x by group]
      have hW4 : Nat.card (conjSub x V) = 4 := by rw [card_conjSub, hV4]
      have hWsq : ∀ y ∈ conjSub x V, y ^ 8 = 1 := fun y hy => by
        have hy2 : y ^ 2 = 1 := sq_eq_one_of_conj (hsq _ (mem_conjSub.1 hy))
        rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, hy2, one_pow]
      rcases hP.split (conjSub x V) hWsq hlW with hle | hle
      · left
        have hWV : conjSub x V = V := Subgroup.eq_of_le_of_card_ge hle (by rw [hW4, hV4])
        have hxN : x ∈ N := mem_normalizer_iff''.2 fun z => by
          rw [← mem_conjSub, hWV]
        rw [QuotientGroup.eq, mul_one]
        exact inv_mem hxN
      · right
        have hWQ : conjSub x V = Q := Subgroup.eq_of_le_of_card_ge hle (by rw [hW4, hP.card])
        have hhx : h * x ∈ N := mem_normalizer_iff''.2 fun y => by
          have e1 : y ∈ V ↔ h⁻¹ * y * h ∈ Q := by
            rw [hQ, show h * (h⁻¹ * y * h) * h⁻¹ = y by group]
          have e2 : h⁻¹ * y * h ∈ Q ↔ x⁻¹ * (h⁻¹ * y * h) * x ∈ V := by
            rw [← hWQ, mem_conjSub]
          rw [e1, e2, show (h * x)⁻¹ * y * (h * x) = x⁻¹ * (h⁻¹ * y * h) * x by group]
        rw [QuotientGroup.eq]
        have := inv_mem hhx
        rwa [mul_inv_rev] at this
    · rintro (hx | hx)
      · rw [QuotientGroup.eq, mul_one] at hx
        have hxN : x ∈ N := by simpa using inv_mem hx
        exact mul_mem (mul_mem (inv_mem hxN) hl) hxN
      · rw [QuotientGroup.eq] at hx
        have hhx : h * x ∈ N := by simpa using inv_mem hx
        rw [show x⁻¹ * l₀ * x = (h * x)⁻¹ * (h * l₀ * h⁻¹) * (h * x) by group]
        exact mul_mem (mul_mem (inv_mem hhx) hm) hhx
  have hfix2 : Nat.card {c // f c = c} = 2 := by
    have : Nat.card {c // f c = c} = Nat.card ({c : GL32 ⧸ N | f c = c} : Set (GL32 ⧸ N)) := rfl
    rw [this, Nat.card_coe_set_eq, hS, Set.ncard_pair hab]
  rw [hc7, hfix2] at hmod
  exact absurd hmod (by decide)

private theorem τ_τ (y : GL32) : τ (τ y) = y :=
  congrArg (fun α : MulAut GL32 => α y) τ_mul_τ

private theorem mem_Inn_aux {φ : MulAut GL32} {V : Subgroup GL32} (hV : IsPGroup 2 V)
    (hne : V ≠ ⊥) (hl : l₀ ∈ normalizer (V : Set GL32)) (hφ : ∀ x, φ x ∈ V ↔ x ∈ V) :
    φ ∈ Inn := by
  by_contra hφI
  have hV4 := card_eq_four_aux hV hne hl
  have hsq := sq_eq_one_aux hV hne hl
  obtain ⟨Q, hP⟩ := exists_pair hsq hV4 hl
  obtain ⟨g, hg⟩ : ∃ g, φ = MulAut.conj g * τ := by
    rcases mem_Inn_or φ with h | ⟨g, hg⟩
    · exact absurd h hφI
    · exact ⟨g, by rw [hg, mul_assoc, τ_mul_τ, mul_one]⟩
  let T : Subgroup GL32 := V.comap τ.toMonoidHom
  have hT : ∀ y, y ∈ T ↔ τ y ∈ V := fun y => Iff.rfl
  have hTcard : Nat.card T = 4 := by
    rw [show T = V.map τ.symm.toMonoidHom from Subgroup.comap_equiv_eq_map_symm τ V,
      Subgroup.card_map_of_injective τ.symm.injective, hV4]
  have hTsq : ∀ y ∈ T, y ^ 8 = 1 := fun y hy => by
    have h2 : y ^ 2 = 1 := by
      have := hsq _ ((hT y).1 hy)
      rw [← map_pow] at this
      exact τ.injective (by rw [this, map_one])
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, h2, one_pow]
  have hTl : l₀ ∈ normalizer (T : Set GL32) := by
    refine mem_normalizer_iff.2 fun y => ?_
    simp only [hT, map_mul, map_inv, τ_l₀]
    exact mem_normalizer_iff.1 hl (τ y)
  rcases hP.split T hTsq hTl with hle | hle
  · have hTV : T = V := Subgroup.eq_of_le_of_card_ge hle (by rw [hTcard, hV4])
    obtain ⟨p, hpV, hp⟩ := hP.tau
    refine hp (le_normalizer ?_)
    have : τ p ∈ T := by rw [hT, τ_τ]; exact hpV
    rwa [hTV] at this
  · have hTQ : T = Q := Subgroup.eq_of_le_of_card_ge hle (by rw [hTcard, hP.card])
    refine not_conj_of_pair hP hl hsq hV4 (h := g) fun q => ?_
    rw [← hTQ, hT]
    have := hφ (τ q)
    rw [hg, MulAut.mul_apply, MulAut.conj_apply, τ_τ] at this
    exact this.symm

theorem mem_Inn_of_map_eq_of_normalized {φ : MulAut GL32} {V : Subgroup GL32} {l : GL32}
    (hl : orderOf l = 3) (hV : IsPGroup 2 V) (hne : V ≠ ⊥)
    (hlV : l ∈ normalizer (V : Set GL32)) (hφ : V.map φ.toMonoidHom = V) : φ ∈ Inn := by
  obtain ⟨g, hg⟩ := exists_conj_normalized hl hlV
  have hφ1 : ∀ x, φ x ∈ V ↔ x ∈ V := fun x => by
    have := SetLike.ext_iff.1 hφ (φ x)
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at this
    exact this.symm
  have hφ2 : ∀ x, (MulAut.conj g * φ * MulAut.conj g⁻¹) x ∈ conjSub g V ↔
      x ∈ conjSub g V := fun x => by
    rw [mem_conjSub, mem_conjSub]
    simp only [MulAut.mul_apply, MulAut.conj_apply, inv_inv]
    rw [show g⁻¹ * (g * φ (g⁻¹ * x * g) * g⁻¹) * g = φ (g⁻¹ * x * g) by group]
    exact hφ1 _
  have h1 := mem_Inn_aux (isPGroup_conjSub hV) (conjSub_ne_bot hne) hg hφ2
  have h2 : φ = MulAut.conj g⁻¹ * (MulAut.conj g * φ * MulAut.conj g⁻¹) * MulAut.conj g := by
    rw [map_inv]
    group
  rw [h2]
  exact mul_mem (mul_mem ⟨g⁻¹, rfl⟩ h1) ⟨g, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.L32Insp
