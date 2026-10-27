module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L32Insp

open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped MatrixGroups

private structure B9 where
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

private def B9.mul (x y : B9) : B9 :=
  ⟨(x.a && y.a) ^^ (x.b && y.d) ^^ (x.c && y.g), (x.a && y.b) ^^ (x.b && y.e) ^^ (x.c && y.h),
    (x.a && y.c) ^^ (x.b && y.f) ^^ (x.c && y.i), (x.d && y.a) ^^ (x.e && y.d) ^^ (x.f && y.g),
    (x.d && y.b) ^^ (x.e && y.e) ^^ (x.f && y.h), (x.d && y.c) ^^ (x.e && y.f) ^^ (x.f && y.i),
    (x.g && y.a) ^^ (x.h && y.d) ^^ (x.i && y.g), (x.g && y.b) ^^ (x.h && y.e) ^^ (x.i && y.h),
    (x.g && y.c) ^^ (x.h && y.f) ^^ (x.i && y.i)⟩

private def B9.tr (x : B9) : B9 := ⟨x.a, x.d, x.g, x.b, x.e, x.h, x.c, x.f, x.i⟩

private def B9.p8 (w : B9) : B9 :=
  let w2 := w.mul w
  let w4 := w2.mul w2
  w4.mul w4

private def B9.p7 (w : B9) : B9 :=
  let w2 := w.mul w
  (w.mul w2).mul (w2.mul w2)

private def zb (x : ZMod 2) : Bool := decide (x = 1)

private theorem zb_injective : Function.Injective zb := by decide

private theorem zb_dot (a b c d e f : ZMod 2) :
    zb (a * b + c * d + e * f) = ((zb a && zb b) ^^ (zb c && zb d) ^^ (zb e && zb f)) := by
  revert a b c d e f
  decide

private def enc (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : B9 :=
  ⟨zb (A 0 0), zb (A 0 1), zb (A 0 2), zb (A 1 0), zb (A 1 1), zb (A 1 2), zb (A 2 0),
    zb (A 2 1), zb (A 2 2)⟩

private theorem enc_mul (A B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    enc (A * B) = (enc A).mul (enc B) := by
  simp only [enc, B9.mul, Matrix.mul_apply, Fin.sum_univ_three, zb_dot]

private theorem enc_injective : Function.Injective enc := by
  intro A B h
  simp only [enc, B9.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  ext i j
  fin_cases i <;> fin_cases j
  exacts [zb_injective h1, zb_injective h2, zb_injective h3, zb_injective h4, zb_injective h5,
    zb_injective h6, zb_injective h7, zb_injective h8, zb_injective h9]

private def E (g : GL32) : B9 := enc (g : Matrix (Fin 3) (Fin 3) (ZMod 2))

private theorem E_mul (g h : GL32) : E (g * h) = (E g).mul (E h) := by
  simp only [E, Units.val_mul, enc_mul]

private theorem E_injective : Function.Injective E := fun _ _ h => Units.ext (enc_injective h)

private theorem E_conj (g s : GL32) : E (g * s * g⁻¹) = ((E g).mul (E s)).mul (E g⁻¹) := by
  rw [E_mul, E_mul]

private theorem E_inv_conj (g s : GL32) :
    E (g⁻¹ * s * g) = ((E g⁻¹).mul (E s)).mul (E g) := by
  rw [E_mul, E_mul]

private def one9 : B9 := ⟨true, false, false, false, true, false, false, false, true⟩

private theorem E_one : E 1 = one9 := by decide

private theorem E_pow_eight (g : GL32) : E (g ^ 8) = (E g).p8 := by
  rw [show g ^ 8 = g * g * (g * g) * (g * g * (g * g)) by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
  simp only [E_mul]
  rfl

private theorem E_pow_seven (g : GL32) : E (g ^ 7) = (E g).p7 := by
  rw [show g ^ 7 = g * (g * g) * (g * g * (g * g)) by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
  simp only [E_mul]
  rfl

def l₀ : GL32 :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩

def tL : GL32 :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide, by decide⟩

private def v1 : GL32 :=
  ⟨!![0, 0, 1; 1, 1, 1; 1, 0, 0], !![0, 0, 1; 1, 1, 1; 1, 0, 0], by decide, by decide⟩

private def u1 : GL32 :=
  ⟨!![0, 1, 1; 0, 1, 0; 1, 1, 0], !![0, 1, 1; 0, 1, 0; 1, 1, 0], by decide, by decide⟩

private def l0B : B9 := ⟨false, false, true, true, false, false, false, true, false⟩
private def l0iB : B9 := ⟨false, true, false, false, false, true, true, false, false⟩
private def tB : B9 := ⟨true, false, false, false, false, true, false, true, false⟩
private def v1B : B9 := ⟨false, false, true, true, true, true, true, false, false⟩
private def u1B : B9 := ⟨false, true, true, false, true, false, true, true, false⟩

private theorem E_l₀ : E l₀ = l0B := by decide
private theorem E_l₀_inv : E l₀⁻¹ = l0iB := by decide
private theorem E_tL : E tL = tB := by decide
private theorem E_tL_inv : E tL⁻¹ = tB := by decide
private theorem E_v1 : E v1 = v1B := by decide
private theorem E_v1_inv : E v1⁻¹ = v1B := by decide
private theorem E_u1 : E u1 = u1B := by decide
private theorem E_u1_inv : E u1⁻¹ = u1B := by decide

private def cl (s : B9) : B9 := (l0B.mul s).mul l0iB

private def cli (s : B9) : B9 := (l0iB.mul s).mul l0B

private theorem E_conj_l₀ (s : GL32) : E (l₀ * s * l₀⁻¹) = cl (E s) := by
  rw [E_conj, E_l₀, E_l₀_inv, cl]

private theorem E_inv_conj_l₀ (s : GL32) : E (l₀⁻¹ * s * l₀) = cli (E s) := by
  rw [E_inv_conj, E_l₀, E_l₀_inv, cli]

private def listV : List B9 :=
  [one9, v1B, ⟨false, true, false, true, false, false, true, true, true⟩,
    ⟨true, true, true, false, false, true, false, true, false⟩]

private def listU : List B9 :=
  [one9, u1B, ⟨false, true, true, true, false, true, false, false, true⟩,
    ⟨true, false, false, true, false, true, true, true, false⟩]

private def subOfList (l : List B9) (h1 : one9 ∈ l) (hmul : ∀ x ∈ l, ∀ y ∈ l, x.mul y ∈ l)
    (hsq : ∀ x ∈ l, x.mul x = one9) : Subgroup GL32 where
  carrier := {g | E g ∈ l}
  one_mem' := by simpa [E_one] using h1
  mul_mem' {a b} ha hb := by
    change E (a * b) ∈ l
    rw [E_mul]
    exact hmul _ ha _ hb
  inv_mem' {a} ha := by
    have haa : a * a = 1 := E_injective (by rw [E_mul, E_one]; exact hsq _ ha)
    change E a⁻¹ ∈ l
    rw [inv_eq_of_mul_eq_one_right haa]
    exact ha

private def V₀ : Subgroup GL32 := subOfList listV (by decide) (by decide) (by decide)

private def U₀ : Subgroup GL32 := subOfList listU (by decide) (by decide) (by decide)

private theorem check_split : ∀ a b c d e f g h i : Bool,
    (B9.p8 ⟨a, b, c, d, e, f, g, h, i⟩ = one9 →
      B9.p8 ((B9.mul ⟨a, b, c, d, e, f, g, h, i⟩ (cl ⟨a, b, c, d, e, f, g, h, i⟩)).mul
        (cli ⟨a, b, c, d, e, f, g, h, i⟩)) = one9 →
      B9.p8 (B9.mul ⟨a, b, c, d, e, f, g, h, i⟩ (cl (B9.p7 ⟨a, b, c, d, e, f, g, h, i⟩))) =
        one9 →
      (⟨a, b, c, d, e, f, g, h, i⟩ : B9) ∈ listV ∨ (⟨a, b, c, d, e, f, g, h, i⟩ : B9) ∈ listU) := by
  decide +kernel

private theorem check_cent : ∀ a b c d e f g h i : Bool,
    (B9.mul ⟨a, b, c, d, e, f, g, h, i⟩ l0B = l0B.mul ⟨a, b, c, d, e, f, g, h, i⟩ →
      B9.mul ⟨a, b, c, d, e, f, g, h, i⟩ ⟨a, b, c, d, e, f, g, h, i⟩ = one9 →
      (⟨a, b, c, d, e, f, g, h, i⟩ : B9) = one9) := by
  decide +kernel

private theorem check_split' {s : B9} (h1 : s.p8 = one9)
    (h2 : ((s.mul (cl s)).mul (cli s)).p8 = one9) (h3 : (s.mul (cl s.p7)).p8 = one9) :
    s ∈ listV ∨ s ∈ listU := by
  cases s
  exact check_split _ _ _ _ _ _ _ _ _ h1 h2 h3

private theorem check_cent' {s : B9} (h1 : s.mul l0B = l0B.mul s) (h2 : s.mul s = one9) :
    s = one9 := by
  cases s
  exact check_cent _ _ _ _ _ _ _ _ _ h1 h2

private theorem card_subOfList {l : List B9} {h1 : one9 ∈ l}
    {hmul : ∀ x ∈ l, ∀ y ∈ l, x.mul y ∈ l} {hsq : ∀ x ∈ l, x.mul x = one9} (hnd : l.Nodup)
    (hpre : ∀ x ∈ l, ∃ g, E g = x) : Nat.card (subOfList l h1 hmul hsq) = l.length := by
  classical
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← Set.ncard_image_of_injective _ E_injective]
  have : E '' (subOfList l h1 hmul hsq : Set GL32) = ↑l.toFinset := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, List.mem_toFinset]
    refine ⟨fun ⟨g, hg, hgx⟩ => hgx ▸ hg, fun hx => ?_⟩
    obtain ⟨g, hg⟩ := hpre x hx
    exact ⟨g, show E g ∈ l by rw [hg]; exact hx, hg⟩
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

private theorem card_V₀ : Nat.card V₀ = 4 := by
  refine card_subOfList (by decide) fun x hx => ?_
  simp only [listV, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  exacts [⟨1, E_one⟩, ⟨v1, E_v1⟩, ⟨l₀ * v1 * l₀⁻¹, by rw [E_conj_l₀, E_v1]; decide⟩,
    ⟨l₀⁻¹ * v1 * l₀, by rw [E_inv_conj_l₀, E_v1]; decide⟩]

private theorem card_U₀ : Nat.card U₀ = 4 := by
  refine card_subOfList (by decide) fun x hx => ?_
  simp only [listU, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  exacts [⟨1, E_one⟩, ⟨u1, E_u1⟩, ⟨l₀ * u1 * l₀⁻¹, by rw [E_conj_l₀, E_u1]; decide⟩,
    ⟨l₀⁻¹ * u1 * l₀, by rw [E_inv_conj_l₀, E_u1]; decide⟩]

private theorem sq_of_mem_subOfList {l : List B9} {h1 : one9 ∈ l}
    {hmul : ∀ x ∈ l, ∀ y ∈ l, x.mul y ∈ l} {hsq : ∀ x ∈ l, x.mul x = one9} {g : GL32}
    (hg : g ∈ subOfList l h1 hmul hsq) : g ^ 2 = 1 :=
  E_injective (by rw [sq, E_mul, E_one]; exact hsq _ hg)

private theorem mem_normalizer_subOfList {l : List B9} {h1 : one9 ∈ l}
    {hmul : ∀ x ∈ l, ∀ y ∈ l, x.mul y ∈ l} {hsq : ∀ x ∈ l, x.mul x = one9} {g : GL32}
    (hg : ∀ x ∈ l, ((E g).mul x).mul (E g⁻¹) ∈ l)
    (hg' : ∀ x ∈ l, ((E g⁻¹).mul x).mul (E g) ∈ l) :
    g ∈ normalizer (subOfList l h1 hmul hsq : Set GL32) := by
  refine mem_normalizer_iff.2 fun s => ⟨fun hs => ?_, fun hs => ?_⟩
  · change E (g * s * g⁻¹) ∈ l
    rw [E_conj]
    exact hg _ hs
  · have := hg' _ hs
    rwa [← E_mul, ← E_mul, show g⁻¹ * (g * s * g⁻¹) * g = s by group] at this

private theorem eq_of_le_subOfList {l : List B9} {h1 : one9 ∈ l}
    {hmul : ∀ x ∈ l, ∀ y ∈ l, x.mul y ∈ l} {hsq : ∀ x ∈ l, x.mul x = one9}
    (hcyc : ∀ q ∈ l, q ≠ one9 → ∀ r ∈ l, r = one9 ∨ r = q ∨ r = cl q ∨ r = cli q)
    {S : Subgroup GL32} (hle : S ≤ subOfList l h1 hmul hsq) (hne : S ≠ ⊥)
    (hl : l₀ ∈ normalizer (S : Set GL32)) : S = subOfList l h1 hmul hsq := by
  obtain ⟨⟨s, hs⟩, hs1⟩ := ne_bot_iff_exists_ne_one.1 hne
  have hs1' : E s ≠ one9 := fun h => hs1 (Subtype.ext (E_injective (h.trans E_one.symm)))
  refine le_antisymm hle fun r hr => ?_
  rcases hcyc _ (hle hs) hs1' _ hr with h | h | h | h
  · rw [E_injective (h.trans E_one.symm)]
    exact one_mem S
  · rw [E_injective h]
    exact hs
  · rw [E_injective (h.trans (E_conj_l₀ s).symm)]
    exact (mem_normalizer_iff.1 hl s).1 hs
  · rw [E_injective (h.trans (E_inv_conj_l₀ s).symm)]
    exact (mem_normalizer_iff''.1 hl s).1 hs

private theorem l₀_mem_normalizer_V₀ : l₀ ∈ normalizer (V₀ : Set GL32) :=
  mem_normalizer_subOfList (by rw [E_l₀, E_l₀_inv]; decide) (by rw [E_l₀, E_l₀_inv]; decide)

private theorem l₀_mem_normalizer_U₀ : l₀ ∈ normalizer (U₀ : Set GL32) :=
  mem_normalizer_subOfList (by rw [E_l₀, E_l₀_inv]; decide) (by rw [E_l₀, E_l₀_inv]; decide)

private theorem tL_mem_normalizer_V₀ : tL ∈ normalizer (V₀ : Set GL32) :=
  mem_normalizer_subOfList (by rw [E_tL, E_tL_inv]; decide) (by rw [E_tL, E_tL_inv]; decide)

private theorem tL_mem_normalizer_U₀ : tL ∈ normalizer (U₀ : Set GL32) :=
  mem_normalizer_subOfList (by rw [E_tL, E_tL_inv]; decide) (by rw [E_tL, E_tL_inv]; decide)

private theorem v1_mem_V₀ : v1 ∈ V₀ := show E v1 ∈ listV by rw [E_v1]; decide

private theorem u1_mem_U₀ : u1 ∈ U₀ := show E u1 ∈ listU by rw [E_u1]; decide

private theorem u1_not_mem_normalizer_V₀ : u1 ∉ normalizer (V₀ : Set GL32) := fun h => by
  have := (mem_normalizer_iff.1 h v1).1 v1_mem_V₀
  change E (u1 * v1 * u1⁻¹) ∈ listV at this
  rw [E_conj, E_u1, E_v1, E_u1_inv] at this
  revert this
  decide

private theorem v1_not_mem_normalizer_U₀ : v1 ∉ normalizer (U₀ : Set GL32) := fun h => by
  have := (mem_normalizer_iff.1 h u1).1 u1_mem_U₀
  change E (v1 * u1 * v1⁻¹) ∈ listU at this
  rw [E_conj, E_v1, E_u1, E_v1_inv] at this
  revert this
  decide

private theorem le_or_le_of_forall_mem {G : Type*} [Group G] {S A B : Subgroup G}
    (h : ∀ s ∈ S, s ∈ A ∨ s ∈ B) : S ≤ A ∨ S ≤ B := by
  by_contra hc
  rw [not_or, IsConcreteLE.not_le_iff_exists, IsConcreteLE.not_le_iff_exists] at hc
  obtain ⟨⟨a, haS, haA⟩, ⟨b, hbS, hbB⟩⟩ := hc
  have haB := (h a haS).resolve_left haA
  have hbA := (h b hbS).resolve_right hbB
  rcases h (a * b) (mul_mem haS hbS) with hab | hab
  · exact haA (by simpa using mul_mem hab (inv_mem hbA))
  · exact hbB (by simpa using mul_mem (inv_mem haB) hab)

private theorem le_V₀_or_le_U₀ {S : Subgroup GL32} (hS : ∀ g ∈ S, g ^ 8 = 1)
    (hl : l₀ ∈ normalizer (S : Set GL32)) : S ≤ V₀ ∨ S ≤ U₀ := by
  refine le_or_le_of_forall_mem fun s hs => ?_
  have h1 : l₀ * s * l₀⁻¹ ∈ S := (mem_normalizer_iff.1 hl s).1 hs
  have h2 : l₀⁻¹ * s * l₀ ∈ S := (mem_normalizer_iff''.1 hl s).1 hs
  have h7 : l₀ * s ^ 7 * l₀⁻¹ ∈ S := (mem_normalizer_iff.1 hl _).1 (pow_mem hs 7)
  have k1 : (E s).p8 = one9 := by rw [← E_pow_eight, hS s hs, E_one]
  have k2 : (((E s).mul (cl (E s))).mul (cli (E s))).p8 = one9 := by
    rw [← E_one, ← hS _ (mul_mem (mul_mem hs h1) h2), E_pow_eight, E_mul, E_mul, E_conj_l₀,
      E_inv_conj_l₀]
  have k3 : ((E s).mul (cl (E s).p7)).p8 = one9 := by
    rw [← E_one, ← hS _ (mul_mem hs h7), E_pow_eight, E_mul, E_conj_l₀, E_pow_seven]
  exact check_split' k1 k2 k3

private theorem eq_V₀_of_le {S : Subgroup GL32} (hle : S ≤ V₀) (hne : S ≠ ⊥)
    (hl : l₀ ∈ normalizer (S : Set GL32)) : S = V₀ :=
  eq_of_le_subOfList (by decide) hle hne hl

private theorem eq_U₀_of_le {S : Subgroup GL32} (hle : S ≤ U₀) (hne : S ≠ ⊥)
    (hl : l₀ ∈ normalizer (S : Set GL32)) : S = U₀ :=
  eq_of_le_subOfList (by decide) hle hne hl

theorem l₀_pow_three : l₀ ^ 3 = 1 :=
  E_injective (by rw [pow_succ, pow_succ, pow_one, E_mul, E_mul, E_l₀, E_one]; decide)

theorem orderOf_l₀ : orderOf l₀ = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime l₀_pow_three fun h => absurd (congrArg E h) (by rw [E_l₀, E_one]; decide)

theorem tL_conj_l₀ : tL * l₀ * tL⁻¹ = l₀⁻¹ :=
  E_injective (by rw [E_conj, E_tL, E_l₀, E_tL_inv, E_l₀_inv]; decide)

theorem tL_mem_normalizer_zpowers : tL ∈ normalizer ((zpowers l₀ : Subgroup GL32) : Set GL32) := by
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change zpowers (tL * l₀ * tL⁻¹) = zpowers l₀
  rw [tL_conj_l₀, zpowers_inv]

theorem eq_one_of_commute_l₀ {s : GL32} (hs : s * l₀ = l₀ * s) (hs2 : s ^ 2 = 1) : s = 1 := by
  have h1 : (E s).mul l0B = l0B.mul (E s) := by rw [← E_l₀, ← E_mul, ← E_mul, hs]
  have h2 : (E s).mul (E s) = one9 := by rw [← E_mul, ← sq, hs2, E_one]
  exact E_injective ((check_cent' h1 h2).trans E_one.symm)

theorem card_GL : Nat.card GL32 = 168 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem pow_eight_eq_one {g : GL32} {k : ℕ} (h : g ^ 2 ^ k = 1) : g ^ 8 = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h)
  have hdvd : 2 ^ j ∣ 168 := card_GL ▸ hj ▸ orderOf_dvd_natCard g
  have hj3 : j ≤ 3 := by
    by_contra hj3
    have : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at this
  exact orderOf_dvd_iff_pow_eq_one.1 (hj ▸ pow_dvd_pow 2 hj3)

theorem eq_or_eq_top_of_index_seven {G : Type*} [Group G] {N H : Subgroup G}
    (hN : N.index = 7) (hle : N ≤ H) : H = N ∨ H = ⊤ := by
  have h := relIndex_mul_index hle
  rw [hN] at h
  rcases (Nat.dvd_prime (by norm_num)).1 (Dvd.intro_left _ h) with h1 | h7
  · exact Or.inr (index_eq_one.1 h1)
  · rw [h7] at h
    exact Or.inl (le_antisymm (relIndex_eq_one.1 (by omega)) hle)

private theorem index_normalizer_eq_seven {P : Subgroup GL32} (hP : Nat.card P = 4)
    (hl : l₀ ∈ normalizer (P : Set GL32)) (hne : normalizer (P : Set GL32) ≠ ⊤) :
    (normalizer (P : Set GL32)).index = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hPS⟩ := (IsPGroup.of_card (p := 2) (n := 2) (by rw [hP]; norm_num)).exists_le_sylow
  have h8 : 2 ^ 3 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (by rw [card_GL]; norm_num)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 S.isPGroup'
  have hSdvd : Nat.card S ∣ 168 := card_GL ▸ (S : Subgroup GL32).card_subgroup_dvd_card
  have hS8 : Nat.card S = 8 := by
    rw [hk] at h8 hSdvd ⊢
    have : k < 8 := by
      by_contra hk8
      have := Nat.le_of_dvd (by norm_num) hSdvd
      have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> revert h8 hSdvd <;> norm_num
  have hrel : P.relIndex S = 2 := by
    have := relIndex_mul_card P S
    rw [inf_eq_left.2 hPS, hP, hS8] at this
    omega
  have : (P.subgroupOf S).Normal := normal_of_index_eq_two hrel
  have h8N : 8 ∣ Nat.card (normalizer (P : Set GL32)) :=
    hS8 ▸ card_dvd_of_le (le_normalizer_of_normal_subgroupOf hPS)
  have h3N : 3 ∣ Nat.card (normalizer (P : Set GL32)) := by
    have := orderOf_dvd_natCard (⟨l₀, hl⟩ : normalizer (P : Set GL32))
    rwa [Subgroup.orderOf_mk, orderOf_l₀] at this
  have hNdvd : Nat.card (normalizer (P : Set GL32)) ∣ 168 :=
    card_GL ▸ card_subgroup_dvd_card _
  have hNne : Nat.card (normalizer (P : Set GL32)) ≠ 168 :=
    fun h => hne ((card_eq_iff_eq_top _).1 (h.trans card_GL.symm))
  obtain ⟨m, hm⟩ : 24 ∣ Nat.card (normalizer (P : Set GL32)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8N h3N
  have hm7 : m ∣ 7 := by
    rw [hm, show (168 : ℕ) = 24 * 7 by norm_num] at hNdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hNdvd
  have h24 : Nat.card (normalizer (P : Set GL32)) = 24 := by
    rcases (Nat.dvd_prime (by norm_num)).1 hm7 with rfl | rfl <;> omega
  have := card_mul_index (normalizer (P : Set GL32))
  rw [h24, card_GL] at this
  omega

abbrev τ : MulAut GL32 := CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 (ZMod 2)

private theorem E_τ (g : GL32) : E (τ g) = (E g⁻¹).tr := by
  rw [E, CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut_matrix]
  rfl

theorem τ_l₀ : τ l₀ = l₀ := E_injective (by rw [E_τ, E_l₀_inv, E_l₀]; decide)

private theorem τ_v1 : τ v1 = u1 := E_injective (by rw [E_τ, E_v1_inv, E_u1]; decide)

private theorem τ_u1 : τ u1 = v1 := E_injective (by rw [E_τ, E_u1_inv, E_v1]; decide)

structure Pair (P Q : Subgroup GL32) : Prop where
  sq : ∀ g ∈ Q, g ^ 2 = 1
  card : Nat.card Q = 4
  l₀_mem : l₀ ∈ normalizer (Q : Set GL32)
  tL_mem : tL ∈ normalizer (Q : Set GL32)
  not_le : ¬ Q ≤ normalizer (P : Set GL32)
  index : (normalizer (P : Set GL32)).index = 7
  min : ∀ S ≤ Q, S ≠ ⊥ → l₀ ∈ normalizer (S : Set GL32) → S = Q
  split : ∀ S : Subgroup GL32, (∀ g ∈ S, g ^ 8 = 1) → l₀ ∈ normalizer (S : Set GL32) →
    S ≤ P ∨ S ≤ Q
  tau : ∃ p ∈ P, τ p ∉ normalizer (P : Set GL32)

private theorem pair_V₀_U₀ : Pair V₀ U₀ where
  sq _ hg := sq_of_mem_subOfList hg
  card := card_U₀
  l₀_mem := l₀_mem_normalizer_U₀
  tL_mem := tL_mem_normalizer_U₀
  not_le h := u1_not_mem_normalizer_V₀ (h u1_mem_U₀)
  index := index_normalizer_eq_seven card_V₀ l₀_mem_normalizer_V₀
    fun h => u1_not_mem_normalizer_V₀ (h ▸ mem_top u1)
  min _ hle hne hl := eq_U₀_of_le hle hne hl
  split _ hS hl := le_V₀_or_le_U₀ hS hl
  tau := ⟨v1, v1_mem_V₀, τ_v1 ▸ u1_not_mem_normalizer_V₀⟩

private theorem pair_U₀_V₀ : Pair U₀ V₀ where
  sq _ hg := sq_of_mem_subOfList hg
  card := card_V₀
  l₀_mem := l₀_mem_normalizer_V₀
  tL_mem := tL_mem_normalizer_V₀
  not_le h := v1_not_mem_normalizer_U₀ (h v1_mem_V₀)
  index := index_normalizer_eq_seven card_U₀ l₀_mem_normalizer_U₀
    fun h => v1_not_mem_normalizer_U₀ (h ▸ mem_top v1)
  min _ hle hne hl := eq_V₀_of_le hle hne hl
  split _ hS hl := (le_V₀_or_le_U₀ hS hl).symm
  tau := ⟨u1, u1_mem_U₀, τ_u1 ▸ v1_not_mem_normalizer_U₀⟩

theorem exists_pair {P : Subgroup GL32} (hsq : ∀ g ∈ P, g ^ 2 = 1) (hP : Nat.card P = 4)
    (hl : l₀ ∈ normalizer (P : Set GL32)) : ∃ Q, Pair P Q := by
  have h8 : ∀ g ∈ P, g ^ 8 = 1 := fun g hg => by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, hsq g hg, one_pow]
  rcases le_V₀_or_le_U₀ h8 hl with h | h
  · obtain rfl : P = V₀ := eq_of_le_of_card_ge h (by rw [card_V₀, hP])
    exact ⟨U₀, pair_V₀_U₀⟩
  · obtain rfl : P = U₀ := eq_of_le_of_card_ge h (by rw [card_U₀, hP])
    exact ⟨V₀, pair_U₀_V₀⟩

theorem exists_conj_mem_zpowers {l : GL32} (hl : l ^ 3 = 1) :
    ∃ g : GL32, g * l * g⁻¹ ∈ zpowers l₀ := by
  by_cases hl1 : l = 1
  · exact ⟨1, by simp [hl1]⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : ∀ y : GL32, orderOf y = 3 → ¬ 3 ∣ (zpowers y).index := fun y hy h => by
    have := card_mul_index (zpowers y)
    rw [Nat.card_zpowers, hy, card_GL] at this
    omega
  have hp : ∀ y : GL32, orderOf y = 3 → IsPGroup 3 (zpowers y) := fun y hy =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hol : orderOf l = 3 := orderOf_eq_prime hl hl1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GL32 ((hp l hol).toSylow (hsyl l hol))
    ((hp l₀ orderOf_l₀).toSylow (hsyl l₀ orderOf_l₀))
  refine ⟨g, ?_⟩
  have h := smul_mem_pointwise_smul l (MulAut.conj g)
    (((hp l hol).toSylow (hsyl l hol) : Sylow 3 GL32) : Subgroup GL32) (by simp)
  rw [← Sylow.coe_subgroup_smul, hg] at h
  simpa [MulAut.smul_def] using h

noncomputable def pslEquiv : PSL(3, ZMod 2) ≃* GL32 :=
  ((QuotientGroup.quotientMulEquivOfEq (by
      rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
      exact scalars_zmod_two 3)).trans QuotientGroup.quotientBot).trans (slEquivGL 3)

theorem innConj_injective : Function.Injective (MulAut.conj : GL32 →* MulAut GL32) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ center GL32 := mem_center_iff.2 fun h => by
    have := congrArg (fun φ : MulAut GL32 => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc h * g = g * h * g⁻¹ * g := by rw [this]
      _ = g * h := by group
  rwa [center_GL32, mem_bot] at hc

abbrev Inn : Subgroup (MulAut GL32) := (MulAut.conj : GL32 →* MulAut GL32).range

theorem mem_Inn {α : MulAut GL32} : α ∈ Inn ↔ ∃ g, MulAut.conj g = α := MonoidHom.mem_range

private theorem τ_not_mem_Inn : τ ∉ Inn := fun ⟨s, hs⟩ => glGraphAut_ne_conj s hs.symm

theorem τ_mul_τ : τ * τ = 1 := by
  rw [← sq]
  exact CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut_sq 3 (ZMod 2)

theorem mem_Inn_or (α : MulAut GL32) : α ∈ Inn ∨ α * τ ∈ Inn := by
  rcases aut_GL32_cases α with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exact Or.inl ⟨s, rfl⟩
  · exact Or.inr ⟨s, by rw [mul_assoc, τ_mul_τ, mul_one]⟩

theorem index_Inn : Inn.index = 2 := by
  refine index_eq_two_iff.2 ⟨τ, fun b => ?_⟩
  rcases mem_Inn_or b with h | h
  · exact Or.inr ⟨h, fun h' => τ_not_mem_Inn (by simpa using mul_mem (inv_mem h) h')⟩
  · exact Or.inl ⟨h, fun h' => τ_not_mem_Inn (by simpa using mul_mem (inv_mem h') h)⟩

theorem aut_mul_conj (α : MulAut GL32) (g : GL32) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) :=
  MulEquiv.ext fun h => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]

theorem eq_one_of_mem_center_aut {α : MulAut GL32} (hα : α ∈ center (MulAut GL32)) :
    α = 1 := by
  refine MulEquiv.ext fun g => ?_
  rw [MulAut.one_apply]
  apply innConj_injective
  rw [← aut_mul_conj, ← mem_center_iff.1 hα (MulAut.conj g), mul_inv_cancel_right]

end CFSG.LocalAnalysis.RankThreeTheoremC.L32Insp
