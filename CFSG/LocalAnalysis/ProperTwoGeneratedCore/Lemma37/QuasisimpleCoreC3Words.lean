module

public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.Group

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {H : Type*} [Group H]

structure C3Relations (a b c d e f : H) : Prop where
  a_sq : a * a = 1
  b_sq : b * b = 1
  c_sq : c * c = 1
  d_sq : d * d = 1
  e_sq : e * e = 1
  f_sq : f * f = 1
  ab : Commute a b
  ac : Commute a c
  ad : Commute a d
  bc : Commute b c
  bd : Commute b d
  cd : Commute c d
  ef : Commute e f
  ea : e * a * e⁻¹ = a
  eb : e * b * e⁻¹ = a * b
  ec : e * c * e⁻¹ = c
  ed : e * d * e⁻¹ = c * d
  fa : f * a * f⁻¹ = c
  fb : f * b * f⁻¹ = d
  fc : f * c * f⁻¹ = a
  fd : f * d * f⁻¹ = b

@[expose] def c3WordW (a b c d : H) (i j k l : ℕ) : H := a ^ i * b ^ j * c ^ k * d ^ l

@[expose] def c3Word (a b c d e f : H) (v : Fin 64) : H :=
  a ^ (v.val / 32 % 2) * b ^ (v.val / 16 % 2) * c ^ (v.val / 8 % 2) * d ^ (v.val / 4 % 2) *
    e ^ (v.val / 2 % 2) * f ^ (v.val % 2)

theorem pow_mod_two_of_mul_self {x : H} (hx : x * x = 1) (n : ℕ) : x ^ n = x ^ (n % 2) := by
  conv_lhs => rw [← Nat.mod_add_div n 2, pow_add, pow_mul, pow_two, hx, one_pow, mul_one]

theorem c3Word_eq {a b c d e f : H} (v : Fin 64) :
    c3Word a b c d e f v = c3WordW a b c d (v.val / 32 % 2) (v.val / 16 % 2) (v.val / 8 % 2)
      (v.val / 4 % 2) * e ^ (v.val / 2 % 2) * f ^ (v.val % 2) := by
  simp only [c3Word, c3WordW]

theorem c3Word_of_digits {a b c d e f : H} {v : Fin 64} {A B C D E F : ℕ} (hA : A < 2)
    (hB : B < 2) (hC : C < 2)
    (hD : D < 2) (hE : E < 2) (hF : F < 2)
    (hv : v.val = 32 * A + 16 * B + 8 * C + 4 * D + 2 * E + F) :
    c3Word a b c d e f v = c3WordW a b c d A B C D * e ^ E * f ^ F := by
  rw [c3Word_eq, hv]
  have hA' := hA
  have h1 : (32 * A + 16 * B + 8 * C + 4 * D + 2 * E + F) / 32 % 2 = A := by omega
  have h2 : (32 * A + 16 * B + 8 * C + 4 * D + 2 * E + F) / 16 % 2 = B := by omega
  have h3 : (32 * A + 16 * B + 8 * C + 4 * D + 2 * E + F) / 8 % 2 = C := by omega
  have h4 : (32 * A + 16 * B + 8 * C + 4 * D + 2 * E + F) / 4 % 2 = D := by omega
  have h5 : (32 * A + 16 * B + 8 * C + 4 * D + 2 * E + F) / 2 % 2 = E := by omega
  have h6 : (32 * A + 16 * B + 8 * C + 4 * D + 2 * E + F) % 2 = F := by omega
  rw [h1, h2, h3, h4, h5, h6]

namespace C3Relations

variable {a b c d e f : H} (h : C3Relations a b c d e f)
include h

theorem wordW_mul_wordW (i j k l i' j' k' l' : ℕ) :
    c3WordW a b c d i j k l * c3WordW a b c d i' j' k' l' =
      c3WordW a b c d (i + i') (j + j') (k + k') (l + l') := by
  simp only [c3WordW]
  have h1 : Commute (b ^ j * c ^ k * d ^ l) (a ^ i') :=
    ((h.ab.symm.pow_pow _ _).mul_left (h.ac.symm.pow_pow _ _)).mul_left
      (h.ad.symm.pow_pow _ _)
  have h2 : Commute (c ^ k * d ^ l) (b ^ j') :=
    (h.bc.symm.pow_pow _ _).mul_left (h.bd.symm.pow_pow _ _)
  have h3 : Commute (d ^ l) (c ^ k') := h.cd.symm.pow_pow _ _
  calc a ^ i * b ^ j * c ^ k * d ^ l * (a ^ i' * b ^ j' * c ^ k' * d ^ l') =
        a ^ i * ((b ^ j * c ^ k * d ^ l) * a ^ i') * b ^ j' * c ^ k' * d ^ l' := by group
    _ = a ^ i * (a ^ i' * (b ^ j * c ^ k * d ^ l)) * b ^ j' * c ^ k' * d ^ l' := by rw [h1.eq]
    _ = a ^ (i + i') * b ^ j * ((c ^ k * d ^ l) * b ^ j') * c ^ k' * d ^ l' := by
        rw [pow_add]; group
    _ = a ^ (i + i') * b ^ j * (b ^ j' * (c ^ k * d ^ l)) * c ^ k' * d ^ l' := by rw [h2.eq]
    _ = a ^ (i + i') * b ^ (j + j') * c ^ k * (d ^ l * c ^ k') * d ^ l' := by
        rw [pow_add]; group
    _ = a ^ (i + i') * b ^ (j + j') * c ^ k * (c ^ k' * d ^ l) * d ^ l' := by rw [h3.eq]
    _ = a ^ (i + i') * b ^ (j + j') * c ^ (k + k') * d ^ (l + l') := by
        rw [pow_add, pow_add]; group

theorem wordW_mod (i j k l : ℕ) :
    c3WordW a b c d i j k l = c3WordW a b c d (i % 2) (j % 2) (k % 2) (l % 2) := by
  simp only [c3WordW]
  rw [pow_mod_two_of_mul_self h.a_sq i, pow_mod_two_of_mul_self h.b_sq j,
    pow_mod_two_of_mul_self h.c_sq k, pow_mod_two_of_mul_self h.d_sq l]

theorem wordW_mul (i j k l i' j' k' l' : ℕ) :
    c3WordW a b c d i j k l * c3WordW a b c d i' j' k' l' =
      c3WordW a b c d ((i + i') % 2) ((j + j') % 2) ((k + k') % 2) ((l + l') % 2) := by
  rw [h.wordW_mul_wordW, h.wordW_mod]

theorem conj_e_wordW (i j k l : ℕ) :
    e * c3WordW a b c d i j k l * e⁻¹ = c3WordW a b c d (i + j) j (k + l) l := by
  have hconj : e * c3WordW a b c d i j k l * e⁻¹ =
      (e * a * e⁻¹) ^ i * (e * b * e⁻¹) ^ j * (e * c * e⁻¹) ^ k * (e * d * e⁻¹) ^ l := by
    simp only [c3WordW, ← MulAut.conj_apply, map_mul, map_pow]
  have h' := h.wordW_mul_wordW i 0 k 0 j j l l
  rw [zero_add, zero_add] at h'
  rw [hconj, h.ea, h.eb, h.ec, h.ed, h.ab.mul_pow, h.cd.mul_pow, ← h']
  simp only [c3WordW, pow_zero, mul_one]
  have hc : Commute (a ^ j * b ^ j) (c ^ k) :=
    ((h.ac.pow_pow _ _).mul_left (h.bc.pow_pow _ _))
  calc a ^ i * (a ^ j * b ^ j) * c ^ k * (c ^ l * d ^ l) =
        a ^ i * ((a ^ j * b ^ j) * c ^ k) * (c ^ l * d ^ l) := by group
    _ = a ^ i * (c ^ k * (a ^ j * b ^ j)) * (c ^ l * d ^ l) := by rw [hc.eq]
    _ = a ^ i * c ^ k * (a ^ j * b ^ j * c ^ l * d ^ l) := by group

theorem conj_f_wordW (i j k l : ℕ) :
    f * c3WordW a b c d i j k l * f⁻¹ = c3WordW a b c d k l i j := by
  have hconj : f * c3WordW a b c d i j k l * f⁻¹ =
      (f * a * f⁻¹) ^ i * (f * b * f⁻¹) ^ j * (f * c * f⁻¹) ^ k * (f * d * f⁻¹) ^ l := by
    simp only [c3WordW, ← MulAut.conj_apply, map_mul, map_pow]
  rw [hconj, h.fa, h.fb, h.fc, h.fd]
  have h' := h.wordW_mul_wordW 0 0 i j k l 0 0
  simp only [c3WordW, pow_zero, one_mul, mul_one, zero_add, add_zero] at h'
  simp only [c3WordW]
  rw [← h']
  group

theorem ef_mul_wordW {m n : ℕ} (hm : m < 2) (hn : n < 2) (i j k l : ℕ) :
    e ^ m * f ^ n * c3WordW a b c d i j k l =
      c3WordW a b c d
        (if m = 1 then (if n = 1 then k + l else i + j) else (if n = 1 then k else i))
        (if n = 1 then l else j)
        (if m = 1 then (if n = 1 then i + j else k + l) else (if n = 1 then i else k))
        (if n = 1 then j else l) * e ^ m * f ^ n := by
  have hf : ∀ i j k l : ℕ, f * c3WordW a b c d i j k l = c3WordW a b c d k l i j * f :=
    fun i j k l => by rw [← h.conj_f_wordW i j k l]; group
  have he : ∀ i j k l : ℕ, e * c3WordW a b c d i j k l =
      c3WordW a b c d (i + j) j (k + l) l * e :=
    fun i j k l => by rw [← h.conj_e_wordW i j k l]; group
  have h01 : (0 : ℕ) ≠ 1 := by norm_num
  obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
  · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · simp only [pow_zero, one_mul, mul_one, eq_false h01, ite_false]
    · simp only [pow_zero, pow_one, one_mul, mul_one, eq_false h01, ite_false, ite_true]
      exact hf i j k l
  · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · simp only [pow_zero, pow_one, mul_one, eq_false h01, ite_false, ite_true]
      exact he i j k l
    · simp only [pow_one, ite_true]
      rw [mul_assoc, hf, ← mul_assoc, he]

theorem wordW_ef_mul {i j k l m n i' j' k' l' m' n' : ℕ} (hm : m < 2) (hn : n < 2) :
    c3WordW a b c d i j k l * e ^ m * f ^ n * (c3WordW a b c d i' j' k' l' * e ^ m' * f ^ n') =
      c3WordW a b c d
        ((i + (if m = 1 then (if n = 1 then k' + l' else i' + j') else
          (if n = 1 then k' else i'))) % 2)
        ((j + (if n = 1 then l' else j')) % 2)
        ((k + (if m = 1 then (if n = 1 then i' + j' else k' + l') else
          (if n = 1 then i' else k'))) % 2)
        ((l + (if n = 1 then j' else l')) % 2) * e ^ ((m + m') % 2) * f ^ ((n + n') % 2) := by
  have hfe : f ^ n * e ^ m' = e ^ m' * f ^ n := ((h.ef.pow_pow _ _).symm).eq
  calc c3WordW a b c d i j k l * e ^ m * f ^ n * (c3WordW a b c d i' j' k' l' * e ^ m' * f ^ n')
      = c3WordW a b c d i j k l * (e ^ m * f ^ n * c3WordW a b c d i' j' k' l') * e ^ m' *
          f ^ n' := by group
    _ = c3WordW a b c d i j k l * (c3WordW a b c d
          (if m = 1 then (if n = 1 then k' + l' else i' + j') else (if n = 1 then k' else i'))
          (if n = 1 then l' else j')
          (if m = 1 then (if n = 1 then i' + j' else k' + l') else (if n = 1 then i' else k'))
          (if n = 1 then j' else l')) * e ^ m * (f ^ n * e ^ m') * f ^ n' := by
        rw [h.ef_mul_wordW hm hn]; group
    _ = _ := by
        rw [hfe, h.wordW_mul]
        rw [show ∀ x y z t u : H, x * y * (z * t) * u = x * (y * z) * (t * u) from
          fun _ _ _ _ _ => by group, ← pow_add, ← pow_add, pow_mod_two_of_mul_self h.e_sq,
          pow_mod_two_of_mul_self h.f_sq (n + n')]

end C3Relations

@[expose] def c3Mul (v w : Fin 64) : Fin 64 :=
  ⟨32 * ((v.val / 32 % 2 + (if v.val / 2 % 2 = 1 then
      (if v.val % 2 = 1 then w.val / 8 % 2 + w.val / 4 % 2 else w.val / 32 % 2 + w.val / 16 % 2)
      else (if v.val % 2 = 1 then w.val / 8 % 2 else w.val / 32 % 2))) % 2) +
    16 * ((v.val / 16 % 2 + (if v.val % 2 = 1 then w.val / 4 % 2 else w.val / 16 % 2)) % 2) +
    8 * ((v.val / 8 % 2 + (if v.val / 2 % 2 = 1 then
      (if v.val % 2 = 1 then w.val / 32 % 2 + w.val / 16 % 2 else w.val / 8 % 2 + w.val / 4 % 2)
      else (if v.val % 2 = 1 then w.val / 32 % 2 else w.val / 8 % 2))) % 2) +
    4 * ((v.val / 4 % 2 + (if v.val % 2 = 1 then w.val / 16 % 2 else w.val / 4 % 2)) % 2) +
    2 * ((v.val / 2 % 2 + w.val / 2 % 2) % 2) + (v.val % 2 + w.val % 2) % 2, by omega⟩

namespace C3Relations

variable {a b c d e f : H} (h : C3Relations a b c d e f)
include h

theorem c3Word_mul (v w : Fin 64) :
    c3Word a b c d e f v * c3Word a b c d e f w = c3Word a b c d e f (c3Mul v w) := by
  rw [c3Word_eq, c3Word_eq, h.wordW_ef_mul (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num))]
  exact (c3Word_of_digits (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) rfl).symm

end C3Relations

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
