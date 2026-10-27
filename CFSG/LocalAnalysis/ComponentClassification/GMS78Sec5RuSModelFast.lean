module

public import Certificates.Data.GMS78RuSModelCheck
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GMS78

open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

namespace RuSModel

theorem dPartN_fst_lt (d : Fin 8) (c n : ℕ) : (dPartN d c n).1 < 256 := by
  induction n with
  | zero => simp [dPartN]
  | succ n ih =>
    simp only [dPartN]
    split_ifs
    · exact Nat.xor_lt_two_pow (by simpa using ih)
        (Nat.pow_lt_pow_right (by norm_num) (dMul d (fin8Of n)).isLt)
    · exact ih

theorem dPart_fst_lt (d : Fin 8) (c : ℕ) : (dPart d c).1 < 256 := dPartN_fst_lt d c 8

theorem dPartArr_getD (d : Fin 8) {c : ℕ} (hc : c < 256) :
    dPartArr.getD (256 * d.val + c) (0, 0) = dPart d c := by
  have hi : 256 * d.val + c < 2048 := by omega
  simp only [dPartArr, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hi,
    ite_true, Option.map_some, Option.getD_some]
  congr 1
  · ext; simp [fin8Of]; omega
  · omega

theorem gamArr_getD {c c' : ℕ} (hc : c < 256) (hc' : c' < 256) :
    gamArr.getD (256 * c + c') 0 = gam c c' := by
  have hi : 256 * c + c' < 65536 := by omega
  simp only [gamArr, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hi,
    ite_true, Option.map_some, Option.getD_some]
  congr 1 <;> omega

theorem sMulF_eq (ε : Bool) {p q : ℕ × Fin 8 × Fin 8} (hp : p.1 < 256) (hq : q.1 < 256) :
    sMulF ε p q = sMul ε p q := by
  simp only [sMulF, sMul, dPartArr_getD _ hq, gamArr_getD hp (dPart_fst_lt _ _)]

theorem sMul_fst_lt (ε : Bool) {p : ℕ × Fin 8 × Fin 8} (hp : p.1 < 256)
    (q : ℕ × Fin 8 × Fin 8) : (sMul ε p q).1 < 256 :=
  Nat.xor_lt_two_pow (n := 8) (by simpa using hp) (by simpa using dPart_fst_lt p.2.2 q.1)

@[expose] def s0List : List (Fin 8) := [0, 3, 4, 7]

theorem s0d_mem (j : ℕ) : s0d j ∈ s0List := by
  rcases Nat.lt_or_ge j 4 with hj | hj
  · interval_cases j <;> decide
  · rw [s0d, List.getD_eq_default _ _ (by simpa using hj)]
    decide

theorem dMul_mem_s0 : ∀ d ∈ s0List, ∀ e ∈ s0List, dMul d e ∈ s0List := by decide

theorem s0d_s0dIdx : ∀ d ∈ s0List, s0d (s0dIdx d) = d := by decide

theorem s0dIdx_lt (d : Fin 8) : s0dIdx d < 4 := by
  simp only [s0dIdx]; omega

theorem lift16_fst_lt (p : ℕ) : (lift16 p).1 < 256 := Nat.mod_lt _ (by norm_num)

theorem mul16_eq (ε : Bool) (p q : ℕ) : mul16 ε p q = enc16 (sMul ε (lift16 p) (lift16 q)) := by
  rw [mul16, sMulF_eq ε (lift16_fst_lt p) (lift16_fst_lt q)]

theorem enc16_lt {x : ℕ × Fin 8 × Fin 8} (hx : x.1 < 256) : enc16 x < 2048 := by
  have h1 : x.2.1.val / 4 ≤ 1 := by have := x.2.1.isLt; omega
  have h2 := s0dIdx_lt x.2.2
  simp only [enc16]
  omega

theorem mul16_lt (ε : Bool) (p q : ℕ) : mul16 ε p q < 2048 := by
  rw [mul16_eq]
  exact enc16_lt (sMul_fst_lt ε (lift16_fst_lt p) _)

theorem lift16_enc16 {x : ℕ × Fin 8 × Fin 8} (hx : x.1 < 256) (hd : x.2.2 ∈ s0List) :
    lift16 (enc16 x) = (x.1, fin8Of (4 * (x.2.1.val / 4)), x.2.2) := by
  have h1 : x.2.1.val / 4 ≤ 1 := by have := x.2.1.isLt; omega
  have h2 := s0dIdx_lt x.2.2
  simp only [lift16, enc16]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only; omega
  · simp only
    congr 2
    omega
  · simp only
    rw [show (x.1 + 256 * (x.2.1.val / 4) + 512 * s0dIdx x.2.2) / 512 = s0dIdx x.2.2 by omega]
    exact s0d_s0dIdx _ hd

theorem enc16_lift16 {p : ℕ} (hp : p < 2048) : enc16 (lift16 p) = p := by
  have hs : ∀ j < 4, s0dIdx (s0d j) = j := by decide
  simp only [enc16, lift16]
  rw [hs _ (by omega)]
  have : (fin8Of (4 * (p / 256 % 2))).val / 4 = p / 256 % 2 := by
    simp only [fin8Of]
    omega
  rw [this]
  omega

theorem lift16_snd_mem (p : ℕ) : (lift16 p).2.2 ∈ s0List := s0d_mem _

theorem lift16_code (p : ℕ) : (lift16 p).2.1 = 0 ∨ (lift16 p).2.1 = 4 := by
  simp only [lift16, fin8Of]
  rcases Nat.mod_two_eq_zero_or_one (p / 256) with h | h <;> rw [h] <;> decide

theorem check16_spec {ε : Bool} (h : check16 ε = true) :
    (∀ u ∈ inv16 ε, ∀ v ∈ inv16 ε, (cent16 ε u).length = (cent16 ε v).length →
      cntR16 ε (cent16 ε u) u = cntR16 ε (cent16 ε v) 256 →
      cntR16 ε (cent16 ε u) 256 = cntR16 ε (cent16 ε v) v → (cent16 ε u).length = 128) ∧
    (∀ u ∈ inv16 ε, (cent16 ε u).length = 128 → conjSq16 ε u = true) ∧
    (∀ p < 2048, mul16 ε 256 (mul16 ε p p) / 512 = 0) ∧
    (∀ u ∈ inv16 ε, u / 512 = 0 → (cent16 ε u).length ≠ 128) ∧
    (∀ p < 2048, mul16 ε p 256 = mul16 ε 256 p) := by
  simp only [check16, Bool.and_eq_true, List.all_eq_true, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, key16, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_iff_eq, bne_iff_ne, ne_eq, List.mem_range, Nat.div_eq_zero_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun u hu v hv e1 e2 e3 => ?_, fun u hu e => ?_, fun p hp => ?_, fun u hu e => ?_, h5⟩
  · rcases h1 u hu v hv with ((h | h) | h) | h
    · exact absurd e1 (by simpa using h)
    · exact absurd e2 (by simpa using h)
    · exact absurd e3 (by simpa using h)
    · exact h
  · rcases h2 u hu with h | h
    · exact absurd e h
    · exact h
  · have := h3 p hp
    omega
  · rcases h4 u hu with h | h
    · omega
    · exact h

theorem lift17_fst_lt (p : ℕ) : (lift17 p).1 < 256 := Nat.mod_lt _ (by norm_num)

theorem mul17_eq (ε : Bool) (p q : ℕ) : mul17 ε p q = enc17 (sMul ε (lift17 p) (lift17 q)) := by
  rw [mul17, sMulF_eq ε (lift17_fst_lt p) (lift17_fst_lt q)]

theorem enc17_lt {x : ℕ × Fin 8 × Fin 8} (hx : x.1 < 256) : enc17 x < 8192 := by
  have h1 : x.2.1.val / 2 ≤ 3 := by have := x.2.1.isLt; omega
  have h2 := x.2.2.isLt
  simp only [enc17]
  omega

theorem mul17_lt (ε : Bool) (p q : ℕ) : mul17 ε p q < 8192 := by
  rw [mul17_eq]
  exact enc17_lt (sMul_fst_lt ε (lift17_fst_lt p) _)

theorem lift17_enc17 {x : ℕ × Fin 8 × Fin 8} (hx : x.1 < 256) :
    lift17 (enc17 x) = (x.1, fin8Of (2 * (x.2.1.val / 2)), x.2.2) := by
  have h1 : x.2.1.val / 2 ≤ 3 := by have := x.2.1.isLt; omega
  have h2 := x.2.2.isLt
  simp only [lift17, enc17]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only; omega
  · simp only
    congr 2
    omega
  · simp only
    ext
    simp only [fin8Of]
    omega

theorem enc17_lift17 {p : ℕ} (hp : p < 8192) : enc17 (lift17 p) = p := by
  simp only [enc17, lift17, fin8Of]
  omega

theorem lift17_code (p : ℕ) : (lift17 p).2.1.val % 2 = 0 := by
  simp only [lift17, fin8Of]
  omega

theorem check17_spec {ε : Bool} (h : check17 ε = true) :
    (∀ p < 8192, mul17 ε p 256 = mul17 ε 256 p) ∧
    ∀ u ∈ inv17 ε, inX17 u = false → ∀ v ∈ inv17 ε,
      (cent17 ε u).length = (cent17 ε v).length →
      cntR17 ε (cent17 ε u) u = cntR17 ε (cent17 ε v) 256 →
      cntR17 ε (cent17 ε u) 256 = cntR17 ε (cent17 ε v) v →
      ((cent17 ε u).length = 128 ∧ (u / 1024 = 1 ∨ u / 1024 = 5)) ∨
      (zx17 ε (cent17 ε u) u ≠ zx17 ε (cent17 ε v) 256 ∨
        zx17 ε (cent17 ε u) 256 ≠ zx17 ε (cent17 ε v) v) := by
  simp only [check17, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, key17, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_iff_eq, bne_iff_ne, ne_eq, Bool.and_eq_true, List.mem_range] at h
  obtain ⟨h0, h⟩ := h
  refine ⟨h0, fun u hu hX v hv e1 e2 e3 => ?_⟩
  rcases h u hu with h | h
  · rw [hX] at h
    exact absurd h (by decide)
  · rcases h v hv with (((h | h) | h) | h) | h
    · exact absurd e1 (by simpa using h)
    · exact absurd e2 (by simpa using h)
    · exact absurd e3 (by simpa using h)
    · exact Or.inl h
    · obtain ⟨⟨hu', hv'⟩, hz⟩ := h
      right
      simp only [hu', hv', ite_true] at hz
      exact hz

end RuSModel

end CFSG.ComponentClassification.GMS78
