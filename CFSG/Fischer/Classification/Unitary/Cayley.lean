module

public import CFSG.Fischer.Classification.Unitary.Basic
public import CFSG.Fischer.Classification.Uniqueness.Star
import all CFSG.Fischer.F4

public section

namespace CFSG.Fischer.Classification.Unitary

open Matrix CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

theorem trace_frob_mul_eq_zero_iff_of_trace {a a' : K} (ha : a + frob a = 1)
    (ha' : a' + frob a' = 1) : frob a * a' + frob (frob a * a') = 0 ↔ a = a' := by
  obtain ⟨a, rfl⟩ := eF4.surjective a
  obtain ⟨a', rfl⟩ := eF4.surjective a'
  simp only [frob_eF4, ← map_mul, ← map_add, ← map_zero eF4, ← map_one eF4, eF4_inj] at ha ha' ⊢
  revert a a'
  decide

theorem trace_frob_mul_eq_zero_iff {l l' : K} (hl : l ≠ 0) (hl' : l' ≠ 0) :
    frob l * l' + frob (frob l * l') = 0 ↔ l = l' := by
  obtain ⟨l, rfl⟩ := eF4.surjective l
  obtain ⟨l', rfl⟩ := eF4.surjective l'
  rw [Ne, ← map_zero eF4, eF4_inj] at hl hl'
  simp only [frob_eF4, ← map_mul, ← map_add, ← map_zero eF4, eF4_inj]
  revert l l'
  decide

theorem eq_add_one_of_trace {a a' : K} (ha : a + frob a = 1) (ha' : a' + frob a' = 1)
    (h : a' ≠ a) : a' = a + 1 := by
  obtain ⟨a, rfl⟩ := eF4.surjective a
  obtain ⟨a', rfl⟩ := eF4.surjective a'
  simp only [frob_eF4, ← map_add, ← map_one eF4, eF4_inj, Ne] at ha ha' h ⊢
  revert a a'
  decide

theorem trace_add_one {a : K} (ha : a + frob a = 1) : (a + 1) + frob (a + 1) = 1 := by
  rw [map_add, map_one, add_add_add_comm, ha, add_self_K, add_zero]

theorem add_one_ne_self (a : K) : a + 1 ≠ a := by
  intro h
  have h' : a + 1 = a + 0 := by rw [add_zero]; exact h
  exact one_ne_zero (add_left_cancel h')

theorem eq_of_add_eq_zero_K {a b : K} (h : a + b = 0) : a = b := by
  rw [← neg_K b]
  exact eq_neg_of_add_eq_zero_left h

theorem exists_ne_ne (l l' : K) : ∃ μ : K, μ ≠ 0 ∧ μ ≠ l ∧ μ ≠ l' := by
  obtain ⟨l, rfl⟩ := eF4.surjective l
  obtain ⟨l', rfl⟩ := eF4.surjective l'
  have : ∀ l l' : F4, ∃ μ : F4, μ ≠ 0 ∧ μ ≠ l ∧ μ ≠ l' := by decide
  obtain ⟨μ, h1, h2, h3⟩ := this l l'
  refine ⟨eF4 μ, ?_, ?_, ?_⟩
  · rwa [Ne, ← map_zero eF4, eF4_inj]
  · rwa [Ne, eF4_inj]
  · rwa [Ne, eF4_inj]

theorem ne_zero_of_trace {a : K} (ha : a + frob a = 1) : a ≠ 0 := by
  rintro rfl
  rw [map_zero, add_zero] at ha
  exact zero_ne_one ha

theorem trace_frob (c : K) : frob c + frob (frob c) = c + frob c := by
  rw [frob_frob, add_comm]

theorem trace_omega : ω + frob ω = 1 := omega_add_frob

theorem trace_frob_omega : frob ω + frob (frob ω) = 1 := by rw [trace_frob, omega_add_frob]

theorem trace_one : (1 : K) + frob 1 = 0 := one_add_frob_one

theorem trace_zero : (0 : K) + frob 0 = 0 := by rw [map_zero, add_zero]

theorem trace_add (c c' : K) : (c + c') + frob (c + c') = (c + frob c) + (c' + frob c') := by
  rw [map_add]
  ring

variable {n : ℕ}

theorem herm_add_self (a b : Fin n → K) :
    herm frob (a + b) (a + b) =
      herm frob a a + herm frob b b + (herm frob a b + frob (herm frob a b)) := by
  rw [herm_add_left, herm_add_right, herm_add_right, herm_conj frob frob_frob a b]
  ring

theorem herm_sub_self (a b : Fin n → K) :
    herm frob (a - b) (a - b) =
      herm frob a a + herm frob b b + (herm frob a b + frob (herm frob a b)) := by
  rw [sub_eq_add_neg, herm_add_self, herm_neg_left, herm_neg_right, neg_neg, herm_neg_right,
    map_neg, neg_K, neg_K]

theorem trace_herm_comm (a b : Fin n → K) :
    herm frob a b + frob (herm frob a b) = herm frob b a + frob (herm frob b a) := by
  rw [herm_conj frob frob_frob a b, frob_frob, add_comm]

theorem herm_smul_self_eq (c : K) (a : Fin n → K) :
    herm frob (c • a) (c • a) = frob c * c * herm frob a a := by
  rw [herm_smul_left, herm_smul_right, mul_assoc]

@[expose] def cayleyGraph (n : ℕ) : SimpleGraph (Fin n → K) where
  Adj y y' := y ≠ y' ∧ herm frob (y' - y) (y' - y) = 0
  symm := ⟨fun y y' h =>
    ⟨h.1.symm, by rw [← neg_sub, herm_neg_left, herm_neg_right, neg_neg]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem cayleyGraph_adj {y y' : Fin n → K} :
    (cayleyGraph n).Adj y y' ↔ y ≠ y' ∧ herm frob (y' - y) (y' - y) = 0 :=
  Iff.rfl

theorem cayleyGraph_adj_zero {v : Fin n → K} :
    (cayleyGraph n).Adj 0 v ↔ v ≠ 0 ∧ herm frob v v = 0 := by
  rw [cayleyGraph_adj, sub_zero, ne_comm]

theorem herm_eq_one_of_not_adj {v : Fin n → K} (hv0 : v ≠ 0)
    (hv : ¬ (cayleyGraph n).Adj 0 v) : herm frob v v = 1 :=
  (herm_self_eq_zero_or_one v).resolve_left fun h => hv (cayleyGraph_adj_zero.2 ⟨hv0, h⟩)

theorem adj_zero_and_adj_iff {v x : Fin n → K} (hv : herm frob v v = 1) :
    ((cayleyGraph n).Adj 0 x ∧ (cayleyGraph n).Adj x v) ↔
      x ≠ 0 ∧ herm frob x x = 0 ∧ herm frob v x + frob (herm frob v x) = 1 := by
  rw [cayleyGraph_adj_zero, cayleyGraph_adj, herm_sub_self, hv]
  constructor
  · rintro ⟨⟨hx0, hx⟩, -, h⟩
    refine ⟨hx0, hx, ?_⟩
    rw [hx, add_zero] at h
    exact (eq_of_add_eq_zero_K h).symm
  · rintro ⟨hx0, hx, h⟩
    refine ⟨⟨hx0, hx⟩, fun e => ?_, ?_⟩
    · rw [e, hv] at hx
      exact one_ne_zero hx
    · rw [hx, h, add_zero, add_self_K]

theorem exists_mid (hn : 2 ≤ n) {v : Fin n → K} (hv : herm frob v v = 1) :
    ∃ x : Fin n → K, x ≠ 0 ∧ herm frob x x = 0 ∧ herm frob v x + frob (herm frob v x) = 1 := by
  obtain ⟨w, hw, hvw⟩ := exists_norm_one_perp isUnitaryInvolution_frob hn hv
  have hvx : herm frob v (ω • (v + w)) = ω := by
    rw [herm_smul_right, herm_add_right, hv, hvw, add_zero, mul_one]
  refine ⟨ω • (v + w), fun h => ?_, ?_, by rw [hvx, trace_omega]⟩
  · rw [h, herm_zero_right] at hvx
    exact omega_ne_zero hvx.symm
  · rw [herm_smul_self_eq, herm_add_self, hv, hw, hvw, trace_zero, add_self_K, add_zero,
      mul_zero]

theorem exists_mid_mid {v w : Fin n → K} (hv : herm frob v v = 1) (hw : herm frob w w = 1)
    (hvw : (cayleyGraph n).Adj v w) :
    ∃ x : Fin n → K, x ≠ 0 ∧ herm frob x x = 0 ∧ herm frob v x + frob (herm frob v x) = 1 ∧
      herm frob w x + frob (herm frob w x) = 1 := by
  have hσ := isUnitaryInvolution_frob
  obtain ⟨hne, hq⟩ := cayleyGraph_adj.1 hvw
  rw [herm_sub_self, hw, hv, add_self_K, zero_add, trace_herm_comm] at hq
  rcases (add_frob_eq_zero_iff _).1 hq with h0 | h1
  ·
    have h0' : herm frob w v = 0 := herm_eq_zero_comm frob frob_frob h0
    have hvx : herm frob v (ω • (v + w)) = ω := by
      rw [herm_smul_right, herm_add_right, hv, h0, add_zero, mul_one]
    have hwx : herm frob w (ω • (v + w)) = ω := by
      rw [herm_smul_right, herm_add_right, hw, h0', zero_add, mul_one]
    refine ⟨ω • (v + w), fun h => ?_, ?_, by rw [hvx, trace_omega], by rw [hwx, trace_omega]⟩
    · rw [h, herm_zero_right] at hvx
      exact omega_ne_zero hvx.symm
    · rw [herm_smul_self_eq, herm_add_self, hv, hw, h0, trace_zero, add_self_K, add_zero,
        mul_zero]
  ·
    set z := w - v with hz
    have hz0 : z ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have hvz : herm frob v z = 0 := by rw [hz, herm_sub_right, h1, hv, sub_self]
    have hzz : herm frob z z = 0 := by
      rw [hz, herm_sub_self, hw, hv, add_self_K, zero_add, trace_herm_comm, h1, trace_one]
    obtain ⟨z', hvz', hz'z', hzz'⟩ := exists_partner_perp hσ hv hz0 hzz hvz
    have hzv : herm frob z v = 0 := herm_eq_zero_comm frob frob_frob hvz
    have hz'z : herm frob z' z = 1 := by rw [herm_conj frob frob_frob, hzz', map_one]
    set y := ω • z + z' with hy
    have hvy : herm frob v y = 0 := by
      rw [hy, herm_add_right, herm_smul_right, hvz, hvz', mul_zero, add_zero]
    have hyy : herm frob y y = 1 := by
      rw [hy, herm_add_self, herm_smul_self_eq, hzz, hz'z', herm_smul_left, hzz', mul_one,
        mul_zero, zero_add, zero_add, trace_frob_omega]
    set x := ω • v + y with hx
    have hvx : herm frob v x = ω := by
      rw [hx, herm_add_right, herm_smul_right, hv, hvy, mul_one, add_zero]
    have hzx : herm frob z x = 1 := by
      rw [hx, hy, herm_add_right, herm_add_right, herm_smul_right, herm_smul_right, hzv, hzz,
        hzz']
      simp
    have hwx : herm frob w x = ω + 1 := by
      rw [show w = v + z by rw [hz]; abel, herm_add_left, hvx, hzx]
    refine ⟨x, fun h => ?_, ?_, by rw [hvx, trace_omega], ?_⟩
    · rw [h, herm_zero_right] at hvx
      exact omega_ne_zero hvx.symm
    · rw [hx, herm_add_self, herm_smul_self_eq, hv, hyy, herm_smul_left, hvy, mul_zero,
        trace_zero, frob_mul_self omega_ne_zero, mul_one, add_self_K, add_zero]
    · rw [hwx, trace_add, trace_omega, trace_one, add_zero]

section Connected

variable {v : Fin n → K} (hv : herm frob v v = 1)

abbrev midSet (v : Fin n → K) : Set (Fin n → K) :=
  {x | (cayleyGraph n).Adj 0 x ∧ (cayleyGraph n).Adj x v}

include hv

theorem mem_midSet {y : Fin n → K} (hvy : herm frob v y = 0) (hy : herm frob y y = 1) {a l : K}
    (ha : a + frob a = 1) (hl : l ≠ 0) : a • v + l • y ∈ midSet v := by
  have hva : herm frob v (a • v + l • y) = a := by
    rw [herm_add_right, herm_smul_right, herm_smul_right, hv, hvy, mul_one, mul_zero, add_zero]
  refine (adj_zero_and_adj_iff hv).2 ⟨fun h => ?_, ?_, by rw [hva, ha]⟩
  · rw [h, herm_zero_right] at hva
    exact ne_zero_of_trace ha hva.symm
  · rw [herm_add_self, herm_smul_self_eq, herm_smul_self_eq, hv, hy, herm_smul_left,
      herm_smul_right, hvy, mul_zero, mul_zero, trace_zero, add_zero, mul_one, mul_one,
      frob_mul_self (ne_zero_of_trace ha), frob_mul_self hl, add_self_K]

theorem herm_combo {y y' : Fin n → K} (hvy : herm frob v y = 0) (hvy' : herm frob v y' = 0)
    (a l a' l' : K) :
    herm frob (a • v + l • y) (a' • v + l' • y') = frob a * a' + frob l * l' * herm frob y y' := by
  have hyv : herm frob y v = 0 := herm_eq_zero_comm frob frob_frob hvy
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hv, hvy', hyv,
    mul_zero, add_zero, zero_add, mul_one]
  ring

theorem adj_combo_iff {y y' : Fin n → K} (hvy : herm frob v y = 0) (hy : herm frob y y = 1)
    (hvy' : herm frob v y' = 0) (hy' : herm frob y' y' = 1) {a l a' l' : K}
    (ha : a + frob a = 1) (hl : l ≠ 0) (ha' : a' + frob a' = 1) (hl' : l' ≠ 0) :
    (cayleyGraph n).Adj (a • v + l • y) (a' • v + l' • y') ↔
      a • v + l • y ≠ a' • v + l' • y' ∧
        (frob a * a' + frob l * l' * herm frob y y') +
          frob (frob a * a' + frob l * l' * herm frob y y') = 0 := by
  have h1 := ((adj_zero_and_adj_iff hv).1 (mem_midSet hv hvy hy ha hl)).2.1
  have h2 := ((adj_zero_and_adj_iff hv).1 (mem_midSet hv hvy' hy' ha' hl')).2.1
  rw [cayleyGraph_adj, herm_sub_self, h1, h2, add_zero, zero_add, trace_herm_comm,
    herm_combo hv hvy hvy']

theorem adj_hexagon {y : Fin n → K} (hvy : herm frob v y = 0) (hy : herm frob y y = 1)
    {a l a' l' : K} (ha : a + frob a = 1) (hl : l ≠ 0) (ha' : a' + frob a' = 1) (hl' : l' ≠ 0)
    (haa : a ≠ a') (hll : l ≠ l') : (cayleyGraph n).Adj (a • v + l • y) (a' • v + l' • y) := by
  rw [adj_combo_iff hv hvy hy hvy hy ha hl ha' hl', hy, mul_one, trace_add]
  refine ⟨fun h => haa ?_, ?_⟩
  · have := congrArg (herm frob v) h
    rwa [herm_add_right, herm_add_right, herm_smul_right, herm_smul_right, herm_smul_right,
      herm_smul_right, hv, hvy, mul_one, mul_one, mul_zero, mul_zero, add_zero, add_zero] at this
  · have t1 := (add_frob_eq_zero_or_one (frob a * a')).resolve_left
      ((trace_frob_mul_eq_zero_iff_of_trace ha ha').not.2 haa)
    have t2 := (add_frob_eq_zero_or_one (frob l * l')).resolve_left
      ((trace_frob_mul_eq_zero_iff hl hl').not.2 hll)
    rw [t1, t2, add_self_K]

theorem reachable_hexagon {y : Fin n → K} (hvy : herm frob v y = 0) (hy : herm frob y y = 1)
    {a l a' l' : K} (ha : a + frob a = 1) (hl : l ≠ 0) (ha' : a' + frob a' = 1) (hl' : l' ≠ 0) :
    ((cayleyGraph n).induce (midSet v)).Reachable ⟨a • v + l • y, mem_midSet hv hvy hy ha hl⟩
      ⟨a' • v + l' • y, mem_midSet hv hvy hy ha' hl'⟩ := by
  have adj : ∀ {b c b' c' : K} (hb : b + frob b = 1) (hc : c ≠ 0) (hb' : b' + frob b' = 1)
      (hc' : c' ≠ 0), b ≠ b' → c ≠ c' →
      ((cayleyGraph n).induce (midSet v)).Adj ⟨b • v + c • y, mem_midSet hv hvy hy hb hc⟩
        ⟨b' • v + c' • y, mem_midSet hv hvy hy hb' hc'⟩ :=
    fun hb hc hb' hc' hbb hcc => adj_hexagon hv hvy hy hb hc hb' hc' hbb hcc
  obtain ⟨μ, hμ0, hμl, hμl'⟩ := exists_ne_ne l l'
  have hā := trace_add_one ha
  have step1 := (adj ha hl hā hμ0 (add_one_ne_self a).symm hμl.symm).reachable
  by_cases haa : a' = a
  · subst haa
    exact step1.trans (adj hā hμ0 ha hl' (add_one_ne_self a') hμl').reachable
  · have ha'1 : a' = a + 1 := eq_add_one_of_trace ha ha' haa
    subst ha'1
    obtain ⟨ν, hν0, hνμ, hνl'⟩ := exists_ne_ne μ l'
    exact step1.trans ((adj hā hμ0 ha hν0 (add_one_ne_self a) hνμ.symm).reachable.trans
      (adj ha hν0 hā hl' (add_one_ne_self a).symm hνl').reachable)

theorem midSet_decomp {x : Fin n → K} (hx : x ∈ midSet v) :
    herm frob v x + frob (herm frob v x) = 1 ∧ herm frob v (x - herm frob v x • v) = 0 ∧
      herm frob (x - herm frob v x • v) (x - herm frob v x • v) = 1 ∧
      x = herm frob v x • v + (1 : K) • (x - herm frob v x • v) := by
  obtain ⟨-, hxx, ha⟩ := (adj_zero_and_adj_iff hv).1 hx
  have hvy : herm frob v (x - herm frob v x • v) = 0 := by
    rw [herm_sub_right, herm_smul_right, hv, mul_one, sub_self]
  refine ⟨ha, hvy, ?_, by rw [one_smul]; abel⟩
  have hx' : x = herm frob v x • v + (x - herm frob v x • v) := by abel
  have := hxx
  rw [hx', herm_add_self, herm_smul_self_eq, hv, frob_mul_self (ne_zero_of_trace ha), mul_one,
    herm_smul_left, hvy, mul_zero, trace_zero, add_zero] at this
  rcases herm_self_eq_zero_or_one (x - herm frob v x • v) with h | h
  · rw [h, add_zero] at this
    exact absurd this one_ne_zero
  · exact h

theorem reachable_midSet {x : Fin n → K} (hx : x ∈ midSet v) {x' : Fin n → K}
    (hx' : x' ∈ midSet v) :
    ((cayleyGraph n).induce (midSet v)).Reachable ⟨x, hx⟩ ⟨x', hx'⟩ := by
  classical
  obtain ⟨ha, hvy, hy, hxe⟩ := midSet_decomp hv hx
  obtain ⟨ha', hvy', hy', hxe'⟩ := midSet_decomp hv hx'
  set a := herm frob v x
  set y := x - a • v
  set a' := herm frob v x'
  set y' := x' - a' • v
  have e1 : (⟨x, hx⟩ : midSet v) = ⟨a • v + (1 : K) • y, mem_midSet hv hvy hy ha one_ne_zero⟩ :=
    Subtype.ext hxe
  have e2 : (⟨x', hx'⟩ : midSet v) =
      ⟨a' • v + (1 : K) • y', mem_midSet hv hvy' hy' ha' one_ne_zero⟩ :=
    Subtype.ext hxe'
  rw [e1, e2]
  by_cases hyy : ∃ μ : K, y' = μ • y
  · obtain ⟨μ, hμ⟩ := hyy
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [hμ, zero_smul, herm_zero_left] at hy'
      exact zero_ne_one hy'
    have e3 : (⟨a' • v + (1 : K) • y', mem_midSet hv hvy' hy' ha' one_ne_zero⟩ : midSet v) =
        ⟨a' • v + μ • y, mem_midSet hv hvy hy ha' hμ0⟩ :=
      Subtype.ext (show a' • v + (1 : K) • y' = a' • v + μ • y by rw [hμ, one_smul])
    rw [e3]
    exact reachable_hexagon hv hvy hy ha one_ne_zero ha' hμ0
  · push Not at hyy
    set l₀ : K := if herm frob y y' = 0 then 1 else (herm frob y y')⁻¹ with hl₀def
    have hl₀ : l₀ ≠ 0 := by
      rw [hl₀def]
      split_ifs with h
      · exact one_ne_zero
      · exact inv_ne_zero h
    have hl₀t : l₀ * herm frob y y' + frob (l₀ * herm frob y y') = 0 := by
      rw [hl₀def]
      split_ifs with h
      · rw [h, mul_zero, trace_zero]
      · rw [inv_mul_cancel₀ h, trace_one]
    have hedge : (cayleyGraph n).Adj (a • v + (1 : K) • y) (a • v + l₀ • y') := by
      rw [adj_combo_iff hv hvy hy hvy' hy' ha one_ne_zero ha hl₀]
      refine ⟨fun h => ?_, ?_⟩
      · apply hyy l₀⁻¹
        have h' : (1 : K) • y = l₀ • y' := add_left_cancel h
        rw [one_smul] at h'
        rw [h', smul_smul, inv_mul_cancel₀ hl₀, one_smul]
      · rw [map_one, one_mul, trace_add, frob_mul_self (ne_zero_of_trace ha), trace_one,
          zero_add, hl₀t]
    exact (show ((cayleyGraph n).induce (midSet v)).Adj
      ⟨a • v + (1 : K) • y, mem_midSet hv hvy hy ha one_ne_zero⟩
      ⟨a • v + l₀ • y', mem_midSet hv hvy' hy' ha hl₀⟩ from hedge).reachable.trans
        (reachable_hexagon hv hvy' hy' ha hl₀ ha' one_ne_zero)

theorem connected_mid (hn : 2 ≤ n) : ((cayleyGraph n).induce (midSet v)).Connected := by
  obtain ⟨x₀, hx₀0, hx₀, hx₀t⟩ := exists_mid hn hv
  have hx₀m : x₀ ∈ midSet v := (adj_zero_and_adj_iff hv).2 ⟨hx₀0, hx₀, hx₀t⟩
  refine (SimpleGraph.connected_iff _).2 ⟨fun u w => ?_, ⟨⟨x₀, hx₀m⟩⟩⟩
  exact reachable_midSet hv u.2 w.2

end Connected

theorem coverRigid_cayleyGraph (hn : 2 ≤ n) : CoverRigid (cayleyGraph n) 0 where
  exists_adj_adj v hv0 hv := by
    obtain ⟨x, hx0, hx, hxt⟩ := exists_mid hn (herm_eq_one_of_not_adj hv0 hv)
    exact ⟨x, ((adj_zero_and_adj_iff (herm_eq_one_of_not_adj hv0 hv)).2 ⟨hx0, hx, hxt⟩)⟩
  connected v hv0 hv := connected_mid (herm_eq_one_of_not_adj hv0 hv) hn
  exists_adj_adj_adj v w hv0 hv hw0 hw hvw := by
    have hv1 := herm_eq_one_of_not_adj hv0 hv
    have hw1 := herm_eq_one_of_not_adj hw0 hw
    obtain ⟨x, hx0, hx, hxv, hxw⟩ := exists_mid_mid hv1 hw1 hvw
    obtain ⟨h1, h2⟩ := (adj_zero_and_adj_iff hv1).2 ⟨hx0, hx, hxv⟩
    exact ⟨x, h1, h2, ((adj_zero_and_adj_iff hw1).2 ⟨hx0, hx, hxw⟩).2⟩

end CFSG.Fischer.Classification.Unitary
