module

public import Certificates.Data.Kernel.F2Set24Block
public import CFSG.Certificates.Kernel.F2Set24Sound
public import CFSG.Certificates.Kernel.Co1PumpFixLemmas

public section

namespace CFSG.KS.Co1PumpFix

open CFSG.KC.Co1Pairs CFSG.KC.F2Set24 CFSG.KS.F2Set24 CFSG.Sporadic.Co1Schreier
open CFSG.Sporadic.SmallF2 (toVecD)

theorem entsK_sound {M J : ℕ} {F : List (ℕ × ℕ × ℕ)} (h : entsK M J F 0 = true) :
    ∃ L : List ℕ, L.Nodup ∧ L.length = 2 ^ popK J ∧ (∀ x ∈ L, x < 2 ^ 24) ∧
      (∀ v < 2 ^ 24, CFSG.KS.SporSch.M24.actK M v = v ↔ v ∈ L) ∧
      ∀ mem : ℕ → Bool, cntK mem J F 0 0 0 = L.countP mem :=
  entsK_fixed h

@[expose] def grayWs (B : List ℕ) : List ℕ → ℕ → List ℕ
  | [], x => [x]
  | j :: g, x => x :: grayWs B g (x ^^^ B.getD j 0)

theorem iterK_eq {α : Sort*} (P Q : List (ℕ × ℕ)) :
    ∀ (r S : ℕ) (k : ℕ → α), iterK P Q r S k = k ((round P Q)^[r] S)
  | 0, S, k => rfl
  | r + 1, S, k => by
    change strict (round P Q S) (fun S' => iterK P Q r S' k) = _
    rw [strict_eq, iterK_eq P Q r, Function.iterate_succ_apply]

theorem iterate_round_root (P Q : List (ℕ × ℕ)) (root : ℕ) :
    ∀ (r S : ℕ), S.testBit root = true → ((round P Q)^[r] S).testBit root = true
  | 0, S, h => h
  | r + 1, S, h => by
    rw [Function.iterate_succ_apply]
    refine iterate_round_root P Q root r _ ?_
    change (S ||| (img P S ||| img Q S)).testBit root = true
    simp [h]

theorem swpT_bits {i : ℕ} (hi : i < 24) {m : ℕ}
    (hm : ∀ p, m.testBit p = (decide (p < 2 ^ 24) && !p.testBit i)) (S q : ℕ) :
    (swp (1 <<< i) m S).testBit q =
      if q < 2 ^ 24 then S.testBit (q ^^^ 2 ^ i) else S.testBit q := by
  change (S ^^^ (((S ^^^ (S >>> (1 <<< i))) &&& m) ^^^
    (((S ^^^ (S >>> (1 <<< i))) &&& m) <<< (1 <<< i)))).testBit q = _
  rw [Nat.one_shiftLeft]
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, hm]
  cases hqi : q.testBit i
  · rw [xor_clear hqi]
    have hsh : (decide (q ≥ 2 ^ i) && ((S.testBit (q - 2 ^ i) ^^
        S.testBit (2 ^ i + (q - 2 ^ i))) && (decide (q - 2 ^ i < 2 ^ 24) &&
        !(q - 2 ^ i).testBit i))) = false := by
      by_cases hge : 2 ^ i ≤ q
      · simp [clear_sub hqi hge]
      · simp [hge]
    rw [hsh, Bool.xor_false, Nat.add_comm (2 ^ i) q]
    by_cases hq : q < 2 ^ 24 <;> simp [-Nat.reducePow, hq] <;>
      cases S.testBit q <;> cases S.testBit (q + 2 ^ i) <;> rfl
  · have hge := Nat.ge_two_pow_of_testBit hqi
    rw [xor_set hqi, set_sub hqi, show 2 ^ i + (q - 2 ^ i) = q by omega,
      show decide (q - 2 ^ i < 2 ^ 24) = decide (q < 2 ^ 24) from
        decide_eq_decide.2 (sub_lt_iff hi hqi)]
    by_cases hq : q < 2 ^ 24 <;> simp [-Nat.reducePow, hq, hge] <;>
      cases S.testBit q <;> cases S.testBit (q - 2 ^ i) <;> rfl

noncomputable def tstp (i : ℕ) : ℕ × ℕ :=
  (1 <<< i, Nat.xor (@HPow.hPow ℕ ℕ ℕ (@instHPow ℕ ℕ instPowNat) 2 W - 1) (pms24.getD i 0))

theorem zip_map_self {β γ : Type*} (f : ℕ → β) (g : ℕ × β → γ) :
    ∀ L : List ℕ, (L.zip (L.map f)).map g = L.map fun i => g (i, f i)
  | [] => rfl
  | i :: L => by simp [zip_map_self f g L]

set_option maxRecDepth 8192 in
theorem ks24_eq : ks24 = List.range' 0 24 := rfl

theorem withCms_eq {α : Sort*} (k : List (ℕ × ℕ) → α) :
    withCms pms24 k = k ((List.range' 0 24).map tstp) := by
  unfold withCms
  rw [mapRevK_eq, List.map_reverse, List.reverse_reverse, List.append_nil, zip_map_self, ks24_eq]
  exact congrArg k (List.map_congr_left fun i _ => rfl)

theorem tstp_mask {i : ℕ} (hi : i < 24) (p : ℕ) :
    (tstp i).2.testBit p = (decide (p < 2 ^ 24) && !p.testBit i) := by
  have hW : W = 2 ^ 24 := by norm_num [W]
  have hp : pms24 = (List.range' 0 24).map pmask := by
    have e := withPms_eq (α := List ℕ) id
    unfold withPms at e
    rw [mapRevK_eq, List.map_reverse, List.reverse_reverse, List.append_nil, ks24_eq] at e
    exact e.symm
  have hg : pms24.getD i 0 = pmask i := by
    rw [hp, List.getD_eq_getElem _ _ (by simp; omega)]
    simp
  have hx : ∀ a b q : ℕ, (Nat.xor a b).testBit q = (a.testBit q ^^ b.testBit q) :=
    fun a b q => Nat.testBit_xor a b q
  unfold tstp
  rw [hx, hg, hW, Nat.testBit_two_pow_sub_one, pmask_bits hi]
  generalize decide (p < 2 ^ 24) = d
  cases d <;> cases p.testBit i <;> rfl

theorem shift_split (b k : ℕ) : b <<< k = (b / 2) <<< (k + 1) ^^^ (b % 2) <<< k := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_shiftLeft, Nat.testBit_xor]
  rcases Nat.lt_or_ge j k with h | h
  · simp [show ¬ j ≥ k by omega, show ¬ j ≥ k + 1 by omega]
  rcases Nat.eq_or_lt_of_le h with rfl | h'
  · have h0 : (b % 2).testBit 0 = b.testBit 0 := by
      rw [← Nat.pow_one 2, Nat.testBit_mod_two_pow]
      simp
    simp [h0]
  · have e : j - k = (j - (k + 1)) + 1 := by omega
    have hmod : (b % 2).testBit (j - k) = false := by
      rw [e, ← Nat.pow_one 2, Nat.testBit_mod_two_pow]
      simp
    rw [hmod, e, Nat.testBit_succ]
    simp [show j ≥ k by omega, show j ≥ k + 1 by omega]

theorem trV_bits : ∀ (n k b S q : ℕ), k + n = 24 → b < 2 ^ n →
    (trV ((List.range' k n).map tstp) b S).testBit q =
      if q < 2 ^ 24 then S.testBit (q ^^^ (b <<< k)) else S.testBit q
  | 0, k, b, S, q, _, hb => by
    obtain rfl : b = 0 := by simpa using hb
    change S.testBit q = _
    split_ifs <;> simp
  | n + 1, k, b, S, q, hkn, hb => by
    change (trV ((List.range' (k + 1) n).map tstp) (b / 2)
      (Bool.rec (motive := fun _ => ℕ) S (swp (tstp k).1 (tstp k).2 S) (Nat.beq (b % 2) 1))).testBit q = _
    have hb2 : b / 2 < 2 ^ n := by rw [pow_succ] at hb; omega
    rw [trV_bits n (k + 1) (b / 2) _ q (by omega) hb2, shift_split b k]
    have hS1 : ∀ r, (Bool.rec (motive := fun _ => ℕ) S (swp (tstp k).1 (tstp k).2 S)
        (Nat.beq (b % 2) 1)).testBit r =
          if r < 2 ^ 24 then S.testBit (r ^^^ (b % 2) <<< k) else S.testBit r := by
      intro r
      rcases Nat.mod_two_eq_zero_or_one b with h | h
      · rw [h]
        change S.testBit r = _
        split_ifs <;> simp
      · rw [h]
        change (swp (1 <<< k) (tstp k).2 S).testBit r = _
        rw [swpT_bits (by omega) (tstp_mask (by omega)), Nat.one_shiftLeft]
    split_ifs with hq
    · have hy : (b / 2) <<< (k + 1) < 2 ^ 24 := by
        rw [Nat.shiftLeft_eq]
        calc b / 2 * 2 ^ (k + 1) < 2 ^ n * 2 ^ (k + 1) :=
              Nat.mul_lt_mul_of_lt_of_le hb2 (le_refl _) (by positivity)
          _ = 2 ^ 24 := by rw [← pow_add]; congr 1; omega
      rw [hS1, if_pos (Nat.xor_lt_two_pow hq hy), Nat.xor_assoc]
    · rw [hS1, if_neg hq]

theorem trV24_bits {b : ℕ} (hb : b < 2 ^ 24) (S q : ℕ) :
    (trV ((List.range' 0 24).map tstp) b S).testBit q =
      if q < 2 ^ 24 then S.testBit (q ^^^ b) else S.testBit q := by
  rw [trV_bits 24 0 b S q rfl hb, Nat.shiftLeft_zero]

def v7 (a0 a1 a2 a3 a4 a5 a6 : Bool) : ℕ :=
  a0.toNat + 2 * a1.toNat + 4 * a2.toNat + 8 * a3.toNat + 16 * a4.toNat + 32 * a5.toNat +
    64 * a6.toNat

theorem v7_lt : ∀ a0 a1 a2 a3 a4 a5 a6 : Bool, v7 a0 a1 a2 a3 a4 a5 a6 < 128 := by decide

theorem v7_add : ∀ a0 a1 a2 a3 a4 a5 a6 p : Bool,
    v7 (a0 ^^ p) (a1 ^^ (a0 && p)) (a2 ^^ (a1 && (a0 && p))) (a3 ^^ (a2 && (a1 && (a0 && p))))
      (a4 ^^ (a3 && (a2 && (a1 && (a0 && p)))))
      (a5 ^^ (a4 && (a3 && (a2 && (a1 && (a0 && p))))))
      (a6 ^^ (a5 && (a4 && (a3 && (a2 && (a1 && (a0 && p))))))) =
      (v7 a0 a1 a2 a3 a4 a5 a6 + p.toNat) % 128 := by decide

theorem v7_ge : ∀ a0 a1 a2 a3 a4 a5 a6 : Bool,
    (a6 || (a5 || (a4 || (a3 && (a2 || a1))))) = decide (10 ≤ v7 a0 a1 a2 a3 a4 a5 a6) := by
  decide

def cv (q c0 c1 c2 c3 c4 c5 c6 : ℕ) : ℕ :=
  v7 (c0.testBit q) (c1.testBit q) (c2.testBit q) (c3.testBit q) (c4.testBit q) (c5.testBit q)
    (c6.testBit q)

theorem add7_spec {α : Sort*} (P c0 c1 c2 c3 c4 c5 c6 : ℕ)
    (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → α) :
    ∃ d0 d1 d2 d3 d4 d5 d6, add7 P c0 c1 c2 c3 c4 c5 c6 k = k d0 d1 d2 d3 d4 d5 d6 ∧
      ∀ q, cv q d0 d1 d2 d3 d4 d5 d6 = (cv q c0 c1 c2 c3 c4 c5 c6 + (P.testBit q).toNat) % 128 := by
  refine ⟨c0 ^^^ P, c1 ^^^ (c0 &&& P), c2 ^^^ (c1 &&& (c0 &&& P)),
    c3 ^^^ (c2 &&& (c1 &&& (c0 &&& P))), c4 ^^^ (c3 &&& (c2 &&& (c1 &&& (c0 &&& P)))),
    c5 ^^^ (c4 &&& (c3 &&& (c2 &&& (c1 &&& (c0 &&& P))))),
    c6 ^^^ (c5 &&& (c4 &&& (c3 &&& (c2 &&& (c1 &&& (c0 &&& P)))))), ?_, fun q => ?_⟩
  · unfold add7
    simp only [strict_eq]
    rfl
  · simp only [cv, Nat.testBit_xor, Nat.testBit_and]
    exact v7_add ..

theorem getD_lt {B : List ℕ} (hB : ∀ b ∈ B, b < 2 ^ 24) (j : ℕ) : B.getD j 0 < 2 ^ 24 := by
  by_cases hj : j < B.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hB _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    positivity

theorem grayWs_lt {B : List ℕ} (hB : ∀ b ∈ B, b < 2 ^ 24) :
    ∀ (g : List ℕ) (x : ℕ), x < 2 ^ 24 → ∀ w ∈ grayWs B g x, w < 2 ^ 24
  | [], x, hx, w, hw => by
    rw [grayWs, List.mem_singleton] at hw
    exact hw ▸ hx
  | j :: g, x, hx, w, hw => by
    rw [grayWs, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hx
    · exact grayWs_lt hB g _ (Nat.xor_lt_two_pow hx (getD_lt hB j)) w hw

theorem grayWs_eq (B g : List ℕ) (x : ℕ) : grayWs B g x = x :: (grayWs B g x).tail := by
  cases g <;> rfl

theorem length_grayWs (B : List ℕ) : ∀ (g : List ℕ) (x : ℕ), (grayWs B g x).length = g.length + 1
  | [], _ => rfl
  | j :: g, x => by rw [grayWs, List.length_cons, length_grayWs B g, List.length_cons]

theorem walk_spec {α : Sort*} (Sf : ℕ) {B : List ℕ} (hB : ∀ b ∈ B, b < 2 ^ 24) :
    ∀ (g : List ℕ) (x Sc c0 c1 c2 c3 c4 c5 c6 : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → α),
      (∀ q < 2 ^ 24, Sc.testBit q = Sf.testBit (q ^^^ x)) →
      ∃ d0 d1 d2 d3 d4 d5 d6,
        walk ((List.range' 0 24).map tstp) B g Sc c0 c1 c2 c3 c4 c5 c6 k = k d0 d1 d2 d3 d4 d5 d6 ∧
        ∀ q < 2 ^ 24, cv q d0 d1 d2 d3 d4 d5 d6 = (cv q c0 c1 c2 c3 c4 c5 c6 +
          (grayWs B g x).tail.countP fun w => Sf.testBit (q ^^^ w)) % 128
  | [], x, Sc, c0, c1, c2, c3, c4, c5, c6, k, _ => by
    refine ⟨c0, c1, c2, c3, c4, c5, c6, rfl, fun q _ => ?_⟩
    rw [grayWs, List.tail_cons, List.countP_nil, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (v7_lt ..)).symm
  | j :: g, x, Sc, c0, c1, c2, c3, c4, c5, c6, k, hSc => by
    have hb := getD_lt hB j
    change ∃ d0 d1 d2 d3 d4 d5 d6, strict (trV ((List.range' 0 24).map tstp) (B.getD j 0) Sc)
      (fun S' => add7 S' c0 c1 c2 c3 c4 c5 c6 fun d0 d1 d2 d3 d4 d5 d6 =>
        walk ((List.range' 0 24).map tstp) B g S' d0 d1 d2 d3 d4 d5 d6 k) = _ ∧ _
    rw [strict_eq]
    set S' := trV ((List.range' 0 24).map tstp) (B.getD j 0) Sc with hS'
    have hS'b : ∀ q < 2 ^ 24, S'.testBit q = Sf.testBit (q ^^^ (x ^^^ B.getD j 0)) := by
      intro q hq
      rw [hS', trV24_bits hb, if_pos hq, hSc _ (Nat.xor_lt_two_pow hq hb), Nat.xor_assoc,
        Nat.xor_comm (B.getD j 0) x]
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, he, hev⟩ := add7_spec S' c0 c1 c2 c3 c4 c5 c6
      fun d0 d1 d2 d3 d4 d5 d6 => walk ((List.range' 0 24).map tstp) B g S' d0 d1 d2 d3 d4 d5 d6 k
    obtain ⟨d0, d1, d2, d3, d4, d5, d6, hd, hdv⟩ :=
      walk_spec Sf hB g (x ^^^ B.getD j 0) S' e0 e1 e2 e3 e4 e5 e6 k hS'b
    refine ⟨d0, d1, d2, d3, d4, d5, d6, he.trans hd, fun q hq => ?_⟩
    rw [hdv q hq, hev q, hS'b q hq, grayWs, List.tail_cons,
      grayWs_eq B g (x ^^^ B.getD j 0), List.countP_cons]
    have := v7_lt (c0.testBit q) (c1.testBit q) (c2.testBit q) (c3.testBit q) (c4.testBit q)
      (c5.testBit q) (c6.testBit q)
    unfold cv at this ⊢
    generalize Sf.testBit (q ^^^ (x ^^^ B.getD j 0)) = s
    cases s <;> simp <;> omega

theorem spanSet_bits (B : List ℕ) : ∀ (g : List ℕ) (x acc q : ℕ),
    (spanSet B g x acc).testBit q = (acc.testBit q || decide (q ∈ (grayWs B g x).tail))
  | [], x, acc, q => by simp [spanSet, grayWs]
  | j :: g, x, acc, q => by
    change (strict (Nat.xor x (B.getD j 0)) (fun y =>
      strict (Nat.lor acc (Nat.shiftLeft 1 y)) (spanSet B g y))).testBit q = _
    rw [strict_eq, strict_eq, spanSet_bits B g, grayWs, List.tail_cons]
    conv_rhs => rw [grayWs_eq B g]
    change ((acc ||| 1 <<< (x ^^^ B.getD j 0)).testBit q || _) = _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp only [List.mem_cons, show Nat.xor x (B.getD j 0) = x ^^^ B.getD j 0 from rfl]
    generalize x ^^^ B.getD j 0 = y
    by_cases h1 : y = q
    · subst h1
      simp
    · simp [h1, Ne.symm h1]

open scoped Classical in
theorem blockOK_sound {P Q : GL24} {cP cQ : List ℕ} {opsP opsQ : List (ℕ × ℕ)}
    {root n steps : ℕ} {B gray : List ℕ} (hP : ActsBy P cP.toArray) (hQ : ActsBy Q cQ.toArray)
    (h : blockOK cP cQ opsP opsQ root n steps B gray = true) (hB : ∀ b ∈ B, b < 2 ^ 24)
    (hg : gray.length < 127) :
    orbOK cP cQ opsP opsQ root n steps = true ∧
      ∀ x < 2 ^ 24, toVecD 24 x ∈ kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root) →
        x ∉ grayWs B gray 0 →
        ((grayWs B gray 0).toFinset.filter fun w =>
          toVecD 24 (x ^^^ w) ∈ kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root)).card ≤ 9 := by
  have hW : W = 2 ^ 24 := by norm_num [W]
  have h' := h
  unfold blockOK at h'
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨hPo, hQo⟩, hroot⟩, h'⟩ := h'
  rw [withPms_eq, withPrep_eq, withPrep_eq, iterK_eq] at h'
  set Sf := (round (opsP.map stp) (opsQ.map stp))^[steps] (Nat.shiftLeft 1 root) with hSf
  simp only [Bool.and_eq_true] at h'
  obtain ⟨hfin, hblk⟩ := h'
  have horb : orbOK cP cQ opsP opsQ root n steps = true := by
    unfold orbOK
    rw [withPms_eq, withPrep_eq, withPrep_eq, iterK_eq, hPo, hQo, hroot]
    exact hfin
  refine ⟨horb, ?_⟩
  have hroot' : root < 2 ^ 24 := by
    have := hroot
    simp only [Nat.blt_eq] at this
    rwa [hW] at this
  obtain ⟨hPok, hPF⟩ := opsOK_facts hPo
  obtain ⟨hQok, hQF⟩ := opsOK_facts hQo
  have hSr : Sf.testBit root = true := by
    rw [hSf]
    apply iterate_round_root
    change (1 <<< root).testBit root = true
    rw [Nat.one_shiftLeft]
    exact Nat.testBit_two_pow_self
  have hfin' : (Nat.beq (round (opsP.map stp) (opsQ.map stp) Sf) Sf &&
      Nat.beq (Sf &&& (2 ^ root - 1)) 0 && Nat.beq (popc pms24 Sf) n) = true := hfin
  simp only [Bool.and_eq_true, Nat.beq_eq] at hfin'
  have hcl := hfin'.1.1
  let T := (Finset.range (2 ^ 24)).filter (fun v => Sf.testBit v = true)
  have hmem : ∀ v, v ∈ T ↔ v < 2 ^ 24 ∧ Sf.testBit v = true := fun v => by simp [T]
  have hTlt : ∀ v ∈ T, v < 2 ^ 24 := fun v hv => ((hmem v).1 hv).1
  have hround : ∀ q < 2 ^ 24, (Sf.testBit q || (Sf.testBit (opsApp opsP q) ||
      Sf.testBit (opsApp opsQ q))) = Sf.testBit q := by
    intro q hq
    have := congrArg (fun x => x.testBit q) hcl
    change (Sf ||| (img (opsP.map stp) Sf ||| img (opsQ.map stp) Sf)).testBit q =
      Sf.testBit q at this
    rwa [Nat.testBit_or, Nat.testBit_or, img_bits hPok, img_bits hQok, if_pos hq,
      if_pos hq] at this
  have hpreP : ∀ q < 2 ^ 24, opsApp opsP q ∈ T → q ∈ T := by
    intro q hq h
    rw [hmem] at h ⊢
    refine ⟨hq, ?_⟩
    rw [← hround q hq, h.2]
    simp
  have hpreQ : ∀ q < 2 ^ 24, opsApp opsQ q ∈ T → q ∈ T := by
    intro q hq h
    rw [hmem] at h ⊢
    refine ⟨hq, ?_⟩
    rw [← hround q hq, h.2]
    simp
  have hclP := closed_of_preimage (opsApp_inj hPok) (fun q hq => opsApp_lt hPok hq) hTlt hpreP
  have hclQ := closed_of_preimage (opsApp_inj hQok) (fun q hq => opsApp_lt hQok hq) hTlt hpreQ
  have hsub : kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root) ⊆ toVecD 24 '' (T : Set ℕ) := by
    rintro _ ⟨k, hk, rfl⟩
    refine closure_mapsTo ((T.finite_toSet).image _) ?_ ?_ hk _
      ⟨root, (hmem root).2 ⟨hroot', hSr⟩, rfl⟩
    · rintro _ ⟨v, hv, rfl⟩
      refine ⟨_, ?_, (hP v).symm⟩
      rw [← hPF v (hTlt v hv)]
      exact hclP v hv
    · rintro _ ⟨v, hv, rfl⟩
      refine ⟨_, ?_, (hQ v).symm⟩
      rw [← hQF v (hTlt v hv)]
      exact hclQ v hv
  have hin : ∀ y < 2 ^ 24, toVecD 24 y ∈ kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root) →
      Sf.testBit y = true := by
    intro y hy hm
    obtain ⟨v, hv, hvy⟩ := hsub hm
    rw [← CFSG.Sporadic.SmallF2.toVecD_injective (hTlt v hv) hy hvy]
    exact ((hmem v).1 hv).2
  have hblk' := Nat.eq_of_beq_eq_true hblk
  unfold blockK at hblk'
  rw [withCms_eq] at hblk'
  generalize hM : 2 ^ W - 1 = M at hblk'
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, he, hev⟩ := add7_spec Sf 0 0 0 0 0 0 0
    fun c0 c1 c2 c3 c4 c5 c6 => walk ((List.range' 0 24).map tstp) B gray Sf c0 c1 c2 c3 c4 c5 c6
      fun _ c1 c2 c3 c4 c5 c6 => strict (spanSet B gray 0 1) fun Wset =>
        Nat.land (Nat.land Sf (Nat.xor M Wset))
          (Nat.lor c6 (Nat.lor c5 (Nat.lor c4 (Nat.land c3 (Nat.lor c2 c1)))))
  rw [he] at hblk'
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, hd, hdv⟩ := walk_spec Sf hB gray 0 Sf e0 e1 e2 e3 e4 e5 e6
    (fun _ c1 c2 c3 c4 c5 c6 => strict (spanSet B gray 0 1) fun Wset =>
        Nat.land (Nat.land Sf (Nat.xor M Wset))
          (Nat.lor c6 (Nat.lor c5 (Nat.lor c4 (Nat.land c3 (Nat.lor c2 c1))))))
    (fun q _ => by rw [Nat.xor_zero])
  rw [hd, strict_eq] at hblk'
  intro x hx hxo hxg
  have hbit := congrArg (fun z => z.testBit x) hblk'
  have hWs : (spanSet B gray 0 1).testBit x = false := by
    rw [spanSet_bits]
    rw [grayWs_eq B gray 0, List.mem_cons, not_or] at hxg
    have h1 : Nat.testBit 1 x = false := by
      rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
      exact decide_eq_false (Ne.symm hxg.1)
    simp [h1, hxg.2]
  have hMx : M.testBit x = true := by
    rw [← hM, hW, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hx
  change ((Sf &&& (M ^^^ spanSet B gray 0 1)) &&&
    (d6 ||| (d5 ||| (d4 ||| (d3 &&& (d2 ||| d1)))))).testBit x = (0 : ℕ).testBit x at hbit
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hMx,
    hWs, hin x hx hxo, Nat.zero_testBit, Bool.true_and, Bool.xor_false] at hbit
  rw [v7_ge (d0.testBit x)] at hbit
  have hc : cv x d0 d1 d2 d3 d4 d5 d6 < 10 := by
    unfold cv
    simpa using hbit
  rw [hdv x hx, hev x] at hc
  have hcnt : ((grayWs B gray 0).countP fun w => Sf.testBit (x ^^^ w)) ≤ 9 := by
    have hc0 : cv x 0 0 0 0 0 0 0 = 0 := by simp [cv, v7]
    rw [hc0, Nat.zero_add] at hc
    have htl : (grayWs B gray 0).tail.length = gray.length := by
      have := length_grayWs B gray 0
      rw [grayWs_eq B gray 0, List.length_cons] at this
      omega
    have hle := List.countP_le_length (p := fun w => Sf.testBit (x ^^^ w))
      (l := (grayWs B gray 0).tail)
    rw [grayWs_eq B gray 0, List.countP_cons, Nat.xor_zero]
    generalize List.countP (fun w => Sf.testBit (x ^^^ w)) (grayWs B gray 0).tail = c at hc hle
    generalize Sf.testBit x = s at hc ⊢
    cases s <;> simp at hc ⊢ <;> omega
  refine le_trans ?_ hcnt
  rw [List.countP_eq_length_filter]
  refine le_trans (Finset.card_le_card ?_) (List.toFinset_card_le _)
  intro w hw
  rw [Finset.mem_filter, List.mem_toFinset] at hw
  rw [List.mem_toFinset, List.mem_filter]
  refine ⟨hw.1, ?_⟩
  have hwl := grayWs_lt hB gray 0 (by positivity) w hw.1
  simpa using hin _ (Nat.xor_lt_two_pow hx hwl) hw.2

end CFSG.KS.Co1PumpFix

end
