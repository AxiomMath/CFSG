module

public import Certificates.Data.Kernel.GammaUFrameFixK
public import CFSG.Certificates.Kernel.GammaUOrbSound
public import CFSG.GF2Type.Smith1979.GammaU.FrameFixInputs
public import CFSG.GF2Type.Smith1979.GammaU.NativeBridge
public import CFSG.GF2Type.Smith1979.GammaU.PairBridge

public section

namespace CFSG.KC.GUX

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUV CFSG.KC.GUS CFSG.KC.GUO
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem allL_iff (f : Nat → Bool) : ∀ l : List Nat, allL f l = true ↔ ∀ x ∈ l, f x = true
  | [] => by simp [allL]
  | a :: l => by
    change (f a && allL f l) = true ↔ _
    rw [Bool.and_eq_true, allL_iff f l]
    simp

theorem fixK_spec {PG : List Nat} (h : fixK PG = true) :
    ∀ n < 4096, (∀ P ∈ PG, ap12 P n = n) → n = 0 ∨ n = 3072 := by
  intro n hn hP
  have h1 := (allBelow_iff _ _).1 h n hn
  have h2 : allL (fun P => Nat.beq (ap12 P n) n) PG = true :=
    (allL_iff _ PG).2 fun P hm => by
      simp only [Nat.beq_eq]
      exact hP P hm
  rw [h2] at h1
  simpa only [Bool.not_true, Bool.or_false, Bool.or_eq_true, Nat.beq_eq] using h1

theorem appN_eq_ap12 {r : Array ℕ} (h : rowsOK r.toList = true) (n : ℕ) :
    appN r n = ap12 (packR r) n :=
  vecOf_inj (appN_lt (rows_lt h) n) (ap12_lt _ _) (by
    rw [vecOf_appN, vecOf_ap12, linP_eq_of_rowsP (rowsP_packR h)])

theorem single_eq_smul (j : Fin 12) (c : ZMod 2) :
    (Pi.single j c : V12) = c • (Pi.single j 1 : V12) := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp
  · simp [Pi.single_apply, hk]

theorem mem_of_perp (φ : V12 →ₗ[ZMod 2] V12) (D : Submodule (ZMod 2) V12)
    (h1 : ∀ j : Fin 12, j ≠ 4 → j ≠ 5 → φ (Pi.single j 1) ∈ D)
    (h2 : φ (Pi.single 4 1 + Pi.single 5 1) ∈ D) (v : V12) (hv : v 4 = v 5) : φ v ∈ D := by
  set e : V12 := Pi.single 4 1 + Pi.single 5 1 with he
  set w : V12 := v - v 4 • e with hw
  have hvw : v = w + v 4 • e := by rw [hw]; abel
  have hsum : w = ∑ j, Pi.single j (w j) := (Finset.univ_sum_single w).symm
  rw [hvw, map_add, map_smul, hsum, map_sum]
  refine D.add_mem (D.sum_mem fun j _ => ?_) (D.smul_mem _ h2)
  by_cases h4 : j = 4
  · subst h4
    have : w 4 = 0 := by simp [hw, he]
    rw [this, Pi.single_zero, map_zero]
    exact D.zero_mem
  by_cases h5 : j = 5
  · subst h5
    have : w 5 = 0 := by simp [hw, he, hv]
    rw [this, Pi.single_zero, map_zero]
    exact D.zero_mem
  rw [single_eq_smul, map_smul]
  exact D.smul_mem _ (h1 j h4 h5)

theorem f0b_a0 (x : ℕ) : f0b x a0 = (x.testBit 4 ^^ x.testBit 5) := by
  have t0 : Nat.testBit 3072 0 = false := by decide
  have t1 : Nat.testBit 3072 1 = false := by decide
  have t2 : Nat.testBit 3072 2 = false := by decide
  have t3 : Nat.testBit 3072 3 = false := by decide
  have t4 : Nat.testBit 3072 4 = false := by decide
  have t5 : Nat.testBit 3072 5 = false := by decide
  have t6 : Nat.testBit 3072 6 = false := by decide
  have t7 : Nat.testBit 3072 7 = false := by decide
  have t8 : Nat.testBit 3072 8 = false := by decide
  have t9 : Nat.testBit 3072 9 = false := by decide
  have t10 : Nat.testBit 3072 10 = true := by decide
  have t11 : Nat.testBit 3072 11 = true := by decide
  simp only [f0b, a0, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, Nat.add_zero, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10,
    t11, Bool.and_false, Bool.and_true, Bool.false_xor, Bool.xor_false]

theorem perp_coord {x : ℕ} (h : f0b x a0 = false) : vecOf x 4 = vecOf x 5 := by
  rw [f0b_a0] at h
  have h45 : x.testBit 4 = x.testBit 5 := by
    revert h
    cases x.testBit 4 <;> cases x.testBit 5 <;> simp
  change (if x.testBit 4 then (1 : ZMod 2) else 0) = if x.testBit 5 then 1 else 0
  rw [h45]

theorem comm_of_perpB {r : Array ℕ} (hr : rowsOK r.toList = true)
    (hc : ∀ c ∈ perpB, (spanList d0).contains (appN r c ^^^ c) = true) {x : ℕ} (hx : x < 4096)
    (hf : f0b x a0 = false) : appN r x ^^^ x ∈ spanList d0 := by
  have hd : ∀ d ∈ d0, d < 4096 := by decide
  have hrl := rows_lt hr
  have hpl : ∀ c ∈ perpB, c < 4096 := by decide
  let φ : V12 →ₗ[ZMod 2] V12 := linOfRows r + LinearMap.id
  have hφ : ∀ n, vecOf (appN r n ^^^ n) = φ (vecOf n) := fun n => by
    rw [vecOf_xor, vecOf_appN]
    rfl
  have hmem : ∀ c ∈ perpB, φ (vecOf c) ∈ spanOf d0 := fun c hcm => by
    have h := hc c hcm
    rw [List.contains_iff_mem, mem_spanList_iff hd (xor_lt (appN_lt hrl c) (hpl c hcm))] at h
    rw [← hφ]
    exact h
  rw [mem_spanList_iff hd (xor_lt (appN_lt hrl x) hx), hφ]
  refine mem_of_perp φ _ (fun j h4 h5 => ?_) ?_ (vecOf x) (perp_coord hf)
  · have hj : 2 ^ (j : ℕ) ∈ perpB := by revert j; decide
    rw [← vecOf_two_pow]
    exact hmem _ hj
  · have h48 : vecOf 48 = Pi.single 4 1 + Pi.single 5 1 := by
      rw [show (48 : ℕ) = 2 ^ ((4 : Fin 12) : ℕ) ^^^ 2 ^ ((5 : Fin 12) : ℕ) by decide, vecOf_xor,
        vecOf_two_pow, vecOf_two_pow]
    rw [← h48]
    exact hmem 48 (by decide)

theorem q0b_of_guOK {r : Array ℕ} (hr : rowsOK r.toList = true)
    (h : guOK (packR SigmaP.thetaRows) (packR r) = true) (n : ℕ) : q0b (appN r n) = q0b n := by
  have hTH : ∀ v, linP (packR SigmaP.thetaRows) v = theta0 v := fun v => by
    rw [linP_eq_of_rowsP (rowsP_packR rowsOK_thetaRows), linOfRows_thetaRows]
  obtain ⟨U, hUP, hUg⟩ := exists_of_guOK hTH h
  have hY : appN r n = Y U n := by
    rw [Y, hUP, linP_eq_of_rowsP (rowsP_packR hr), ← vecOf_appN, codeOf_vecOf (appN_lt (rows_lt hr) n)]
  rw [hY, q0b_Y hUg]

theorem gammaUN_of {r : Array ℕ} (hr : rowsOK r.toList = true)
    (h : guOK (packR SigmaP.thetaRows) (packR r) = true) (hu : (unitaryN r || antiN r) = true) :
    gammaUN r = true := by
  obtain ⟨hl, hb⟩ := rowsOK_spec hr
  have hs : r.size = 12 := by simpa using hl
  have hall : (r.all fun x => decide (x < 4096)) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro x hx
    simpa using hb x (by simpa using hx)
  have hq : ((List.range 4096).all fun n => q0b (appN r n) == q0b n) = true :=
    List.all_eq_true.2 fun n _ => by rw [q0b_of_guOK hr h n]; exact beq_self_eq_true _
  unfold gammaUN isoN
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨by simp [hs], hall⟩, hq⟩, hu⟩

theorem frameFixAt_of {i : ℕ} (hrg : rowsG i = true) (hrc : rowsC i = true) (hfix : fix i = true)
    (ha : fixA i = true) (hc : comm i = true) (hw : wit i = true) (hn : n2 i = true) :
    frameFixAt i = true := by
  have hrg' : ∀ g ∈ ResPair.compGens i, rowsOK g.toList = true := List.all_eq_true.1 hrg
  have hrc' : ∀ r ∈ compOf i, rowsOK r.toList = true := List.all_eq_true.1 hrc
  simp only [frameFixAt, Bool.and_eq_true, native_compGens, native_compOf, native_appN, native_a0,
    native_f0b, native_spanList, native_d0, native_n2Gens, native_gammaUN]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine List.all_eq_true.2 fun n hn => ?_
    have hn' := List.mem_range.1 hn
    by_cases hg : ((ResPair.compGens i).all fun g => appN g n == n) = true
    · have := fixK_spec hfix n hn' fun P hP => by
        obtain ⟨g, hgm, rfl⟩ := List.mem_map.1 hP
        rw [← appN_eq_ap12 (hrg' g hgm)]
        exact beq_iff_eq.1 (List.all_eq_true.1 hg g hgm)
      rcases this with h | h <;> simp [h, a0]
    · simp [Bool.eq_false_iff.2 hg]
  · exact ha
  · refine List.all_eq_true.2 fun r hr => List.all_eq_true.2 fun x hx => ?_
    cases hfx : f0b x a0
    · have := comm_of_perpB (hrc' r hr) (List.all_eq_true.1 (List.all_eq_true.1 hc r hr))
        (List.mem_range.1 hx) hfx
      simp [List.contains_iff_mem, this]
    · rfl
  · simp only [wit, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hw
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, f1⟩, f2⟩, f3⟩, f4⟩, f5⟩, w1⟩, w2⟩, w3⟩, w4⟩, w5⟩ := hw
    have m16 : (compOf i).getD 16 idR ∈ compOf i := by
      rw [getD_of_lt idR (by omega : 16 < (compOf i).length)]
      exact List.getElem_mem _
    have m8 : (compOf i).getD 8 idR ∈ compOf i := by
      rw [getD_of_lt idR (by omega : 8 < (compOf i).length)]
      exact List.getElem_mem _
    have key : ∀ l ∈ compOf i, ∀ x < 4096, ∀ d, f0b x a0 = false → appN l x ^^^ x = d →
        ((compOf i).any fun l => (List.range 4096).any fun x =>
          !f0b x a0 && (appN l x ^^^ x) == d) = true := fun l hl x hx d hf he =>
      List.any_eq_true.2 ⟨l, hl, List.any_eq_true.2 ⟨x, List.mem_range.2 hx, by simp [hf, he]⟩⟩
    refine List.all_eq_true.2 fun d hd => ?_
    simp only [d0, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [key _ m16 65 (by norm_num) _ f1 w1]
    · simp [key _ m8 1 (by norm_num) _ f2 w2]
    · simp [key _ m16 385 (by norm_num) _ f3 w3]
    · simp [key _ m16 320 (by norm_num) _ f4 w4]
    · simp [key _ m16 192 (by norm_num) _ f5 w5]
    · simp [a0]
  · refine List.all_eq_true.2 fun r hr => ?_
    have h := List.all_eq_true.1 hn r hr
    simp only [Bool.and_eq_true] at h
    exact gammaUN_of h.1.1 h.1.2 h.2

end CFSG.KC.GUX

end
