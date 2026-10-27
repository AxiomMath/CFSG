module

public import Certificates.Data.Kernel.TwistDce3.CoverNet
public import CFSG.Certificates.Kernel.TwistDce3.CoverSound
public import CFSG.Certificates.Kernel.YModel.NetSem
import CFSG.Certificates.Kernel.KDense.SortSound

public section

namespace CFSG.Certificates.TwDce3

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange andB
open CFSG.KC (andB)
open CFSG.KC.TwDce2 hiding evP isOne tStep posStep walkRun walkOK recOK foldStep foldRange
  lettersOK coverK coverRange relsOK fixAll stabRange
open CFSG.KC.TwDce3 CFSG.KC.YModel
open CFSG.Certificates.TwDce.Words (sB_eq sN_eq)
open CFSG.Certificates.TwDce3.Words (evP_eq lst_eq digs_succ land15 shr4)

theorem shlK (K : ℕ) : Nat.shiftLeft (nat_lit 1) K = 2 ^ K := Nat.one_shiftLeft K

theorem andB_two {a b : Bool} (h : (Bool.rec false b a : Bool) = true) : a = true ∧ b = true :=
  CFSG.KC.Benes.andB_true h

theorem testBit_tabPlaneN {K NP RAW b a : ℕ} (hK : 0 < K) (hNP : NP ≤ 2 ^ K) (ha : a < NP) :
    (tabPlaneN K NP RAW b).testBit a = RAW.testBit (K * a + b) := by
  have h1 : a < Nat.shiftLeft (nat_lit 1) K := by rw [shlK]; omega
  unfold tabPlaneN
  simp only [CFSG.KC.Benes.nlor, CFSG.KC.Benes.nland, CFSG.KC.Benes.nxor, Nat.testBit_or,
    Nat.testBit_and, Nat.testBit_xor, CFSG.KC.KDense.SortAux.testBit_ones]
  rw [CFSG.KC.KDense.SortAux.testBit_rawPlane (rec := K) (n := Nat.shiftLeft (nat_lit 1) K) (h := K)
    hK (shlK K)]
  have h1' : a < 1 <<< K := h1
  simp [ha, h1, h1']

theorem tabPlaneN_lt (K NP RAW b : ℕ) (hNP : NP ≤ 2 ^ K) :
    tabPlaneN K NP RAW b < 2 ^ Nat.shiftLeft (nat_lit 1) K := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have h2 : ¬ i < Nat.shiftLeft (nat_lit 1) K := by omega
  have h1 : ¬ i < NP := by rw [shlK] at hi; omega
  unfold tabPlaneN
  simp only [CFSG.KC.Benes.nlor, CFSG.KC.Benes.nland, CFSG.KC.Benes.nxor, Nat.testBit_or,
    Nat.testBit_and, Nat.testBit_xor, CFSG.KC.KDense.SortAux.testBit_ones]
  have h3 : 1 <<< K ≤ i := hi
  have h2' : ¬ i < 1 <<< K := h2
  simp [h1, h2, h2', h3]

theorem testBit_tabPlanesN {K NP RAW u a : ℕ} (hK : 0 < K) (hNP : NP ≤ 2 ^ K) (hu : u < K)
    (ha : a < NP) : (tabPlanesN K NP RAW).testBit (2 ^ K * u + a) = RAW.testBit (K * a + u) := by
  have hP := (CFSG.KC.YModel.Sem.testBit_planes (S := Nat.shiftLeft (nat_lit 1) K)
    (fun b => tabPlaneN K NP RAW b) K (fun b _ => tabPlaneN_lt K NP RAW b hNP)).1 u hu a
    (by rw [shlK]; omega)
  rw [← shlK K]
  exact hP.trans (testBit_tabPlaneN hK hNP ha)

theorem testBit_fieldAt (K RAW a u : ℕ) :
    (fieldAt K RAW a).testBit u = (RAW.testBit (K * a + u) && decide (u < K)) := by
  unfold fieldAt
  change ((RAW >>> (K * a)) &&& (Nat.shiftLeft (nat_lit 1) K - 1)).testBit u = _
  rw [shlK, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]

theorem fieldAt_lt (K RAW a : ℕ) : fieldAt K RAW a < 2 ^ K := by
  unfold fieldAt
  change (RAW >>> (K * a)) &&& (Nat.shiftLeft (nat_lit 1) K - 1) < _
  rw [shlK, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos K)

theorem bindN_sound {K NP RAW N : ℕ} (hK : 0 < K) (hNP : NP ≤ 2 ^ K) (h : bindN K NP RAW N = true) :
    CFSG.KC.Benes.StagesValid K N ∧ ∀ a < NP, CFSG.KC.Benes.benesPerm K N a = fieldAt K RAW a := by
  obtain ⟨h1, h2⟩ := andB_two h
  have hv := CFSG.KC.Benes.stagesValid_of_netValid h1
  refine ⟨hv, fun a ha => ?_⟩
  have e := Nat.eq_of_beq_eq_true h2
  rw [shlK] at e
  have ha' : a < 2 ^ K := by omega
  apply CFSG.KC.YModel.Sem.eq_of_bits (CFSG.KC.Benes.benesPerm_lt hv ha') (fieldAt_lt K RAW a)
  intro u hu
  have e1 : (CFSG.KC.MonsterConv.Perm.netApply K (2 ^ K) (CFSG.KC.MonsterConv.Perm.repU (2 ^ K) K)
      N (CFSG.KC.MonsterConv.Perm.idP K)).testBit (2 ^ K * u + a) =
      (tabPlanesN K NP RAW).testBit (2 ^ K * u + a) := by rw [e]
  rw [(CFSG.KC.Benes.testBit_netApply rfl hv (CFSG.KC.MonsterConv.Perm.idP K)).1 u hu a ha',
    CFSG.KC.YModel.Sem.testBit_idP hu (CFSG.KC.Benes.benesPerm_lt hv ha'),
    testBit_tabPlanesN hK hNP hu ha] at e1
  rw [e1, testBit_fieldAt, decide_eq_true hu, Bool.and_true]

theorem bindAll_sound {K NP NL : ℕ} {F NS : ℕ → ℕ} (hK : 0 < K) (hNP : NP ≤ 2 ^ K)
    (h : bindAll K NP NL F NS = true) :
    ∀ c < NL, CFSG.KC.Benes.StagesValid K (NS c) ∧
      ∀ a < NP, CFSG.KC.Benes.benesPerm K (NS c) a = fieldAt K (F c) a := by
  intro c hc
  have := allRange_sound h c hc
  rw [Nat.zero_add] at this
  exact bindN_sound hK hNP this

section
variable {PB : ℕ} {F : ℕ → ℕ} {INVM : ℕ} {RD RW NS : ℕ → ℕ} {K NL NP n : ℕ} {DS : List ℕ}

noncomputable def wsLoop (INVM : ℕ) (NS : ℕ → ℕ) (K : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih s x => sN (CFSG.KC.MonsterConv.Perm.netApply K (Nat.shiftLeft (nat_lit 1) K)
        (CFSG.KC.MonsterConv.Perm.repU (Nat.shiftLeft (nat_lit 1) K) (nat_lit 2))
        (NS (ivL INVM (Nat.land s (nat_lit 15)))) x)
      (fun y => sN (Nat.shiftRight s (nat_lit 4)) (fun s' => ih s' y)))

theorem wsLoop_succ (n s X : ℕ) : wsLoop INVM NS K (n + 1) s X = wsLoop INVM NS K n (s / 16)
    (CFSG.KC.MonsterConv.Perm.netApply K (2 ^ K) (CFSG.KC.MonsterConv.Perm.repU (2 ^ K) 2)
      (NS (ivL INVM (s % 16))) X) := by
  simp only [wsLoop, Nat.rec_add_one, sN_eq]
  rw [land15, shr4, shlK]

structure NetFacts (PB : ℕ) (F : ℕ → ℕ) (INVM : ℕ) (NS : ℕ → ℕ) (K NL NP : ℕ) : Prop where
  np : NP ≤ 2 ^ K
  net : ∀ c < NL, CFSG.KC.Benes.StagesValid K (NS c) ∧
    ∀ a < NP, CFSG.KC.Benes.benesPerm K (NS c) a = fieldAt PB (F c) a
  tab : ∀ c < NL, ivL INVM c < NL ∧ ∀ x < NP, fieldAt PB (F c) x < NP ∧
    fieldAt PB (F (ivL INVM c)) (fieldAt PB (F c) x) = x
  inv : ∀ c < NL, ivL INVM (ivL INVM c) = c

theorem wsLoop_sound (hN : NetFacts PB F INVM NS K NL NP) : ∀ n s X,
    (∀ i < n, s / 16 ^ i % 16 < NL) → ∀ q < NP, ∃ y < NP,
      (wsLoop INVM NS K n s X).testBit (2 ^ K + q) = X.testBit (2 ^ K + y) ∧
      ((List.range n).map (fun i => s / 16 ^ i % 16)).foldl (fun p c => fieldAt PB (F c) p) y = q
  | 0, s, X, _, q, hq => ⟨q, hq, rfl, rfl⟩
  | n + 1, s, X, hs, q, hq => by
    have hc : s % 16 < NL := by simpa using hs 0 (by omega)
    have hc' := (hN.tab _ hc).1
    have hs' : ∀ i < n, s / 16 / 16 ^ i % 16 < NL := by
      intro i hi
      have := hs (i + 1) (by omega)
      rwa [pow_succ', ← Nat.div_div_eq_div_mul] at this
    obtain ⟨y', hy', hb, hf⟩ := wsLoop_sound hN n (s / 16)
      (CFSG.KC.MonsterConv.Perm.netApply K (2 ^ K) (CFSG.KC.MonsterConv.Perm.repU (2 ^ K) 2)
        (NS (ivL INVM (s % 16))) X) hs' q hq
    obtain ⟨hv, hp⟩ := hN.net _ hc'
    have hnp := hN.np
    refine ⟨fieldAt PB (F (ivL INVM (s % 16))) y', ((hN.tab _ hc').2 y' hy').1, ?_, ?_⟩
    · rw [wsLoop_succ, hb]
      have e := (CFSG.KC.Benes.testBit_netApply (P := 2) rfl hv X).1 1 (by decide) y' (by omega)
      rw [Nat.mul_one] at e
      rw [e, hp y' hy']
    · rw [digs_succ, List.foldl_cons]
      have e := ((hN.tab _ hc').2 y' hy').2
      rw [hN.inv _ hc] at e
      rw [e, hf]

theorem testBit_hi {K q : ℕ} (hq : q < 2 ^ K) :
    (Nat.shiftLeft (ones (Nat.shiftLeft (nat_lit 1) K)) (Nat.shiftLeft (nat_lit 1) K)).testBit
      (2 ^ K + q) = true := by
  unfold ones
  change ((Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft (nat_lit 1) K) - 1) <<<
    Nat.shiftLeft (nat_lit 1) K).testBit _ = true
  rw [shlK, shlK, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  have h2 : q < 2 ^ 2 ^ K := lt_trans hq Nat.lt_two_pow_self
  simp [h2, hq]

theorem testBit_ones_iff {N q : ℕ} : (ones N).testBit q = decide (q < N) := by
  unfold ones
  change (Nat.shiftLeft (nat_lit 1) N - 1).testBit q = _
  rw [shlK, Nat.testBit_two_pow_sub_one]

theorem appsN_sound (hN : NetFacts PB F INVM NS K NL NP) {k : ℕ} : ∀ (AL : List ℕ) (X : ℕ),
    appsN INVM RD RW NS K NL NP n k AL X = true →
    (∀ q < NP, X.testBit (2 ^ K + q) = true → Reached PB F INVM RD RW n DS k q) →
    ∀ p < NP, Reached PB F INVM RD RW n DS k p
  | [], X, h, hinit => fun p hp => by
    have hm := Nat.eq_of_beq_eq_true h
    apply hinit p hp
    have hb := congrArg (fun x => Nat.testBit x p) hm
    simp only at hb
    change ((X >>> Nat.shiftLeft (nat_lit 1) K) &&& ones NP).testBit p = _ at hb
    rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones_iff, decide_eq_true hp,
      Bool.and_true, shlK] at hb
    exact hb
  | c :: AL, X, h, hinit => by
    change sB (gWord INVM RW c) (fun w => andB (andB (isStabOf RD n k (Nat.shiftRight c 1))
      (wBelow NL w)) (sB (wSetN INVM NS K w X) (fun Y => sB (Nat.lor Y (Nat.land X
        (Nat.shiftLeft (ones (Nat.shiftLeft (nat_lit 1) K)) (Nat.shiftLeft (nat_lit 1) K))))
          (appsN INVM RD RW NS K NL NP n k AL)))) = true at h
    rw [sB_eq] at h
    obtain ⟨h1, h⟩ := andB_two h
    obtain ⟨hst, hwb⟩ := andB_two h1
    rw [sB_eq, sB_eq] at h
    refine appsN_sound hN AL _ h (fun q hq hb => ?_)
    have hqW : q < 2 ^ K := lt_of_lt_of_le hq hN.np
    change (Nat.lor _ (Nat.land X _)).testBit _ = true at hb
    rw [CFSG.KC.Benes.nlor, CFSG.KC.Benes.nland, Nat.testBit_or, Nat.testBit_and, testBit_hi hqW,
      Bool.and_true, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · have hlt := (CFSG.Certificates.TwDce2.Words.wBelow_spec hwb).2
      rw [lst_eq] at hlt
      have hs : ∀ i < wLen (gWord INVM RW c), wStr (gWord INVM RW c) / 16 ^ i % 16 < NL :=
        fun i hi => hlt _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
      obtain ⟨y, hy, hby, hf⟩ := wsLoop_sound hN _ _ X hs q hq
      have hb' : X.testBit (2 ^ K + y) = true := by
        rw [← hby]
        exact hb
      obtain ⟨f, hf1, hfa, hk, hnd, cs, hcs, hy0⟩ := hinit y hy hb'
      refine ⟨f, hf1, hfa, hk, hnd, cs ++ [c], fun d hd => ?_, ?_⟩
      · rcases List.mem_append.1 hd with hd | hd
        · exact hcs d hd
        · rw [List.mem_singleton.1 hd]
          have e2 : c / 2 = Nat.shiftRight c 1 := by
            change _ = c >>> 1
            rw [Nat.shiftRight_eq_div_pow, pow_one]
          rw [e2]
          exact hst
      · rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hy0, evP_eq, lst_eq]
        exact hf.symm
    · exact hinit q hq hb

theorem rootsN_sound (hN : NetFacts PB F INVM NS K NL NP) {k : ℕ} {AL : List ℕ} :
    ∀ (RL : List ℕ) (X : ℕ), rootsN PB F INVM RD RW NS K NL NP n DS k RL AL X = true →
    (∀ q < NP, X.testBit (2 ^ K + q) = true → Reached PB F INVM RD RW n DS k q) →
    ∀ p < NP, Reached PB F INVM RD RW n DS k p
  | [], X, h, hinit => appsN_sound hN AL X h hinit
  | f :: RL, X, h, hinit => by
    change sB (RD f) (fun d =>
      andB (andB (Nat.blt f n) (andB (isFact (dKind d))
          (andB (Nat.beq (dN1 d) k) (CFSG.KC.LaneChain.memN (dN2 d) DS))))
        (sB (evP PB F (wInv INVM (RW f)) (nat_lit 0)) (fun x =>
          sB (Nat.lor X (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (nat_lit 1) K) x)))
            (rootsN PB F INVM RD RW NS K NL NP n DS k RL AL)))) = true at h
    rw [sB_eq] at h
    obtain ⟨h1, h⟩ := andB_two h
    obtain ⟨hf, h1⟩ := andB_two h1
    obtain ⟨hfa, h1⟩ := andB_two h1
    obtain ⟨hk, hnd⟩ := andB_two h1
    rw [sB_eq, sB_eq] at h
    refine rootsN_sound hN RL _ h (fun q hq hb => ?_)
    change (X ||| (1 <<< (Nat.shiftLeft (nat_lit 1) K + evP PB F (wInv INVM (RW f)) 0))).testBit
      _ = true at hb
    rw [shlK, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_iff] at hb
    rcases hb with hb | hb
    · exact hinit q hq hb
    · have hq' : q = evP PB F (wInv INVM (RW f)) 0 := by omega
      exact ⟨f, Nat.blt_eq.mp hf, hfa, Nat.eq_of_beq_eq_true hk, memN_sound hnd, [],
        by simp, hq'⟩

theorem coverNK_sound (hN : NetFacts PB F INVM NS K NL NP) {k : ℕ} {RL AL : List ℕ}
    (h : coverNK PB F INVM RD RW NS K NL NP n DS k RL AL = true) :
    ∀ p < NP, Reached PB F INVM RD RW n DS k p := by
  refine rootsN_sound hN RL _ h (fun q _ hq => absurd hq ?_)
  have hs : saltN K < 2 ^ (2 ^ K) := by
    unfold saltN
    change _ % Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft (nat_lit 1) K) < _
    rw [shlK, shlK]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) (by omega)))]
  exact Bool.false_ne_true

theorem coverRangeN_sound (hN : NetFacts PB F INVM NS K NL NP) {CR CA : List (List ℕ)} {a m : ℕ}
    (h : coverRangeN PB F INVM RD RW NS K NL NP n DS CR CA a m = true) :
    ∀ j < m, ∀ p < NP,
      Reached PB F INVM RD RW n DS (CFSG.KC.LaneChain.getN DS (a + j)) p :=
  fun j hj => coverNK_sound hN (allRange_sound h j hj)

end

end CFSG.Certificates.TwDce3

end
