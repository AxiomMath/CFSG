module

public import CFSG.Certificates.Kernel.D4QK.TwinSound
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.D4QK

open CFSG.KC.Enum CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.LargeExtraspecial.S63
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native
open CFSG.Quasithin.Background.Harris.R1.D4Vert
open CFSG.KS.SporSch.M24 (gtPinK gtClosK gtStepK bfsK bfsTree gensArr gtBFS_of_K unpackR_eq_unpack)
open CFSG.Sporadic.Co1.TwoBNative (gtOK gtPointOK)
open CFSG.KC.Co1B (mulWK)

variable {GM P PAR LAB W S : Nat → Nat} {ng cap N : Nat}

theorem pin_parts (h : gtPinK GM ng cap N P PAR LAB W S = true) :
    0 < N ∧ P 0 = CFSG.KS.SporSch.M24.idM ∧ (∀ i < N, P i < 2 ^ 576) ∧
      (∀ a < N, ∀ b < N, P a = P b → a = b) ∧
      ∀ h < N, ∀ l < ng, W (h * ng + l) < N ∧ P (W (h * ng + l)) = mulWK (P h) (GM l) := by
  unfold gtPinK at h
  rw [bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨hb, hc⟩ := h
  unfold bfsK at hb
  simp only [bAnd_eq', Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hb
  obtain ⟨hN, hP0, -, -, hd, -⟩ := hb
  obtain ⟨hP, hinj⟩ := bfsDistK_sound hd
  refine ⟨hN, hP0, hP, hinj, fun i hi l hl => ?_⟩
  unfold gtClosK at hc
  have := allN_iff'.1 (allN_iff'.1 hc i hi) l hl
  rw [strictB_eq', bAnd_eq', Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
  exact this

theorem allIn_iff {lo hi : Nat} {p : Nat → Bool} :
    CFSG.Sporadic.Th.Native.allIn lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true := by
  unfold CFSG.Sporadic.Th.Native.allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hlo hhi
    have := h ⟨i - lo, by omega⟩ (List.mem_finRange _)
    simpa [Nat.add_sub_cancel' hlo] using this
  · rintro h ⟨k, hk⟩ _
    exact h (lo + k) (by omega) (by omega)

theorem pin_tree (h : gtPinK GM ng cap N P PAR LAB W S = true) :
    ∀ c, 0 < c → c < N → PAR c < c ∧ LAB c < ng ∧
      unpackR 24 (P c) = mulR (unpackR 24 (P (PAR c))) (unpackR 24 (GM (LAB c))) := by
  have hT := (gtBFS_of_K h).2
  unfold gtOK at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hpts⟩, -⟩, -⟩ := hT
  have hsz : (bfsTree N P PAR LAB).pts.size = N := by simp [bfsTree]
  rw [allIn_iff, hsz] at hpts
  intro c hc0 hcN
  have hp := hpts c (Nat.zero_le _) hcN
  unfold gtPointOK at hp
  have hne : (c == 0) = false := by simpa using Nat.pos_iff_ne_zero.1 hc0
  have epts : ∀ i < N, (bfsTree N P PAR LAB).pts[i]! = CFSG.KS.Raw.unpack 24 24 (P i) := by
    intro i hi
    rw [getElem!_pos _ i (by simp [bfsTree, hi])]
    simp [bfsTree]
  have epar : (bfsTree N P PAR LAB).par[c]! = PAR c := by
    rw [getElem!_pos _ c (by simp [bfsTree, hcN])]
    simp [bfsTree]
  have elb : (bfsTree N P PAR LAB).lab[c]! = LAB c := by
    rw [getElem!_pos _ c (by simp [bfsTree, hcN])]
    simp [bfsTree]
  have egs : (gensArr ng GM).size = ng := by simp [gensArr]
  rw [hne, if_neg (by simp), epar, elb, egs] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  obtain ⟨-, ⟨h1, h2⟩, h3⟩ := hp
  refine ⟨h1, h2, ?_⟩
  have eg : (gensArr ng GM)[LAB c]! = CFSG.KS.Raw.unpack 24 24 (GM (LAB c)) := by
    rw [getElem!_pos _ (LAB c) (by simp [gensArr, h2])]
    simp [gensArr]
  rw [epts c hcN, epts (PAR c) (by omega), eg] at h3
  rw [unpackR_eq_unpack, unpackR_eq_unpack, unpackR_eq_unpack]
  exact h3

theorem plK_sound : ∀ (pl : List (ℕ × ℕ)) (c : ℕ), plK PAR LAB N pl c = true →
    c ≤ N ∧ pl = (List.range (N - c)).map fun i => (PAR (c + i), LAB (c + i))
  | [], c, h => by
    have e : c = N := Nat.eq_of_beq_eq_true h
    subst e
    simp
  | e :: pl, c, h => by
    change Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (plK PAR LAB N pl (c + 1)) (Nat.beq e.2 (LAB c)))
      (Nat.beq e.1 (PAR c)) = true at h
    rw [bAnd_eq', bAnd_eq', Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨hc, ih⟩ := plK_sound pl (c + 1) h3
    refine ⟨by omega, ?_⟩
    obtain ⟨a, b⟩ := e
    have e1 : a = PAR c := Nat.eq_of_beq_eq_true h1
    have e2 : b = LAB c := Nat.eq_of_beq_eq_true h2
    have hn : N - c = (N - (c + 1)) + 1 := by omega
    rw [hn, List.range_succ_eq_map, List.map_cons, List.map_map, ih, e1, e2]
    refine congrArg _ (List.map_congr_left fun i _ => ?_)
    simp only [Function.comp_apply]
    rw [show c + (i + 1) = c + 1 + i by omega]

theorem getD_eq_get! (a : Array (Array ℕ)) {i : Nat} (hi : i < a.size) (d : Array ℕ) :
    a.getD i d = a[i]! := by
  simp [Array.getD, getElem!_pos, hi]

theorem ofFn_push (f : Nat → Array ℕ) (k : Nat) :
    (Array.ofFn (n := k + 1) fun i => f i.val).push (f (k + 1)) =
      Array.ofFn (n := k + 2) fun i => f i.val := by
  apply Array.ext
  · simp
  · intro i h1 h2
    rw [Array.getElem_ofFn]
    by_cases hi : i < k + 1
    · rw [Array.getElem_push_lt (by simpa using hi), Array.getElem_ofFn]
    · have e : i = k + 1 := by simp at h1; omega
      subst e
      rw [Array.getElem_push, dif_neg (by simp)]

theorem buildTabR_eq {gs : Array (Array ℕ)} (hP0 : unpackR 24 (P 0) = oneR) (hgs : gs.size = ng)
    (hg : ∀ l < ng, gs[l]! = unpackR 24 (GM l))
    (ht : ∀ c, 0 < c → c < N → PAR c < c ∧ LAB c < ng ∧
      unpackR 24 (P c) = mulR (unpackR 24 (P (PAR c))) (unpackR 24 (GM (LAB c))))
    (hN : 0 < N) :
    buildTabR gs ((List.range (N - 1)).map fun i => (PAR (1 + i), LAB (1 + i))) = ElG P N := by
  have key : ∀ k, k + 1 ≤ N →
      ((List.range k).map fun i => (PAR (1 + i), LAB (1 + i))).foldl
        (fun acc pr => acc.push (mulR (acc.getD pr.1 oneR) (gs.getD pr.2 oneR))) #[oneR] =
        Array.ofFn (n := k + 1) fun i => unpackR 24 (P i.val) := by
    intro k
    induction k with
    | zero =>
      intro _
      apply Array.ext
      · simp
      · intro i h1 _
        have e : i = 0 := by simpa using h1
        subst e
        simp [hP0]
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      obtain ⟨h1, h2, h3⟩ := ht (1 + k) (by omega) (by omega)
      rw [getD_eq_get! _ (by simp; omega), getD_eq_get! _ (by rw [hgs]; exact h2), hg _ h2,
        getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn, ← h3,
        show 1 + k = k + 1 by omega]
      exact ofFn_push (fun i => unpackR 24 (P i)) k
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [show M + 1 - 1 = M by omega]
  exact key M le_rfl

theorem memR_elG (hP : ∀ i < N, P i < 2 ^ 576) (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b)
    (Y : Nat) :
    memR (ElG P N) (lookup (mkIdx (ElG P N))) (unpackR 24 Y) = true ↔
      ∃ w < N, unpackR 24 (P w) = unpackR 24 Y := by
  have hsz : (ElG P N).size = N := by simp [ElG]
  constructor
  · intro h
    unfold memR at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hsz] at h
    obtain ⟨hk, he⟩ := h
    exact ⟨_, hk, by rw [← elG_get hk]; exact he⟩
  · rintro ⟨w, hw, e⟩
    rw [← e]
    unfold memR
    have hl : lookup (mkIdx (ElG P N)) (unpackR 24 (P w)) = w := lookup_mkIdx hP hinj hw
    rw [hl, hsz, elG_get hw]
    simp [hw]

theorem mulR_assocK (A B C : Nat) :
    mulR (mulR (unpackR 24 A) (unpackR 24 B)) (unpackR 24 C) =
      mulR (unpackR 24 A) (mulR (unpackR 24 B) (unpackR 24 C)) := by
  apply eq_of_rowsMatrix_eq
  · rw [mulWK_eq, mulWK_eq]
    exact validR_unpackR _
  · rw [mulWK_eq, mulWK_eq]
    exact validR_unpackR _
  · unfold mulR
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, mul_assoc]

theorem mulR_oneK (A : Nat) : mulR (unpackR 24 A) oneR = unpackR 24 A := by
  apply eq_of_rowsMatrix_eq
  · rw [oneR_eq, mulWK_eq]
    exact validR_unpackR _
  · exact validR_unpackR _
  · unfold mulR oneR
    rw [rowsMatrix_mulRows, rowsMatrix_idRows, mul_one]

theorem tabOK_of (h : gtPinK GM ng cap N P PAR LAB W S = true) {gs gi : Array (Array ℕ)}
    {pl : List (ℕ × ℕ)} (hgs : gs.size = ng) (hg : ∀ l < ng, gs[l]! = unpackR 24 (GM l))
    (hgi : ∀ l < ng, mulR gs[l]! gi[l]! = oneR) (hgiv : ∀ l < ng, ∃ GI, gi[l]! = unpackR 24 GI)
    (hT : buildTabR gs pl = ElG P N) : tabOK gs gi pl N = true := by
  obtain ⟨-, -, hP, hinj, hcl⟩ := pin_parts h
  have hs : (ElG P N).size = N := by simp [ElG]
  unfold tabOK tabOKWith
  rw [hT]
  unfold tabOKOn
  simp only [Bool.and_eq_true, beq_iff_eq, CFSG.Monster.B.Co2.allLt_iff, hs, hgs]
  refine ⟨⟨⟨trivial, fun i hi => ?_⟩, fun i hi => hgi i hi⟩, fun j hj i hi => ⟨?_, ?_⟩⟩
  · rw [elG_get hi]
    exact lookup_mkIdx hP hinj hi
  · rw [elG_get hj, hg i hi, mulWK_eq, memR_elG hP hinj]
    exact ⟨W (j * ng + i), (hcl j hj i hi).1, by rw [(hcl j hj i hi).2]⟩
  · obtain ⟨GI, hGI⟩ := hgiv i hi
    have key : ∀ x, unpackR 24 x = mulR (unpackR 24 (mulWK x (GM i))) (unpackR 24 GI) := by
      intro x
      rw [← mulWK_eq, mulR_assocK, ← hGI, ← hg i hi, hgi i hi, mulR_oneK]
    let f : Fin N → Fin N := fun a => ⟨W (a.val * ng + i), (hcl a.val a.isLt i hi).1⟩
    have hf : Function.Injective f := by
      intro a b hab
      have e : P (W (a.val * ng + i)) = P (W (b.val * ng + i)) :=
        congrArg (fun x : Fin N => P x.val) hab
      rw [(hcl a.val a.isLt i hi).2, (hcl b.val b.isLt i hi).2] at e
      have e2 : unpackR 24 (P a.val) = unpackR 24 (P b.val) := by rw [key (P a.val), key (P b.val), e]
      rw [unpackR_inj, Nat.mod_eq_of_lt (hP a.val a.isLt), Nat.mod_eq_of_lt (hP b.val b.isLt)] at e2
      exact Fin.ext (hinj _ a.isLt _ b.isLt e2)
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hf) ⟨j, hj⟩
    have ew : W (a.val * ng + i) = j := congrArg Fin.val ha
    rw [elG_get hj, hGI, mulWK_eq, memR_elG hP hinj]
    refine ⟨a.val, a.isLt, ?_⟩
    rw [key (P a.val), ← (hcl a.val a.isLt i hi).2, ew, mulWK_eq]

end CFSG.KC.D4QK

end
