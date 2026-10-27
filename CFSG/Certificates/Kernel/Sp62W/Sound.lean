module

public import Certificates.Data.Kernel.Sp62W.Defs
public import CFSG.Certificates.Kernel.Misc.BfsKSound
public import CFSG.Certificates.Kernel.Misc.G22WSound
public import CFSG.Quasithin.H13.L32NKGG22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData

public section

namespace CFSG.KC.Sp62W

open CFSG.KD.Sp62W CFSG.KD.BfsK CFSG.KC.Mat8P CFSG.KC.Loop CFSG.KGroups.Sp6
  CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U

theorem validB_iff {c : List ℕ} : validB c = true ↔ CFSG.Quasithin.H13.KGCert.ValidC c := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    CFSG.Quasithin.H13.KGCert.ValidC]

theorem validB8 {c : List ℕ} (h : validB c = true) :
    CFSG.Quasithin.H13.Mat8Cert.validB (c ++ [64, 128]) = true := by
  obtain ⟨hl, hc⟩ := validB_iff.1 h
  unfold CFSG.Quasithin.H13.Mat8Cert.validB
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨by simp [hl], fun x hx => decide_eq_true ?_⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact lt_trans (hc x hx) (by norm_num)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> norm_num

theorem unpackM_numC {c : List ℕ} (h : validB c = true) : unpackM (numC c) = c ++ [64, 128] :=
  unpackM_code64R _ (validB8 h)

theorem numC_inj {a b : List ℕ} (ha : validB a = true) (hb : validB b = true)
    (h : numC a = numC b) : a = b := by
  have e := congrArg unpackM h
  rw [unpackM_numC ha, unpackM_numC hb] at e
  exact List.append_cancel_right e

theorem validB_mulC {a b : List ℕ} (ha : validB a = true) (hb : validB b = true) :
    validB (mulC a b) = true :=
  validB_iff.2 (CFSG.Quasithin.H13.KGCert.validC_mulC (validB_iff.1 ha) (validB_iff.1 hb))

theorem numC_mulC {a b : List ℕ} (ha : validB a = true) (hb : validB b = true) :
    numC (mulC a b) = mulP (numC a) (numC b) := by
  have hu : unpackM (mulP (numC a) (numC b)) = mulC a b ++ [64, 128] :=
    CFSG.KC.G22W.mulP_cols (unpackM_numC ha) (validB_iff.1 ha).1 (unpackM_numC hb)
      (validB_iff.1 hb)
  have e := code64_unpackS (mulP (numC a) (numC b))
  rw [← unpackM_eq, hu, Nat.mod_eq_of_lt (mulP_lt _ _)] at e
  exact e

theorem commN_eq {x y : List ℕ} (hx : validB x = true) (hy : validB y = true) :
    commN (numC x) (numC y) = commB x y := by
  unfold commN commB
  rw [← numC_mulC hx hy, ← numC_mulC hy hx]
  apply Bool.eq_iff_iff.2
  rw [Nat.beq_eq, beq_iff_eq]
  exact ⟨numC_inj (validB_mulC hx hy) (validB_mulC hy hx), fun h => h ▸ rfl⟩

theorem all_commN {G : List (List ℕ)} (hG : G.all validB = true) {x : List ℕ}
    (hx : validB x = true) : (G.map numC).all (commN (numC x)) = G.all (commB x) := by
  induction G with
  | nil => rfl
  | cons g G ih =>
    rw [List.all_cons, Bool.and_eq_true] at hG
    rw [List.map_cons, List.all_cons, List.all_cons, commN_eq hx hG.1, ih hG.2]

theorem contains_numC {L : List (List ℕ)} (hL : L.all validB = true) {x : List ℕ}
    (hx : validB x = true) : (L.map numC).contains (numC x) = L.contains x := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨y, hy, e⟩
    rw [numC_inj (List.all_eq_true.1 hL y hy) hx e] at hy
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem cenB_eq {G Z : List (List ℕ)} (hG : G.all validB = true) (hZ : Z.all validB = true)
    {x : List ℕ} (hx : validB x = true) :
    cenB (G.map numC) (Z.map numC) (numC x) = (!(G.all (commB x)) || Z.contains x) := by
  unfold cenB
  rw [all_commN hG hx, contains_numC hZ hx]

theorem allSl_of {m S : ℕ} {f : ℕ → Bool} (hS : m ≤ 4096 * S)
    (h : ∀ j < S, allSl m f j = true) : ∀ i < m, f i = true := by
  intro i hi
  have hj := h (i / 4096) (by omega)
  have h1 := CFSG.KC.G2Three.allBelow_g2 hj (by norm_num) (i % 4096) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (i / 4096) 4096) (i % 4096) = i := by
    change i / 4096 * 4096 + i % 4096 = i
    omega
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact hi
  rw [e, hb] at h1
  simpa using h1

theorem recAnd_of_all (f : ℕ → Bool) : ∀ n, (∀ i < n, f i = true) →
    Nat.rec (motive := fun _ => Bool) true
      (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) n = true
  | 0, _ => rfl
  | n + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (Nat.rec (motive := fun _ => Bool) true
      (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) n) (f n) = true
    rw [h n (by omega)]
    exact recAnd_of_all f n fun i hi => h i (by omega)

theorem allBelow_of_sl {m hi S : ℕ} {f : ℕ → Bool} (hS : m ≤ 4096 * S)
    (h : ∀ j < S, allSl m f j = true) : allBelow m hi f = true := by
  have hf := allSl_of hS h
  unfold allBelow
  refine recAnd_of_all _ hi fun h' _ => recAnd_of_all (fun l => (fun i =>
    bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h' 6) l)) 64 fun l _ => ?_
  dsimp only
  by_cases hb : Nat.blt (Nat.add (Nat.shiftLeft h' 6) l) m = true
  · have hlt := hb
    rw [Nat.blt_eq] at hlt
    rw [hb]
    exact hf _ hlt
  · rw [Bool.eq_false_iff.2 hb]

theorem table_ok {R : ℕ → ℕ} {gens : List (List ℕ)} {o n k Sb Ss St : ℕ}
    (hk : gens.length = k) (hk0 : 0 < k) (hn : 0 < n)
    (hg : gens.all validB = true) (hG : gensK R gens = true)
    (h0 : (Nat.beq (recX R o 0) (numC oneC) && Nat.beq (recC R o k 0) 1 &&
      Nat.beq (recC R o k (n * k)) n) = true)
    (hSb : n - 1 ≤ 4096 * Sb) (hb : ∀ j < Sb, buildSl R o n k j = true)
    (hSs : n * k ≤ 4096 * Ss) (hs : ∀ j < Ss, stepSl R o n k j = true)
    (hSt : n ≤ 4096 * St) (ht : ∀ j < St, sortSl R o n j = true) :
    (tabOf gens n).size = n ∧ closedCheck mulC gens (tabOf gens n) = true ∧
      distinctCheck (tabOf gens n) = true ∧
      ∀ t < n, validB ((tabOf gens n).getD t []) = true ∧
        numC ((tabOf gens n).getD t []) = recX R o t := by
  simp only [Bool.and_eq_true, Nat.beq_eq] at h0
  obtain ⟨⟨hX0, hC0⟩, hCn⟩ := h0
  have hst : ∀ x N, CFSG.KC.BfsK.Enc validB numC x N → ∀ s < k, ∀ d : List ℕ,
      CFSG.KC.BfsK.Enc validB numC (mulC x (gens.getD s d)) (rst R N s) := by
    intro x N hx s hs d
    rw [CFSG.KC.G2Three.listGetD_irrel (by rw [hk]; exact hs) d []]
    have hsl : s < gens.length := by rw [hk]; exact hs
    have hvg : validB (gens.getD s []) = true := by
      rw [List.getD_eq_getElem _ _ hsl]
      exact List.all_eq_true.1 hg _ (List.getElem_mem hsl)
    have hR : R s = numC (gens.getD s []) := by
      have := List.all_eq_true.1 hG s (List.mem_range.2 hsl)
      exact Nat.eq_of_beq_eq_true this
    refine ⟨validB_mulC hx.1 hvg, ?_⟩
    rw [numC_mulC hx.1 hvg, hx.2, ← hR]
    rfl
  have hB : CFSG.KD.Sp62.buildG (rst R) (recX R o) (recF R o 0) (recF R o 1) n k n = true :=
    allBelow_of_sl (f := bBody (rst R) (recX R o) (recF R o 0) (recF R o 1) k) hSb hb
  have hS : CFSG.KD.Sp62.stepG (rst R) (recX R o) (recF R o 0) (recF R o 1) (recC R o k)
      (recPOS R o k) n k (n * k) = true := by
    unfold CFSG.KD.Sp62.stepG
    rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq]
    exact ⟨⟨hC0, hCn⟩, allBelow_of_sl (f := sBody (rst R) (recX R o) (recF R o 0) (recF R o 1)
      (recC R o k) (recPOS R o k) n k) hSs hs⟩
  have hT : CFSG.KD.G2Three.sortK (recX R o) (recF R o 2) (recF R o 3) n n = true :=
    allBelow_of_sl (f := tBody (recX R o) (recF R o 2) (recF R o 3) n) hSt ht
  obtain ⟨hpar, -, hsz, hcl, hdi, hrec⟩ :=
    CFSG.KC.BfsK.tableE (fuel := n) (fun a b ha hb e => numC_inj ha hb e) hk hk0 hn le_rfl hst
      ⟨by decide, hX0.symm⟩ hB (by omega) hS (Nat.le_mul_of_pos_left _ (by norm_num)) hT
      (by omega)
  have e : tabOf gens n = build oneC mulC gens
      ((List.range (n - 1)).map (fun i => (recF R o 0 i, recF R o 1 i))) := by
    unfold tabOf
    rw [hpar]
  rw [e]
  exact ⟨hsz, hcl, hdi, hrec⟩

theorem tabCheck_of_table {gens : List (List ℕ)} {n : ℕ} {P : Array (List ℕ) → Bool}
    (hsz : (tabOf gens n).size = n) (hcl : closedCheck mulC gens (tabOf gens n) = true)
    (hdi : distinctCheck (tabOf gens n) = true)
    (hv : ∀ t < n, validB ((tabOf gens n).getD t []) = true)
    (hgen : gens.all genB = true) (hP : P (tabOf gens n) = true) : tabCheck gens n P = true := by
  dsimp only [tabCheck]
  rw [hgen, hsz, beq_self_eq_true, hcl, hdi, hP,
    CFSG.KC.G2Three.allCheck_of fun t ht => hv t (by rw [hsz] at ht; exact ht)]
  rfl

theorem mems_of {R : ℕ → ℕ} {q o n : ℕ} {tab : Array (List ℕ)} {cs : List (List ℕ)}
    (hsz : tab.size = n)
    (hrec : ∀ t < n, validB (tab.getD t []) = true ∧ numC (tab.getD t []) = recX R o t)
    (hcs : cs.all validB = true) (h : memsK R q o n cs = true) : cs.all (inTab tab) = true := by
  unfold memsK at h
  rw [List.all_eq_true] at h hcs ⊢
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have h1 := h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
  obtain ⟨hp, he⟩ := h1
  rw [List.getD_eq_getElem _ _ hi] at he
  obtain ⟨hv, hx⟩ := hrec _ hp
  have e : tab.getD (R (Nat.add q i)) [] = cs[i] := numC_inj hv (hcs _ hc) (by rw [hx, he])
  have hp' : R (Nat.add q i) < tab.size := by rw [hsz]; exact hp
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hp', Option.getD_some] at e
  unfold inTab
  rw [Array.contains_iff_mem, ← e]
  exact Array.getElem_mem hp'

theorem cen_of {R : ℕ → ℕ} {o n S : ℕ} {tab : Array (List ℕ)} {G1 Z1 G2 Z2 : List (List ℕ)}
    (hsz : tab.size = n)
    (hrec : ∀ t < n, validB (tab.getD t []) = true ∧ numC (tab.getD t []) = recX R o t)
    (hG1 : G1.all validB = true) (hZ1 : Z1.all validB = true) (hG2 : G2.all validB = true)
    (hZ2 : Z2.all validB = true) (hS : n ≤ 4096 * S)
    (h : ∀ j < S, cenSl R o n (G1.map numC) (Z1.map numC) (G2.map numC) (Z2.map numC) j = true) :
    allCheck (fun x => (!(G1.all (commB x)) || Z1.contains x) &&
      (!(G2.all (commB x)) || Z2.contains x)) tab = true := by
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  rw [hsz] at ht
  obtain ⟨hv, hx⟩ := hrec t ht
  have h1 := allSl_of (f := fun t => cenB (G1.map numC) (Z1.map numC) (recX R o t) &&
    cenB (G2.map numC) (Z2.map numC) (recX R o t)) hS h t ht
  rw [← hx, cenB_eq hG1 hZ1 hv, cenB_eq hG2 hZ2 hv] at h1
  exact h1

theorem allCheck_mono {p q : List ℕ → Bool} {tab : Array (List ℕ)} (h : allCheck q tab = true)
    (hpq : ∀ x, q x = true → p x = true) : allCheck p tab = true := by
  unfold allCheck at h ⊢
  rw [List.all_eq_true] at h ⊢
  exact fun t ht => hpq _ (h t ht)

end CFSG.KC.Sp62W

end
