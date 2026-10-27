module

public import CFSG.Certificates.Kernel.SL4ModClassSound
public import Certificates.Data.Kernel.SL4ModNoneCerts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Module Native CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

@[expose] def NoneCertData : Prop :=
  ∀ j < 3, ∃ dd : CosetData, checkTau j dd = true ∧ ∀ i < 3, ∃ od : OrbData,
    checkOrb dd i od = true ∧ ∃ es : List (ℕ × NoneRec × NoneRec), es.length = 64 ∧
      checkNoneFrom (tabL dd.tau) od 0 es = true

theorem vec105_xor (a b : ℕ) : vec (a ^^^ b) = vec a + vec b := toVecD_xor 105 a b

theorem vec_onesV : vec onesV = fun _ => 1 := by
  funext k
  rw [vec, toVecD_apply, onesV, Nat.testBit_two_pow_sub_one, decide_eq_true k.isLt, if_pos rfl]

theorem nz_of_vec_ne_zero {x : ℕ} (h : vec x ≠ 0) : nz x = true := by
  by_contra hn
  apply h
  have h0 : x &&& (2 ^ 105 - 1) = 0 := by simpa [nz] using hn
  funext k
  have hb : (x &&& (2 ^ 105 - 1)).testBit k.val = false := by rw [h0, Nat.zero_testBit]
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true k.isLt, Bool.and_true] at hb
  rw [vec, toVecD_apply, Pi.zero_apply, hb]
  rfl

theorem xorSelL_mem {X : Submodule (ZMod 2) (Fin 105 → ZMod 2)} (mask : ℕ) {L : List ℕ}
    (hL : ∀ i < L.length, vec (L.getD i 0) ∈ X) : vec (xorSelL mask L) ∈ X := by
  have := xorSel_mem (X := X) mask (L := L.toArray) fun i hi => by
    rw [toArray_getElem!]
    exact hL i (by simpa using hi)
  rwa [xorSel_eq, List.toList_toArray] at this

theorem xorSelL_mem_spanB (mask : ℕ) (B : List ℕ) : vec (xorSelL mask B) ∈ spanB B.toArray :=
  xorSelL_mem mask fun i hi =>
    Submodule.subset_span ⟨⟨i, by simpa using hi⟩, by simp only [toArray_getElem!]⟩

theorem mem_of_derivOKL {taus : Array (Array ℕ)} {X : Submodule (ZMod 2) (Fin 105 → ZMod 2)}
    (hX : IsTauInv taus X) {m : ℕ} (hm : vec m ∈ X) {L : List ℕ} {src : List (ℕ × ℕ)}
    (h : derivOKL (tabL taus) m L src = true) : ∀ t < L.length, vec (L.getD t 0) ∈ X := by
  intro t ht
  have h' : derivOK taus m L.toArray src.toArray = true := by
    rw [derivOK_eq, List.toList_toArray, List.toList_toArray]
    exact h
  have := mem_of_derivOK hX hm h' t (by simpa using ht)
  rwa [toArray_getElem!] at this

theorem add_ones_mem_of_derivOK {taus : Array (Array ℕ)}
    {X : Submodule (ZMod 2) (Fin 105 → ZMod 2)} (hX : IsTauInv taus X) {m : ℕ}
    (hm : vec m + vec onesV ∈ X) {L : Array ℕ} {src : Array (ℕ × ℕ)}
    (h : derivOK taus m L src = true) : ∀ t < L.size, vec L[t]! + vec onesV ∈ X := by
  rw [derivOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨h0, h⟩ := h
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · rw [h0]
      exact hm
    · have := h t (List.mem_range.mpr ht)
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
      rcases this with h' | ⟨⟨hs, hp⟩, heq⟩
      · omega
      · rw [heq, vec_actV]
        have hmem := hX _ hs _ (ih _ hp (lt_trans hp ht))
        convert hmem using 1
        funext k
        simp only [Function.comp_apply, Pi.add_apply, vec_onesV]

theorem add_ones_mem_of_derivOKL {taus : Array (Array ℕ)}
    {X : Submodule (ZMod 2) (Fin 105 → ZMod 2)} (hX : IsTauInv taus X) {m : ℕ}
    (hm : vec m + vec onesV ∈ X) {L : List ℕ} {src : List (ℕ × ℕ)}
    (h : derivOKL (tabL taus) m L src = true) :
    ∀ t < L.length, vec (L.getD t 0) + vec onesV ∈ X := by
  intro t ht
  have h' : derivOK taus m L.toArray src.toArray = true := by
    rw [derivOK_eq, List.toList_toArray, List.toList_toArray]
    exact h
  have := add_ones_mem_of_derivOK hX hm h' t (by simpa using ht)
  rwa [toArray_getElem!] at this

theorem xorGo_xor (c : ℕ) : ∀ (m : ℕ) (L : List ℕ) (acc : ℕ),
    xorGo m L (acc ^^^ c) = xorGo m L acc ^^^ c
  | _, [], _ => rfl
  | m, a :: L, acc => by
    rw [xorGo, xorGo]
    by_cases hb : m.testBit 0 = true
    · rw [if_pos hb, if_pos hb]
      have e : acc ^^^ c ^^^ a = acc ^^^ a ^^^ c := by
        rw [Nat.xor_assoc, Nat.xor_comm c a, ← Nat.xor_assoc]
      rw [e]
      exact xorGo_xor c (m / 2) L (acc ^^^ a)
    · rw [if_neg hb, if_neg hb]
      exact xorGo_xor c (m / 2) L acc

theorem xorGo_map_xor (c : ℕ) : ∀ (m : ℕ) (L : List ℕ) (acc : ℕ),
    xorGo m (L.map (· ^^^ c)) acc = xorGo m L acc ∨
      xorGo m (L.map (· ^^^ c)) acc = xorGo m L acc ^^^ c
  | _, [], _ => Or.inl rfl
  | m, a :: L, acc => by
    rw [List.map_cons, xorGo, xorGo]
    by_cases hb : m.testBit 0 = true
    · rw [if_pos hb, if_pos hb]
      have e : acc ^^^ (a ^^^ c) = acc ^^^ a ^^^ c := by rw [Nat.xor_assoc]
      rw [e]
      rcases xorGo_map_xor c (m / 2) L (acc ^^^ a ^^^ c) with h | h
      · rw [h, xorGo_xor c (m / 2) L (acc ^^^ a)]
        exact Or.inr rfl
      · rw [h, xorGo_xor c (m / 2) L (acc ^^^ a), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        exact Or.inl rfl
    · rw [if_neg hb, if_neg hb]
      exact xorGo_map_xor c (m / 2) L acc

theorem xorSelL_map_xor (c mask : ℕ) (L : List ℕ) :
    xorSelL mask (L.map (· ^^^ c)) = xorSelL mask L ∨
      xorSelL mask (L.map (· ^^^ c)) = xorSelL mask L ^^^ c :=
  xorGo_map_xor c mask L 0

theorem isTauInv_sup_ones {taus : Array (Array ℕ)} {Y : Submodule (ZMod 2) (Fin 105 → ZMod 2)}
    (hY : IsTauInv taus Y) : IsTauInv taus (Y ⊔ Submodule.span (ZMod 2) {vec onesV}) := by
  intro s hs F hF
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hF
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have e : (y + a • vec onesV) ∘ tauF taus[s]! = y ∘ tauF taus[s]! + a • vec onesV := by
    funext k
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, vec_onesV]
  rw [e]
  exact Submodule.add_mem_sup (hY s hs y hy) (Submodule.mem_span_singleton.mpr ⟨a, rfl⟩)

theorem finrank_sup_ones_le (Y : Submodule (ZMod 2) (Fin 105 → ZMod 2)) :
    finrank (ZMod 2) ↥(Y ⊔ Submodule.span (ZMod 2) {vec onesV}) ≤ finrank (ZMod 2) Y + 1 := by
  refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ?_ _)
  have := finrank_span_le_card (R := ZMod 2) ({vec onesV} : Set (Fin 105 → ZMod 2))
  simpa using this

theorem isTauInv_spanB_of_closedCL {taus : Array (Array ℕ)} {B coef : List ℕ}
    (h : closedCL (tabL taus) B coef = true) : IsTauInv taus (spanB B.toArray) :=
  isTauInv_spanB_of_forall fun t ht s hs =>
    ⟨coef.toArray[6 * t + s]!, forall_of_closedC (closedC_of_closedCL h) t ht s hs⟩

theorem le_finrank_of_echOKL {Y : Submodule (ZMod 2) (Fin 105 → ZMod 2)} {N : ℕ}
    {L masks piv : List ℕ} (hL : ∀ t < L.length, vec (L.getD t 0) ∈ Y)
    (h : echOKL N L masks piv = true) : N ≤ finrank (ZMod 2) Y := by
  rw [echOKL, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hm, hp⟩, hg⟩ := h
  have hs := echGo_spec L _ [] _ hg
  have spec : ∀ k < N, piv.getD k 0 < 105 ∧
      (xorSelL (masks.getD k 0) L).testBit (piv.getD k 0) = true ∧
        ∀ j < k, (xorSelL (masks.getD k 0) L).testBit (piv.getD j 0) = false := by
    intro k hk
    obtain ⟨h1, h2, -, h4⟩ := hs k (by rw [List.length_take]; omega)
      (by rw [List.length_take]; omega)
    rw [getD_take_of_lt piv hk] at h1
    rw [getD_take_of_lt piv hk, getD_take_of_lt masks hk] at h2
    refine ⟨h1, h2, fun j hj => ?_⟩
    have := h4 j hj
    rwa [getD_take_of_lt piv (lt_trans hj hk), getD_take_of_lt masks hk] at this
  have hli : LinearIndependent (ZMod 2)
      (fun k : Fin N => vec (xorSelL (masks.getD k.val 0) L)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k₀
    induction k₀ using Fin.strong_induction_on with
    | h k₀ ih =>
      obtain ⟨hpiv, hset, -⟩ := spec k₀.val k₀.isLt
      have hcoord : (∑ k : Fin N,
          (g k • vec (xorSelL (masks.getD k.val 0) L)) ⟨piv.getD k₀.val 0, hpiv⟩) = 0 := by
        have h := congrFun hg ⟨piv.getD k₀.val 0, hpiv⟩
        rw [Fintype.sum_apply, Pi.zero_apply] at h
        exact h
      have hsingle : (∑ k : Fin N,
          (g k • vec (xorSelL (masks.getD k.val 0) L)) ⟨piv.getD k₀.val 0, hpiv⟩) =
          (g k₀ • vec (xorSelL (masks.getD k₀.val 0) L)) ⟨piv.getD k₀.val 0, hpiv⟩ := by
        refine Finset.sum_eq_single k₀ ?_ ?_
        · intro b _ hbne
          rw [Pi.smul_apply]
          have hbval : b.val ≠ k₀.val := fun h => hbne (Fin.ext h)
          rcases lt_or_gt_of_ne hbval with hlt | hgt
          · rw [ih b (Fin.lt_iff_val_lt_val.mpr hlt), zero_smul]
          · have hbit0 : (vec (xorSelL (masks.getD b.val 0) L))
                ⟨piv.getD k₀.val 0, hpiv⟩ = 0 := by
              rw [vec, toVecD_apply, (spec b.val b.isLt).2.2 k₀.val hgt,
                if_neg Bool.false_ne_true]
            rw [hbit0, smul_zero]
        · intro hmem
          exact absurd (Finset.mem_univ k₀) hmem
      have hbit1 : (vec (xorSelL (masks.getD k₀.val 0) L)) ⟨piv.getD k₀.val 0, hpiv⟩ = 1 := by
        rw [vec, toVecD_apply, hset, if_pos rfl]
      rw [hsingle, Pi.smul_apply, hbit1, smul_eq_mul, mul_one] at hcoord
      exact hcoord
  let v : Fin N → Y := fun k => ⟨vec (xorSelL (masks.getD k.val 0) L), xorSelL_mem _ hL⟩
  have hv : LinearIndependent (ZMod 2) v := LinearIndependent.of_comp Y.subtype hli
  have hle := hv.fintype_card_le_finrank
  rwa [Fintype.card_fin] at hle

theorem false_of_mem_small {taus : Array (Array ℕ)}
    {X Z : Submodule (ZMod 2) (Fin 105 → ZMod 2)} {d : ℕ} (hX : IsIrredTau taus X d)
    {w : Fin 105 → ZMod 2} (hwX : w ∈ X) (hwZ : w ∈ Z) (hw0 : w ≠ 0) (hZ : IsTauInv taus Z)
    (hZd : finrank (ZMod 2) Z < d) : False := by
  have hinv : IsTauInv taus (X ⊓ Z) := fun s hs F hF => ⟨hX.1 s hs F hF.1, hZ s hs F hF.2⟩
  have hne : X ⊓ Z ≠ ⊥ := by
    intro h0
    apply hw0
    have : w ∈ X ⊓ Z := ⟨hwX, hwZ⟩
    rwa [h0, Submodule.mem_bot] at this
  have hle := hX.2.2 _ hinv inf_le_left hne
  have h1 : finrank (ZMod 2) X ≤ finrank (ZMod 2) Z :=
    Submodule.finrank_mono (le_trans hle inf_le_right)
  have h2 : finrank (ZMod 2) X = d := hX.2.1
  omega

theorem isEmpty_eq_false_of_length_pos {l : List ℕ} (h : 0 < l.length) : l.isEmpty = false := by
  cases l with
  | nil => exact absurd h (Nat.lt_irrefl 0)
  | cons _ _ => rfl

theorem false_of_noneCL {taus : Array (Array ℕ)} {X : Submodule (ZMod 2) (Fin 105 → ZMod 2)}
    {d : ℕ} (hX : IsIrredTau taus X d) (hd : d ∈ noneDims) {m : ℕ} (hm : vec m ∈ X)
    {c : NoneRec} (h : noneCL (tabL taus) m c = true) : False := by
  rw [noneCL, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hder, hech⟩, hB⟩, hcov⟩, -⟩ := h
  have hL := mem_of_derivOKL hX.1 hm hder
  rw [coverOwn, List.all_eq_true] at hcov
  have hc := hcov d hd
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with he | ⟨hB0, hBd⟩
  · have := le_finrank_of_echOKL hL hech
    rw [hX.2.1] at this
    omega
  · rw [isEmpty_eq_false_of_length_pos hB0, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true,
      beq_iff_eq] at hB
    obtain ⟨⟨hnz, hmB⟩, hcl⟩ := hB
    refine false_of_mem_small hX (xorSelL_mem c.sel hL) ?_ (vec_ne_zero_of_nz hnz)
      (isTauInv_spanB_of_closedCL hcl) ?_
    · rw [← hmB]
      exact xorSelL_mem_spanB c.mB c.B
    · have := finrank_spanB_le c.B.toArray
      rw [List.size_toArray] at this
      omega

theorem false_of_noneCL_partner {taus : Array (Array ℕ)}
    {X : Submodule (ZMod 2) (Fin 105 → ZMod 2)} {d : ℕ} (hX : IsIrredTau taus X d)
    (hd : d ∈ noneDims) {x m : ℕ} (hm : vec m ∈ X) (hxm : x ^^^ m = onesV) {c : NoneRec}
    (h : noneCL (tabL taus) x c = true) (hp : c.pair = 1) : False := by
  rw [noneCL, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hder, hech⟩, hB⟩, -⟩, hpc⟩ := h
  have hpc' : coverPartner c = true := by
    rw [hp] at hpc
    simpa using hpc
  have hx : x = m ^^^ onesV := by
    rw [← hxm, Nat.xor_comm x m, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hm' : m = x ^^^ onesV := by
    rw [← hxm, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [coverPartner, List.all_eq_true] at hpc'
  have hc := hpc' d hd
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with he | ⟨⟨hB0, hnz⟩, hBd⟩
  · have hxY : vec x ∈ X ⊔ Submodule.span (ZMod 2) {vec onesV} := by
      rw [hx, vec105_xor]
      exact Submodule.add_mem_sup hm (Submodule.mem_span_singleton_self _)
    have hL := mem_of_derivOKL (isTauInv_sup_ones hX.1) hxY hder
    have h1 := le_finrank_of_echOKL hL hech
    have h2 := finrank_sup_ones_le X
    rw [hX.2.1] at h2
    omega
  · rw [isEmpty_eq_false_of_length_pos hB0, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true,
      beq_iff_eq] at hB
    obtain ⟨⟨-, hmB⟩, hcl⟩ := hB
    have hL1 := add_ones_mem_of_derivOKL hX.1 (by rw [← vec105_xor, ← hm']; exact hm) hder
    have hL' : ∀ i < (c.L.map (· ^^^ onesV)).length,
        vec ((c.L.map (· ^^^ onesV)).getD i 0) ∈ X := by
      intro i hi
      rw [List.length_map] at hi
      have e : (c.L.map (· ^^^ onesV)).getD i 0 = c.L.getD i 0 ^^^ onesV := by
        simp [List.getD_eq_getElem?_getD, hi]
      rw [e, vec105_xor]
      exact hL1 i hi
    refine false_of_mem_small hX (xorSelL_mem c.sel hL') ?_ (vec_ne_zero_of_nz hnz)
      (isTauInv_sup_ones (isTauInv_spanB_of_closedCL hcl)) ?_
    · have hB' : vec (xorSelL c.sel c.L) ∈ spanB c.B.toArray := by
        rw [← hmB]
        exact xorSelL_mem_spanB c.mB c.B
      rcases xorSelL_map_xor onesV c.sel c.L with e | e
      · rw [e]
        exact Submodule.mem_sup_left hB'
      · rw [e, vec105_xor]
        exact Submodule.add_mem_sup hB' (Submodule.mem_span_singleton_self _)
    · have h1 := finrank_sup_ones_le (spanB c.B.toArray)
      have h2 := finrank_spanB_le c.B.toArray
      rw [List.size_toArray] at h2
      omega

theorem entryOK_spec {tl : List (List ℕ)} {a b m : ℕ} {ent : ℕ × NoneRec × NoneRec}
    (h : entryOK tl a b ent = true) (hm : m = a ∨ m = b) (hnz : nz m = true) :
    (∃ r, noneCL tl m r = true) ∨
      ∃ x r, noneCL tl x r = true ∧ r.pair = 1 ∧ x ^^^ m = onesV := by
  have key : ∀ x₁ x₂, (m = x₁ ∨ m = x₂) → (noneCL tl x₁ ent.2.1 &&
      (!nz x₂ || (ent.2.1.pair == 1 && x₁ ^^^ x₂ == onesV) || noneCL tl x₂ ent.2.2)) = true →
      (∃ r, noneCL tl m r = true) ∨
        ∃ x r, noneCL tl x r = true ∧ r.pair = 1 ∧ x ^^^ m = onesV := by
    rintro x₁ x₂ (rfl | rfl) h
    · rw [Bool.and_eq_true] at h
      exact Or.inl ⟨_, h.1⟩
    · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨h1, (h2 | ⟨hp, hx⟩) | h2⟩ := h
      · rw [hnz] at h2
        exact absurd h2 (by decide)
      · exact Or.inr ⟨x₁, _, h1, hp, hx⟩
      · exact Or.inl ⟨_, h2⟩
  rw [entryOK] at h
  by_cases hw : (ent.1 == 0) = true
  · simp only [if_pos hw] at h
    exact key a b hm h
  · simp only [if_neg hw] at h
    exact key b a hm.symm h

theorem entryOK_of_checkNoneFrom {tl : List (List ℕ)} {od : OrbData} :
    ∀ (es : List (ℕ × NoneRec × NoneRec)) (n : ℕ), checkNoneFrom tl od n es = true →
      ∀ k < es.length, entryOK tl (expand od (64 + (n + k))) (expand od (63 - (n + k)))
        (es.getD k default) = true
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | e :: es, n, h, k, hk => by
    rw [checkNoneFrom, Bool.and_eq_true, ← expand_eq, ← expand_eq] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := entryOK_of_checkNoneFrom es (n + 1) h.2 k (by simpa using hk)
      have e : n + (k + 1) = n + 1 + k := by omega
      rw [e]
      simpa using this

theorem checkNoneFrom_append (tl : List (List ℕ)) (od : OrbData) :
    ∀ (l₁ l₂ : List (ℕ × NoneRec × NoneRec)) (n : ℕ),
      checkNoneFrom tl od n (l₁ ++ l₂) =
        (checkNoneFrom tl od n l₁ && checkNoneFrom tl od (n + l₁.length) l₂)
  | [], l₂, n => by rw [List.nil_append, checkNoneFrom, List.length_nil, Nat.add_zero,
      Bool.true_and]
  | e :: l₁, l₂, n => by
    rw [List.cons_append, checkNoneFrom, checkNoneFrom, checkNoneFrom_append tl od l₁ l₂ (n + 1),
      Bool.and_assoc, List.length_cons]
    have e : n + 1 + l₁.length = n + (l₁.length + 1) := by omega
    rw [e]

theorem checkNoneFrom_split {tl : List (List ℕ)} {od : OrbData} {n : ℕ} (m : ℕ)
    {es : List (ℕ × NoneRec × NoneRec)} (hm : m ≤ es.length)
    (h₁ : checkNoneFrom tl od n (es.take m) = true)
    (h₂ : checkNoneFrom tl od (n + m) (es.drop m) = true) :
    checkNoneFrom tl od n es = true := by
  rw [← List.take_append_drop m es, checkNoneFrom_append, List.length_take, Nat.min_eq_left hm,
    h₁, h₂, Bool.and_self]

theorem no_irred_of_noneCertData (hD : NoneCertData) {d : ℕ} (hd : d ∈ noneDims) {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = d) (ρ : SL4 →* (V ≃ₗ[ZMod 2] V)) : ¬ IsIrredGen ρ := by
  intro hirr
  have hd' : 0 < d ∧ d < 64 := by
    simp only [noneDims, List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; exact hd'.1)
  have hVd : finrank (ZMod 2) (Module.Dual (ZMod 2) V) = d := by
    rw [Subspace.dual_finrank_eq, hV]
  have : Nontrivial (Module.Dual (ZMod 2) V) :=
    Module.nontrivial_of_finrank_pos (by rw [hVd]; exact hd'.1)
  obtain ⟨i, v, hv0, hvn, hvU⟩ := exists_fixed_parabolic ρ (by rw [hV]; exact hd'.2)
  obtain ⟨j, f, hf0, hfn, hfU⟩ := exists_fixed_parabolic (dualRep ρ) (by rw [hVd]; exact hd'.2)
  have hf : IsFixPj ρ j.val f := by
    refine ⟨fun u hu w => ?_, fun w => ?_⟩
    · have : dualRep ρ u⁻¹ f w = f w :=
        congrArg (fun φ : Module.Dual (ZMod 2) V => φ w) (hfU u⁻¹ (U.inv_mem hu))
      rwa [dualRep_apply, inv_inv] at this
    · have : dualRep ρ (nn j) f w = f w := congrArg (fun φ : Module.Dual (ZMod 2) V => φ w) hfn
      rwa [dualRep_apply, nn_inv] at this
  obtain ⟨dj, hT, hrest⟩ := hD j.val j.isLt
  obtain ⟨od, hO, es, hl, hS⟩ := hrest i.val i.isLt
  have hinj := iota_injective hirr hT hf hf0
  have hX := isTauInv_range_iota hT hf
  have hdim : finrank (ZMod 2) (LinearMap.range (iota ρ dj f)) = d := by
    rw [LinearMap.finrank_range_of_inj hinj, hV]
  have hF : ∀ s ∈ orbGens i.val, iota ρ dj f v ∘ tauF dj.tau[s]! = iota ρ dj f v := by
    intro s hs
    have hs6 : s < 6 := by
      simp only [orbGens, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> omega
    rw [← iota_gen ρ hT hf hs6]
    congr 1
    simp only [orbGens, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact hvU _ (xx_mem 0)
    · exact hvU _ (xx_mem 1)
    · exact hvU _ (xx_mem 2)
    · exact hvn
  have hF0 : iota ρ dj f v ≠ 0 := by
    intro h0
    exact hv0 (hinj (h0.trans (map_zero _).symm))
  obtain ⟨c, hc, hFc, -⟩ := eq_vec_expand hO hF
  have hm : vec (expand od c) ∈ LinearMap.range (iota ρ dj f) := hFc ▸ ⟨v, rfl⟩
  have hm0 : vec (expand od c) ≠ 0 := hFc ▸ hF0
  have hXirr : IsIrredTau dj.tau (LinearMap.range (iota ρ dj f)) d :=
    ⟨hX, hdim, range_iota_le hirr hT hf⟩
  obtain ⟨k, hk, hck⟩ : ∃ k < 64, c = 64 + k ∨ c = 63 - k := by
    by_cases h64 : 64 ≤ c
    · exact ⟨c - 64, by omega, Or.inl (by omega)⟩
    · exact ⟨63 - c, by omega, Or.inr (by omega)⟩
  have hent := entryOK_of_checkNoneFrom es 0 hS k (by omega)
  rw [Nat.zero_add] at hent
  have hcm : expand od c = expand od (64 + k) ∨ expand od c = expand od (63 - k) := by
    rcases hck with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases entryOK_spec hent hcm (nz_of_vec_ne_zero hm0) with ⟨r, hr⟩ | ⟨x, r, hr, hp, hx⟩
  · exact false_of_noneCL hXirr hd hm hr
  · exact false_of_noneCL_partner hXirr hd hm hx hr hp

end CFSG.LargeExtraspecial.SL4Mod
