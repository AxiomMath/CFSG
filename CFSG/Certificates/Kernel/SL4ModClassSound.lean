module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoOversize
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoSmall
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoRef
public import Certificates.Data.Kernel.SL4ModClassCerts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Module Native CFSG.Sporadic.SmallF2.Native Matrix

@[expose] def ClassCertData (d : ℕ) (refs : Array (Array (Array ℕ))) : Prop :=
  ∀ j < 3, ∃ dd : CosetData, checkTau j dd = true ∧ ∀ i < 3, ∃ od : OrbData,
    checkOrb dd i od = true ∧ ∀ c < 128, c ≠ 0 →
      ∃ cert, validClass d refs dd.tau (expand od c) cert = true

@[expose] def certOf (c : ClassRec) (k : ℕ) : ClassCert :=
  { L := c.L.toArray, src := c.src.toArray, kind := k, masks := c.masks.toArray,
    piv := c.piv.toArray, sel := c.sel, B := c.B.toArray, coef := c.coef.toArray, mB := c.mB,
    ref := c.ref }

theorem getD_take_of_lt {α : Type} (l : List α) {n k : ℕ} (hk : k < n) (a : α) :
    (l.take n).getD k a = l.getD k a := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hk, if_true]

theorem getD_drop {α : Type} (l : List α) (i k : ℕ) (a : α) :
    (l.drop i).getD k a = l.getD (i + k) a := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem toArray_getElem! (l : List ℕ) (k : ℕ) : l.toArray[k]! = l.getD k 0 := by
  rw [getElem!_eq_toList_getD, List.toList_toArray]
  rfl

theorem refsL_getD (refs : Array (Array (Array ℕ))) (r : ℕ) :
    (refsL refs).getD r [] = (refs[r]!).toList.map Array.toList := by
  rw [refsL, getElem!_eq_toList_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases refs.toList[r]? <;> rfl

theorem echGo_spec (L : List ℕ) (ms : List ℕ) : ∀ (prev ps : List ℕ), echGo L prev ms ps = true →
    ∀ k, k < ms.length → k < ps.length →
      ps.getD k 0 < 105 ∧ (xorSelL (ms.getD k 0) L).testBit (ps.getD k 0) = true ∧
        (∀ q ∈ prev, (xorSelL (ms.getD k 0) L).testBit q = false) ∧
        ∀ j < k, (xorSelL (ms.getD k 0) L).testBit (ps.getD j 0) = false := by
  induction ms with
  | nil =>
    intro _ _ _ k hk
    exact absurd hk (Nat.not_lt_zero k)
  | cons mk ms ih =>
    intro prev ps h k hk hk'
    cases ps with
    | nil => exact absurd hk' (Nat.not_lt_zero k)
    | cons p ps =>
      rw [echGo, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at h
      obtain ⟨⟨⟨hp, hset⟩, hprev⟩, hrest⟩ := h
      cases k with
      | zero =>
        refine ⟨hp, hset, fun q hq => ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
        simpa using hprev q hq
      | succ k =>
        obtain ⟨h1, h2, h3, h4⟩ := ih (p :: prev) ps hrest k
          (by simpa using hk) (by simpa using hk')
        refine ⟨by simpa using h1, by simpa using h2, fun q hq => ?_, fun j hj => ?_⟩
        · simpa using h3 q (List.mem_cons_of_mem p hq)
        · cases j with
          | zero => simpa using h3 p List.mem_cons_self
          | succ j => simpa using h4 j (by omega)

theorem echelonOK_of_echOKL {N n : ℕ} {L masks piv : List ℕ} (h : echOKL N L masks piv = true)
    (hn : n ≤ N) : echelonOK n L.toArray masks.toArray piv.toArray = true := by
  rw [echOKL, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hm, hp⟩, hg⟩ := h
  have hs := echGo_spec L _ [] _ hg
  have spec : ∀ k < n, piv.getD k 0 < 105 ∧
      (xorSelL (masks.getD k 0) L).testBit (piv.getD k 0) = true ∧
        ∀ j < k, (xorSelL (masks.getD k 0) L).testBit (piv.getD j 0) = false := by
    intro k hk
    have hkN : k < N := by omega
    obtain ⟨h1, h2, -, h4⟩ := hs k (by rw [List.length_take]; omega)
      (by rw [List.length_take]; omega)
    rw [getD_take_of_lt piv hkN] at h1
    rw [getD_take_of_lt piv hkN, getD_take_of_lt masks hkN] at h2
    refine ⟨h1, h2, fun j hj => ?_⟩
    have hjN : j < N := by omega
    have := h4 j hj
    rwa [getD_take_of_lt piv hjN, getD_take_of_lt masks hkN] at this
  rw [echelonOK, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    List.all_eq_true]
  refine ⟨⟨by simp only [List.size_toArray]; omega, by simp only [List.size_toArray]; omega⟩,
    fun k hk => ?_⟩
  rw [List.mem_range] at hk
  obtain ⟨h1, h2, -⟩ := spec k hk
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  simp only [toArray_getElem!, xorSel_eq, List.toList_toArray]
  refine ⟨⟨h1, h2⟩, fun j hj => ?_⟩
  rw [List.mem_range] at hj
  rw [Bool.or_eq_true, decide_eq_true_eq]
  by_cases hjk : j ≤ k
  · exact Or.inl hjk
  · refine Or.inr ?_
    rw [(spec j hj).2.2 k (by omega)]
    rfl

theorem closedGo_spec (tl : List (List ℕ)) (B : List ℕ) : ∀ (bs cf : List ℕ),
    closedGo tl B bs cf = true → ∀ t < bs.length, ∀ s < 6,
      xorSelL (cf.getD (6 * t + s) 0) B = actVL (tl.getD s []) (bs.getD t 0)
  | [], _, _, t, ht, _, _ => absurd ht (Nat.not_lt_zero t)
  | b :: bs, cf, h, t, ht, s, hs => by
    rw [closedGo, Bool.and_eq_true, List.all_eq_true] at h
    cases t with
    | zero =>
      have := h.1 s (List.mem_range.mpr hs)
      simpa using this
    | succ t =>
      have := closedGo_spec tl B bs (cf.drop 6) h.2 t (by simpa using ht) s hs
      rw [getD_drop] at this
      have e : 6 + (6 * t + s) = 6 * (t + 1) + s := by omega
      rw [e] at this
      simpa using this

theorem closedC_of_closedCL {taus : Array (Array ℕ)} {B coef : List ℕ}
    (h : closedCL (tabL taus) B coef = true) : closedC taus B.toArray coef.toArray = true := by
  have hsp := closedGo_spec (tabL taus) B B coef h
  rw [closedC, List.all_eq_true]
  intro t ht
  rw [List.mem_range, List.size_toArray] at ht
  rw [List.all_eq_true]
  intro s hs
  rw [List.mem_range] at hs
  have hts := hsp t ht s hs
  rw [tabL_getD] at hts
  rw [beq_iff_eq, toArray_getElem! coef, toArray_getElem! B, xorSel_eq, actV_eq,
    List.toList_toArray, hts]

theorem refOK_of_refOKL {taus : Array (Array ℕ)} {L : List ℕ} {refs : Array (Array (Array ℕ))}
    {r : ℕ} (h : refOKL (tabL taus) L ((refsL refs).getD r []) = true) :
    refOK taus L.toArray refs[r]! = true := by
  rw [refsL_getD, refOKL, Bool.and_eq_true, beq_iff_eq, List.length_map, Array.length_toList,
    List.all_eq_true] at h
  rw [refOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨h.1, fun s hs => ?_⟩
  have hs' := h.2 s hs
  rw [List.mem_range] at hs
  have hrow : ((refs[r]!).toList.map Array.toList).getD s [] = (refs[r]!)[s]!.toList := by
    rw [getElem!_eq_toList_getD (refs[r]!), List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (refs[r]!).toList[s]? <;> rfl
  rw [hrow, Bool.and_eq_true, beq_iff_eq, Array.length_toList, List.all_eq_true] at hs'
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.size_toArray]
  refine ⟨hs'.1, fun k hk => ?_⟩
  have hk' := hs'.2 k hk
  rw [beq_iff_eq, tabL_getD] at hk'
  rw [beq_iff_eq, xorSel_eq, actV_eq, List.toList_toArray, toArray_getElem! L k,
    getElem!_eq_toList_getD (refs[r]!)[s]!]
  exact hk'

theorem validClass_certOf {d k : ℕ} {refs : Array (Array (Array ℕ))} {taus : Array (Array ℕ)}
    {m : ℕ} {c : ClassRec} (hd : derivOKL (tabL taus) m c.L c.src = true)
    (hk : kindOKL d (refsL refs) (tabL taus) c k = true)
    (h0 : k = 0 → ∃ N, d + 1 ≤ N ∧ echOKL N c.L c.masks c.piv = true)
    (h1 : k = 1 → (nz (xorSelL c.sel c.L) && xorSelL c.mB c.B == xorSelL c.sel c.L &&
      closedCL (tabL taus) c.B c.coef) = true) :
    validClass d refs taus m (certOf c k) = true := by
  rw [validClass, Bool.and_eq_true]
  refine ⟨by rw [derivOK_eq]; exact hd, ?_⟩
  rw [kindOKL] at hk
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨N, hN, he⟩ := h0 rfl
    have e : (0 == 0) = true := rfl
    have e' : ((certOf c 0).kind == 0) = true := rfl
    rw [if_pos e, decide_eq_true_eq] at hk
    rw [if_pos e', Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hk, echelonOK_of_echOKL he hN⟩
  have n0 : ¬((k == 0) = true) := by simpa using hk0
  have n0' : ¬(((certOf c k).kind == 0) = true) := n0
  rw [if_neg n0] at hk
  rw [if_neg n0']
  by_cases hk1 : k = 1
  · subst hk1
    have h := h1 rfl
    have e : (1 == 1) = true := rfl
    have e' : ((certOf c 1).kind == 1) = true := rfl
    rw [if_pos e, decide_eq_true_eq] at hk
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    rw [if_pos e', Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨?_, hk⟩, ?_⟩, closedC_of_closedCL h.2⟩
    · rw [xorSel_eq]
      exact h.1.1
    · rw [xorSel_eq, xorSel_eq]
      exact h.1.2
  have n1 : ¬((k == 1) = true) := by simpa using hk1
  have n1' : ¬(((certOf c k).kind == 1) = true) := n1
  rw [if_neg n1] at hk
  rw [if_neg n1']
  by_cases hk2 : k = 2
  · subst hk2
    have e : (2 == 2) = true := rfl
    have e' : ((certOf c 2).kind == 2) = true := rfl
    rw [if_pos e, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at hk
    rw [if_pos e', Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    refine ⟨⟨hk.1.1, ?_⟩, refOK_of_refOKL hk.2⟩
    have := hk.1.2
    rwa [refsL, List.length_map, Array.length_toList] at this
  · have n2 : ¬((k == 2) = true) := by simpa using hk2
    rw [if_neg n2] at hk
    exact absurd hk Bool.false_ne_true

theorem validClass_of_validCL {taus : Array (Array ℕ)} {r14 r20 : Array (Array (Array ℕ))}
    {m : ℕ} {c : ClassRec} (h : validCL (tabL taus) (refsL r14) (refsL r20) m c = true) :
    validClass 14 r14 taus m (certOf c c.k14) = true ∧
      validClass 20 r20 taus m (certOf c c.k20) = true := by
  rw [validCL, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hd, he⟩, hs⟩, hk14⟩, hk20⟩ := h
  have hsm : c.k14 = 1 ∨ c.k20 = 1 → (nz (xorSelL c.sel c.L) &&
      xorSelL c.mB c.B == xorSelL c.sel c.L && closedCL (tabL taus) c.B c.coef) = true := by
    intro h1
    have h1' : (c.k14 == 1 || c.k20 == 1) = true := by
      rcases h1 with h1 | h1 <;> simp [h1]
    rwa [if_pos h1'] at hs
  refine ⟨validClass_certOf hd hk14 (fun h0 => ?_) (fun h1 => hsm (Or.inl h1)),
    validClass_certOf hd hk20 (fun h0 => ⟨21, le_rfl, ?_⟩) (fun h1 => hsm (Or.inr h1))⟩
  · by_cases h20 : c.k20 = 0
    · rw [if_pos (by simp [h20])] at he
      exact ⟨21, by norm_num, he⟩
    · rw [if_neg (by simpa using h20), if_pos (by simp [h0])] at he
      exact ⟨15, le_rfl, he⟩
  · rwa [if_pos (by simp [h0])] at he

theorem validCL_of_checkClassFrom {tl : List (List ℕ)} {r14 r20 : List (List (List ℕ))}
    {od : OrbData} : ∀ (cs : List ClassRec) (n : ℕ), checkClassFrom tl r14 r20 od n cs = true →
      ∀ k < cs.length, validCL tl r14 r20 (expand od (n + k)) (cs.getD k default) = true
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | c :: cs, n, h, k, hk => by
    rw [checkClassFrom, Bool.and_eq_true, ← expand_eq] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := validCL_of_checkClassFrom cs (n + 1) h.2 k (by simpa using hk)
      have e : n + (k + 1) = n + 1 + k := by omega
      rw [e]
      simpa using this

theorem checkClassFrom_append (tl : List (List ℕ)) (r14 r20 : List (List (List ℕ)))
    (od : OrbData) : ∀ (l₁ l₂ : List ClassRec) (n : ℕ),
      checkClassFrom tl r14 r20 od n (l₁ ++ l₂) =
        (checkClassFrom tl r14 r20 od n l₁ && checkClassFrom tl r14 r20 od (n + l₁.length) l₂)
  | [], l₂, n => by rw [List.nil_append, checkClassFrom, List.length_nil, Nat.add_zero,
      Bool.true_and]
  | c :: l₁, l₂, n => by
    rw [List.cons_append, checkClassFrom, checkClassFrom,
      checkClassFrom_append tl r14 r20 od l₁ l₂ (n + 1), Bool.and_assoc, List.length_cons]
    have e : n + 1 + l₁.length = n + (l₁.length + 1) := by omega
    rw [e]

theorem checkClassFrom_split {tl : List (List ℕ)} {r14 r20 : List (List (List ℕ))}
    {od : OrbData} {n : ℕ} (m : ℕ) {cs : List ClassRec} (hm : m ≤ cs.length)
    (h₁ : checkClassFrom tl r14 r20 od n (cs.take m) = true)
    (h₂ : checkClassFrom tl r14 r20 od (n + m) (cs.drop m) = true) :
    checkClassFrom tl r14 r20 od n cs = true := by
  rw [← List.take_append_drop m cs, checkClassFrom_append, List.length_take, Nat.min_eq_left hm,
    h₁, h₂, Bool.and_self]

theorem classCertData_of {r14 r20 : Array (Array (Array ℕ))}
    (h : ∀ j < 3, ∃ dd : CosetData, checkTau j dd = true ∧ ∀ i < 3, ∃ od : OrbData,
      checkOrb dd i od = true ∧ ∃ cs : List ClassRec, cs.length = 127 ∧
        checkClassFrom (tabL dd.tau) (refsL r14) (refsL r20) od 1 cs = true) :
    ClassCertData 14 r14 ∧ ClassCertData 20 r20 := by
  have key : ∀ j < 3, ∃ dd : CosetData, checkTau j dd = true ∧ ∀ i < 3, ∃ od : OrbData,
      checkOrb dd i od = true ∧ ∀ c < 128, c ≠ 0 → ∃ rc : ClassRec,
        validClass 14 r14 dd.tau (expand od c) (certOf rc rc.k14) = true ∧
          validClass 20 r20 dd.tau (expand od c) (certOf rc rc.k20) = true := by
    intro j hj
    obtain ⟨dd, hT, hd⟩ := h j hj
    refine ⟨dd, hT, fun i hi => ?_⟩
    obtain ⟨od, hO, cs, hl, hc⟩ := hd i hi
    refine ⟨od, hO, fun c hc128 hc0 => ?_⟩
    have hv := validCL_of_checkClassFrom cs 1 hc (c - 1) (by omega)
    have e : 1 + (c - 1) = c := by omega
    rw [e] at hv
    exact ⟨_, validClass_of_validCL hv⟩
  constructor
  all_goals
    intro j hj
    obtain ⟨dd, hT, hd⟩ := key j hj
    refine ⟨dd, hT, fun i hi => ?_⟩
    obtain ⟨od, hO, hc⟩ := hd i hi
    refine ⟨od, hO, fun c hc128 hc0 => ?_⟩
    obtain ⟨rc, h14, h20⟩ := hc c hc128 hc0
  · exact ⟨_, h14⟩
  · exact ⟨_, h20⟩

theorem classify_of_classCertData {d : ℕ} (hd0 : 0 < d) (hd : d < 64)
    {refs : Array (Array (Array ℕ))} (hD : ClassCertData d refs) {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V = d)
    {ρ : SL4 →* (V ≃ₗ[ZMod 2] V)} (hirr : IsIrredGen ρ) :
    ∃ r < refs.size, ∃ e : V ≃ₗ[ZMod 2] (Fin d → ZMod 2),
      ∀ (s : Fin 6) (v : V), e (ρ (genN s.val) v) = refMat d ((refs[r]!)[s.val]!) *ᵥ e v := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; exact hd0)
  have hVd : finrank (ZMod 2) (Module.Dual (ZMod 2) V) = d := by
    rw [Subspace.dual_finrank_eq, hV]
  have : Nontrivial (Module.Dual (ZMod 2) V) :=
    Module.nontrivial_of_finrank_pos (by rw [hVd]; exact hd0)
  obtain ⟨i, v, hv0, hvn, hvU⟩ := exists_fixed_parabolic ρ (by rw [hV]; exact hd)
  obtain ⟨j, f, hf0, hfn, hfU⟩ := exists_fixed_parabolic (dualRep ρ) (by rw [hVd]; exact hd)
  have hf : IsFixPj ρ j.val f := by
    refine ⟨fun u hu w => ?_, fun w => ?_⟩
    · have : dualRep ρ u⁻¹ f w = f w :=
        congrArg (fun φ : Module.Dual (ZMod 2) V => φ w) (hfU u⁻¹ (U.inv_mem hu))
      rwa [dualRep_apply, inv_inv] at this
    · have : dualRep ρ (nn j) f w = f w := congrArg (fun φ : Module.Dual (ZMod 2) V => φ w) hfn
      rwa [dualRep_apply, nn_inv] at this
  obtain ⟨dj, hT, hrest⟩ := hD j.val j.isLt
  obtain ⟨od, hO, hS⟩ := hrest i.val i.isLt
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
  obtain ⟨c, hc, hFc, hc0⟩ := eq_vec_expand hO hF
  obtain ⟨cert, hcert⟩ := hS c hc (hc0 hF0)
  have hm : vec (expand od c) ∈ LinearMap.range (iota ρ dj f) := hFc ▸ ⟨v, rfl⟩
  have hm0 : vec (expand od c) ≠ 0 := hFc ▸ hF0
  have hXirr : IsIrredTau dj.tau (LinearMap.range (iota ρ dj f)) d :=
    ⟨hX, hdim, range_iota_le hirr hT hf⟩
  rcases kind_cases hcert with hk | hk | hk
  · exact (false_of_validClass_oversize hXirr hm hcert hk).elim
  · exact (false_of_validClass_small hXirr hm hcert hk).elim
  · obtain ⟨hr, e, he⟩ := exists_equiv_of_validClass_ref hXirr hm hm0 hcert hk
    refine ⟨_, hr, (LinearEquiv.ofInjective (iota ρ dj f) hinj).trans e, fun s w => ?_⟩
    set w' := LinearEquiv.ofInjective (iota ρ dj f) hinj w with hw'
    have h2 : ∀ hmem : w'.1 ∘ tauF dj.tau[s.val]! ∈ LinearMap.range (iota ρ dj f),
        (⟨w'.1 ∘ tauF dj.tau[s.val]!, hmem⟩ : LinearMap.range (iota ρ dj f)) =
          LinearEquiv.ofInjective (iota ρ dj f) hinj (ρ (genN s.val) w) := by
      intro hmem
      apply Subtype.ext
      change w'.1 ∘ tauF dj.tau[s.val]! =
        (LinearEquiv.ofInjective (iota ρ dj f) hinj (ρ (genN s.val) w)).1
      have hw1 : w'.1 = iota ρ dj f w := rfl
      rw [hw1, LinearEquiv.ofInjective_apply]
      exact (iota_gen ρ hT hf s.2 w).symm
    have h1 := he s w'
    rw [h2] at h1
    simpa only [LinearEquiv.trans_apply] using h1

end CFSG.LargeExtraspecial.SL4Mod
