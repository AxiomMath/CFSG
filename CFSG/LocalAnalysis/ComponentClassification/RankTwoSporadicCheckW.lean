module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open scoped commutatorElement

@[expose] def keysAsc : List ℕ → Bool
  | a :: b :: l => decide (a < b) && keysAsc (b :: l)
  | _ => true

@[expose] def invK (n : ℕ) (t : Array ℕ) : Array ℕ :=
  (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)

@[expose] def validK (n : ℕ) (a : Array ℕ) : Bool := isInvA n a (invK n a)

@[expose] def GFac.okK (n : ℕ) (inX : Array ℕ → Bool) (basis : Array (Array ℕ)) (f : GFac) :
    Bool :=
  !(eqA n (maskA n basis f.t) (idA n)) && validK n f.c₁ && validK n f.c₂ && inX f.c₁ &&
    inX f.c₂ && commA n f.c₁ (maskA n basis f.t) && commA n f.c₂ (maskA n basis f.t)

@[expose] def NFac.okK (n : ℕ) (inX : Array ℕ → Bool) (basis : Array (Array ℕ)) (f : NFac) :
    Bool :=
  f.γ.all (GFac.okK n inX basis) && validK n (maskA n basis f.e) && validK n (gammaA n f.γ)

@[expose] def CFac.okK (n : ℕ) (inX : Array ℕ → Bool) (basis : Array (Array ℕ)) (f : CFac) :
    Bool :=
  validK n f.x₁ && validK n f.x₂ && inX f.x₁ && inX f.x₂ &&
    allLt basis.size fun k => commA n f.x₁ basis[k]! && commA n f.x₂ basis[k]!

@[expose] def enumOKK (n : ℕ) (gs : Array (Array ℕ)) (ps : List ℕ) (c : ArrCert) : Bool :=
  allLt gs.size (fun k => validK n gs[k]!) &&
    (decide (0 < c.pts.size) && c.pts[0]! == idA n &&
      (List.range c.pts.size).all (arrPointOK (leftA n gs) gs.size (validK n) c) &&
      keysAsc ((c.pts.toList.map (keyA n ps)).insertionSort (· ≤ ·)))

@[expose] def maskCert (n : ℕ) (basis : Array (Array ℕ)) : ArrCert :=
  let r := List.range (2 ^ basis.size)
  ⟨(r.map (maskA n basis)).toArray,
    (r.map fun i => ((List.range basis.size).map fun k => i ^^^ 2 ^ k).toArray).toArray,
    (r.map fun i => i - 2 ^ Nat.log2 i).toArray,
    (r.map Nat.log2).toArray⟩

@[expose] def witOKW (n : ℕ) (ps : List ℕ) (inX outX : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (basis : Array (Array ℕ)) (cE : ArrCert)
    (cs : Array ArrCert) : Wit → Bool
  | .order4 w m =>
    let y := powA n (nA n basis w) m
    w.all (NFac.okK n inX basis) && !(eqA n (compA n y y) (idA n)) &&
      eqA n (powA n y 4) (idA n)
  | .twoGroup gens k =>
    let gs := (gens.map fun l => powA n (nA n basis l.1) l.2).toArray
    let cP := cs[0]!
    gens.all (fun l => l.1.all (NFac.okK n inX basis)) && enumOKK n gs ps cP &&
      cP.pts.size == 2 ^ k && decide (countA outX cE < 2 ^ k)
  | .perfect gens comms x k conjs e g =>
    let gs := (gens.map fun l => powA n (gammaA n l.1) l.2).toArray
    let cP := cs[0]!
    let m := cP.pts.size
    let qs := (comms.map fun ij => commutatorA n cP.pts[ij.1]! cP.pts[ij.2]!).toArray
    let cQ := cs[1]!
    let xa := cP.pts[x]!
    let rs := (conjs.map fun p => conjA n cP.pts[p]! (compA n xa xa)).toArray
    let cR := cs[2]!
    allowPW && gens.all (fun l => l.1.all (GFac.okK n inX basis)) && enumOKK n gs ps cP &&
      comms.all (fun ij => decide (ij.1 < m) && decide (ij.2 < m)) && enumOKK n qs ps cQ &&
      cQ.pts.size == m && decide (x < m) && eqA n (powA n xa (2 ^ k)) (idA n) &&
      conjs.all (fun p => decide (p < m)) && enumOKK n rs ps cR && cR.pts.size == m &&
      decide (g < m) && !(commA n (maskA n basis e) cP.pts[g]!)
  | .inX => allowInX && allLt basis.size fun k => inX basis[k]!
  | .small => decide (cE.pts.size < 4)
  | .closing s t c kc v gens comms =>
    let gs := (gens.map fun l => powA n (prodA n (l.1.map (CFac.val n))) l.2).toArray
    let cP := cs[0]!
    let m := cP.pts.size
    let qs := (comms.map fun ij => commutatorA n cP.pts[ij.1]! cP.pts[ij.2]!).toArray
    let cQ := cs[1]!
    allowU && !(eqA n (maskA n basis s) (idA n)) && !(eqA n (maskA n basis t) (idA n)) &&
      validK n c && inX c && commA n c (maskA n basis t) && eqA n (powA n c (2 ^ kc)) (idA n) &&
      validK n (maskA n basis v) &&
      eqA n (commutatorA n (maskA n basis v) c) (maskA n basis s) &&
      gens.all (fun l => l.1.all (CFac.okK n inX basis)) && enumOKK n gs ps cP &&
      comms.all (fun ij => decide (ij.1 < m) && decide (ij.2 < m)) && enumOKK n qs ps cQ &&
      cQ.pts.size == m && memA n cP (maskA n basis s)

@[expose] def nodeOKW (n : ℕ) (ps : List ℕ) (inX outX : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (cS : ArrCert) (nodes : Array Node) (cN : Array ArrCert)
    (wcs : Array (Array ArrCert)) (i : ℕ) : Bool :=
  enumOKK n nodes[i]!.basis ps cN[i]! &&
    witOKW n ps inX outX allowPW allowInX allowU nodes[i]!.basis cN[i]! wcs[i]! nodes[i]!.wit &&
    (nodes[i]!.wit.isMono || allLt cS.pts.size fun p =>
      !(eqA n (compA n cS.pts[p]! cS.pts[p]!) (idA n)) ||
        !(allLt nodes[i]!.basis.size fun k => commA n cS.pts[p]! nodes[i]!.basis[k]!) ||
        memA n cN[i]! cS.pts[p]! || childOK n nodes cN i cS.pts[p]! nodes[i]!.children[p]!)

@[expose] def censusOKW (n : ℕ) (ps : List ℕ) (inX outX : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (sGens : Array (Array ℕ)) (roots : Array ℕ)
    (nodes : Array Node) (cS : ArrCert) (wcs : Array (Array ArrCert)) : Bool :=
  let cN := nodes.map fun nd => maskCert n nd.basis
  enumOKK n sGens ps cS && (allLt cS.pts.size fun p => rootOK n nodes cN cS.pts[p]! roots[p]!) &&
    allLt nodes.size (nodeOKW n ps inX outX allowPW allowInX allowU cS nodes cN wcs)

@[expose] def inRegsL (n : ℕ) (regs : Array (Array ℕ)) (a : Array ℕ) : Bool :=
  (List.range regs.size).any fun k => eqA n a regs[k]!

section Soundness

variable {n : ℕ}

theorem keysAsc_pairwise : ∀ l : List ℕ, keysAsc l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [keysAsc, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := keysAsc_pairwise (b :: l) h.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hc)

theorem invK_eq (t : Array ℕ) : invK n t = invCand n t := by
  unfold invCand invK
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem validK_eq : validK n = validA n := by
  funext a
  rw [validK, validA, invK_eq]

theorem GFac.okK_eq {inX : Array ℕ → Bool} {basis : Array (Array ℕ)} :
    GFac.okK n inX basis = GFac.ok n inX basis := by
  funext f
  simp only [GFac.okK, GFac.ok, validK_eq]

theorem NFac.okK_eq {inX : Array ℕ → Bool} {basis : Array (Array ℕ)} :
    NFac.okK n inX basis = NFac.ok n inX basis := by
  funext f
  simp only [NFac.okK, NFac.ok, validK_eq, GFac.okK_eq]

theorem CFac.okK_eq {inX : Array ℕ → Bool} {basis : Array (Array ℕ)} :
    CFac.okK n inX basis = CFac.ok n inX basis := by
  funext f
  simp only [CFac.okK, CFac.ok, validK_eq]

theorem enumOK_of_enumOKK {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (h : enumOKK n gs ps c = true) : enumOK n gs ps c = true := by
  simp only [enumOKK, validK_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [enumOK, arrCertOK, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨h.1, h.2.1, ?_⟩
  rw [List.mergeSort_eq_insertionSort (· ≤ ·)]
  exact keysAsc_pairwise _ h.2.2

theorem mem_closure_of_inRegsL {gens : Array (Array ℕ)} {prog : List (ℕ × ℕ)}
    (hslp : slpOK n gens prog = true) {a : Array ℕ} (hv : validA n a = true)
    (h : inRegsL n (slpRegs n gens prog) a = true) :
    permOfArr n a ∈ closure (permsA n gens) := by
  simp only [inRegsL, List.any_eq_true, List.mem_range] at h
  obtain ⟨k, hk, he⟩ := h
  obtain ⟨g, hg, hr⟩ := rep_slpRegs hslp k hk
  rw [eq_of_eqA (rep_of_validA hv) hr he]
  exact hg

variable {X : Subgroup (Equiv.Perm (Fin n))} {inX outX : Array ℕ → Bool}
  {basis : Array (Array ℕ)}

theorem witOKW_sound {ps : List ℕ} {allowPW allowInX allowU : Bool} {cE : ArrCert}
    {cs : Array ArrCert} (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ X → outX a = true)
    (hE : enumOK n basis ps cE = true) {w : Wit}
    (h : witOKW n ps inX outX allowPW allowInX allowU basis cE cs w = true) :
    MonoW X allowPW (closure (permsA n basis)) ∨ (w.isMono = false ∧
      (4 ≤ Nat.card (closure (permsA n basis)) →
        WitW X allowPW allowInX allowU (closure (permsA n basis)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : ∀ k < basis.size, validA n basis[k]! = true := fun k hk => enumOK_gens_valid hE hk
  cases w with
  | order4 w m =>
    simp only [witOKW, NFac.okK_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hw, h2⟩, h4⟩ := h
    obtain ⟨y, hyN, hy⟩ := rep_nA hin hb hw
    have hym := rep_powA hy m
    have h2' : ¬ (y ^ m) ^ 2 ^ 1 = 1 := by
      intro hc
      rw [pow_one, sq] at hc
      rw [(eqA_iff (rep_compA hym hym) rep_idA).2 hc] at h2
      exact Bool.noConfusion h2
    have h4' : (y ^ m) ^ 2 ^ (1 + 1) = 1 := eq_of_eqA (rep_powA hym 4) rep_idA h4
    have hord := orderOf_eq_prime_pow h2' h4'
    refine Or.inl (Or.inl ⟨y ^ m, pow_mem hyN m, ?_⟩)
    rw [hord]
    norm_num
  | twoGroup gens k =>
    simp only [witOKW, NFac.okK_eq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hgens, hP⟩, hsize⟩, hcount⟩ := h
    replace hP := enumOK_of_enumOKK hP
    refine Or.inr ⟨rfl, fun _ => Or.inl (Or.inr ⟨closure (permsA n
      (gens.map fun l => powA n (nA n basis l.1) l.2).toArray), ?_, ?_, ?_⟩)⟩
    · refine closure_le_of_rep fun l hl => ?_
      obtain ⟨y, hyN, hy⟩ := rep_nA hin hb (List.all_eq_true.mp hgens l hl)
      exact ⟨y ^ l.2, pow_mem hyN _, rep_powA hy _⟩
    · obtain ⟨-, hcard, -⟩ := enumOK_spec hps hP
      exact IsPGroup.of_card (n := k) (by rw [hcard, hsize])
    · obtain ⟨-, hcard, -⟩ := enumOK_spec hps hP
      rw [hcard, hsize]
      exact (card_inf_le_countA hps hE hout).trans_lt hcount
  | perfect gens comms x k conjs e g =>
    simp only [witOKW, GFac.okK_eq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Bool.not_eq_true', List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hPW, hgens⟩, hP⟩, hcomms⟩, hQ⟩, hQsize⟩, hx⟩, hxpow⟩, hconjs⟩, hR⟩,
      hRsize⟩, hg⟩, hnc⟩ := h
    replace hP := enumOK_of_enumOKK hP
    replace hQ := enumOK_of_enumOKK hQ
    replace hR := enumOK_of_enumOKK hR
    set gs := (gens.map fun l => powA n (gammaA n l.1) l.2).toArray
    set cP := cs[0]!
    set P := closure (permsA n gs)
    obtain ⟨hPmem, hPcard, hPval⟩ := enumOK_spec hps hP
    have hpt : ∀ i < cP.pts.size, permOfArr n cP.pts[i]! ∈ P := fun i hi => (hPmem _).2 ⟨i, hi, rfl⟩
    have hPΓ : P ≤ gammaE X (closure (permsA n basis)) := by
      refine closure_le_of_rep fun l hl => ?_
      obtain ⟨y, hyN, hy⟩ := rep_gammaA hin hb (List.all_eq_true.mpr (hgens l hl))
      exact ⟨y ^ l.2, pow_mem hyN _, rep_powA hy _⟩
    have hperf : ⁅P, P⁆ = P := commutator_eq_self_of_check hps hP hcomms hQ hQsize
    set xa := cP.pts[x]!
    have hxr := rep_of_validA (hPval x hx)
    have hxP : permOfArr n xa ∈ P := hpt x hx
    have hx2 : IsPGroup 2 (zpowers (permOfArr n xa)) := by
      have hpow : permOfArr n xa ^ 2 ^ k = 1 := eq_of_eqA (rep_powA hxr _) rep_idA hxpow
      obtain ⟨b, -, hb'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
      exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb'])
    have hgen : P ≤ closure {y | ∃ p ∈ P, y = p * permOfArr n xa ^ 2 * p⁻¹} := by
      set R := closure (permsA n (conjs.map fun p =>
        conjA n cP.pts[p]! (compA n xa xa)).toArray)
      have hRle : R ≤ closure {y | ∃ p ∈ P, y = p * permOfArr n xa ^ 2 * p⁻¹} := by
        refine closure_le_of_rep fun p hp => ?_
        have hpP := hpt p (hconjs p hp)
        refine ⟨_, subset_closure ⟨_, hpP, rfl⟩, ?_⟩
        rw [sq]
        exact rep_conjA (hPval p (hconjs p hp)) (rep_compA hxr hxr)
      have hRP : R ≤ P := by
        refine closure_le_of_rep fun p hp => ?_
        have hpP := hpt p (hconjs p hp)
        exact ⟨_, P.mul_mem (P.mul_mem hpP (P.mul_mem hxP hxP)) (P.inv_mem hpP),
          rep_conjA (hPval p (hconjs p hp)) (rep_compA hxr hxr)⟩
      obtain ⟨-, hRcard, -⟩ := enumOK_spec hps hR
      have hRP' : R = P := eq_of_le_of_card_ge hRP (by rw [hPcard, ← hRsize, hRcard])
      exact hRP' ▸ hRle
    have hncent : ¬ closure (permsA n basis) ≤ centralizer (P : Set (Equiv.Perm (Fin n))) := by
      intro hc
      obtain ⟨e', he'E, he'⟩ := rep_maskA hb e
      have hgr := rep_of_validA (hPval g hg)
      have := mem_centralizer_iff.mp (hc he'E) _ (hpt g hg)
      rw [(commA_iff he' hgr).2 this.symm] at hnc
      exact Bool.noConfusion hnc
    exact Or.inl (Or.inr ⟨hPW, P, hPΓ, hperf, hncent, _, hxP, hx2, hgen⟩)
  | inX =>
    simp only [witOKW, Bool.and_eq_true] at h
    obtain ⟨hX, hall⟩ := h
    refine Or.inr ⟨rfl, fun _ => Or.inr (Or.inr (Or.inl ⟨hX, ?_⟩))⟩
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hin _ (hb k hk) (allLt_spec hall hk)
  | small =>
    simp only [witOKW, decide_eq_true_eq] at h
    obtain ⟨-, hcard, -⟩ := enumOK_spec hps hE
    refine Or.inr ⟨rfl, fun h4 => ?_⟩
    rw [hcard] at h4
    omega
  | closing s t c kc v gens comms =>
    simp only [witOKW, CFac.okK_eq, validK_eq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Bool.not_eq_true', List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hU, hs1⟩, ht1⟩, hcv⟩, hcX⟩, hct⟩, hcpow⟩, hvv⟩, hvc⟩, hgens⟩, hP⟩,
      hcomms⟩, hQ⟩, hQsize⟩, hsP⟩ := h
    replace hP := enumOK_of_enumOKK hP
    replace hQ := enumOK_of_enumOKK hQ
    set E := closure (permsA n basis)
    obtain ⟨s', hs'E, hs'⟩ := rep_maskA hb s
    obtain ⟨t', ht'E, ht'⟩ := rep_maskA hb t
    obtain ⟨v', hv'E, hv'⟩ := rep_maskA hb v
    have hcr := rep_of_validA hcv
    have hne : ∀ {a : Array ℕ} {g : Equiv.Perm (Fin n)}, Rep n a g →
        eqA n a (idA n) = false → g ≠ 1 := by
      rintro a g ha hf rfl
      rw [(eqA_iff ha rep_idA).2 rfl] at hf
      exact Bool.noConfusion hf
    set gs := (gens.map fun l => powA n (prodA n (l.1.map (CFac.val n))) l.2).toArray
    set P := closure (permsA n gs)
    have hcf : ∀ f : CFac, CFac.ok n inX basis f = true →
        ∃ g ∈ ⁅X ⊓ centralizer (E : Set (Equiv.Perm (Fin n))),
          X ⊓ centralizer (E : Set (Equiv.Perm (Fin n)))⁆, Rep n (f.val n) g := by
      intro f hf
      simp only [CFac.ok, Bool.and_eq_true] at hf
      obtain ⟨⟨⟨⟨hv1, hv2⟩, hx1⟩, hx2⟩, hcb⟩ := hf
      have hr1 := rep_of_validA hv1
      have hr2 := rep_of_validA hv2
      have hcent : ∀ {a : Array ℕ}, Rep n a (permOfArr n a) →
          (∀ k < basis.size, commA n a basis[k]! = true) →
          permOfArr n a ∈ centralizer (E : Set (Equiv.Perm (Fin n))) := by
        intro a ha hk
        refine mem_centralizer_closure_of_commute ?_
        rintro _ ⟨k, hk', rfl⟩
        exact (commA_iff ha (rep_of_validA (hb k hk'))).1 (hk k hk')
      have hk1 : ∀ k < basis.size, commA n f.x₁ basis[k]! = true := fun k hk => by
        have := allLt_spec hcb hk
        simp only [Bool.and_eq_true] at this
        exact this.1
      have hk2 : ∀ k < basis.size, commA n f.x₂ basis[k]! = true := fun k hk => by
        have := allLt_spec hcb hk
        simp only [Bool.and_eq_true] at this
        exact this.2
      exact ⟨_, commutator_mem_commutator ⟨hin _ hv1 hx1, hcent hr1 hk1⟩
        ⟨hin _ hv2 hx2, hcent hr2 hk2⟩, rep_commutatorA hv1 hv2⟩
    have hPle : P ≤ ⁅X ⊓ centralizer (E : Set (Equiv.Perm (Fin n))),
        X ⊓ centralizer (E : Set (Equiv.Perm (Fin n)))⁆ := by
      refine closure_le_of_rep fun l hl => ?_
      obtain ⟨y, hy, hyr⟩ := rep_prodA (H := ⁅X ⊓ centralizer (E : Set (Equiv.Perm (Fin n))),
        X ⊓ centralizer (E : Set (Equiv.Perm (Fin n)))⁆) (l := l.1.map (CFac.val n)) (by
          intro a ha
          rw [List.mem_map] at ha
          obtain ⟨f, hf, rfl⟩ := ha
          exact hcf f (hgens l hl f hf))
      exact ⟨y ^ l.2, pow_mem hy _, rep_powA hyr _⟩
    have hperf : ⁅P, P⁆ = P := commutator_eq_self_of_check hps hP hcomms hQ hQsize
    have hc2 : IsPGroup 2 (zpowers (permOfArr n c)) := by
      have hpow : permOfArr n c ^ 2 ^ kc = 1 := eq_of_eqA (rep_powA hcr _) rep_idA hcpow
      obtain ⟨b, -, hb'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
      exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb'])
    have hvc' : ⁅v', permOfArr n c⁆ = s' := by
      have h1 := rep_commutatorA hvv hcv
      rw [permOfArr_eq_of_rep hv'] at h1
      exact eq_of_eqA h1 hs' hvc
    refine Or.inr ⟨rfl, fun _ => Or.inr (Or.inr (Or.inr ⟨hU, s', hs'E, hne hs' hs1,
      ⟨t', ht'E, hne ht' ht1, permOfArr n c, hin _ hcv hcX, (commA_iff hcr ht').1 hct, hc2, v',
        hv'E, hvc'⟩, P, hPle, hperf, enumOK_mem_of_any hps hP hs' hsP⟩))⟩

theorem census_of_censusOKW {ps : List ℕ} {allowPW allowInX allowU : Bool}
    {sGens : Array (Array ℕ)} {roots : Array ℕ} {nodes : Array Node} {cS : ArrCert}
    {wcs : Array (Array ArrCert)} (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ X → outX a = true)
    (h : censusOKW n ps inX outX allowPW allowInX allowU sGens roots nodes cS wcs = true)
    {E : Subgroup (Equiv.Perm (Fin n))} (hES : E ≤ closure (permsA n sGens))
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) :
    YWitness X E ∨ (allowPW = true ∧ PWitness X E) ∨ (allowInX = true ∧ E ≤ X) ∨
      (allowU = true ∧ UWitness X E) := by
  simp only [censusOKW, Bool.and_eq_true] at h
  obtain ⟨⟨hS, hroot⟩, hnodes⟩ := h
  set cN := nodes.map fun nd => maskCert n nd.basis
  obtain ⟨hSmem, -, hSval⟩ := enumOK_spec hps (enumOK_of_enumOKK hS)
  have hnode : ∀ i < nodes.size,
      nodeOKW n ps inX outX allowPW allowInX allowU cS nodes cN wcs i = true :=
    fun i hi => allLt_spec hnodes hi
  have hnodeE : ∀ i < nodes.size, enumOK n nodes[i]!.basis ps cN[i]! = true := by
    intro i hi
    have := hnode i hi
    simp only [nodeOKW, Bool.and_eq_true] at this
    exact enumOK_of_enumOKK this.1.1
  have hbasis : ∀ i < nodes.size, ∀ k < nodes[i]!.basis.size,
      validA n nodes[i]!.basis[k]! = true := fun i hi k hk => enumOK_gens_valid (hnodeE i hi) hk
  have hmemN : ∀ i < nodes.size, ∀ {a : Array ℕ} {g : Equiv.Perm (Fin n)}, Rep n a g →
      memA n cN[i]! a = true → g ∈ nodeSub n nodes i :=
    fun i hi a g ha hm => enumOK_mem_of_any hps (hnodeE i hi) ha hm
  refine forall_of_tree (S := closure (permsA n sGens)) (WitW X allowPW allowInX allowU)
    (MonoW X allowPW) (fun E₀ E hm hle _ _ _ => witW_of_monoW allowInX allowU hm hle)
    (nodeSub n nodes) nodes.size ?_ ?_ ?_ hES hE hE4
  · intro a ha ha2 ha1
    obtain ⟨p, hp, rfl⟩ := (hSmem a).1 ha
    have hr := rep_of_validA (hSval p hp)
    have := allLt_spec hroot hp
    simp only [rootOK, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
      decide_eq_true_eq] at this
    rcases this with (h1 | h1) | ⟨⟨hj, hall⟩, hu⟩
    · rw [(eqA_iff (rep_compA hr hr) rep_idA).2 (by rw [← sq]; exact ha2)] at h1
      exact Bool.noConfusion h1
    · exact absurd (eq_of_eqA hr rep_idA h1) ha1
    · refine ⟨_, hj, le_antisymm ?_ (zpowers_le.mpr (hmemN _ hj hr hu))⟩
      rw [nodeSub, closure_le]
      rintro _ ⟨k, hk, rfl⟩
      dsimp only
      have hbk := rep_of_validA (hbasis _ hj k hk)
      have h2 := allLt_spec hall hk
      simp only [Bool.or_eq_true] at h2
      rcases h2 with h2 | h2
      · rw [SetLike.mem_coe, eq_of_eqA hbk hr h2]
        exact mem_zpowers _
      · rw [SetLike.mem_coe, eq_of_eqA hbk rep_idA h2]
        exact one_mem _
  · intro i hi
    have hn := hnode i hi
    simp only [nodeOKW, Bool.and_eq_true, Bool.or_eq_true] at hn
    obtain ⟨⟨hEi, hwit⟩, hch⟩ := hn
    rcases witOKW_sound hps hin hout (enumOK_of_enumOKK hEi) hwit with hm | ⟨hnm, -⟩
    · exact Or.inl hm
    rcases hch with hm | hch
    · rw [hnm] at hm
      exact Bool.noConfusion hm
    refine Or.inr fun u hu hu2 hui hcomm => ?_
    obtain ⟨p, hp, rfl⟩ := (hSmem u).1 hu
    have hr := rep_of_validA (hSval p hp)
    have hcp := allLt_spec hch hp
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hcp
    rcases hcp with ((h1 | h1) | h1) | h1
    · rw [(eqA_iff (rep_compA hr hr) rep_idA).2 (by rw [← sq]; exact hu2)] at h1
      exact Bool.noConfusion h1
    · have : (allLt nodes[i]!.basis.size fun k => commA n cS.pts[p]! nodes[i]!.basis[k]!) =
          true := by
        rw [allLt_iff]
        intro k hk
        have hbk := rep_of_validA (hbasis i hi k hk)
        exact (commA_iff hr hbk).2 (hcomm _ (subset_closure (mem_permsA hk))).symm
      rw [this] at h1
      exact Bool.noConfusion h1
    · exact absurd (hmemN i hi hr h1) hui
    · simp only [childOK, Bool.and_eq_true, decide_eq_true_eq] at h1
      obtain ⟨⟨⟨hj, hjb⟩, hib⟩, hu'⟩ := h1
      refine ⟨_, hj, le_antisymm ?_ (sup_le ?_ (zpowers_le.mpr (hmemN _ hj hr hu')))⟩
      · rw [nodeSub, closure_le]
        rintro _ ⟨k, hk, rfl⟩
        dsimp only
        have hbk := rep_of_validA (hbasis _ hj k hk)
        have h2 := allLt_spec hjb hk
        simp only [Bool.or_eq_true] at h2
        rw [SetLike.mem_coe]
        rcases h2 with h2 | h2
        · exact mem_sup_left (hmemN i hi hbk h2)
        · have hm := hmemN i hi (rep_compA hr hbk) h2
          rw [show permOfArr n nodes[nodes[i]!.children[p]!]!.basis[k]! =
              (permOfArr n cS.pts[p]!)⁻¹ * (permOfArr n cS.pts[p]! *
                permOfArr n nodes[nodes[i]!.children[p]!]!.basis[k]!) by group]
          exact mul_mem (mem_sup_right (inv_mem (mem_zpowers _))) (mem_sup_left hm)
      · rw [nodeSub, closure_le]
        rintro _ ⟨k, hk, rfl⟩
        exact hmemN _ hj (rep_of_validA (hbasis i hi k hk)) (allLt_spec hib hk)
  · intro i hi h4
    have hn := hnode i hi
    simp only [nodeOKW, Bool.and_eq_true] at hn
    rcases witOKW_sound hps hin hout (enumOK_of_enumOKK hn.1.1) hn.1.2 with hm | ⟨-, hw⟩
    · exact Or.inl hm
    · exact Or.inr (hw h4)

end Soundness

end CFSG.ComponentClassification.RankTwoSporadic.Cert
