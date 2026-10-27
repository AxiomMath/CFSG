module

public import CFSG.Sporadic.Schreier.TitsChain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.RootCensus

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

@[expose] def allProds (n : ℕ) (levels : Array Level) (p : Array ℕ → Bool) (l : ℕ)
    (acc : Array ℕ) : Bool :=
  if h : l < levels.size then
    allLt levels[l].pts.size fun k => allProds n levels p (l + 1) (compA n acc levels[l].tr[k]!)
  else p acc
termination_by levels.size - l

variable {n : ℕ}

theorem allProds_spec {levels : Array Level} {base : Array ℕ} {p : Array ℕ → Bool}
    (hinv : ∀ i (hi : i < levels.size), ∀ k < levels[i].pts.size,
      isInvA n levels[i].tr[k]! levels[i].trInv[k]! = true) :
    ∀ d l, l + d = levels.size → ∀ (acc : Array ℕ) (A : Equiv.Perm (Fin n)), Rep n acc A →
      allProds n levels p l acc = true → ∀ (g : Array ℕ) (G : Equiv.Perm (Fin n)), Rep n g G →
        siftA n levels base l g = true → ∃ a, Rep n a (A * G) ∧ p a = true := by
  intro d
  induction d with
  | zero =>
    intro l hl acc A hA hp g G hG hs
    have hl' : ¬ l < levels.size := by omega
    rw [allProds, dite_eq_right_iff.mpr (fun h => absurd h hl')] at hp
    rw [siftA, dite_eq_right_iff.mpr (fun h => absurd h hl')] at hs
    have hG1 : G = 1 := eq_of_eqA hG rep_idA hs
    exact ⟨acc, by rw [hG1, mul_one]; exact hA, hp⟩
  | succ d ih =>
    intro l hl acc A hA hp g G hG hs
    have hl' : l < levels.size := by omega
    rw [allProds, dite_eq_left hl'] at hp
    rw [siftA, dite_eq_left hl'] at hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨hk, hs'⟩ := hs
    set k := levels[l].pos[g[base[l]!]!]!
    have hpk := allLt_spec hp hk
    obtain ⟨hT, hTi⟩ := rep_permOfArr (hinv l hl' k hk)
    obtain ⟨a, ha, hpa⟩ := ih (l + 1) (by omega) _ _ (rep_compA hA hT) hpk _ _
      (rep_compA hTi hG) hs'
    refine ⟨a, ?_, hpa⟩
    rwa [show A * permOfArr n levels[l].tr[k]! * ((permOfArr n levels[l].tr[k]!)⁻¹ * G) =
      A * G by group] at ha

@[expose] noncomputable def arrOf (G : Equiv.Perm (Fin n)) : Array ℕ :=
  Array.ofFn fun i : Fin n => (G i : ℕ)

theorem rep_arrOf (G : Equiv.Perm (Fin n)) : Rep n (arrOf G) G := fun x => by
  rw [arrOf, getElem!_ofFn_nat _ x.2]

theorem allProds_of_chain [NeZero n] {S : Array (Array ℕ)} {b : List ℕ}
    (hb : (finList n b).Nodup) (hP : allPermsOK n S = true)
    (hc : rawChainOK n (S.extract 0 S.size) S (baseArr n b) (wordsArr S.size S.size []) 1 = true)
    {p : Array ℕ → Bool} (hp : allProds n (rawLevels n S (baseArr n b)) p 0 (idA n) = true)
    {G : Equiv.Perm (Fin n)}
    (hG : G ∈ closure (Set.range fun i : Fin S.size => permOfArr n S[(i : ℕ)]!)) :
    ∃ a, Rep n a G ∧ p a = true := by
  have hF := chainCheckFacts hc
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hsift : siftA n (rawLevels n S (baseArr n b)) (baseArr n b) 0 (arrOf G) = true := by
    rw [siftA_iff_mem_ofArrays (hn := hn) (hk := le_rfl) (hb := hb) hP (by norm_num) hc
      (rep_arrOf G), originalSubgroup_ofArrays]
    exact hG
  have hinv : ∀ i (hi : i < (rawLevels n S (baseArr n b)).size),
      ∀ k < (rawLevels n S (baseArr n b))[i].pts.size,
        isInvA n (rawLevels n S (baseArr n b))[i].tr[k]!
          (rawLevels n S (baseArr n b))[i].trInv[k]! = true := by
    intro i hi k hk
    have hi' : i < (baseArr n b).size := by rwa [size_rawLevels] at hi
    have hL := ChainArrays.levelFacts_of_levelOK (hF.level i hi')
    rw [← getElem!_pos (rawLevels n S (baseArr n b)) i hi] at hk ⊢
    exact hL.tr_inv k hk
  obtain ⟨a, ha, hpa⟩ := allProds_spec hinv (rawLevels n S (baseArr n b)).size 0 (by simp) _ _
    rep_idA hp _ _ (rep_arrOf G) hsift
  exact ⟨a, by rwa [one_mul] at ha, hpa⟩

@[expose] def involA (n : ℕ) (a : Array ℕ) : Bool :=
  (allLt n fun i => a[a[i]!]! == i) && !(allLt n fun i => a[i]! == i)

theorem involA_iff {a : Array ℕ} {G : Equiv.Perm (Fin n)} (hG : Rep n a G) :
    involA n a = true ↔ G ^ 2 = 1 ∧ G ≠ 1 := by
  have h2 : (allLt n fun i => a[a[i]!]! == i) = true ↔ G ^ 2 = 1 := by
    rw [allLt_iff, sq]
    constructor
    · intro h
      refine Equiv.ext fun x => Fin.ext ?_
      have := h x x.2
      rw [beq_iff_eq, hG.apply x.2, hG.apply (G x).2] at this
      simpa using this
    · intro h i hi
      rw [beq_iff_eq, hG.apply hi, hG.apply (G ⟨i, hi⟩).2]
      have := congrArg (fun f : Equiv.Perm (Fin n) => ((f ⟨i, hi⟩ : Fin n) : ℕ)) h
      simpa using this
  have h1 : (allLt n fun i => a[i]! == i) = true ↔ G = 1 := by
    rw [← eqA_iff hG rep_idA, eqA, allLt_iff, allLt_iff]
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [idA_get hi]
  rw [involA, Bool.and_eq_true, h2, Bool.not_eq_true', ← Bool.not_eq_true, h1]

@[expose] def fixA (n : ℕ) (a : Array ℕ) : ℕ := (List.range n).countP fun i => a[i]! == i

@[expose] noncomputable def fixP (g : Equiv.Perm (Fin n)) : ℕ := Fintype.card {p : Fin n // g p = p}

theorem fixA_eq {a : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n a g) : fixA n a = fixP g := by
  have h1 : fixA n a = Nat.count (fun i => a[i]! = i) n := by
    rw [fixA, Nat.count]
    congr 1
  rw [h1, Nat.count_eq_card_filter_range, fixP, Fintype.card_subtype]
  refine Finset.card_bij (fun i hi => ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩)
    (fun i hi => ?_) (fun i _ j _ hij => by simpa using hij) (fun p hp => ?_)
  · rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, Fin.ext ?_⟩
    rw [← h.apply (Finset.mem_range.mp hi.1)]
    exact hi.2
  · refine ⟨p.val, ?_, rfl⟩
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨Finset.mem_range.mpr p.2, ?_⟩
    rw [h.apply p.2]
    exact congrArg Fin.val hp.2

theorem fixP_conj (g h : Equiv.Perm (Fin n)) : fixP (h * g * h⁻¹) = fixP g := by
  refine Fintype.card_congr (Equiv.subtypeEquiv h⁻¹ fun p => ?_)
  simp only [Equiv.Perm.mul_apply]
  constructor
  · intro hp
    have := congrArg (fun q => h⁻¹ q) hp
    simpa using this
  · intro hp
    have := congrArg (fun q => h q) hp
    simpa using this

inductive RootWit where
  | perf (l : ℕ)
  | ord4 (l m : ℕ)
  | ord4p (ls : List ℕ) (m : ℕ)
  | ord4c (e : ℕ) (c₁ c₂ : Array ℕ) (m : ℕ)
deriving Inhabited

structure PerfCert where
  gens : List (List ℕ × ℕ)
  comms : List (ℕ × ℕ)
  x : ℕ
  k : ℕ
  conjs : List ℕ
deriving Inhabited

structure RootCert where
  x : Array ℕ
  strong : Array (Array ℕ)
  base : List ℕ
  cs : Array (Array ℕ)
  gams : Array (ℕ × ℕ)
  perfs : Array PerfCert
  cands : List RootWit
deriving Inhabited

@[expose] def gamA (n : ℕ) (r : RootCert) (l : ℕ) : Array ℕ :=
  commutatorA n r.cs[r.gams[l]!.1]! r.cs[r.gams[l]!.2]!

@[expose] def gamInvA (n : ℕ) (r : RootCert) (l : ℕ) : Array ℕ :=
  commutatorA n r.cs[r.gams[l]!.2]! r.cs[r.gams[l]!.1]!

@[expose] def perfGen (n : ℕ) (r : RootCert) (gl : List ℕ × ℕ) : Array ℕ :=
  powA n (prodA n (gl.1.map (gamA n r))) gl.2

@[expose] def perfGens (n : ℕ) (r : RootCert) (P : PerfCert) : Array (Array ℕ) :=
  (P.gens.map (perfGen n r)).toArray

@[expose] def perfOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (r : RootCert) (P : PerfCert) : Bool :=
  let gs := perfGens n r P
  let cP := enumBfs n gs ps fuel
  let m := cP.pts.size
  let qs := (P.comms.map fun ij => commutatorA n cP.pts[ij.1]! cP.pts[ij.2]!).toArray
  let cQ := enumBfs n qs ps fuel
  let xa := cP.pts[P.x]!
  let rs := (P.conjs.map fun p => conjA n cP.pts[p]! (compA n xa xa)).toArray
  let cR := enumBfs n rs ps fuel
  P.gens.all (fun gl => gl.1.all fun l => decide (l < r.gams.size)) && enumOK n gs ps cP &&
    P.comms.all (fun ij => decide (ij.1 < m) && decide (ij.2 < m)) && enumOK n qs ps cQ &&
    cQ.pts.size == m && decide (P.x < m) && eqA n (powA n xa (2 ^ P.k)) (idA n) &&
    P.conjs.all (fun p => decide (p < m)) && enumOK n rs ps cR && cR.pts.size == m

@[expose] def candOK (n : ℕ) (inX : Array ℕ → Bool) (x : Array ℕ) (gA gI : Array (Array ℕ))
    (pG : Array (Array (Array ℕ))) (b : Array ℕ) : RootWit → Bool
  | .perf l => (pG[l]!).toList.any fun g => !(commA n b g)
  | .ord4 l m =>
    let y := powA n (compA n (compA n b gA[l]!) (compA n b gI[l]!)) m
    !(eqA n (compA n y y) (idA n)) && eqA n (powA n y 4) (idA n)
  | .ord4p ls m =>
    let y := powA n (prodA n (ls.map fun l => compA n (compA n b gA[l]!) (compA n b gI[l]!))) m
    !(eqA n (compA n y y) (idA n)) && eqA n (powA n y 4) (idA n)
  | .ord4c e c₁ c₂ m =>
    let e' := if e = 0 then b else compA n x b
    let y := powA n (compA n (compA n x (commutatorA n c₁ c₂)) (compA n x (commutatorA n c₂ c₁))) m
    validA n c₁ && validA n c₂ && inX c₁ && inX c₂ && commA n c₁ e' && commA n c₂ e' &&
      !(eqA n (compA n y y) (idA n)) && eqA n (powA n y 4) (idA n)

@[expose] def leafOK (n : ℕ) (inX : Array ℕ → Bool) (bmode : ℕ) (skip : List ℕ) (x : Array ℕ)
    (gA gI : Array (Array ℕ)) (pG : Array (Array (Array ℕ))) (cands : List RootWit)
    (b : Array ℕ) : Bool :=
  !(involA n b) || eqA n b x || (bmode == 1 && !(inX b)) || (bmode == 2 && inX b) ||
    skip.contains (fixA n b) || skip.contains (fixA n (compA n x b)) ||
    cands.any (candOK n inX x gA gI pG b)

@[expose] def RootWit.inRange (r : RootCert) : RootWit → Bool
  | .perf l => decide (l < r.perfs.size)
  | .ord4 l _ => decide (l < r.gams.size)
  | .ord4p ls _ => ls.all fun l => decide (l < r.gams.size)
  | .ord4c .. => true

@[expose] def rootCertOK (n : ℕ) [NeZero n] (ps : List ℕ) (fuel : ℕ) (inX inW : Array ℕ → Bool)
    (pw : Bool) (bmode : ℕ) (skip : List ℕ) (r : RootCert) : Bool :=
  let gA := (Array.range r.gams.size).map (gamA n r)
  let gI := (Array.range r.gams.size).map (gamInvA n r)
  let pG := r.perfs.map (perfGens n r)
  validA n r.x && involA n r.x && inW r.x && allPermsOK n r.strong &&
    decide (finList n r.base).Nodup &&
    rawChainOK n (r.strong.extract 0 r.strong.size) r.strong (baseArr n r.base)
      (wordsArr r.strong.size r.strong.size []) 1 &&
    (allLt r.strong.size fun k => commA n r.strong[k]! r.x && inW r.strong[k]!) &&
    (allLt r.cs.size fun k => validA n r.cs[k]! && inX r.cs[k]! && commA n r.cs[k]! r.x) &&
    (allLt r.gams.size fun l =>
      decide (r.gams[l]!.1 < r.cs.size) && decide (r.gams[l]!.2 < r.cs.size)) &&
    (pw || r.perfs.size == 0) && r.perfs.all (perfOK n ps fuel r) &&
    r.cands.all (RootWit.inRange r) &&
    allProds n (rawLevels n r.strong (baseArr n r.base))
      (leafOK n inX bmode skip r.x gA gI pG r.cands) 0 (idA n)

section Soundness

variable {ps : List ℕ} {fuel : ℕ} {inX inW : Array ℕ → Bool} {pw : Bool} {bmode : ℕ}
  {skip : List ℕ} {r : RootCert} {X W : Subgroup (Equiv.Perm (Fin n))}

@[expose] noncomputable def RootCert.T (n : ℕ) (r : RootCert) : Subgroup (Equiv.Perm (Fin n)) :=
  closure (Set.range fun i : Fin r.strong.size => permOfArr n r.strong[(i : ℕ)]!)

theorem getElem!_map_range {α : Type*} [Inhabited α] (f : ℕ → α) {m l : ℕ} (hl : l < m) :
    ((Array.range m).map f)[l]! = f l := by
  rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, Array.getElem_range]

theorem gam_spec (hinX : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hcs : ∀ k < r.cs.size, validA n r.cs[k]! = true ∧ inX r.cs[k]! = true ∧
      commA n r.cs[k]! r.x = true)
    (hgams : ∀ l < r.gams.size, r.gams[l]!.1 < r.cs.size ∧ r.gams[l]!.2 < r.cs.size)
    {xP : Equiv.Perm (Fin n)} (hx : Rep n r.x xP) {l : ℕ} (hl : l < r.gams.size) :
    ∃ Γ ∈ centDer X xP, Rep n (gamA n r l) Γ ∧ Rep n (gamInvA n r l) Γ⁻¹ := by
  obtain ⟨hi, hj⟩ := hgams l hl
  obtain ⟨hvi, hXi, hci⟩ := hcs _ hi
  obtain ⟨hvj, hXj, hcj⟩ := hcs _ hj
  have hmem : ∀ {k : ℕ}, validA n r.cs[k]! = true → inX r.cs[k]! = true →
      commA n r.cs[k]! r.x = true →
      permOfArr n r.cs[k]! ∈ X ⊓ centralizer ({xP} : Set (Equiv.Perm (Fin n))) :=
    fun hv hX hc => ⟨hinX _ hv hX, mem_centralizer_singleton_iff.mpr
      ((commA_iff (rep_of_validA hv) hx).mp hc)⟩
  refine ⟨_, commutator_mem_commutator (hmem hvi hXi hci) (hmem hvj hXj hcj),
    rep_commutatorA hvi hvj, ?_⟩
  rw [commutatorElement_inv]
  exact rep_commutatorA hvj hvi

theorem perfOK_spec (hps : ∀ p ∈ ps, p < n)
    (hinX : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hcs : ∀ k < r.cs.size, validA n r.cs[k]! = true ∧ inX r.cs[k]! = true ∧
      commA n r.cs[k]! r.x = true)
    (hgams : ∀ l < r.gams.size, r.gams[l]!.1 < r.cs.size ∧ r.gams[l]!.2 < r.cs.size)
    {xP : Equiv.Perm (Fin n)} (hx : Rep n r.x xP) {P : PerfCert}
    (h : perfOK n ps fuel r P = true) :
    closure (permsA n (perfGens n r P)) ≤ centDer X xP ∧
      ⁅closure (permsA n (perfGens n r P)), closure (permsA n (perfGens n r P))⁆ =
        closure (permsA n (perfGens n r P)) ∧
      ∃ y ∈ closure (permsA n (perfGens n r P)), IsPGroup 2 (zpowers y) ∧
        closure (permsA n (perfGens n r P)) ≤
          closure {z | ∃ p ∈ closure (permsA n (perfGens n r P)), z = p * y ^ 2 * p⁻¹} := by
  simp only [perfOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hgl, hP⟩, hcomms⟩, hQ⟩, hQsize⟩, hx'⟩, hxpow⟩, hconjs⟩, hR⟩, hRsize⟩ := h
  set gs := perfGens n r P
  set cP := enumBfs n gs ps fuel
  set Pg := closure (permsA n gs)
  obtain ⟨hPmem, hPcard, hPval⟩ := enumOK_spec hps hP
  have hpt : ∀ i < cP.pts.size, permOfArr n cP.pts[i]! ∈ Pg := fun i hi => (hPmem _).2 ⟨i, hi, rfl⟩
  refine ⟨?_, commutator_eq_self_of_check hps hP hcomms hQ hQsize, ?_⟩
  ·
    refine closure_le_of_rep fun gl hgl' => ?_
    have hprod : ∃ g ∈ centDer X xP, Rep n (prodA n (gl.1.map (gamA n r))) g := by
      apply rep_prodA
      intro a ha
      rw [List.mem_map] at ha
      obtain ⟨l, hl, rfl⟩ := ha
      obtain ⟨Γ, hΓ, hrep, -⟩ := gam_spec hinX hcs hgams hx (hgl gl hgl' l hl)
      exact ⟨Γ, hΓ, hrep⟩
    obtain ⟨g, hg, hrep⟩ := hprod
    exact ⟨g ^ gl.2, pow_mem hg _, rep_powA hrep _⟩
  · set xa := cP.pts[P.x]!
    have hxr := rep_of_validA (hPval P.x hx')
    have hxP : permOfArr n xa ∈ Pg := hpt P.x hx'
    refine ⟨permOfArr n xa, hxP, ?_, ?_⟩
    · have hpow : permOfArr n xa ^ 2 ^ P.k = 1 := eq_of_eqA (rep_powA hxr _) rep_idA hxpow
      obtain ⟨b, -, hb'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
      exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb'])
    · set R := closure (permsA n (P.conjs.map fun p =>
        conjA n cP.pts[p]! (compA n xa xa)).toArray)
      have hRle : R ≤ closure {y | ∃ p ∈ Pg, y = p * permOfArr n xa ^ 2 * p⁻¹} := by
        refine closure_le_of_rep fun p hp => ?_
        have hpP := hpt p (hconjs p hp)
        refine ⟨_, subset_closure ⟨_, hpP, rfl⟩, ?_⟩
        rw [sq]
        exact rep_conjA (hPval p (hconjs p hp)) (rep_compA hxr hxr)
      have hRP : R ≤ Pg := by
        refine closure_le_of_rep fun p hp => ?_
        have hpP := hpt p (hconjs p hp)
        exact ⟨_, Pg.mul_mem (Pg.mul_mem hpP (Pg.mul_mem hxP hxP)) (Pg.inv_mem hpP),
          rep_conjA (hPval p (hconjs p hp)) (rep_compA hxr hxr)⟩
      obtain ⟨-, hRcard, -⟩ := enumOK_spec hps hR
      have hRP' : R = Pg := eq_of_le_of_card_ge hRP (by rw [hPcard, ← hRsize, hRcard])
      exact hRP' ▸ hRle

theorem allPermsOK_of_rootCertOK [NeZero n]
    (h : rootCertOK n ps fuel inX inW pw bmode skip r = true) :
    allPermsOK n r.strong = true := by
  simp only [rootCertOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.2

theorem root_spec [NeZero n] (hps : ∀ p ∈ ps, p < n)
    (hsX : ∀ a g, Rep n a g → inX a = true → g ∈ X)
    (hcX : bmode = 1 → ∀ a g, Rep n a g → g ∈ X → inX a = true)
    (hsW : ∀ a g, Rep n a g → inW a = true → g ∈ W)
    (h : rootCertOK n ps fuel inX inW pw bmode skip r = true) :
    validA n r.x = true ∧ permOfArr n r.x ∈ W ∧ permOfArr n r.x ^ 2 = 1 ∧ permOfArr n r.x ≠ 1 ∧
      r.T n ≤ W ⊓ centralizer {permOfArr n r.x} ∧
      Nat.card (r.T n) = (rawOrbitSizes n r.strong (baseArr n r.base)).prod ∧
      ∀ b ∈ r.T n, b ^ 2 = 1 → b ≠ 1 → b ≠ permOfArr n r.x → (bmode = 1 → b ∈ X) →
        (bmode = 2 → b ∉ X) →
        MonoW X pw (closure {permOfArr n r.x, b}) ∨ fixP b ∈ skip ∨
          fixP (permOfArr n r.x * b) ∈ skip := by
  have hinX : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X :=
    fun a hv ha => hsX a _ (rep_of_validA hv) ha
  have hinW : ∀ a, validA n a = true → inW a = true → permOfArr n a ∈ W :=
    fun a hv ha => hsW a _ (rep_of_validA hv) ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  simp only [rootCertOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hxv, hxi⟩, hxW⟩, hP⟩, hb⟩, hc⟩, hT⟩, hcs⟩, hgams⟩, hpw⟩, hperfs⟩,
    hcands⟩, hprods⟩ := h
  set xP := permOfArr n r.x
  have hxr : Rep n r.x xP := rep_of_validA hxv
  obtain ⟨hx2, hx1⟩ := (involA_iff hxr).mp hxi
  have hcs' : ∀ k < r.cs.size, validA n r.cs[k]! = true ∧ inX r.cs[k]! = true ∧
      commA n r.cs[k]! r.x = true := fun k hk => by
    simpa [Bool.and_eq_true, and_assoc] using allLt_spec hcs hk
  have hgams' : ∀ l < r.gams.size, r.gams[l]!.1 < r.cs.size ∧ r.gams[l]!.2 < r.cs.size :=
    fun l hl => by simpa [Bool.and_eq_true, decide_eq_true_eq] using allLt_spec hgams hl
  refine ⟨hxv, hinW _ hxv hxW, hx2, hx1, ?_, ?_, ?_⟩
  ·
    rw [RootCert.T, closure_le]
    rintro _ ⟨k, rfl⟩
    have hk := allLt_spec hT k.2
    simp only [Bool.and_eq_true] at hk
    have hv : validA n r.strong[(k : ℕ)]! = true := isInvA_of_allPermsOK hP k.2
    exact ⟨hinW _ hv hk.2, mem_centralizer_singleton_iff.mpr
      ((commA_iff (rep_of_validA hv) hxr).mp hk.1)⟩
  ·
    rw [RootCert.T, ← originalSubgroup_ofArrays (hn := hn) (hk := le_rfl) (hb := hb)
      (W := wordsArr r.strong.size r.strong.size [])]
    exact card_ofArrays hP (by norm_num) hc
  ·
    intro b hbT hb2 hb1 hbx hb1X hb2X
    obtain ⟨a, ha, hleaf⟩ := allProds_of_chain hb hP hc hprods hbT
    have hinv : involA n a = true := (involA_iff ha).mpr ⟨hb2, hb1⟩
    have hneq : eqA n a r.x = false := by
      by_contra hne
      exact hbx (eq_of_eqA ha hxr (by simpa using hne))
    have hm1 : (bmode == 1 && !(inX a)) = false := by
      by_cases hm : bmode = 1
      · simp [hm, hcX hm a b ha (hb1X hm)]
      · simp [hm]
    have hm2 : (bmode == 2 && inX a) = false := by
      by_cases hm : bmode = 2
      · have : inX a = false := by
          by_contra hc
          exact hb2X hm (hsX a b ha (by simpa using hc))
        simp [hm, this]
      · simp [hm]
    simp only [leafOK, hinv, hneq, hm1, hm2, Bool.not_true, Bool.false_or, Bool.or_eq_true,
      List.contains_iff_mem, List.any_eq_true] at hleaf
    rcases hleaf with (hs | hs) | ⟨c, hc', hcOK⟩
    · exact Or.inr (Or.inl (by rwa [fixA_eq ha] at hs))
    · exact Or.inr (Or.inr (by rwa [fixA_eq (rep_compA hxr ha)] at hs))
    refine Or.inl ?_
    set V := closure ({xP, b} : Set (Equiv.Perm (Fin n)))
    have hxV : xP ∈ V := subset_closure (Set.mem_insert _ _)
    have hbV : b ∈ V := subset_closure (Set.mem_insert_of_mem _ rfl)
    have hΓV : centDer X xP ≤ gammaE X V := le_iSup₂_of_le xP hxV (le_iSup_of_le hx1 le_rfl)
    have hrange := hcands c hc'
    cases c with
    | perf l =>
      simp only [RootWit.inRange, decide_eq_true_eq] at hrange
      have hpw' : pw = true := by
        rcases hpw with hpw | hpw
        · exact hpw
        · omega
      simp only [candOK, List.any_eq_true, Bool.not_eq_true'] at hcOK
      obtain ⟨g, hg, hgc⟩ := hcOK
      have hpG : (r.perfs.map (perfGens n r))[l]! = perfGens n r r.perfs[l]! := by
        rw [getElem!_pos _ l (by simpa using hrange), Array.getElem_map,
          getElem!_pos r.perfs l hrange]
      rw [hpG] at hg
      have hPl := (Array.all_eq_true'.mp hperfs) r.perfs[l]! (by
        rw [getElem!_pos r.perfs l hrange]
        exact Array.getElem_mem hrange)
      obtain ⟨hPΓ, hperf, y, hyP, hy2, hgen⟩ := perfOK_spec hps hinX hcs' hgams' hxr hPl
      obtain ⟨hPok, -, -⟩ := enumOK_spec hps (by
        simp only [perfOK, Bool.and_eq_true] at hPl
        exact hPl.1.1.1.1.1.1.1.1.2)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have hj' : j < (perfGens n r r.perfs[l]!).size := by simpa using hj
      have hgv : validA n (perfGens n r r.perfs[l]!)[j]! = true := by
        simp only [perfOK, Bool.and_eq_true] at hPl
        exact enumOK_gens_valid hPl.1.1.1.1.1.1.1.1.2 hj'
      have hgr := rep_of_validA hgv
      have hgP : permOfArr n (perfGens n r r.perfs[l]!)[j]! ∈
          closure (permsA n (perfGens n r r.perfs[l]!)) := subset_closure (mem_permsA hj')
      refine Or.inr ⟨hpw', _, hPΓ.trans hΓV, hperf, ?_, y, hyP, hy2, hgen⟩
      intro hVC
      have hcomm := mem_centralizer_iff.mp (hVC hbV) _ hgP
      rw [Array.getElem_toList, ← getElem!_pos _ j hj'] at hgc
      rw [(commA_iff ha hgr).mpr hcomm.symm] at hgc
      exact Bool.noConfusion hgc
    | ord4 l m =>
      simp only [RootWit.inRange, decide_eq_true_eq] at hrange
      obtain ⟨Γ, hΓ, hΓr, hΓi⟩ := gam_spec hinX hcs' hgams' hxr hrange
      rw [← getElem!_map_range (gamA n r) hrange] at hΓr
      rw [← getElem!_map_range (gamInvA n r) hrange] at hΓi
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb2)
      have hw : Rep n (compA n (compA n a ((Array.range r.gams.size).map (gamA n r))[l]!)
          (compA n a ((Array.range r.gams.size).map (gamInvA n r))[l]!)) ⁅b, Γ⁆ := by
        rw [commutatorElement_def, hbinv, mul_assoc]
        exact rep_compA (rep_compA ha hΓr) (rep_compA ha hΓi)
      have hwN : ⁅b, Γ⁆ ∈ nE X V := commutator_mem_commutator hbV (hΓV hΓ)
      simp only [candOK, Bool.and_eq_true, Bool.not_eq_true'] at hcOK
      obtain ⟨h2, h4⟩ := hcOK
      have hym := rep_powA hw m
      have h2' : ¬ (⁅b, Γ⁆ ^ m) ^ 2 ^ 1 = 1 := by
        intro hc
        rw [pow_one, sq] at hc
        rw [(eqA_iff (rep_compA hym hym) rep_idA).2 hc] at h2
        exact Bool.noConfusion h2
      have h4' : (⁅b, Γ⁆ ^ m) ^ 2 ^ (1 + 1) = 1 := eq_of_eqA (rep_powA hym 4) rep_idA h4
      have hord := orderOf_eq_prime_pow h2' h4'
      refine Or.inl ⟨⁅b, Γ⁆ ^ m, pow_mem hwN m, ?_⟩
      rw [hord]
      norm_num
    | ord4p ls m =>
      simp only [RootWit.inRange, List.all_eq_true, decide_eq_true_eq] at hrange
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb2)
      have hprod : ∃ w ∈ nE X V, Rep n (prodA n (ls.map fun l =>
          compA n (compA n a ((Array.range r.gams.size).map (gamA n r))[l]!)
            (compA n a ((Array.range r.gams.size).map (gamInvA n r))[l]!))) w := by
        apply rep_prodA
        intro c hcl
        rw [List.mem_map] at hcl
        obtain ⟨l, hl, rfl⟩ := hcl
        obtain ⟨Γ, hΓ, hΓr, hΓi⟩ := gam_spec hinX hcs' hgams' hxr (hrange l hl)
        rw [← getElem!_map_range (gamA n r) (hrange l hl)] at hΓr
        rw [← getElem!_map_range (gamInvA n r) (hrange l hl)] at hΓi
        refine ⟨⁅b, Γ⁆, commutator_mem_commutator hbV (hΓV hΓ), ?_⟩
        rw [commutatorElement_def, hbinv, mul_assoc]
        exact rep_compA (rep_compA ha hΓr) (rep_compA ha hΓi)
      obtain ⟨w, hwN, hw⟩ := hprod
      simp only [candOK, Bool.and_eq_true, Bool.not_eq_true'] at hcOK
      obtain ⟨h2, h4⟩ := hcOK
      have hym := rep_powA hw m
      have h2' : ¬ (w ^ m) ^ 2 ^ 1 = 1 := by
        intro hc
        rw [pow_one, sq] at hc
        rw [(eqA_iff (rep_compA hym hym) rep_idA).2 hc] at h2
        exact Bool.noConfusion h2
      have h4' : (w ^ m) ^ 2 ^ (1 + 1) = 1 := eq_of_eqA (rep_powA hym 4) rep_idA h4
      have hord := orderOf_eq_prime_pow h2' h4'
      refine Or.inl ⟨w ^ m, pow_mem hwN m, ?_⟩
      rw [hord]
      norm_num
    | ord4c e c₁ c₂ m =>
      simp only [candOK, Bool.and_eq_true, Bool.not_eq_true'] at hcOK
      obtain ⟨⟨⟨⟨⟨⟨⟨hv1, hv2⟩, hX1⟩, hX2⟩, hc1⟩, hc2⟩, h2⟩, h4⟩ := hcOK
      have hxinv : xP⁻¹ = xP := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx2)
      obtain ⟨e', he'r, he'V, he'1⟩ : ∃ e' : Equiv.Perm (Fin n),
          Rep n (if e = 0 then a else compA n r.x a) e' ∧ e' ∈ V ∧ e' ≠ 1 := by
        by_cases he : e = 0
        · simp only [he, ite_true]
          exact ⟨b, ha, hbV, hb1⟩
        · simp only [he, ite_false]
          refine ⟨xP * b, rep_compA hxr ha, V.mul_mem hxV hbV, fun h1 => hbx ?_⟩
          rw [← hxinv]
          exact eq_inv_of_mul_eq_one_right h1
      have hmem : ∀ {c : Array ℕ}, validA n c = true → inX c = true →
          commA n c (if e = 0 then a else compA n r.x a) = true →
          permOfArr n c ∈ X ⊓ centralizer ({e'} : Set (Equiv.Perm (Fin n))) :=
        fun hv hX hc => ⟨hinX _ hv hX, mem_centralizer_singleton_iff.mpr
          ((commA_iff (rep_of_validA hv) he'r).mp hc)⟩
      have hγV : centDer X e' ≤ gammaE X V := le_iSup₂_of_le e' he'V (le_iSup_of_le he'1 le_rfl)
      have hγ : ⁅permOfArr n c₁, permOfArr n c₂⁆ ∈ gammaE X V :=
        hγV (commutator_mem_commutator (hmem hv1 hX1 hc1) (hmem hv2 hX2 hc2))
      have hw : Rep n (compA n (compA n r.x (commutatorA n c₁ c₂))
          (compA n r.x (commutatorA n c₂ c₁))) ⁅xP, ⁅permOfArr n c₁, permOfArr n c₂⁆⁆ := by
        rw [commutatorElement_def xP, hxinv, mul_assoc, ← commutatorElement_inv]
        exact rep_compA (rep_compA hxr (rep_commutatorA hv1 hv2))
          (rep_compA hxr (rep_commutatorA hv2 hv1))
      have hwN : ⁅xP, ⁅permOfArr n c₁, permOfArr n c₂⁆⁆ ∈ nE X V :=
        commutator_mem_commutator hxV hγ
      have hym := rep_powA hw m
      have h2' : ¬ (⁅xP, ⁅permOfArr n c₁, permOfArr n c₂⁆⁆ ^ m) ^ 2 ^ 1 = 1 := by
        intro hc
        rw [pow_one, sq] at hc
        rw [(eqA_iff (rep_compA hym hym) rep_idA).2 hc] at h2
        exact Bool.noConfusion h2
      have h4' : (⁅xP, ⁅permOfArr n c₁, permOfArr n c₂⁆⁆ ^ m) ^ 2 ^ (1 + 1) = 1 :=
        eq_of_eqA (rep_powA hym 4) rep_idA h4
      have hord := orderOf_eq_prime_pow h2' h4'
      refine Or.inl ⟨_ ^ m, pow_mem hwN m, ?_⟩
      rw [hord]
      norm_num

end Soundness

section Decode

variable (tk : Array ℕ) (regs : Array (Array ℕ))

@[expose] def rdNat (p : ℕ) : ℕ × ℕ := (tk[p]!, p + 1)

@[expose] def rdPerf (p : ℕ) : PerfCert × ℕ :=
  let g := rdListC tk (rdPow tk (rdNat tk)) p
  let c := rdListC tk (rdPair tk) g.2
  let q := c.2
  let cj := rdListC tk (rdNat tk) (q + 2)
  (⟨g.1, c.1, tk[q]!, tk[q + 1]!, cj.1⟩, cj.2)

@[expose] def rdCand (p : ℕ) : RootWit × ℕ :=
  if tk[p]! = 0 then (.perf tk[p + 1]!, p + 2)
  else if tk[p]! = 2 then
    let l := rdListC tk (rdNat tk) (p + 1)
    (.ord4p l.1 tk[l.2]!, l.2 + 1)
  else if tk[p]! = 3 then
    (.ord4c tk[p + 1]! (regs[tk[p + 2]!]!) (regs[tk[p + 3]!]!) tk[p + 4]!, p + 5)
  else (.ord4 tk[p + 1]! tk[p + 2]!, p + 3)

@[expose] def rdRoot (x : Array ℕ) (p : ℕ) : RootCert × ℕ :=
  let s := rdListC tk (rdReg tk regs) p
  let b := rdListC tk (rdNat tk) s.2
  let c := rdListC tk (rdReg tk regs) b.2
  let g := rdListC tk (rdPair tk) c.2
  let f := rdListC tk (rdPerf tk) g.2
  let d := rdListC tk (rdCand tk regs) f.2
  (⟨x, s.1.toArray, b.1, c.1.toArray, g.1.toArray, f.1.toArray, d.1⟩, d.2)

@[expose] def rdRoots : List (Array ℕ) → ℕ → List RootCert
  | [], _ => []
  | x :: xs, p => (rdRoot tk regs x p).1 :: rdRoots xs (rdRoot tk regs x p).2

theorem rdRoots_x : ∀ (xs : List (Array ℕ)) (p : ℕ), (rdRoots tk regs xs p).map RootCert.x = xs
  | [], _ => rfl
  | x :: xs, p => by
    rw [rdRoots, List.map_cons, rdRoots_x xs]
    rfl

end Decode

@[expose] def decodeRoots (regs : Array (Array ℕ)) (xs : List (Array ℕ)) (s : String) :
    List RootCert :=
  rdRoots (decodeNats s) regs xs 0

theorem decodeRoots_x (regs : Array (Array ℕ)) (xs : List (Array ℕ)) (s : String) :
    (decodeRoots regs xs s).map RootCert.x = xs :=
  rdRoots_x _ regs xs 0

end CFSG.ComponentClassification.RankTwoSporadic.RootCensus
