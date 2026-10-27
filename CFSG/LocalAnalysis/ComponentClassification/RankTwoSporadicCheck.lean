module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicTree
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCensus

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open scoped commutatorElement

@[expose] def prodA (n : ℕ) (l : List (Array ℕ)) : Array ℕ := l.foldr (compA n) (idA n)

@[expose] def powA (n : ℕ) (a : Array ℕ) (m : ℕ) : Array ℕ := prodA n (List.replicate m a)

@[expose] def maskA (n : ℕ) (basis : Array (Array ℕ)) (m : ℕ) : Array ℕ :=
  prodA n (((List.range basis.size).filter fun k => m.testBit k).map fun k => basis[k]!)

@[expose] def commA (n : ℕ) (a b : Array ℕ) : Bool := eqA n (compA n a b) (compA n b a)

@[expose] def memA (n : ℕ) (c : ArrCert) (a : Array ℕ) : Bool := c.pts.toList.any (eqA n a)

@[expose] def countA (outX : Array ℕ → Bool) (c : ArrCert) : ℕ :=
  ((Finset.range c.pts.size).filter fun i => outX c.pts[i]! = true).card

structure GFac where
  t : ℕ
  c₁ : Array ℕ
  c₂ : Array ℕ
deriving Inhabited

structure NFac where
  e : ℕ
  γ : List GFac
deriving Inhabited

structure CFac where
  x₁ : Array ℕ
  x₂ : Array ℕ
deriving Inhabited

inductive Wit where
  | order4 (w : List NFac) (m : ℕ)
  | twoGroup (gens : List (List NFac × ℕ)) (k : ℕ)
  | perfect (gens : List (List GFac × ℕ)) (comms : List (ℕ × ℕ)) (x k : ℕ) (conjs : List ℕ)
      (e g : ℕ)
  | inX
  | small
  | closing (s t : ℕ) (c : Array ℕ) (kc v : ℕ) (gens : List (List CFac × ℕ))
      (comms : List (ℕ × ℕ))
deriving Inhabited

@[expose] def Wit.isMono : Wit → Bool
  | .order4 .. => true
  | .perfect .. => true
  | _ => false

structure Node where
  basis : Array (Array ℕ)
  wit : Wit
  children : Array ℕ
deriving Inhabited

instance arrCertInhabited : Inhabited ArrCert := ⟨⟨#[], #[], #[], #[]⟩⟩

@[expose] def GFac.val (n : ℕ) (f : GFac) : Array ℕ := commutatorA n f.c₁ f.c₂

@[expose] def GFac.ok (n : ℕ) (inX : Array ℕ → Bool) (basis : Array (Array ℕ)) (f : GFac) :
    Bool :=
  !(eqA n (maskA n basis f.t) (idA n)) && validA n f.c₁ && validA n f.c₂ && inX f.c₁ &&
    inX f.c₂ && commA n f.c₁ (maskA n basis f.t) && commA n f.c₂ (maskA n basis f.t)

@[expose] def gammaA (n : ℕ) (l : List GFac) : Array ℕ := prodA n (l.map (GFac.val n))

@[expose] def NFac.val (n : ℕ) (basis : Array (Array ℕ)) (f : NFac) : Array ℕ :=
  commutatorA n (maskA n basis f.e) (gammaA n f.γ)

@[expose] def NFac.ok (n : ℕ) (inX : Array ℕ → Bool) (basis : Array (Array ℕ)) (f : NFac) :
    Bool :=
  f.γ.all (GFac.ok n inX basis) && validA n (maskA n basis f.e) && validA n (gammaA n f.γ)

@[expose] def nA (n : ℕ) (basis : Array (Array ℕ)) (l : List NFac) : Array ℕ :=
  prodA n (l.map (NFac.val n basis))

@[expose] def CFac.val (n : ℕ) (f : CFac) : Array ℕ := commutatorA n f.x₁ f.x₂

@[expose] def CFac.ok (n : ℕ) (inX : Array ℕ → Bool) (basis : Array (Array ℕ)) (f : CFac) :
    Bool :=
  validA n f.x₁ && validA n f.x₂ && inX f.x₁ && inX f.x₂ &&
    allLt basis.size fun k => commA n f.x₁ basis[k]! && commA n f.x₂ basis[k]!

@[expose] def witOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (inX outX : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (basis : Array (Array ℕ)) (cE : ArrCert) : Wit → Bool
  | .order4 w m =>
    let y := powA n (nA n basis w) m
    w.all (NFac.ok n inX basis) && !(eqA n (compA n y y) (idA n)) &&
      eqA n (powA n y 4) (idA n)
  | .twoGroup gens k =>
    let gs := (gens.map fun l => powA n (nA n basis l.1) l.2).toArray
    let cP := enumBfs n gs ps fuel
    gens.all (fun l => l.1.all (NFac.ok n inX basis)) && enumOK n gs ps cP &&
      cP.pts.size == 2 ^ k && decide (countA outX cE < 2 ^ k)
  | .perfect gens comms x k conjs e g =>
    let gs := (gens.map fun l => powA n (gammaA n l.1) l.2).toArray
    let cP := enumBfs n gs ps fuel
    let m := cP.pts.size
    let qs := (comms.map fun ij => commutatorA n cP.pts[ij.1]! cP.pts[ij.2]!).toArray
    let cQ := enumBfs n qs ps fuel
    let xa := cP.pts[x]!
    let rs := (conjs.map fun p => conjA n cP.pts[p]! (compA n xa xa)).toArray
    let cR := enumBfs n rs ps fuel
    allowPW && gens.all (fun l => l.1.all (GFac.ok n inX basis)) && enumOK n gs ps cP &&
      comms.all (fun ij => decide (ij.1 < m) && decide (ij.2 < m)) && enumOK n qs ps cQ &&
      cQ.pts.size == m && decide (x < m) && eqA n (powA n xa (2 ^ k)) (idA n) &&
      conjs.all (fun p => decide (p < m)) && enumOK n rs ps cR && cR.pts.size == m &&
      decide (g < m) && !(commA n (maskA n basis e) cP.pts[g]!)
  | .inX => allowInX && allLt basis.size fun k => inX basis[k]!
  | .small => decide (cE.pts.size < 4)
  | .closing s t c kc v gens comms =>
    let gs := (gens.map fun l => powA n (prodA n (l.1.map (CFac.val n))) l.2).toArray
    let cP := enumBfs n gs ps fuel
    let m := cP.pts.size
    let qs := (comms.map fun ij => commutatorA n cP.pts[ij.1]! cP.pts[ij.2]!).toArray
    let cQ := enumBfs n qs ps fuel
    allowU && !(eqA n (maskA n basis s) (idA n)) && !(eqA n (maskA n basis t) (idA n)) &&
      validA n c && inX c && commA n c (maskA n basis t) && eqA n (powA n c (2 ^ kc)) (idA n) &&
      validA n (maskA n basis v) &&
      eqA n (commutatorA n (maskA n basis v) c) (maskA n basis s) &&
      gens.all (fun l => l.1.all (CFac.ok n inX basis)) && enumOK n gs ps cP &&
      comms.all (fun ij => decide (ij.1 < m) && decide (ij.2 < m)) && enumOK n qs ps cQ &&
      cQ.pts.size == m && memA n cP (maskA n basis s)

@[expose] def childOK (n : ℕ) (nodes : Array Node) (cN : Array ArrCert) (i : ℕ) (u : Array ℕ)
    (j : ℕ) : Bool :=
  decide (j < nodes.size) &&
    (allLt nodes[j]!.basis.size fun k =>
      memA n cN[i]! nodes[j]!.basis[k]! || memA n cN[i]! (compA n u nodes[j]!.basis[k]!)) &&
    (allLt nodes[i]!.basis.size fun k => memA n cN[j]! nodes[i]!.basis[k]!) && memA n cN[j]! u

@[expose] def nodeOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (inX outX : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (cS : ArrCert) (nodes : Array Node) (cN : Array ArrCert)
    (i : ℕ) : Bool :=
  enumOK n nodes[i]!.basis ps cN[i]! &&
    witOK n ps fuel inX outX allowPW allowInX allowU nodes[i]!.basis cN[i]! nodes[i]!.wit &&
    (nodes[i]!.wit.isMono || allLt cS.pts.size fun p =>
      !(eqA n (compA n cS.pts[p]! cS.pts[p]!) (idA n)) ||
        !(allLt nodes[i]!.basis.size fun k => commA n cS.pts[p]! nodes[i]!.basis[k]!) ||
        memA n cN[i]! cS.pts[p]! || childOK n nodes cN i cS.pts[p]! nodes[i]!.children[p]!)

@[expose] def rootOK (n : ℕ) (nodes : Array Node) (cN : Array ArrCert) (u : Array ℕ) (j : ℕ) :
    Bool :=
  !(eqA n (compA n u u) (idA n)) || eqA n u (idA n) ||
    (decide (j < nodes.size) &&
      (allLt nodes[j]!.basis.size fun k =>
        eqA n nodes[j]!.basis[k]! u || eqA n nodes[j]!.basis[k]! (idA n)) && memA n cN[j]! u)

@[expose] def censusOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (inX outX : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (sGens : Array (Array ℕ)) (roots : Array ℕ)
    (nodes : Array Node) : Bool :=
  let cS := enumBfs n sGens ps fuel
  let cN := nodes.map fun nd => enumBfs n nd.basis ps fuel
  enumOK n sGens ps cS && (allLt cS.pts.size fun p => rootOK n nodes cN cS.pts[p]! roots[p]!) &&
    allLt nodes.size (nodeOK n ps fuel inX outX allowPW allowInX allowU cS nodes cN)

section Soundness

variable {n : ℕ}

theorem rep_prodA {H : Subgroup (Equiv.Perm (Fin n))} {l : List (Array ℕ)}
    (h : ∀ a ∈ l, ∃ g ∈ H, Rep n a g) : ∃ g ∈ H, Rep n (prodA n l) g := by
  induction l with
  | nil => exact ⟨1, H.one_mem, rep_idA⟩
  | cons a l ih =>
    obtain ⟨g, hg, hga⟩ := h a (by simp)
    obtain ⟨g', hg', hga'⟩ := ih fun b hb => h b (by simp [hb])
    exact ⟨g * g', H.mul_mem hg hg', rep_compA hga hga'⟩

theorem rep_powA {a : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n a g) (m : ℕ) :
    Rep n (powA n a m) (g ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero]
    exact rep_idA
  | succ m ih =>
    rw [pow_succ']
    exact rep_compA h ih

theorem rep_maskA {basis : Array (Array ℕ)} (hb : ∀ k < basis.size, validA n basis[k]! = true)
    (m : ℕ) : ∃ g ∈ closure (permsA n basis), Rep n (maskA n basis m) g := by
  apply rep_prodA
  intro a ha
  simp only [List.mem_map, List.mem_filter, List.mem_range] at ha
  obtain ⟨k, ⟨hk, -⟩, rfl⟩ := ha
  exact ⟨_, subset_closure (mem_permsA hk), rep_of_validA (hb k hk)⟩

theorem commA_iff {a b : Array ℕ} {g h : Equiv.Perm (Fin n)} (ha : Rep n a g) (hb : Rep n b h) :
    commA n a b = true ↔ g * h = h * g :=
  eqA_iff (rep_compA ha hb) (rep_compA hb ha)

theorem getElem!_toArray_mem {α : Type*} [Inhabited α] {l : List α} {i : ℕ}
    (hi : i < l.toArray.size) : l.toArray[i]! ∈ l := by
  rw [getElem!_pos l.toArray i hi]
  simp

variable {X : Subgroup (Equiv.Perm (Fin n))} {inX outX : Array ℕ → Bool}
  {basis : Array (Array ℕ)}

theorem GFac.mem_gammaE (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hb : ∀ k < basis.size, validA n basis[k]! = true) {f : GFac}
    (h : f.ok n inX basis = true) :
    ∃ g ∈ gammaE X (closure (permsA n basis)), Rep n (f.val n) g := by
  simp only [GFac.ok, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨ht1, hv1⟩, hv2⟩, hx1⟩, hx2⟩, hc1⟩, hc2⟩ := h
  obtain ⟨t, htE, ht⟩ := rep_maskA hb f.t
  have ht1' : t ≠ 1 := by
    rintro rfl
    rw [(eqA_iff ht rep_idA).2 rfl] at ht1
    exact Bool.noConfusion ht1
  have hr1 := rep_of_validA hv1
  have hr2 := rep_of_validA hv2
  have hm1 : permOfArr n f.c₁ ∈ X ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) :=
    ⟨hin _ hv1 hx1, mem_centralizer_singleton_iff.mpr ((commA_iff hr1 ht).mp hc1)⟩
  have hm2 : permOfArr n f.c₂ ∈ X ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) :=
    ⟨hin _ hv2 hx2, mem_centralizer_singleton_iff.mpr ((commA_iff hr2 ht).mp hc2)⟩
  have hle : centDer X t ≤ gammaE X (closure (permsA n basis)) :=
    le_iSup₂_of_le t htE (le_iSup_of_le ht1' le_rfl)
  exact ⟨_, hle (commutator_mem_commutator hm1 hm2), rep_commutatorA hv1 hv2⟩

theorem rep_gammaA (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hb : ∀ k < basis.size, validA n basis[k]! = true) {l : List GFac}
    (h : l.all (GFac.ok n inX basis) = true) :
    ∃ g ∈ gammaE X (closure (permsA n basis)), Rep n (gammaA n l) g := by
  apply rep_prodA
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨f, hf, rfl⟩ := ha
  exact GFac.mem_gammaE hin hb (List.all_eq_true.mp h f hf)

theorem NFac.mem_nE (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hb : ∀ k < basis.size, validA n basis[k]! = true) {f : NFac}
    (h : f.ok n inX basis = true) :
    ∃ g ∈ nE X (closure (permsA n basis)), Rep n (f.val n basis) g := by
  simp only [NFac.ok, Bool.and_eq_true] at h
  obtain ⟨⟨hγ, hve⟩, hvγ⟩ := h
  obtain ⟨e, heE, he⟩ := rep_maskA hb f.e
  obtain ⟨γ, hγE, hγr⟩ := rep_gammaA hin hb hγ
  refine ⟨_, ?_, rep_commutatorA hve hvγ⟩
  rw [permOfArr_eq_of_rep he, permOfArr_eq_of_rep hγr]
  exact commutator_mem_commutator heE hγE

theorem rep_nA (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hb : ∀ k < basis.size, validA n basis[k]! = true) {l : List NFac}
    (h : l.all (NFac.ok n inX basis) = true) :
    ∃ g ∈ nE X (closure (permsA n basis)), Rep n (nA n basis l) g := by
  apply rep_prodA
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨f, hf, rfl⟩ := ha
  exact NFac.mem_nE hin hb (List.all_eq_true.mp h f hf)

theorem card_inf_le_countA {ps : List ℕ} {cE : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (hE : enumOK n basis ps cE = true)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ X → outX a = true) :
    Nat.card ↥(closure (permsA n basis) ⊓ X) ≤ countA outX cE := by
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps hE
  set F := (Finset.range cE.pts.size).filter fun i => outX cE.pts[i]! = true
  have hsub : ((closure (permsA n basis) ⊓ X : Subgroup (Equiv.Perm (Fin n))) :
      Set (Equiv.Perm (Fin n))) ⊆ (fun i => permOfArr n cE.pts[i]!) '' (F : Set ℕ) := by
    rintro x ⟨hxE, hxX⟩
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 hxE
    refine ⟨i, ?_, rfl⟩
    simp only [F, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨hi, hout _ (hval i hi) hxX⟩
  calc Nat.card ↥(closure (permsA n basis) ⊓ X)
      = ((closure (permsA n basis) ⊓ X : Subgroup (Equiv.Perm (Fin n))) :
          Set (Equiv.Perm (Fin n))).ncard := (Nat.card_coe_set_eq _).symm
    _ ≤ ((fun i => permOfArr n cE.pts[i]!) '' (F : Set ℕ)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (F : Set ℕ).ncard := Set.ncard_image_le F.finite_toSet
    _ = countA outX cE := Set.ncard_coe_finset F

theorem closure_le_of_rep {H : Subgroup (Equiv.Perm (Fin n))} {α : Type*} {l : List α}
    {f : α → Array ℕ} (h : ∀ a ∈ l, ∃ g ∈ H, Rep n (f a) g) :
    closure (permsA n (l.map f).toArray) ≤ H := by
  rw [closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hmem := getElem!_toArray_mem hk
  rw [List.mem_map] at hmem
  obtain ⟨a, ha, he⟩ := hmem
  obtain ⟨g, hg, hr⟩ := h a ha
  change permOfArr n (l.map f).toArray[k]! ∈ H
  rw [← he, permOfArr_eq_of_rep hr]
  exact hg

theorem commutator_eq_self_of_check {ps : List ℕ} {gs : Array (Array ℕ)} {cP cQ : ArrCert}
    {comms : List (ℕ × ℕ)} (hps : ∀ p ∈ ps, p < n) (hP : enumOK n gs ps cP = true)
    (hcomms : ∀ ij ∈ comms, ij.1 < cP.pts.size ∧ ij.2 < cP.pts.size)
    (hQ : enumOK n (comms.map fun ij => commutatorA n cP.pts[ij.1]! cP.pts[ij.2]!).toArray ps cQ =
      true)
    (hQsize : cQ.pts.size = cP.pts.size) :
    ⁅closure (permsA n gs), closure (permsA n gs)⁆ = closure (permsA n gs) := by
  set P := closure (permsA n gs)
  obtain ⟨hPmem, hPcard, hPval⟩ := enumOK_spec hps hP
  have hpt : ∀ i < cP.pts.size, permOfArr n cP.pts[i]! ∈ P := fun i hi => (hPmem _).2 ⟨i, hi, rfl⟩
  have hcommP : ⁅P, P⁆ ≤ P := by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
  have hQle : closure (permsA n (comms.map fun ij =>
      commutatorA n cP.pts[ij.1]! cP.pts[ij.2]!).toArray) ≤ ⁅P, P⁆ := by
    refine closure_le_of_rep fun ij hij => ?_
    obtain ⟨h1, h2⟩ := hcomms ij hij
    exact ⟨_, commutator_mem_commutator (hpt _ h1) (hpt _ h2),
      rep_commutatorA (hPval _ h1) (hPval _ h2)⟩
  obtain ⟨-, hQcard, -⟩ := enumOK_spec hps hQ
  refine eq_of_le_of_card_ge hcommP ?_
  calc Nat.card P = _ := hPcard
    _ = _ := hQsize.symm
    _ = _ := hQcard.symm
    _ ≤ Nat.card ↥(⁅P, P⁆ : Subgroup (Equiv.Perm (Fin n))) := card_le_of_le hQle

theorem mem_centralizer_closure_of_commute {S : Set (Equiv.Perm (Fin n))}
    {x : Equiv.Perm (Fin n)} (h : ∀ y ∈ S, x * y = y * x) :
    x ∈ centralizer ((closure S : Subgroup (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))) := by
  have hle : closure S ≤ centralizer ({x} : Set (Equiv.Perm (Fin n))) := by
    rw [closure_le]
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (h y hy).symm
  exact mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hle hy)

@[expose] def MonoW {W : Type*} [Group W] (X : Subgroup W) (allowPW : Bool) (E : Subgroup W) :
    Prop :=
  (∃ w ∈ nE X E, 4 ∣ orderOf w) ∨ (allowPW = true ∧ PWitness X E)

@[expose] def WitW {W : Type*} [Group W] (X : Subgroup W) (allowPW allowInX allowU : Bool)
    (E : Subgroup W) : Prop :=
  YWitness X E ∨ (allowPW = true ∧ PWitness X E) ∨ (allowInX = true ∧ E ≤ X) ∨
    (allowU = true ∧ UWitness X E)

theorem witW_of_monoW {W : Type*} [Group W] {X : Subgroup W} {allowPW : Bool}
    (allowInX allowU : Bool) {E₀ E : Subgroup W} (h : MonoW X allowPW E₀) (hle : E₀ ≤ E) :
    WitW X allowPW allowInX allowU E := by
  rcases h with hw | ⟨hPW, hP⟩
  · exact Or.inl (yWitness_of_le_of_orderOf hle hw)
  · exact Or.inr (Or.inl ⟨hPW, pWitness_of_le hle hP⟩)

theorem witOK_sound {ps : List ℕ} {fuel : ℕ} {allowPW allowInX allowU : Bool} {cE : ArrCert}
    (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ X → outX a = true)
    (hE : enumOK n basis ps cE = true) {w : Wit}
    (h : witOK n ps fuel inX outX allowPW allowInX allowU basis cE w = true) :
    MonoW X allowPW (closure (permsA n basis)) ∨ (w.isMono = false ∧
      (4 ≤ Nat.card (closure (permsA n basis)) →
        WitW X allowPW allowInX allowU (closure (permsA n basis)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : ∀ k < basis.size, validA n basis[k]! = true := fun k hk => enumOK_gens_valid hE hk
  cases w with
  | order4 w m =>
    simp only [witOK, Bool.and_eq_true, Bool.not_eq_true'] at h
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
    simp only [witOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hgens, hP⟩, hsize⟩, hcount⟩ := h
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
    simp only [witOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
      List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hPW, hgens⟩, hP⟩, hcomms⟩, hQ⟩, hQsize⟩, hx⟩, hxpow⟩, hconjs⟩, hR⟩,
      hRsize⟩, hg⟩, hnc⟩ := h
    set gs := (gens.map fun l => powA n (gammaA n l.1) l.2).toArray
    set cP := enumBfs n gs ps fuel
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
    simp only [witOK, Bool.and_eq_true] at h
    obtain ⟨hX, hall⟩ := h
    refine Or.inr ⟨rfl, fun _ => Or.inr (Or.inr (Or.inl ⟨hX, ?_⟩))⟩
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hin _ (hb k hk) (allLt_spec hall hk)
  | small =>
    simp only [witOK, decide_eq_true_eq] at h
    obtain ⟨-, hcard, -⟩ := enumOK_spec hps hE
    refine Or.inr ⟨rfl, fun h4 => ?_⟩
    rw [hcard] at h4
    omega
  | closing s t c kc v gens comms =>
    simp only [witOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
      List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hU, hs1⟩, ht1⟩, hcv⟩, hcX⟩, hct⟩, hcpow⟩, hvv⟩, hvc⟩, hgens⟩, hP⟩,
      hcomms⟩, hQ⟩, hQsize⟩, hsP⟩ := h
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

@[expose] noncomputable def nodeSub (n : ℕ) (nodes : Array Node) (i : ℕ) :
    Subgroup (Equiv.Perm (Fin n)) :=
  closure (permsA n nodes[i]!.basis)

theorem census_of_censusOK {ps : List ℕ} {fuel : ℕ} {allowPW allowInX allowU : Bool}
    {sGens : Array (Array ℕ)} {roots : Array ℕ} {nodes : Array Node} (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ X → outX a = true)
    (h : censusOK n ps fuel inX outX allowPW allowInX allowU sGens roots nodes = true)
    {E : Subgroup (Equiv.Perm (Fin n))} (hES : E ≤ closure (permsA n sGens))
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) :
    YWitness X E ∨ (allowPW = true ∧ PWitness X E) ∨ (allowInX = true ∧ E ≤ X) ∨
      (allowU = true ∧ UWitness X E) := by
  simp only [censusOK, Bool.and_eq_true] at h
  obtain ⟨⟨hS, hroot⟩, hnodes⟩ := h
  set cS := enumBfs n sGens ps fuel
  set cN := nodes.map fun nd => enumBfs n nd.basis ps fuel
  obtain ⟨hSmem, -, hSval⟩ := enumOK_spec hps hS
  have hnode : ∀ i < nodes.size,
      nodeOK n ps fuel inX outX allowPW allowInX allowU cS nodes cN i = true :=
    fun i hi => allLt_spec hnodes hi
  have hnodeE : ∀ i < nodes.size, enumOK n nodes[i]!.basis ps cN[i]! = true := by
    intro i hi
    have := hnode i hi
    simp only [nodeOK, Bool.and_eq_true] at this
    exact this.1.1
  have hbasis : ∀ i < nodes.size, ∀ k < nodes[i]!.basis.size,
      validA n nodes[i]!.basis[k]! = true := fun i hi k hk => enumOK_gens_valid (hnodeE i hi) hk
  have hmemN : ∀ i < nodes.size, ∀ {a : Array ℕ} {g : Equiv.Perm (Fin n)}, Rep n a g →
      memA n cN[i]! a = true → g ∈ nodeSub n nodes i :=
    fun i hi a g ha hm => enumOK_mem_of_any hps (hnodeE i hi) ha hm
  refine forall_of_tree (S := closure (permsA n sGens)) (WitW X allowPW allowInX allowU)
    (MonoW X allowPW) (fun E₀ E hm hle _ _ _ => witW_of_monoW allowInX allowU hm hle)
    (nodeSub n nodes) nodes.size ?_ ?_ ?_ hES hE hE4
  ·
    intro a ha ha2 ha1
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
  ·
    intro i hi
    have hn := hnode i hi
    simp only [nodeOK, Bool.and_eq_true, Bool.or_eq_true] at hn
    obtain ⟨⟨hEi, hwit⟩, hch⟩ := hn
    rcases witOK_sound hps hin hout hEi hwit with hm | ⟨hnm, -⟩
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
  ·
    intro i hi h4
    have hn := hnode i hi
    simp only [nodeOK, Bool.and_eq_true] at hn
    rcases witOK_sound hps hin hout hn.1.1 hn.1.2 with hm | ⟨-, hw⟩
    · exact Or.inl hm
    · exact Or.inr (hw h4)

end Soundness

section Decode

@[expose] def digitOf (c : ℕ) : ℕ × Bool :=
  if 65 ≤ c ∧ c ≤ 90 then (c - 65, true)
  else if 97 ≤ c ∧ c ≤ 102 then (c - 71, true)
  else if 103 ≤ c ∧ c ≤ 122 then (c - 103, false)
  else if 48 ≤ c ∧ c ≤ 57 then (c - 28, false)
  else if c = 43 then (30, false)
  else (31, false)

@[expose] def decodeNats (s : String) : Array ℕ :=
  (s.toUTF8.foldl (fun (st : Array ℕ × ℕ) b =>
    let d := digitOf b.toNat
    if d.2 then (st.1.push (st.2 * 32 + d.1), 0) else (st.1, st.2 * 32 + d.1)) (#[], 0)).1

variable (tk : Array ℕ) (n : ℕ)

@[expose] def rdList {α : Type} (rd : ℕ → α × ℕ) : ℕ → ℕ → List α × ℕ
  | 0, p => ([], p)
  | c + 1, p =>
    let r := rd p
    let rs := rdList rd c r.2
    (r.1 :: rs.1, rs.2)

@[expose] def rdListC {α : Type} (rd : ℕ → α × ℕ) (p : ℕ) : List α × ℕ :=
  rdList rd tk[p]! (p + 1)

@[expose] def rdArr (p : ℕ) : Array ℕ × ℕ := (Array.ofFn (n := n) fun i => tk[p + i.val]!, p + n)

@[expose] def rdGFac (p : ℕ) : GFac × ℕ :=
  let a := rdArr tk n (p + 1)
  let b := rdArr tk n a.2
  (⟨tk[p]!, a.1, b.1⟩, b.2)

@[expose] def rdCFac (p : ℕ) : CFac × ℕ :=
  let a := rdArr tk n p
  let b := rdArr tk n a.2
  (⟨a.1, b.1⟩, b.2)

@[expose] def rdNFac (p : ℕ) : NFac × ℕ :=
  let l := rdListC tk (rdGFac tk n) (p + 1)
  (⟨tk[p]!, l.1⟩, l.2)

@[expose] def rdPow {α : Type} (rd : ℕ → α × ℕ) (p : ℕ) : (List α × ℕ) × ℕ :=
  let l := rdListC tk rd p
  ((l.1, tk[l.2]!), l.2 + 1)

@[expose] def rdPair (p : ℕ) : (ℕ × ℕ) × ℕ := ((tk[p]!, tk[p + 1]!), p + 2)

@[expose] def rdWit (p : ℕ) : Wit × ℕ :=
  match tk[p]! with
  | 0 =>
    let w := rdListC tk (rdNFac tk n) (p + 1)
    (.order4 w.1 tk[w.2]!, w.2 + 1)
  | 1 =>
    let g := rdListC tk (rdPow tk (rdNFac tk n)) (p + 1)
    (.twoGroup g.1 tk[g.2]!, g.2 + 1)
  | 2 =>
    let g := rdListC tk (rdPow tk (rdGFac tk n)) (p + 1)
    let c := rdListC tk (rdPair tk) g.2
    let q := c.2
    let cj := rdListC tk (fun p => (tk[p]!, p + 1)) (q + 2)
    (.perfect g.1 c.1 tk[q]! tk[q + 1]! cj.1 tk[cj.2]! tk[cj.2 + 1]!, cj.2 + 2)
  | 3 => (.inX, p + 1)
  | 5 =>
    let c := rdArr tk n (p + 3)
    let g := rdListC tk (rdPow tk (rdCFac tk n)) (c.2 + 2)
    let cm := rdListC tk (rdPair tk) g.2
    (.closing tk[p + 1]! tk[p + 2]! c.1 tk[c.2]! tk[c.2 + 1]! g.1 cm.1, cm.2)
  | _ => (.small, p + 1)

@[expose] def rdNode (p : ℕ) : Node × ℕ :=
  let b := rdListC tk (rdArr tk n) p
  let w := rdWit tk n b.2
  let c := rdListC tk (fun p => (tk[p]!, p + 1)) w.2
  (⟨b.1.toArray, w.1, c.1.toArray⟩, c.2)

structure CensusData where
  sGens : Array (Array ℕ)
  roots : Array ℕ
  nodes : Array Node

@[expose] def rdCensus : CensusData :=
  let s := rdListC tk (rdArr tk n) 0
  let r := rdListC tk (fun p => (tk[p]!, p + 1)) s.2
  let d := rdListC tk (rdNode tk n) r.2
  ⟨s.1.toArray, r.1.toArray, d.1.toArray⟩

end Decode

@[expose] def decodeCert (n : ℕ) (s : String) : CensusData := rdCensus (decodeNats s) n

end CFSG.ComponentClassification.RankTwoSporadic.Cert
