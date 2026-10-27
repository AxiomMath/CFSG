module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicWitData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheckW

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open scoped commutatorElement

structure PerfW where
  pw : List (List ℕ)
  comms : List (ℕ × ℕ)
  genQ : List (List ℕ)
  x : ℕ
  k : ℕ
  conjs : List ℕ
  genR : List (List ℕ)
  e : ℕ
  g : ℕ
deriving Inhabited

@[expose] def lettersLt (m : ℕ) (ws : List (List ℕ)) : Bool :=
  ws.all fun w => w.all fun i => decide (i < m)

@[expose] def witOKW2 (n : ℕ) (ps : List ℕ) (inX outX : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (basis : Array (Array ℕ)) (cE : ArrCert)
    (cs : Array ArrCert) (pf : PerfW) : Wit → Bool
  | .perfect gens _ _ _ _ _ _ =>
    let gs := (gens.map fun l => powA n (gammaA n l.1) l.2).toArray
    let pts := (pf.pw.map (wordG n gs)).toArray
    let qs := (pf.comms.map fun ij => commutatorA n pts[ij.1]! pts[ij.2]!).toArray
    let xa := pts[pf.x]!
    let rs := (pf.conjs.map fun p => conjA n pts[p]! (compA n xa xa)).toArray
    allowPW && gens.all (fun l => l.1.all (GFac.okK n inX basis)) &&
      lettersLt gs.size pf.pw && ((List.range pts.size).all fun j => validK n pts[j]!) &&
      pf.comms.all (fun ij => decide (ij.1 < pts.size) && decide (ij.2 < pts.size)) &&
      lettersLt qs.size pf.genQ &&
      ((List.range gs.size).all fun i => eqA n gs[i]! (wordG n qs (pf.genQ.getD i []))) &&
      decide (pf.x < pts.size) && eqA n (powA n xa (2 ^ pf.k)) (idA n) &&
      pf.conjs.all (fun p => decide (p < pts.size)) && lettersLt rs.size pf.genR &&
      ((List.range gs.size).all fun i => eqA n gs[i]! (wordG n rs (pf.genR.getD i []))) &&
      decide (pf.g < pts.size) && !(commA n (maskA n basis pf.e) pts[pf.g]!)
  | w => witOKW n ps inX outX allowPW allowInX allowU basis cE cs w

@[expose] def nodeOKW2 (n : ℕ) (ps : List ℕ) (inX outX : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (cS : ArrCert) (nodes : Array Node) (cN : Array ArrCert)
    (wcs : Array (Array ArrCert)) (pfs : Array PerfW) (i : ℕ) : Bool :=
  enumOKK n nodes[i]!.basis ps cN[i]! &&
    witOKW2 n ps inX outX allowPW allowInX allowU nodes[i]!.basis cN[i]! wcs[i]! pfs[i]!
      nodes[i]!.wit &&
    (nodes[i]!.wit.isMono || allLt cS.pts.size fun p =>
      !(eqA n (compA n cS.pts[p]! cS.pts[p]!) (idA n)) ||
        !(allLt nodes[i]!.basis.size fun k => commA n cS.pts[p]! nodes[i]!.basis[k]!) ||
        memA n cN[i]! cS.pts[p]! || childOK n nodes cN i cS.pts[p]! nodes[i]!.children[p]!)

@[expose] def censusOKW2 (n : ℕ) (ps : List ℕ) (inX outX : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (sGens : Array (Array ℕ)) (roots : Array ℕ)
    (nodes : Array Node) (cS : ArrCert) (wcs : Array (Array ArrCert)) (pfs : Array PerfW) :
    Bool :=
  let cN := nodes.map fun nd => maskCert n nd.basis
  enumOKK n sGens ps cS && (allLt cS.pts.size fun p => rootOK n nodes cN cS.pts[p]! roots[p]!) &&
    allLt nodes.size (nodeOKW2 n ps inX outX allowPW allowInX allowU cS nodes cN wcs pfs)

section Soundness

variable {n : ℕ}

theorem rep_toArray {α : Type*} {H : Subgroup (Equiv.Perm (Fin n))} {l : List α}
    {f : α → Array ℕ} (h : ∀ a ∈ l, ∃ g ∈ H, Rep n (f a) g) :
    ∀ i < (l.map f).toArray.size, ∃ g ∈ H, Rep n (l.map f).toArray[i]! g := by
  intro i hi
  have hm := getElem!_toArray_mem hi
  rw [List.mem_map] at hm
  obtain ⟨a, ha, he⟩ := hm
  rw [← he]
  exact h a ha

theorem rep_wordG {H : Subgroup (Equiv.Perm (Fin n))} {as : Array (Array ℕ)}
    (has : ∀ i < as.size, ∃ g ∈ H, Rep n as[i]! g) {w : List ℕ} (hw : ∀ i ∈ w, i < as.size) :
    ∃ g ∈ H, Rep n (wordG n as w) g := by
  apply rep_prodA
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact has i (hw i hi)

theorem lettersLt_spec {m : ℕ} {ws : List (List ℕ)} (h : lettersLt m ws = true) :
    ∀ w ∈ ws, ∀ i ∈ w, i < m := by
  intro w hw i hi
  simp only [lettersLt, List.all_eq_true, decide_eq_true_eq] at h
  exact h w hw i hi

theorem lettersLt_getD {m : ℕ} {ws : List (List ℕ)} (h : lettersLt m ws = true) (j : ℕ) :
    ∀ i ∈ ws.getD j [], i < m := by
  intro i hi
  rcases Nat.lt_or_ge j ws.length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj] at hi
    exact lettersLt_spec h _ (List.getElem_mem hj) i hi
  · rw [List.getD_eq_default _ _ hj] at hi
    simp at hi

variable {X : Subgroup (Equiv.Perm (Fin n))} {inX outX : Array ℕ → Bool}
  {basis : Array (Array ℕ)}

theorem closure_le_of_words {as bs : Array (Array ℕ)} {ws : List (List ℕ)}
    (hbs : ∀ i < bs.size, ∃ g ∈ closure (permsA n bs), Rep n bs[i]! g)
    (hl : lettersLt bs.size ws = true)
    (has : ∀ i < as.size, ∃ g, Rep n as[i]! g)
    (he : ((List.range as.size).all fun i => eqA n as[i]! (wordG n bs (ws.getD i []))) = true) :
    closure (permsA n as) ≤ closure (permsA n bs) := by
  rw [closure_le]
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨g, hg⟩ := has i hi
  obtain ⟨h, hh, hr⟩ := rep_wordG hbs (lettersLt_getD hl i)
  have hei := List.all_eq_true.1 he i (List.mem_range.2 hi)
  change permOfArr n as[i]! ∈ _
  rw [permOfArr_eq_of_rep hg, eq_of_eqA hg hr hei]
  exact hh

theorem witOKW2_sound {ps : List ℕ} {allowPW allowInX allowU : Bool} {cE : ArrCert}
    {cs : Array ArrCert} {pf : PerfW} (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ X → outX a = true)
    (hE : enumOK n basis ps cE = true) {w : Wit}
    (h : witOKW2 n ps inX outX allowPW allowInX allowU basis cE cs pf w = true) :
    MonoW X allowPW (closure (permsA n basis)) ∨ (w.isMono = false ∧
      (4 ≤ Nat.card (closure (permsA n basis)) →
        WitW X allowPW allowInX allowU (closure (permsA n basis)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : ∀ k < basis.size, validA n basis[k]! = true := fun k hk => enumOK_gens_valid hE hk
  cases w with
  | perfect gens comms0 x0 k0 conjs0 e0 g0 =>
    simp only [witOKW2, GFac.okK_eq, validK_eq, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hPW, hgens⟩, hpw⟩, hval⟩, hcomms⟩, hlq⟩, hgq⟩, hx⟩, hxpow⟩, hconjs⟩,
      hlr⟩, hgr⟩, hg⟩, hnc⟩ := h
    set gs := (gens.map fun l => powA n (gammaA n l.1) l.2).toArray
    set P := closure (permsA n gs)
    set pts := (pf.pw.map (wordG n gs)).toArray
    have hgsΓ : ∀ i < gs.size, ∃ g ∈ gammaE X (closure (permsA n basis)), Rep n gs[i]! g := by
      refine rep_toArray fun l hl => ?_
      obtain ⟨y, hyN, hy⟩ := rep_gammaA hin hb (List.all_eq_true.mp hgens l hl)
      exact ⟨y ^ l.2, pow_mem hyN _, rep_powA hy _⟩
    have hgsP : ∀ i < gs.size, ∃ g ∈ P, Rep n gs[i]! g := by
      intro i hi
      obtain ⟨g, -, hr⟩ := hgsΓ i hi
      refine ⟨g, ?_, hr⟩
      rw [← permOfArr_eq_of_rep hr]
      exact subset_closure (mem_permsA hi)
    have hPΓ : P ≤ gammaE X (closure (permsA n basis)) := by
      rw [closure_le]
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨g, hg', hr⟩ := hgsΓ i hi
      change permOfArr n gs[i]! ∈ _
      rw [permOfArr_eq_of_rep hr]
      exact hg'
    have hptsP : ∀ j < pts.size, ∃ g ∈ P, Rep n pts[j]! g := by
      refine rep_toArray fun w hw => rep_wordG hgsP (lettersLt_spec hpw w hw)
    have hvalj : ∀ j < pts.size, validA n pts[j]! = true :=
      fun j hj => List.all_eq_true.1 hval j (List.mem_range.2 hj)
    have hmemP : ∀ j < pts.size, permOfArr n pts[j]! ∈ P := by
      intro j hj
      obtain ⟨g, hg', hr⟩ := hptsP j hj
      rw [permOfArr_eq_of_rep hr]
      exact hg'
    set qs := (pf.comms.map fun ij => commutatorA n pts[ij.1]! pts[ij.2]!).toArray
    have hqs : ∀ i < qs.size, ∃ g ∈ ⁅P, P⁆, Rep n qs[i]! g := by
      refine rep_toArray fun ij hij => ?_
      have h12 := List.all_eq_true.1 hcomms ij hij
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h12
      exact ⟨_, commutator_mem_commutator (hmemP _ h12.1) (hmemP _ h12.2),
        rep_commutatorA (hvalj _ h12.1) (hvalj _ h12.2)⟩
    have hqsQ : ∀ i < qs.size, ∃ g ∈ closure (permsA n qs), Rep n qs[i]! g := by
      intro i hi
      obtain ⟨g, -, hr⟩ := hqs i hi
      refine ⟨g, ?_, hr⟩
      rw [← permOfArr_eq_of_rep hr]
      exact subset_closure (mem_permsA hi)
    have hQ : closure (permsA n qs) ≤ ⁅P, P⁆ := by
      rw [closure_le]
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨g, hg', hr⟩ := hqs i hi
      change permOfArr n qs[i]! ∈ _
      rw [permOfArr_eq_of_rep hr]
      exact hg'
    have hgsRep : ∀ i < gs.size, ∃ g, Rep n gs[i]! g := fun i hi => by
      obtain ⟨g, -, hr⟩ := hgsP i hi
      exact ⟨g, hr⟩
    have hPQ : P ≤ closure (permsA n qs) := closure_le_of_words hqsQ hlq hgsRep hgq
    have hcommP : ⁅P, P⁆ ≤ P := by
      rw [commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
    have hperf : ⁅P, P⁆ = P := le_antisymm hcommP (hPQ.trans hQ)
    set xa := pts[pf.x]!
    have hxr := rep_of_validA (hvalj _ hx)
    have hxP : permOfArr n xa ∈ P := hmemP _ hx
    have hx2 : IsPGroup 2 (zpowers (permOfArr n xa)) := by
      have hpow : permOfArr n xa ^ 2 ^ pf.k = 1 := eq_of_eqA (rep_powA hxr _) rep_idA hxpow
      obtain ⟨b, -, hb'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
      exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb'])
    set rs := (pf.conjs.map fun p => conjA n pts[p]! (compA n xa xa)).toArray
    set K := closure {y | ∃ p ∈ P, y = p * permOfArr n xa ^ 2 * p⁻¹}
    have hrs : ∀ i < rs.size, ∃ g ∈ K, Rep n rs[i]! g := by
      refine rep_toArray fun p hp => ?_
      have hp' := List.all_eq_true.1 hconjs p hp
      rw [decide_eq_true_eq] at hp'
      refine ⟨_, subset_closure ⟨_, hmemP _ hp', rfl⟩, ?_⟩
      rw [sq]
      exact rep_conjA (hvalj _ hp') (rep_compA hxr hxr)
    have hrsR : ∀ i < rs.size, ∃ g ∈ closure (permsA n rs), Rep n rs[i]! g := by
      intro i hi
      obtain ⟨g, -, hr⟩ := hrs i hi
      refine ⟨g, ?_, hr⟩
      rw [← permOfArr_eq_of_rep hr]
      exact subset_closure (mem_permsA hi)
    have hRK : closure (permsA n rs) ≤ K := by
      rw [closure_le]
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨g, hg', hr⟩ := hrs i hi
      change permOfArr n rs[i]! ∈ _
      rw [permOfArr_eq_of_rep hr]
      exact hg'
    have hgen : P ≤ K := (closure_le_of_words hrsR hlr hgsRep hgr).trans hRK
    have hncent : ¬ closure (permsA n basis) ≤ centralizer (P : Set (Equiv.Perm (Fin n))) := by
      intro hc
      obtain ⟨e', he'E, he'⟩ := rep_maskA hb pf.e
      have hgr := rep_of_validA (hvalj _ hg)
      have := mem_centralizer_iff.mp (hc he'E) _ (hmemP _ hg)
      rw [(commA_iff he' hgr).2 this.symm] at hnc
      exact Bool.noConfusion hnc
    exact Or.inl (Or.inr ⟨hPW, P, hPΓ, hperf, hncent, _, hxP, hx2, hgen⟩)
  | order4 l m => exact witOKW_sound (cs := cs) hps hin hout hE h
  | twoGroup gens k => exact witOKW_sound (cs := cs) hps hin hout hE h
  | inX => exact witOKW_sound (cs := cs) hps hin hout hE h
  | small => exact witOKW_sound (cs := cs) hps hin hout hE h
  | closing s t c kc v gens comms => exact witOKW_sound (cs := cs) hps hin hout hE h

theorem census_of_censusOKW2 {ps : List ℕ} {allowPW allowInX allowU : Bool}
    {sGens : Array (Array ℕ)} {roots : Array ℕ} {nodes : Array Node} {cS : ArrCert}
    {wcs : Array (Array ArrCert)} {pfs : Array PerfW} (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ X → outX a = true)
    (h : censusOKW2 n ps inX outX allowPW allowInX allowU sGens roots nodes cS wcs pfs = true)
    {E : Subgroup (Equiv.Perm (Fin n))} (hES : E ≤ closure (permsA n sGens))
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) :
    YWitness X E ∨ (allowPW = true ∧ PWitness X E) ∨ (allowInX = true ∧ E ≤ X) ∨
      (allowU = true ∧ UWitness X E) := by
  simp only [censusOKW2, Bool.and_eq_true] at h
  obtain ⟨⟨hS, hroot⟩, hnodes⟩ := h
  set cN := nodes.map fun nd => maskCert n nd.basis
  obtain ⟨hSmem, -, hSval⟩ := enumOK_spec hps (enumOK_of_enumOKK hS)
  have hnode : ∀ i < nodes.size,
      nodeOKW2 n ps inX outX allowPW allowInX allowU cS nodes cN wcs pfs i = true :=
    fun i hi => allLt_spec hnodes hi
  have hnodeE : ∀ i < nodes.size, enumOK n nodes[i]!.basis ps cN[i]! = true := by
    intro i hi
    have := hnode i hi
    simp only [nodeOKW2, Bool.and_eq_true] at this
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
    simp only [nodeOKW2, Bool.and_eq_true, Bool.or_eq_true] at hn
    obtain ⟨⟨hEi, hwit⟩, hch⟩ := hn
    rcases witOKW2_sound hps hin hout (enumOK_of_enumOKK hEi) hwit with hm | ⟨hnm, -⟩
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
    simp only [nodeOKW2, Bool.and_eq_true] at hn
    rcases witOKW2_sound hps hin hout (enumOK_of_enumOKK hn.1.1) hn.1.2 with hm | ⟨-, hw⟩
    · exact Or.inl hm
    · exact Or.inr (hw h4)

end Soundness

end CFSG.ComponentClassification.RankTwoSporadic.Cert
