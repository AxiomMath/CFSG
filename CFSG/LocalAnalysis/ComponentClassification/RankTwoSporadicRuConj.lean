module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Exc
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open

section Tree

variable {W : Type*} [Group W]

theorem map_conj_map_conj (E : Subgroup W) (s t : W) :
    (E.map (MulAut.conj s).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      E.map (MulAut.conj (t * s)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

variable [Finite W]

theorem forall_of_conjTree {S : Subgroup W} (Wit Mono : Subgroup W → Prop)
    (hWit : ∀ E : Subgroup W, ∀ s ∈ S, Wit (E.map (MulAut.conj s).toMonoidHom) → Wit E)
    (hMono : ∀ E₀ E : Subgroup W, Mono E₀ → E₀ ≤ E → E ≤ S → IsElemAbelian 2 E →
      4 ≤ Nat.card E → Wit E)
    (node : ℕ → Subgroup W) (N : ℕ)
    (hroot : ∀ a ∈ S, a ^ 2 = 1 → a ≠ 1 → ∃ i < N, ∃ s ∈ S,
      node i = (zpowers a).map (MulAut.conj s).toMonoidHom)
    (hchild : ∀ i < N, Mono (node i) ∨ ∀ u ∈ S, u ^ 2 = 1 → u ∉ node i →
      (∀ x ∈ node i, x * u = u * x) → ∃ j < N, ∃ s ∈ S,
        node j = (node i ⊔ zpowers u).map (MulAut.conj s).toMonoidHom)
    (hwit : ∀ i < N, 4 ≤ Nat.card (node i) → Mono (node i) ∨ Wit (node i))
    {E : Subgroup W} (hES : E ≤ S) (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) : Wit E := by
  have hconj : ∀ s ∈ S, E.map (MulAut.conj s).toMonoidHom ≤ S ∧
      IsElemAbelian 2 (E.map (MulAut.conj s).toMonoidHom) ∧
      Nat.card (E.map (MulAut.conj s).toMonoidHom) = Nat.card E := by
    intro s hs
    refine ⟨?_, isElemAbelian_map hE _, card_map_of_injective (MulAut.conj s).injective⟩
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact S.mul_mem (S.mul_mem hs (hES hx)) (S.inv_mem hs)
  have key : ∀ k : ℕ, ∀ i < N, ∀ s ∈ S, node i ≤ E.map (MulAut.conj s).toMonoidHom →
      Nat.card E ≤ Nat.card (node i) + k → Wit E := by
    intro k
    induction k with
    | zero =>
      intro i hi s hs hiE hcard
      obtain ⟨hS', hE', hc'⟩ := hconj s hs
      have heq : node i = E.map (MulAut.conj s).toMonoidHom :=
        eq_of_le_of_card_ge hiE (by omega)
      rcases hwit i hi (by rw [heq, hc']; exact hE4) with hm | hw
      · exact hWit E s hs (hMono _ _ hm hiE hS' hE' (by rw [hc']; exact hE4))
      · exact hWit E s hs (heq ▸ hw)
    | succ k ih =>
      intro i hi s hs hiE hcard
      obtain ⟨hS', hE', hc'⟩ := hconj s hs
      rcases hchild i hi with hm | hch
      · exact hWit E s hs (hMono _ _ hm hiE hS' hE' (by rw [hc']; exact hE4))
      by_cases heq : node i = E.map (MulAut.conj s).toMonoidHom
      · rcases hwit i hi (by rw [heq, hc']; exact hE4) with hm | hw
        · exact hWit E s hs (hMono _ _ hm hiE hS' hE' (by rw [hc']; exact hE4))
        · exact hWit E s hs (heq ▸ hw)
      obtain ⟨u, huE, hui⟩ : ∃ u ∈ E.map (MulAut.conj s).toMonoidHom, u ∉ node i := by
        by_contra hcon
        push Not at hcon
        exact heq (le_antisymm hiE hcon)
      have hcomm : ∀ x ∈ node i, x * u = u * x := fun x hx =>
        congrArg Subtype.val (hE'.1.is_comm.comm ⟨x, hiE hx⟩ ⟨u, huE⟩)
      obtain ⟨j, hj, t, ht, hjeq⟩ := hch u (hS' huE) (hE'.2 u huE) hui hcomm
      have hjE : node j ≤ E.map (MulAut.conj (t * s)).toMonoidHom := by
        rw [hjeq, ← map_conj_map_conj]
        exact map_mono (sup_le hiE (zpowers_le.mpr huE))
      have hlt : Nat.card (node i) < Nat.card (node j) := by
        rw [hjeq, card_map_of_injective (MulAut.conj t).injective]
        refine card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hui ?_)
        exact h ▸ mem_sup_right (mem_zpowers u)
      exact ih j hj (t * s) (S.mul_mem ht hs) hjE (by omega)
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (hcon x hx)
    rw [hbot, card_bot] at hE4
    omega
  obtain ⟨i, hi, s, hs, hieq⟩ := hroot a (hES haE) (hE.2 a haE) ha1
  exact key (Nat.card E) i hi s hs (hieq ▸ map_mono (zpowers_le.mpr haE)) (by omega)

end Tree

namespace Cert

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ABGLocalTools
open CFSG.Monster.B.Fischer

@[expose] def strictlyIncreasing : List ℕ → Bool
  | a :: b :: l => decide (a < b) && strictlyIncreasing (b :: l)
  | _ => true

@[expose] def enumOKLin (n : ℕ) (gs : Array (Array ℕ)) (ps : List ℕ) (c : ArrCert) : Bool :=
  allLt gs.size (fun k => validA n gs[k]!) &&
    (decide (0 < c.pts.size) && c.pts[0]! == idA n &&
      (List.range c.pts.size).all (arrPointOK (leftA n gs) gs.size (validA n) c) &&
      strictlyIncreasing ((c.pts.toList.map (keyA n ps)).mergeSort fun a b => decide (a ≤ b)))

@[expose] def invPos (n : ℕ) (c : ArrCert) : Array ℕ :=
  ((List.range c.pts.size).filter fun p =>
    eqA n (compA n c.pts[p]! c.pts[p]!) (idA n) && !(eqA n c.pts[p]! (idA n))).toArray

@[expose] def conjRootOK (n : ℕ) (nodes : Array Node) (cN : Array ArrCert) (u s : Array ℕ)
    (j : ℕ) : Bool :=
  decide (j < nodes.size) &&
    (allLt nodes[j]!.basis.size fun k =>
      eqA n nodes[j]!.basis[k]! (conjA n s u) || eqA n nodes[j]!.basis[k]! (idA n)) &&
    memA n cN[j]! (conjA n s u)

@[expose] def conjChildOK (n : ℕ) (nodes : Array Node) (cN : Array ArrCert) (i : ℕ)
    (u s : Array ℕ) (j : ℕ) : Bool :=
  decide (j < nodes.size) &&
    (allLt nodes[j]!.basis.size fun k =>
      memA n cN[i]! (conjInvA n s nodes[j]!.basis[k]!) ||
        memA n cN[i]! (compA n u (conjInvA n s nodes[j]!.basis[k]!))) &&
    (allLt nodes[i]!.basis.size fun k => memA n cN[j]! (conjA n s nodes[i]!.basis[k]!)) &&
    memA n cN[j]! (conjA n s u)

@[expose] def conjChildrenOK (n : ℕ) (cS : ArrCert) (inv : Array ℕ) (nodes : Array Node)
    (cN : Array ArrCert) (i : ℕ) : Bool :=
  allLt inv.size fun k =>
    !(allLt nodes[i]!.basis.size fun l => commA n cS.pts[inv[k]!]! nodes[i]!.basis[l]!) ||
      memA n cN[i]! cS.pts[inv[k]!]! ||
      (decide (nodes[i]!.children[2 * k + 1]! < cS.pts.size) &&
        conjChildOK n nodes cN i cS.pts[inv[k]!]! cS.pts[nodes[i]!.children[2 * k + 1]!]!
          nodes[i]!.children[2 * k]!)

@[expose] def conjNodeOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (inX outX inW : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (cS : ArrCert) (inv : Array ℕ) (nodes : Array Node)
    (cN : Array ArrCert) (e0 : Array (Array ℕ)) (excs : List ExcRef) (i : ℕ) : Bool :=
  let w := witOK n ps fuel inX outX allowPW allowInX allowU nodes[i]!.basis cN[i]! nodes[i]!.wit
  enumOK n nodes[i]!.basis ps cN[i]! &&
    ((w && nodes[i]!.wit.isMono) ||
      ((w || excOK n ps fuel inW e0 cN excs i) && conjChildrenOK n cS inv nodes cN i))

@[expose] def conjRootsOK (n : ℕ) (cS : ArrCert) (inv : Array ℕ) (nodes : Array Node)
    (cN : Array ArrCert) (roots : Array ℕ) : Bool :=
  allLt inv.size fun k => decide (roots[2 * k + 1]! < cS.pts.size) &&
    conjRootOK n nodes cN cS.pts[inv[k]!]! cS.pts[roots[2 * k + 1]!]! roots[2 * k]!

@[expose] def conjNodesOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (inX outX inW : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (cS : ArrCert) (inv : Array ℕ) (nodes : Array Node)
    (cN : Array ArrCert) (e0 : Array (Array ℕ)) (excs : List ExcRef) : Bool :=
  allLt nodes.size
    (conjNodeOK n ps fuel inX outX inW allowPW allowInX allowU cS inv nodes cN e0 excs)

@[expose] def conjCensusOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (inX outX inW : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (sGens : Array (Array ℕ)) (roots : Array ℕ)
    (nodes : Array Node) (e0 : Array (Array ℕ)) (excs : List ExcRef) : Bool :=
  let cS := enumBfs n sGens ps fuel
  let inv := invPos n cS
  let cN := nodes.map fun nd => enumBfs n nd.basis ps fuel
  enumOKLin n sGens ps cS && conjRootsOK n cS inv nodes cN roots &&
    conjNodesOK n ps fuel inX outX inW allowPW allowInX allowU cS inv nodes cN e0 excs

section Soundness

variable {n : ℕ}

theorem pairwise_of_strictlyIncreasing :
    ∀ {l : List ℕ}, strictlyIncreasing l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_strictlyIncreasing h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

theorem enumOK_of_enumOKLin {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (h : enumOKLin n gs ps c = true) : enumOK n gs ps c = true := by
  simp only [enumOKLin, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [enumOK, arrCertOK, Bool.and_eq_true, decide_eq_true_eq]
  obtain ⟨h1, ⟨⟨h2, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, ⟨⟨h2, h3⟩, h4⟩, pairwise_of_strictlyIncreasing h5⟩

theorem mem_invPos {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (hc : enumOK n gs ps c = true) {u : Equiv.Perm (Fin n)}
    (hu : u ∈ closure (permsA n gs)) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∃ k < (invPos n c).size, (invPos n c)[k]! < c.pts.size ∧
      permOfArr n c.pts[(invPos n c)[k]!]! = u := by
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps hc
  obtain ⟨p, hp, rfl⟩ := (hmem u).1 hu
  have hr := rep_of_validA (hval p hp)
  have hpI : p ∈ (List.range c.pts.size).filter fun p =>
      eqA n (compA n c.pts[p]! c.pts[p]!) (idA n) && !(eqA n c.pts[p]! (idA n)) := by
    rw [List.mem_filter, List.mem_range]
    refine ⟨hp, ?_⟩
    rw [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨(eqA_iff (rep_compA hr hr) rep_idA).2 (by rw [← sq]; exact hu2), ?_⟩
    cases h : eqA n c.pts[p]! (idA n)
    · rfl
    · exact absurd (eq_of_eqA hr rep_idA h) hu1
  obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hpI
  refine ⟨k, by simpa [invPos] using hk, ?_, ?_⟩
  · rw [invPos, getElem!_pos _ k (by simpa using hk), List.getElem_toArray, hkp]
    exact hp
  · rw [invPos, getElem!_pos _ k (by simpa using hk), List.getElem_toArray, hkp]

variable {X : Subgroup (Equiv.Perm (Fin n))} {inX outX : Array ℕ → Bool}

theorem witW_of_map_conj {allowPW allowInX allowU : Bool} {E : Subgroup (Equiv.Perm (Fin n))}
    {s : Equiv.Perm (Fin n)} (hs : X.map (MulAut.conj s).toMonoidHom = X)
    (h : WitW X allowPW allowInX allowU (E.map (MulAut.conj s).toMonoidHom)) :
    WitW X allowPW allowInX allowU E := by
  set ι := (MulAut.conj s).toMonoidHom
  have hι : Function.Injective ι := (MulAut.conj s).injective
  rw [← hs] at h
  rcases h with h | ⟨h1, h⟩ | ⟨h1, h⟩ | ⟨h1, h⟩
  · exact Or.inl ((yWitness_map_iff ι hι X E).mp h)
  · exact Or.inr (Or.inl ⟨h1, (pWitness_map_iff ι hι X E).mp h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, (map_le_map_iff_of_injective hι).mp h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, (uWitness_map_iff ι hι X E).mp h⟩))

theorem census_of_conjCensusOK {ps : List ℕ} {fuel : ℕ} {allowPW allowInX allowU : Bool}
    {sGens : Array (Array ℕ)} {roots : Array ℕ} {nodes : Array Node} {e0 : Array (Array ℕ)}
    {excs : List ExcRef} {Wg : Subgroup (Equiv.Perm (Fin n))} {inW : Array ℕ → Bool}
    (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ X → outX a = true)
    (hinW : ∀ a, validA n a = true → inW a = true → permOfArr n a ∈ Wg)
    (hSW : closure (permsA n sGens) ≤ Wg)
    (hSX : ∀ s ∈ closure (permsA n sGens), X.map (MulAut.conj s).toMonoidHom = X)
    (h : conjCensusOK n ps fuel inX outX inW allowPW allowInX allowU sGens roots nodes e0 excs =
      true)
    {E : Subgroup (Equiv.Perm (Fin n))} (hES : E ≤ closure (permsA n sGens))
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) :
    WitW X allowPW allowInX allowU E ∨
      ∃ w ∈ Wg, E = (closure (permsA n e0)).map (MulAut.conj w).toMonoidHom := by
  simp only [conjCensusOK, conjRootsOK, conjNodesOK, Bool.and_eq_true] at h
  obtain ⟨⟨hS, hroot⟩, hnodes⟩ := h
  replace hS := enumOK_of_enumOKLin hS
  set cS := enumBfs n sGens ps fuel
  set inv := invPos n cS
  set cN := nodes.map fun nd => enumBfs n nd.basis ps fuel
  obtain ⟨hSmem, -, hSval⟩ := enumOK_spec hps hS
  have hptS : ∀ p < cS.pts.size, permOfArr n cS.pts[p]! ∈ closure (permsA n sGens) :=
    fun p hp => (hSmem _).2 ⟨p, hp, rfl⟩
  have hnode : ∀ i < nodes.size,
      conjNodeOK n ps fuel inX outX inW allowPW allowInX allowU cS inv nodes cN e0 excs i =
        true := fun i hi => allLt_spec hnodes hi
  have hnodeE : ∀ i < nodes.size, enumOK n nodes[i]!.basis ps cN[i]! = true := by
    intro i hi
    have := hnode i hi
    simp only [conjNodeOK, Bool.and_eq_true] at this
    exact this.1
  have hbasis : ∀ i < nodes.size, ∀ k < nodes[i]!.basis.size,
      validA n nodes[i]!.basis[k]! = true := fun i hi k hk => enumOK_gens_valid (hnodeE i hi) hk
  have hmemN : ∀ i < nodes.size, ∀ {a : Array ℕ} {g : Equiv.Perm (Fin n)}, Rep n a g →
      memA n cN[i]! a = true → g ∈ nodeSub n nodes i :=
    fun i hi a g ha hm => enumOK_mem_of_any hps (hnodeE i hi) ha hm
  have hbasisN : ∀ i < nodes.size, ∀ k < nodes[i]!.basis.size,
      permOfArr n nodes[i]!.basis[k]! ∈ nodeSub n nodes i :=
    fun i _ k hk => subset_closure (mem_permsA hk)
  refine forall_of_conjTree (S := closure (permsA n sGens))
    (fun E => WitW X allowPW allowInX allowU E ∨
      ∃ w ∈ Wg, E = (closure (permsA n e0)).map (MulAut.conj w).toMonoidHom)
    (MonoW X allowPW) ?_ (fun E₀ E hm hle _ _ _ => Or.inl (witW_of_monoW allowInX allowU hm hle))
    (nodeSub n nodes) nodes.size ?_ ?_ ?_ hES hE hE4
  ·
    intro E s hs hw
    rcases hw with hw | ⟨w, hw, heq⟩
    · exact Or.inl (witW_of_map_conj (hSX s hs) hw)
    · refine Or.inr ⟨s⁻¹ * w, Wg.mul_mem (Wg.inv_mem (hSW hs)) hw, ?_⟩
      rw [← map_conj_map_conj, ← heq, map_conj_map_conj, inv_mul_cancel]
      ext x
      simp
  ·
    intro a ha ha2 ha1
    obtain ⟨k, hk, hkp, rfl⟩ := mem_invPos hps hS ha ha2 ha1
    have hr := rep_of_validA (hSval _ hkp)
    have hrk := allLt_spec hroot hk
    simp only [conjRootOK, Bool.and_eq_true, decide_eq_true_eq] at hrk
    obtain ⟨hg, ⟨hj, hall⟩, hu⟩ := hrk
    have hgv := hSval _ hg
    have hsr := rep_conjA hgv hr
    refine ⟨_, hj, _, hptS _ hg, le_antisymm ?_ ?_⟩
    · rw [nodeSub, closure_le]
      rintro _ ⟨l, hl, rfl⟩
      dsimp only
      have hbl := rep_of_validA (hbasis _ hj l hl)
      have h2 := allLt_spec hall hl
      simp only [Bool.or_eq_true] at h2
      rw [SetLike.mem_coe, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases h2 with h2 | h2
      · rw [eq_of_eqA hbl hsr h2]
        exact mem_zpowers _
      · rw [eq_of_eqA hbl rep_idA h2]
        exact one_mem _
    · rw [MonoidHom.map_zpowers, zpowers_le, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hmemN _ hj hsr hu
  ·
    intro i hi
    have hn := hnode i hi
    simp only [conjNodeOK, Bool.and_eq_true, Bool.or_eq_true] at hn
    obtain ⟨hEi, hw | ⟨-, hch⟩⟩ := hn
    · rcases witOK_sound hps hin hout hEi hw.1 with hm | ⟨hnm, -⟩
      · exact Or.inl hm
      · rw [hnm] at hw
        exact Bool.noConfusion hw.2
    refine Or.inr fun u hu hu2 hui hcomm => ?_
    have hu1 : u ≠ 1 := fun h1 => hui (h1 ▸ one_mem _)
    obtain ⟨k, hk, hkp, rfl⟩ := mem_invPos hps hS hu hu2 hu1
    have hr := rep_of_validA (hSval _ hkp)
    have hck := allLt_spec hch hk
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq] at hck
    rcases hck with (h1 | h1) | ⟨hg, h1⟩
    · have : (allLt nodes[i]!.basis.size fun l =>
          commA n cS.pts[inv[k]!]! nodes[i]!.basis[l]!) = true := by
        rw [allLt_iff]
        intro l hl
        have hbl := rep_of_validA (hbasis i hi l hl)
        exact (commA_iff hr hbl).2 (hcomm _ (hbasisN i hi l hl)).symm
      rw [this] at h1
      exact Bool.noConfusion h1
    · exact absurd (hmemN i hi hr h1) hui
    simp only [conjChildOK, Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨⟨⟨hj, hjb⟩, hib⟩, hu'⟩ := h1
    have hgv := hSval _ hg
    set s := permOfArr n cS.pts[nodes[i]!.children[2 * k + 1]!]!
    refine ⟨_, hj, s, hptS _ hg, le_antisymm ?_ ?_⟩
    · rw [nodeSub, closure_le]
      rintro _ ⟨l, hl, rfl⟩
      dsimp only
      have hbl := rep_of_validA (hbasis _ hj l hl)
      have hci := rep_conjInvA hgv hbl
      have h2 := allLt_spec hjb hl
      simp only [Bool.or_eq_true] at h2
      have hmem : s⁻¹ * permOfArr n nodes[nodes[i]!.children[2 * k]!]!.basis[l]! * s ∈
          nodeSub n nodes i ⊔ zpowers (permOfArr n cS.pts[inv[k]!]!) := by
        rcases h2 with h2 | h2
        · exact mem_sup_left (hmemN i hi hci h2)
        · have hm := hmemN i hi (rep_compA hr hci) h2
          rw [show s⁻¹ * permOfArr n nodes[nodes[i]!.children[2 * k]!]!.basis[l]! * s =
              (permOfArr n cS.pts[inv[k]!]!)⁻¹ * (permOfArr n cS.pts[inv[k]!]! *
                (s⁻¹ * permOfArr n nodes[nodes[i]!.children[2 * k]!]!.basis[l]! * s)) by group]
          exact mul_mem (mem_sup_right (inv_mem (mem_zpowers _))) (mem_sup_left hm)
      refine ⟨_, hmem, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    · rw [map_le_iff_le_comap]
      refine sup_le ?_ ?_
      · rw [nodeSub, closure_le]
        rintro _ ⟨l, hl, rfl⟩
        dsimp only
        have hbl := rep_of_validA (hbasis i hi l hl)
        rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hmemN _ hj (rep_conjA hgv hbl) (allLt_spec hib hl)
      · rw [zpowers_le, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hmemN _ hj (rep_conjA hgv hr) hu'
  ·
    intro i hi h4
    have hn := hnode i hi
    simp only [conjNodeOK, Bool.and_eq_true, Bool.or_eq_true] at hn
    obtain ⟨hEi, ⟨hw, -⟩ | ⟨hw | hx, -⟩⟩ := hn
    · rcases witOK_sound hps hin hout hEi hw with hm | ⟨-, hw'⟩
      · exact Or.inl hm
      · exact Or.inr (Or.inl (hw' h4))
    · rcases witOK_sound hps hin hout hEi hw with hm | ⟨-, hw'⟩
      · exact Or.inl hm
      · exact Or.inr (Or.inl (hw' h4))
    · exact Or.inr (Or.inr (eq_map_of_excOK hps hinW hi hEi hx))

end Soundness

section Pair

variable {n : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))} {testP : Array ℕ → Bool} {ps : List ℕ}
  {fuel : ℕ} {allowPW allowInX : Bool} {sGens : Array (Array ℕ)} {roots : Array ℕ}
  {nodes : Array Node} {e0 : Array (Array ℕ)} {excs : List ExcRef} {u : Array ℕ}
  {uR : Equiv.Perm (Fin n)} {k m : ℕ}

theorem witness_pair_conj_of_check (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : conjCensusOK n ps fuel testP testP (fun a => testP a || testP (compA n u a)) allowPW
      allowInX false sGens roots nodes e0 excs = true)
    (hgen : (allLt sGens.size fun j => testP sGens[j]! || testP (compA n u sGens[j]!)) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    ∃ S : Subgroup ↥R, IsSylowOf 2 S ⊤ ∧ ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E →
      YWitness (P.subgroupOf R) E ∨ (allowPW = true ∧ PWitness (P.subgroupOf R) E) ∨
        (allowInX = true ∧ E ≤ P.subgroupOf R) ∨ ExcClass R (closure (permsA n e0)) E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (P.subgroupOf R).map R.subtype = P := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hPR]
  have hR : ∀ a, validA n a = true → (testP a || testP (compA n u a)) = true →
      permOfArr n a ∈ R := by
    intro a hv h
    have hr := rep_of_validA hv
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact hPR ((htest _ _ hr).1 h)
    · have h' := (htest _ _ (rep_compA hu hr)).1 h
      have : permOfArr n a = uR⁻¹ * (uR * permOfArr n a) := by group
      rw [this]
      exact mul_mem (inv_mem huR) (hPR h')
  have hc' := hc
  simp only [conjCensusOK, Bool.and_eq_true] at hc'
  obtain ⟨⟨hS, -⟩, -⟩ := hc'
  replace hS := enumOK_of_enumOKLin hS
  set S' := closure (permsA n sGens)
  have hS'R : S' ≤ R := by
    rw [closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact hR _ (enumOK_gens_valid hS hj) (allLt_spec hgen hj)
  have hS'le : S' ≤ R.subtype.range := by rwa [range_subtype]
  have hconjP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P := by
    intro r hr x hx
    have := hN.conj_mem ⟨x, hPR hx⟩ (by rwa [mem_subgroupOf]) ⟨r, hr⟩
    rwa [mem_subgroupOf] at this
  have hSX : ∀ s ∈ S', ((P.subgroupOf R).map R.subtype).map (MulAut.conj s).toMonoidHom =
      (P.subgroupOf R).map R.subtype := by
    intro s hs
    rw [hmap]
    refine le_antisymm ?_ fun x hx => ⟨s⁻¹ * x * s, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hconjP s (hS'R hs) x hx
    · have := hconjP s⁻¹ (R.inv_mem (hS'R hs)) x hx
      rwa [inv_inv] at this
    · simp [MulAut.conj_apply, mul_assoc]
  obtain ⟨-, hS'card, -⟩ := enumOK_spec hps hS
  set S := S'.comap R.subtype
  have hSmap : S.map R.subtype = S' := map_comap_eq_self hS'le
  have hScard : Nat.card S = 2 ^ k := by
    rw [← card_map_of_injective R.subtype_injective, hSmap, hS'card, hsize]
  refine ⟨S, ?_, fun E hES hE hE4 => ?_⟩
  · rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card hScard, fun h2 => ?_⟩
    have h1 := S.card_mul_index
    rw [hScard, hcard] at h1
    have hidx : S.index = m := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) k) h1
    rw [hidx] at h2
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)
  · have hin : ∀ a, validA n a = true → testP a = true →
        permOfArr n a ∈ (P.subgroupOf R).map R.subtype := fun a hv ha => by
      rw [hmap]
      exact (htest _ _ (rep_of_validA hv)).1 ha
    have hout : ∀ a, validA n a = true → permOfArr n a ∈ (P.subgroupOf R).map R.subtype →
        testP a = true := fun a hv ha => by
      rw [hmap] at ha
      exact (htest _ _ (rep_of_validA hv)).2 ha
    have hES' : E.map R.subtype ≤ S' := hSmap ▸ map_mono hES
    have hw := census_of_conjCensusOK hps hin hout hR hS'R hSX hc hES'
      (isElemAbelian_map hE R.subtype) (by rwa [card_map_of_injective R.subtype_injective])
    rcases hw with (hw | hw | hw | ⟨h, -⟩) | ⟨w, hwR, heq⟩
    · exact Or.inl ((yWitness_map_iff _ R.subtype_injective _ _).mp hw)
    · exact Or.inr (Or.inl ⟨hw.1, (pWitness_map_iff _ R.subtype_injective _ _).mp hw.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hw.1, (map_le_map_iff_of_injective R.subtype_injective).mp
        hw.2⟩))
    · exact absurd h (by decide)
    · exact Or.inr (Or.inr (Or.inr ⟨w, hwR, heq⟩))

theorem yCensus17Exc_pair_conj_of_check (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : conjCensusOK n ps fuel testP testP (fun a => testP a || testP (compA n u a)) true
      false false sGens roots nodes e0 excs = true)
    (hgen : (allLt sGens.size fun j => testP sGens[j]! || testP (compA n u sGens[j]!)) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    YCensus17 (P.subgroupOf R) (ExcClass R (closure (permsA n e0))) := by
  obtain ⟨S, hS, hw⟩ := witness_pair_conj_of_check hPR hN hps htest hu huR hc hgen hsize hcard hm
  refine yCensus17_of_le_sylow hN hS (fun E w h => excClass_of_map_conj h)
    fun E hES hE hE4 hnot => ?_
  rcases hw E hES hE hE4 with h | ⟨-, h⟩ | ⟨h, -⟩ | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (by decide)
  · exact absurd h hnot

theorem yCensusExc_pair_conj_of_check (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : conjCensusOK n ps fuel testP testP (fun a => testP a || testP (compA n u a)) false
      false false sGens roots nodes e0 excs = true)
    (hgen : (allLt sGens.size fun j => testP sGens[j]! || testP (compA n u sGens[j]!)) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    YCensus (P.subgroupOf R) (ExcClass R (closure (permsA n e0))) := by
  obtain ⟨S, hS, hw⟩ := witness_pair_conj_of_check hPR hN hps htest hu huR hc hgen hsize hcard hm
  refine yCensus_of_le_sylow hN hS (fun E w h => excClass_of_map_conj h)
    fun E hES hE hE4 hnot => ?_
  rcases hw E hES hE hE4 with h | ⟨h, -⟩ | ⟨h, -⟩ | h
  · exact h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h hnot

theorem yCensusII_pair_conj_of_check (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : conjCensusOK n ps fuel testP testP (fun a => testP a || testP (compA n u a)) false
      true false sGens roots nodes #[] excs = true)
    (hgen : (allLt sGens.size fun j => testP sGens[j]! || testP (compA n u sGens[j]!)) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    YCensus (P.subgroupOf R) (· ≤ P.subgroupOf R) := by
  obtain ⟨S, hS, hw⟩ := witness_pair_conj_of_check hPR hN hps htest hu huR hc hgen hsize hcard hm
  refine yCensus_of_le_sylow hN hS (fun E w h => ?_) fun E hES hE hE4 hnot => ?_
  · have := map_mono (f := (MulAut.conj w⁻¹).toMonoidHom) h
    rwa [map_conj_map_conj, inv_mul_cancel, map_conj_eq_of_normal hN,
      show (MulAut.conj (1 : ↥R)).toMonoidHom = MonoidHom.id ↥R by ext; simp, map_id] at this
  rcases hw E hES hE hE4 with h | ⟨h, -⟩ | ⟨-, h⟩ | ⟨w, -, heq⟩
  · exact h
  · exact absurd h (by decide)
  · exact absurd h hnot
  · exfalso
    have hbot : closure (permsA n (#[] : Array (Array ℕ))) = ⊥ := by
      rw [closure_eq_bot_iff]
      rintro _ ⟨j, hj, -⟩
      exact absurd hj (by simp)
    rw [hbot, Subgroup.map_bot] at heq
    have hEbot : E = ⊥ := by
      rw [← map_eq_bot_iff_of_injective E R.subtype_injective, heq]
    rw [hEbot, card_bot] at hE4
    omega

end Pair

end Cert

end CFSG.ComponentClassification.RankTwoSporadic
