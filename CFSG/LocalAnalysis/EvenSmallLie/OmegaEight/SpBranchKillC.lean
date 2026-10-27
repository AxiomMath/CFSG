module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillG
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKill

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

section Masks

@[expose] def maskOf (L : List ℕ) : ℕ := L.foldl (fun a x => a ||| 2 ^ x) 0

theorem testBit_foldl_or (L : List ℕ) (a x : ℕ) :
    (L.foldl (fun a y => a ||| 2 ^ y) a).testBit x = true ↔ a.testBit x = true ∨ x ∈ L := by
  induction L generalizing a with
  | nil => simp
  | cons y L ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h | rfl) | h)
      exacts [Or.inl h, Or.inr (Or.inl rfl), Or.inr (Or.inr h)]
    · rintro (h | rfl | h)
      exacts [Or.inl (Or.inl h), Or.inl (Or.inr rfl), Or.inr h]

theorem testBit_maskOf (L : List ℕ) (x : ℕ) : (maskOf L).testBit x = true ↔ x ∈ L := by
  rw [maskOf, testBit_foldl_or]
  simp

@[expose] def nodupStep (st : Bool × ℕ) (x : ℕ) : Bool × ℕ :=
  (st.1 && !st.2.testBit x, st.2 ||| 2 ^ x)

@[expose] def nodupM (L : List ℕ) : Bool := (L.foldl nodupStep (true, 0)).1

theorem nodup_of_foldl (L : List ℕ) (b : Bool) (M : ℕ)
    (h : (L.foldl nodupStep (b, M)).1 = true) :
    b = true ∧ (∀ x ∈ L, M.testBit x = false) ∧ L.Nodup := by
  induction L generalizing b M with
  | nil => exact ⟨h, by simp, List.nodup_nil⟩
  | cons y L ih =>
    rw [List.foldl_cons, nodupStep] at h
    obtain ⟨h1, h2, h3⟩ := ih _ _ h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at h1
    refine ⟨h1.1, fun x hx => ?_, List.nodup_cons.2 ⟨fun hy => ?_, h3⟩⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact h1.2
      · have := h2 x hx
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1
    · have := h2 y hy
      rw [Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true] at this
      exact Bool.noConfusion this

theorem nodup_of_nodupM {L : List ℕ} (h : nodupM L = true) : L.Nodup :=
  (nodup_of_foldl L true 0 h).2.2

end Masks

section Data

variable (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (gens : List ℕ) (N : ℕ)

@[expose] def recMStep (st : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) :
    List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ :=
  match st.2.1 with
  | [] => st
  | (o, w) :: q =>
    gens.foldl (fun acc g =>
      let v := cconj mul inv g o
      if acc.2.2.testBit v then acc
      else ((v, mul g w) :: acc.1, acc.2.1 ++ [(v, mul g w)], acc.2.2 ||| 2 ^ v))
      (st.1, q, st.2.2)

@[expose] def recM (u : ℕ) : List (ℕ × ℕ) :=
  ((List.range 130).foldl (fun st _ => recMStep mul inv gens st) ([(u, 0)], [(u, 0)], 2 ^ u)).1

@[expose] def orbOKM (u : ℕ) (O : List (ℕ × ℕ)) : Bool :=
  (O.all fun p => decide (p.2 < N) && p.1 == cconj mul inv p.2 u) && nodupM (O.map Prod.fst)

@[expose] def orbClosedM (u : ℕ) (O : List (ℕ × ℕ)) : Bool :=
  (maskOf (O.map Prod.fst)).testBit u &&
    O.all fun p => gens.all fun g => (maskOf (O.map Prod.fst)).testBit (cconj mul inv g p.1)

theorem orbOK_of_M {u : ℕ} {O : List (ℕ × ℕ)} (h : orbOKM mul inv N u O = true) :
    orbOK mul inv N u O = true := by
  unfold orbOKM at h
  unfold orbOK
  rw [Bool.and_eq_true] at h ⊢
  exact ⟨h.1, decide_eq_true (nodup_of_nodupM h.2)⟩

theorem orbClosed_of_M {u : ℕ} {O : List (ℕ × ℕ)} (h : orbClosedM mul inv gens u O = true) :
    orbClosed mul inv gens u O = true := by
  unfold orbClosedM at h
  unfold orbClosed
  simp only [Bool.and_eq_true, List.all_eq_true, testBit_maskOf, List.contains_iff_mem] at h ⊢
  exact h

@[expose] def kClassOK (C : List (ℕ × ℕ)) : Bool :=
  ((C.zip C.tail).all fun p => decide (p.1.1 < p.2.1)) &&
    (C.all fun r => decide (r.1 < N) && mul r.1 r.1 == 0 && r.1 != 0 &&
      orbOKM mul inv N r.1 (recM mul inv gens r.1) &&
      orbClosedM mul inv gens r.1 (recM mul inv gens r.1) &&
      (recM mul inv gens r.1).length == r.2 &&
      (recM mul inv gens r.1).all fun p => decide (r.1 ≤ p.1)) &&
    (C.map Prod.snd).sum == (kInv mul N).length

@[expose] def kRepsC (C : List (ℕ × ℕ)) (m : ℕ) : List ℕ :=
  (C.filter fun r => r.2 == m).map Prod.fst

@[expose] def killAtCF (I R : List ℕ) (cO : ℕ → ℕ) (m : ℕ) (χ : Array Bool) (n5 : Bool) (t : ℕ)
    (ti : ℕ × ℕ) : Bool :=
  orbClosed mul inv gens t (kRec mul inv gens m t) && (kRec mul inv gens m t).length == m &&
    orbOK mul inv N t (kRec mul inv gens m t) &&
    kCount mul I t == ti.1 && cO t == ti.2 && χ[t]! &&
    R.all fun r => !(kCount mul I r == ti.1) ||
      (if n5 then (kRec mul inv gens m t).any fun p => p.1 == r else χ[r]!) ||
      !(cO r == ti.2)

@[expose] def killAtC (I O R : List ℕ) (m : ℕ) (χ : Array Bool) (n5 : Bool) (t : ℕ)
    (ti : ℕ × ℕ) : Bool :=
  killAtCF mul inv gens N I R (kCount mul O) m χ n5 t ti

theorem killAtC_eq (I O R : List ℕ) (m : ℕ) (χ : Array Bool) (n5 : Bool) (t : ℕ)
    (ti : ℕ × ℕ) : killAtC mul inv gens N I O R m χ n5 t ti = killAt mul inv gens N I O R m χ n5 t ti := by
  unfold killAtC killAtCF killAt kX
  congr 1
  cases n5 <;>
  · simp only [Bool.false_eq_true, ite_false, ite_true, List.all_filter]
    congr 1
    funext r
    cases kCount mul I r == ti.1 <;> cases kCount mul O r == ti.2 <;> simp

@[expose] def queriedIn (I R : List ℕ) (m : ℕ) (χ : Array Bool) (n5 : Bool) (t : ℕ)
    (ti : ℕ × ℕ) (U : List ℕ) : Bool :=
  U.contains t && R.all fun r => !(kCount mul I r == ti.1) ||
    (if n5 then (kRec mul inv gens m t).any fun p => p.1 == r else χ[r]!) || U.contains r

theorem killAtCF_congr (I R : List ℕ) (cO cO' : ℕ → ℕ) (m : ℕ) (χ : Array Bool) (n5 : Bool)
    (t : ℕ) (ti : ℕ × ℕ) (U : List ℕ) (hq : queriedIn mul inv gens I R m χ n5 t ti U = true)
    (hU : ∀ u ∈ U, cO u = cO' u) :
    killAtCF mul inv gens N I R cO m χ n5 t ti = killAtCF mul inv gens N I R cO' m χ n5 t ti := by
  unfold queriedIn at hq
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hq
  unfold killAtCF
  rw [hU t hq.1]
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall₂_congr fun r hr => ?_
  rcases hq.2 r hr with (h | h) | h
  · simp [h]
  · simp [h]
  · rw [hU r h]

@[expose] def isOrd4 (c : ℕ) : Bool := mul c c != 0 && mul (mul c c) (mul c c) == 0

@[expose] def ord4Step (acc : List (ℕ × ℕ)) (c : ℕ) : List (ℕ × ℕ) :=
  if isOrd4 mul c then acc.map fun p => (p.1, if mul c p.1 == mul p.1 c then p.2 + 1 else p.2)
  else acc

theorem foldl_ord4Step (L : List ℕ) (acc : List (ℕ × ℕ)) :
    L.foldl (ord4Step mul) acc = acc.map fun p =>
      (p.1, p.2 + (L.filter fun c => isOrd4 mul c && mul c p.1 == mul p.1 c).length) := by
  induction L generalizing acc with
  | nil => simp
  | cons c L ih =>
    rw [List.foldl_cons, ih, ord4Step]
    split
    · next h =>
      rw [List.map_map]
      refine List.map_congr_left fun p _ => ?_
      simp only [Function.comp_apply, List.filter_cons, h, Bool.true_and]
      split <;> simp_all
      omega
    · next h =>
      refine List.map_congr_left fun p _ => ?_
      simp [h]

theorem kCount_kOrd4_eq (u : ℕ) :
    kCount mul (kOrd4 mul N) u =
      ((List.range N).filter fun c => isOrd4 mul c && mul c u == mul u c).length := by
  unfold kCount kOrd4 isOrd4
  rw [List.filter_filter]
  congr 2
  funext c
  exact Bool.and_comm _ _

@[expose] def groupKillC (m : ℕ) (n5 : Bool) (b : List Bool) (χ : Array Bool)
    (ts : List (ℕ × (ℕ × ℕ))) (C : List (ℕ × ℕ)) : Bool :=
  let I := kInv mul N
  let O := kOrd4 mul N
  let R := kRepsC C m
  invOK mul inv N && kClassOK mul inv gens N C && chiOK mul gens N b χ &&
    ts.all fun p => killAtC mul inv gens N I O R m χ n5 p.1 p.2

end Data

section Spec

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul) {inv : ℕ → ℕ}
  {gens : List ℕ}

theorem chain_of_zip_tail {C : List (ℕ × ℕ)} (h : ∀ p ∈ C.zip C.tail, p.1.1 < p.2.1) :
    C.IsChain (fun a b => a.1 < b.1) := by
  induction C with
  | nil => exact List.isChain_nil
  | cons a l ih =>
    refine List.isChain_cons.2 ⟨fun y hy => ?_, ih fun p hp => h p ?_⟩
    · cases l with
      | nil => simp at hy
      | cons b l =>
        obtain rfl : b = y := by simpa using hy
        exact h (a, b) (by simp)
    · cases l with
      | nil => simp at hp
      | cons b l =>
        simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
        exact Or.inr hp

theorem classOK_parts {C : List (ℕ × ℕ)} (hC : kClassOK mul inv gens N C = true) :
    (C.map Prod.fst).Nodup ∧ (∀ r ∈ C, r.1 < N ∧ mul r.1 r.1 = 0 ∧ r.1 ≠ 0 ∧
      orbOK mul inv N r.1 (recM mul inv gens r.1) = true ∧
      orbClosed mul inv gens r.1 (recM mul inv gens r.1) = true ∧
      (recM mul inv gens r.1).length = r.2 ∧
      ∀ p ∈ recM mul inv gens r.1, r.1 ≤ p.1) ∧
    (C.map Prod.snd).sum = (kInv mul N).length := by
  unfold kClassOK at hC
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
    ne_eq] at hC
  obtain ⟨⟨hz, hr⟩, hs⟩ := hC
  have hpw : C.Pairwise fun a b => a.1 < b.1 :=
    List.isChain_iff_pairwise.1 (chain_of_zip_tail hz)
  refine ⟨List.pairwise_map.2 (hpw.imp ne_of_lt), fun r h => ?_, hs⟩
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hr r h
  exact ⟨h1, h2, h3, orbOK_of_M mul inv N h4, orbClosed_of_M mul inv gens h5, h6, h7⟩

variable (h0 : mul 0 0 = 0) (hinv : invOK mul inv N = true) (hgens : ∀ g ∈ gens, g < N)
  (hG : Gen mul gens N)
include Φ h0 hinv hgens hG

theorem like_rep_C {m : ℕ} {C : List (ℕ × ℕ)} (hC : kClassOK mul inv gens N C = true) {t u : H}
    (htO : orbOK mul inv N (Φ.f t) (kRec mul inv gens m (Φ.f t)) = true)
    (htC : orbClosed mul inv gens (Φ.f t) (kRec mul inv gens m (Φ.f t)) = true)
    (htl : (kRec mul inv gens m (Φ.f t)).length = m) (hm : 1 < m) {ti : ℕ × ℕ}
    (hti1 : kCount mul (kInv mul N) (Φ.f t) = ti.1) (hti2 : kCount mul (kOrd4 mul N) (Φ.f t) = ti.2)
    (hu : ALike t u) :
    ∃ r ∈ kX mul (kInv mul N) (kOrd4 mul N) (kRepsC C m) ti,
      ∃ g : H, g * Φ.g r * g⁻¹ = u := by
  classical
  have hfin := Φ.finite
  obtain ⟨hnd, hrecC, hsumC⟩ := classOK_parts hC
  obtain ⟨D, hD⟩ : ∃ D : List ℕ, D = C.map Prod.fst := ⟨_, rfl⟩
  rw [← hD] at hnd
  have hrec : ∀ r ∈ D, r < N ∧ mul r r = 0 ∧ r ≠ 0 ∧
      orbOK mul inv N r (recM mul inv gens r) = true ∧
      orbClosed mul inv gens r (recM mul inv gens r) = true ∧
      ∀ p ∈ recM mul inv gens r, r ≤ p.1 := by
    intro r hr
    rw [hD] at hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
    obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := hrecC c hc
    exact ⟨h1, h2, h3, h4, h5, h7⟩
  have hsum : (D.map fun r => (recM mul inv gens r).length).sum = (kInv mul N).length := by
    rw [hD, List.map_map, ← hsumC]
    refine congrArg List.sum (List.map_congr_left fun c hc => ?_)
    rw [Function.comp_apply]
    exact (hrecC c hc).2.2.2.2.2.1
  have hnt : (MulAction.orbit (ConjAct H) t).ncard = m := by
    rw [Φ.ncard_eq h0 hinv hgens hG htO htC, htl]
  have hnu : (MulAction.orbit (ConjAct H) u).ncard = m := by
    have e1 := card_centralizer_mul_ncard u
    have e2 := card_centralizer_mul_ncard t
    rw [hu.2.1, ← e2, hnt] at e1
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Subgroup.centralizer ({t} : Set H))) e1
  have hu1 : u ≠ 1 := by
    rintro rfl
    have : (MulAction.orbit (ConjAct H) (1 : H)).ncard = 1 := by
      rw [show MulAction.orbit (ConjAct H) (1 : H) = {1} by
        ext y; rw [mem_orbit_iff_conj]; simp [eq_comm]]
      exact Set.ncard_singleton 1
    omega
  have hmem : Φ.f u ∈ kInv mul N := (mem_kInv).2 ⟨Φ.lt u, (f_mul_self_eq_zero Φ h0 u).2 hu.1,
    fun h => hu1 ((f_eq_zero Φ h0 u).1 h)⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Finset ℕ,
      A = fun r => ((recM mul inv gens r).map Prod.fst).toFinset := ⟨_, rfl⟩
  have hAmem : ∀ r ∈ D, ∀ x : H, x ∈ MulAction.orbit (ConjAct H) (Φ.g r) ↔ Φ.f x ∈ A r := by
    intro r hr x
    obtain ⟨hrl, -, -, hO, hCl, -⟩ := hrec r hr
    rw [hA, List.mem_toFinset]
    exact Φ.mem_orbit_iff h0 hinv hgens hG (O := recM mul inv gens r)
      ((Φ.f_g hrl).symm ▸ hO) ((Φ.f_g hrl).symm ▸ hCl) x
  have hAlt : ∀ r ∈ D, ∀ y ∈ A r, y < N := by
    intro r hr y hy
    obtain ⟨hrl, -, -, hO, -, -⟩ := hrec r hr
    rw [hA, List.mem_toFinset] at hy
    obtain ⟨g, hg⟩ := Φ.exists_conj_of_orbOK h0 hinv (u := Φ.g r)
      (O := recM mul inv gens r) ((Φ.f_g hrl).symm ▸ hO) hy
    rw [← hg]
    exact Φ.lt _
  have hAsub : ∀ r ∈ D, A r ⊆ (kInv mul N).toFinset := by
    intro r hr y hy
    obtain ⟨hrl, hr2, hr0, -, -, -⟩ := hrec r hr
    have hyl := hAlt r hr y hy
    have hyo := (hAmem r hr (Φ.g y)).2 (by rwa [Φ.f_g hyl])
    obtain ⟨g, hg⟩ := mem_orbit_iff_conj.1 hyo
    have hgr2 : Φ.g r * Φ.g r = 1 := (f_mul_self_eq_zero Φ h0 _).1 (by rwa [Φ.f_g hrl])
    have hgr1 : Φ.g r ≠ 1 := fun h => hr0 (by rw [← Φ.f_g hrl, h]; exact Φ.f_one h0)
    rw [List.mem_toFinset, mem_kInv]
    refine ⟨hyl, ?_, fun h => ?_⟩
    · rw [← Φ.f_g hyl, ← hg]
      refine (f_mul_self_eq_zero Φ h0 _).2 ?_
      calc g * Φ.g r * g⁻¹ * (g * Φ.g r * g⁻¹) = g * (Φ.g r * Φ.g r) * g⁻¹ := by group
        _ = 1 := by rw [hgr2]; group
    · have h1 : Φ.g y = 1 := by rw [h, ← Φ.f_one h0, Φ.g_f]
      rw [h1] at hg
      refine hgr1 ?_
      have e : Φ.g r = g⁻¹ * (g * Φ.g r * g⁻¹) * g := by group
      rw [e, hg]
      group
  have hdisj : ∀ r ∈ D, ∀ s ∈ D, r ≠ s → Disjoint (A r) (A s) := by
    intro r hr s hs hrs
    refine Finset.disjoint_left.2 fun y hyr hys => hrs ?_
    have hyl := hAlt r hr y hyr
    have h1 := (hAmem r hr (Φ.g y)).2 (by rwa [Φ.f_g hyl])
    have h2 := (hAmem s hs (Φ.g y)).2 (by rwa [Φ.f_g hyl])
    have hrs' : MulAction.orbit (ConjAct H) (Φ.g r) = MulAction.orbit (ConjAct H) (Φ.g s) := by
      rw [← MulAction.orbit_eq_iff.2 h1, ← MulAction.orbit_eq_iff.2 h2]
    have hrl := (hrec r hr).1
    have hsl := (hrec s hs).1
    have hrA : r ∈ A s := by
      have := (hAmem s hs (Φ.g r)).1 (by rw [← hrs']; exact MulAction.mem_orbit_self _)
      rwa [Φ.f_g hrl] at this
    have hsA : s ∈ A r := by
      have := (hAmem r hr (Φ.g s)).1 (by rw [hrs']; exact MulAction.mem_orbit_self _)
      rwa [Φ.f_g hsl] at this
    rw [hA, List.mem_toFinset, List.mem_map] at hrA hsA
    obtain ⟨p, hp, hpr⟩ := hrA
    obtain ⟨q, hq, hqs⟩ := hsA
    have := (hrec s hs).2.2.2.2.2 p hp
    have := (hrec r hr).2.2.2.2.2 q hq
    omega
  have hcardA : ∀ r ∈ D, (A r).card = (recM mul inv gens r).length := by
    intro r hr
    rw [hA, List.toFinset_card_of_nodup (nodup_of_orbOK (hrec r hr).2.2.2.1), List.length_map]
  have hbu : D.toFinset.biUnion A = (kInv mul N).toFinset := by
    refine Finset.eq_of_subset_of_card_le
      (Finset.biUnion_subset.2 fun r hr => hAsub r (List.mem_toFinset.1 hr)) ?_
    rw [Finset.card_biUnion (fun r hr s hs hrs =>
      hdisj r (List.mem_toFinset.1 hr) s (List.mem_toFinset.1 hs) hrs),
      List.toFinset_card_of_nodup (by unfold kInv; exact (List.nodup_range).filter _), ← hsum,
      ← List.sum_toFinset _ hnd]
    exact (Finset.sum_congr rfl fun r hr => hcardA r (List.mem_toFinset.1 hr)).ge
  have hfu : Φ.f u ∈ D.toFinset.biUnion A := by rw [hbu]; exact List.mem_toFinset.2 hmem
  obtain ⟨r, hrC, hur⟩ := Finset.mem_biUnion.1 hfu
  have hr := List.mem_toFinset.1 hrC
  have hrl := (hrec r hr).1
  have huo := (hAmem r hr u).2 hur
  obtain ⟨g, hg⟩ := mem_orbit_iff_conj.1 huo
  have hgr : Φ.g r = g⁻¹ * u * g⁻¹⁻¹ := by rw [← hg]; group
  have hlr : ALike t (Φ.g r) := by rw [hgr]; exact (aLike_conj _).2 hu
  have hlen : (recM mul inv gens r).length = m := by
    obtain ⟨-, -, -, hO, hCl, -⟩ := hrec r hr
    rw [← Φ.ncard_eq h0 hinv hgens hG (u := Φ.g r) (O := recM mul inv gens r)
      ((Φ.f_g hrl).symm ▸ hO) ((Φ.f_g hrl).symm ▸ hCl), MulAction.orbit_eq_iff.2 huo |>.symm,
      hnu]
  refine ⟨r, ?_, g, hg⟩
  have hrD := hr
  rw [hD] at hrD
  obtain ⟨c, hc, hcr⟩ := List.mem_map.1 hrD
  unfold kX kRepsC
  rw [List.mem_filter]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, ?_⟩, hcr⟩, ?_, ?_⟩
  · rw [beq_iff_eq, ← (hrecC c hc).2.2.2.2.2.1, hcr, hlen]
  · rw [← Φ.f_g hrl, kCount_kInv Φ h0, hlr.2.2.1, ← kCount_kInv Φ h0, hti1]
  · rw [← Φ.f_g hrl, kCount_kOrd4 Φ h0, hlr.2.2.2, ← kCount_kOrd4 Φ h0, hti2]

end Spec

section Kill

variable {G : Type*} [Group G] [Finite G] {t : G} {TH T : Subgroup G} (hTp : IsPGroup 2 T)
  (hTHT : TH ≤ T) (hTH : TH ≤ Subgroup.centralizer ({t} : Set G))
  (hTHmax : ∀ V : Subgroup G, V ≤ Subgroup.centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V →
    V = TH)
  (ht : t ∈ T) (ht2 : t * t = 1)
  {N : ℕ} {mul : ℕ → ℕ → ℕ} {inv : ℕ → ℕ} {gens : List ℕ} (Φ : CodeIso T N mul)
  (h0 : mul 0 0 = 0) (hinv : invOK mul inv N = true) (hgens : ∀ g ∈ gens, g < N)
  (hG : Gen mul gens N) {m : ℕ} (hm : 1 < m)

@[expose] def RepProp (R : List ℕ) (ti : ℕ × ℕ) : Prop :=
  orbOK mul inv N (Φ.f ⟨t, ht⟩) (kRec mul inv gens m (Φ.f ⟨t, ht⟩)) = true →
    orbClosed mul inv gens (Φ.f ⟨t, ht⟩) (kRec mul inv gens m (Φ.f ⟨t, ht⟩)) = true →
    (kRec mul inv gens m (Φ.f ⟨t, ht⟩)).length = m →
    kCount mul (kInv mul N) (Φ.f ⟨t, ht⟩) = ti.1 → kCount mul (kOrd4 mul N) (Φ.f ⟨t, ht⟩) = ti.2 →
    ∀ u : T, ALike ⟨t, ht⟩ u → ∃ r ∈ kX mul (kInv mul N) (kOrd4 mul N) R ti, ∃ g : T,
      g * Φ.g r * g⁻¹ = u

omit [Finite G] in
include h0 hinv hgens hG hm in
theorem repProp_kRepsC {C : List (ℕ × ℕ)} (hC : kClassOK mul inv gens N C = true)
    (ti : ℕ × ℕ) : RepProp ht (inv := inv) (gens := gens) Φ (m := m) (kRepsC C m) ti :=
  fun htO htC htl hti1 hti2 _ hu =>
    like_rep_C Φ h0 hinv hgens hG hC htO htC htl hm hti1 hti2 hu

include hTp hTHT hTH hTHmax ht2 h0 hinv hgens hG in
theorem false_of_killAt_rep (hGt : ∀ K : Subgroup G, K.index = 2 → t ∈ K) {ti : ℕ × ℕ}
    {b : List Bool} {χ : Array Bool} (hchi : chiOK mul gens N b χ = true) {R : List ℕ}
    (hrep : RepProp ht (inv := inv) (gens := gens) Φ (m := m) R ti)
    (hkill : killAt mul inv gens N (kInv mul N) (kOrd4 mul N) R m χ true (Φ.f ⟨t, ht⟩) ti = true) :
    False := by
  unfold killAt at hkill
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true, ite_true] at hkill
  obtain ⟨⟨⟨⟨⟨⟨htC, htl⟩, htO⟩, hti1⟩, hti2⟩, htχ⟩, hX⟩ := hkill
  obtain ⟨hMT, hM2, hMn, htM, -⟩ := chiSub_spec ht Φ h0 hinv hgens hG hchi htχ
  refine false_of_N5 hGt ht2 hTp hTHT hTH hTHmax ht ?_ hMT hM2 hMn htM
  intro u hu
  have huT : u ∈ T := hu.1
  have hl := (like_iff ht huT).1 hu
  obtain ⟨r, hr, g, hg⟩ := hrep htO htC htl hti1 hti2 _ hl
  obtain ⟨p, hp, hpr⟩ := hX r hr
  have hpr' : r ∈ (kRec mul inv gens m (Φ.f ⟨t, ht⟩)).map Prod.fst :=
    List.mem_map.2 ⟨p, hp, hpr⟩
  obtain ⟨k, hk⟩ := Φ.exists_conj_of_orbOK h0 hinv htO hpr'
  have hrk : Φ.g r = k * ⟨t, ht⟩ * k⁻¹ := by rw [← hk, Φ.g_f]
  refine ⟨((g * k : T) : G), (g * k).2, ?_⟩
  have := congrArg Subtype.val hg
  rw [hrk] at this
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
  rw [← this]
  group

include hTp hTHT hTH hTHmax ht2 h0 hinv hgens hG in
theorem not_max_of_killAt_rep (hGt : ∀ K : Subgroup G, K.index = 2 → t ∈ K) {ti : ℕ × ℕ}
    {b : List Bool} {χ : Array Bool} (hchi : chiOK mul gens N b χ = true) {R : List ℕ}
    (hRlt : ∀ r ∈ R, r < N) (hrep : RepProp ht (inv := inv) (gens := gens) Φ (m := m) R ti)
    {n5 : Bool}
    (hkill : killAt mul inv gens N (kInv mul N) (kOrd4 mul N) R m χ n5 (Φ.f ⟨t, ht⟩) ti = true)
    (hn5 : n5 = false) :
    ¬ ∀ P : Subgroup G, IsPGroup 2 P → T ≤ P → P = T := by
  intro hTmax
  subst hn5
  unfold killAt at hkill
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.false_eq_true, ite_false]
    at hkill
  obtain ⟨⟨⟨⟨⟨⟨htC, htl⟩, htO⟩, hti1⟩, hti2⟩, htχ⟩, hX⟩ := hkill
  obtain ⟨hMT, hM2, hMn, -, hmem⟩ := chiSub_spec ht Φ h0 hinv hgens hG hchi htχ
  obtain ⟨u, huM, hu⟩ := exists_like_of_transfer hGt ht2 hTp hTmax hTHT hTH hTHmax hMT hM2
  have huT : u ∈ T := hu.1
  have hl := (like_iff ht huT).1 hu
  obtain ⟨r, hr, g, hg⟩ := hrep htO htC htl hti1 hti2 _ hl
  have hrχ := hX r hr
  have hrlt : r < N := hRlt r (List.mem_of_mem_filter hr)
  have hu' : ((g * Φ.g r * g⁻¹ : T) : G) ∈ chiSub Φ h0 hinv hgens hG hchi := by
    rw [hg]; exact huM
  have hconj := hMn _ (g⁻¹).2 _ hu'
  have e : ((g⁻¹ : T) : G) * ((g * Φ.g r * g⁻¹ : T) : G) * ((g⁻¹ : T) : G)⁻¹ =
      ((Φ.g r : T) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [e, hmem, Φ.f_g hrlt, hrχ] at hconj
  exact Bool.noConfusion hconj

omit [Finite G] in
theorem groupKillC_spec {n5 : Bool} {b : List Bool} {χ : Array Bool} {ts : List (ℕ × (ℕ × ℕ))}
    {C : List (ℕ × ℕ)} (hk : groupKillC mul inv gens N m n5 b χ ts C = true) :
    invOK mul inv N = true ∧ kClassOK mul inv gens N C = true ∧ chiOK mul gens N b χ = true ∧
      ∀ p ∈ ts, killAt mul inv gens N (kInv mul N) (kOrd4 mul N) (kRepsC C m) m χ n5
        p.1 p.2 = true := by
  unfold groupKillC at hk
  simp only [Bool.and_eq_true, List.all_eq_true, killAtC_eq] at hk
  exact ⟨hk.1.1.1, hk.1.1.2, hk.1.2, hk.2⟩

omit [Finite G] in
theorem kRepsC_lt {C : List (ℕ × ℕ)} (hC : kClassOK mul inv gens N C = true) :
    ∀ r ∈ kRepsC C m, r < N := fun r hr => by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  exact ((classOK_parts hC).2.1 c (List.mem_of_mem_filter hc)).1

end Kill

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
