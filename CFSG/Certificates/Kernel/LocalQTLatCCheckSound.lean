module

public import CFSG.Certificates.Kernel.LocalQTLatCSound
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.Certificates.Kernel.LocalQTDcosSound

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

variable {n : ℕ}

theorem recSum {α : Type} (f : α → ℕ) : ∀ l : List α,
    List.rec (motive := fun _ => ℕ) 0 (fun r _ ih => Nat.add ih (f r)) l = (l.map f).sum
  | [] => rfl
  | r :: l => by
    change Nat.add (List.rec (motive := fun _ => ℕ) 0 (fun r _ ih => Nat.add ih (f r)) l) (f r) = _
    rw [recSum f l, List.map_cons, List.sum_cons, Nat.add_eq, Nat.add_comm]

theorem recPair {α : Type} (R : α → α → Bool) : ∀ l : List α,
    List.rec (motive := fun _ => Bool) true
      (fun r rs ih => CFSG.KC.Ord.andB (allA rs (R r)) ih) l = true ↔
      l.Pairwise fun a b => R a b = true
  | [] => by simp
  | r :: l => by
    change CFSG.KC.Ord.andB (allA l (R r)) (List.rec (motive := fun _ => Bool) true
      (fun r rs ih => CFSG.KC.Ord.andB (allA rs (R r)) ih) l) = true ↔ _
    rw [P.andB_iff, allA_eq_true, recPair R l, List.pairwise_cons]

theorem filtL_eq' (l : List ℕ) (f : ℕ → Bool) : filtL l f = l.filter f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Bool.rec (motive := fun _ => List ℕ) (filtL l f) (x :: filtL l f) (f x) = _
    rw [List.filter_cons, ih]
    cases f x <;> rfl

theorem count_filter {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) {E : List β} (hnd : E.Nodup) {S : Finset α}
    (hS : ∀ x, x ∈ S ↔ f x ∈ E) (hE : ∀ b ∈ E, ∃ a, f a = b) (q : β → Bool) :
    (E.filter q).length = (S.filter fun a => q (f a) = true).card := by
  rw [← List.toFinset_card_of_nodup (hnd.filter q)]
  have e : (E.filter q).toFinset = (S.filter fun a => q (f a) = true).image f := by
    ext b
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨hb, hq⟩
      obtain ⟨a, rfl⟩ := hE b hb
      exact ⟨a, ⟨(hS a).2 hb, hq⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hq⟩, rfl⟩
      exact ⟨(hS a).1 ha, hq⟩
  rw [e, Finset.card_image_of_injective _ hf]

theorem natCard_sub {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {x // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem opt_rel {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (hlen : l₁.length = l₂.length)
    (h : ∀ j (h₁ : j < l₁.length) (h₂ : j < l₂.length), R l₁[j] l₂[j]) (j : ℕ) :
    (l₁[j]? = none ∧ l₂[j]? = none) ∨ ∃ p q, l₁[j]? = some p ∧ l₂[j]? = some q ∧ R p q := by
  by_cases hj : j < l₁.length
  · exact Or.inr ⟨l₁[j], l₂[j]'(by omega), List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem _, h j hj _⟩
  · exact Or.inl ⟨List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)⟩

theorem grpM_spec (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (MG : List (Perm (Fin n))) (MW : List (List (List ℕ))) (d : ℕ)
    (h : grpM n C (chainF C) d (MG.map P.code) MW = true) :
    (∀ σ, InC n C σ ↔ RN.enc σ ∈ bfsSet (MG.map RN.enc) d) ∧
      closedH (MG.map RN.enc) (bfsSet (MG.map RN.enc) d) = true ∧
      (bfsSet (MG.map RN.enc) d).size = chainF C := by
  have hC := chainP_lvOK (chainP_of_ok hok hI)
  cases MW with
  | cons w MW =>
    change grpC n C (chainF C) (MG.map P.code) (w :: MW) d = true at h
    have hmem := mem_bfsSet_iff hn hok hI MG h
    obtain ⟨h1, -⟩ := grpC_sound hn hok hI MG h
    refine ⟨fun σ => ⟨fun hσ => (hmem _).2 ⟨σ, hσ, rfl⟩, fun hσ => ?_⟩, ?_,
      size_bfsSet hn hok hI MG h⟩
    · obtain ⟨τ, hτ, e⟩ := (hmem _).1 hσ
      exact RN.enc_inj e ▸ hτ
    · exact closedH_of_grp MG d (InC n C) hmem ((h1 1).2 (Subgroup.one_mem _))
        fun σ hσ g hg => (h1 _).2 (Subgroup.mul_mem _ ((h1 σ).1 hσ) (Subgroup.subset_closure hg))
  | nil =>
    change CFSG.KC.Ord.andB (closedM n C (chainF C) (MG.map P.code)
        (bfsM n C (chainF C) (MG.map P.code) d))
      (Nat.beq (bfsM n C (chainF C) (MG.map P.code) d).size (chainF C)) = true at h
    rw [P.andB_iff, P.beq_iff] at h
    obtain ⟨hc, hs⟩ := h
    have hb : (bfsM n C (chainF C) (MG.map P.code) d).ok = true := (P.andB_iff.1 hc).1
    have hR := repN hn hok hI MG d hb
    have hcl : closedH (MG.map RN.enc) (bfsSet (MG.map RN.enc) d) = true := by
      have := closedM_iff (idxInjN hn hok hI (chainF C)) (rnc_mul hn) rnc_one (MG.map RN.enc) hR hb
      rw [map_rnc_enc] at this
      exact this.1 hc
    have hsz : (bfsSet (MG.map RN.enc) d).size = chainF C := by rw [← repM_size hR, hs]
    have hin : ∀ σ, RN.enc σ ∈ bfsSet (MG.map RN.enc) d → InC n C σ := by
      intro σ hσ
      obtain ⟨E, -, hmem, -, -, -, hlt⟩ := hR
      have := hlt _ ((hmem _).1 hσ)
      rw [rnc_enc] at this
      exact (inC_iff hn hC σ).1 (P.blt_iff.2 this)
    refine ⟨fun σ => ⟨fun hσ => ?_, hin σ⟩, hcl, hsz⟩
    classical
    have hK := mem_closure_iff_H (rawIsEnc n) MG d hcl
    have hA : (Finset.univ.filter fun τ => τ ∈ Subgroup.closure {g | g ∈ MG}) ⊆
        Finset.univ.filter fun τ => InC n C τ := fun τ hτ => by
      rw [Finset.mem_filter] at hτ ⊢
      exact ⟨hτ.1, hin τ ((hK τ).1 hτ.2)⟩
    have hcA : (Finset.univ.filter fun τ => τ ∈ Subgroup.closure {g | g ∈ MG}).card =
        chainF C := by
      rw [← natCard_sub, ← hsz]
      exact card_closure_of_closedH (rawIsEnc n) MG d hcl
    have hcB : (Finset.univ.filter fun τ => InC n C τ).card = chainF C := by
      rw [← natCard_sub]
      exact card_inC hn hok hI
    have e := Finset.eq_of_subset_of_card_le hA (by rw [hcA, hcB])
    have hσ' : σ ∈ Finset.univ.filter fun τ => InC n C τ :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ⟩
    rw [← e, Finset.mem_filter] at hσ'
    exact (hK σ).1 hσ'.2

abbrev MemRel (n : ℕ) (C : List Lvl) (p : Mem × SetX)
    (q : List (Perm (Fin n)) × Std.HashSet (RN n)) : Prop :=
  p.1.1 = q.1.map P.code ∧
    (∀ σ, memX n C (chainF C) p.2 (P.code σ) = true ↔ RN.enc σ ∈ q.2) ∧
    sizeX (chainF C) p.2 = q.2.size ∧ closedH (q.1.map RN.enc) q.2 = true

theorem mem_rel (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) {d : ℕ} {m : Mem} {L : List (Perm (Fin n))}
    (hm : m.1 = L.map P.code) (hc : closedX n C (chainF C) d m (mkX n C (chainF C) d m) = true) :
    MemRel n C (m, mkX n C (chainF C) d m) (L, elts RN.enc d L) := by
  obtain ⟨M, full, W⟩ := m
  dsimp only at hm
  subst hm
  obtain ⟨h1, h2, h3⟩ := member_spec hn hok hI L full W hc
  exact ⟨rfl, h1, h2, h3⟩

theorem ok_mem (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) {d : ℕ} {m : Mem} {L : List (Perm (Fin n))}
    (hm : m.1 = L.map P.code) (hc : closedX n C (chainF C) d m (mkX n C (chainF C) d m) = true) :
    (bfsM n C (chainF C) (L.map P.code) d).ok = true := by
  obtain ⟨M, full, W⟩ := m
  dsimp only at hm
  subst hm
  cases full with
  | false => exact (P.andB_iff.1 hc).1
  | true =>
    change grpC n C (chainF C) (L.map P.code) W d = true at hc
    obtain ⟨h1, -⟩ := grpC_sound hn hok hI L hc
    have hC := chainP_lvOK (chainP_of_ok hok hI)
    refine ok_bfsM (L.map P.code) (fun x => ∃ σ, InC n C σ ∧ P.code σ = x)
      ⟨1, (h1 1).2 (Subgroup.one_mem _), P.code_one.symm⟩ ?_ ?_ d
    · rintro _ ⟨σ, hσ, rfl⟩ g hg
      obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hg
      exact ⟨σ * τ, (h1 _).2 (Subgroup.mul_mem _ ((h1 σ).1 hσ) (Subgroup.subset_closure hτ)),
        (P.code_mul hn σ τ).symm⟩
    · rintro _ ⟨σ, hσ, rfl⟩
      exact P.blt_iff.1 ((inC_iff hn hC σ).2 hσ)

@[expose] noncomputable def memsGo (Ls : List (List ℕ)) (ms : List Mem) : Bool :=
  List.rec (motive := fun _ => List Mem → Bool)
    (fun ms => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ms)
    (fun L _ ih ms => List.rec (motive := fun _ => Bool) false
      (fun m ms' _ => CFSG.KC.Ord.andB (eqL m.1 L) (ih ms')) ms) Ls ms

theorem memsGo_iff : ∀ (Ls : List (List ℕ)) (ms : List Mem),
    memsGo Ls ms = true ↔ ms.map Prod.fst = Ls
  | [], [] => by simp [memsGo]
  | [], _ :: _ => by simp [memsGo]
  | _ :: _, [] => by simp [memsGo]
  | L :: Ls, m :: ms => by
    change CFSG.KC.Ord.andB (eqL m.1 L) (memsGo Ls ms) = true ↔ _
    rw [P.andB_iff, LK.eqL_iff, memsGo_iff Ls ms, List.map_cons, List.cons.injEq]

theorem memsOK_iff {T : List (Perm (Fin n))} {lat : List (List (Perm (Fin n)))} {ms : List Mem}
    (h : memsOK (T.map P.code) (lat.map (List.map P.code)) ms = true) :
    ms.map Prod.fst = (T :: lat).map (List.map P.code) := by
  rw [List.map_cons]
  exact (memsGo_iff (T.map P.code :: lat.map (List.map P.code)) ms).1 h

theorem membersX_eq (n : ℕ) (C : List Lvl) (F d : ℕ) (ms : List Mem) :
    membersX n C F d ms = ms.map fun m => (m, mkX n C F d m) := by
  unfold membersX
  exact LK.recMap _ ms

theorem members_rel (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (c : LatCert (Perm (Fin n))) (ms : List Mem)
    (hms : ms.map Prod.fst = (c.tGens :: c.lat).map (List.map P.code))
    (hcl : ∀ p ∈ membersX n C (chainF C) c.depth ms,
      closedX n C (chainF C) c.depth p.1 p.2 = true) :
    (membersX n C (chainF C) c.depth ms).length = (c.members RN.enc).length ∧
    ∀ j (h₁ : j < (membersX n C (chainF C) c.depth ms).length)
      (h₂ : j < (c.members RN.enc).length),
      MemRel n C (membersX n C (chainF C) c.depth ms)[j] (c.members RN.enc)[j] := by
  have hlen : ms.length = (c.tGens :: c.lat).length := by
    have := congrArg List.length hms
    simpa using this
  have hcl' : ∀ m ∈ ms, closedX n C (chainF C) c.depth m (mkX n C (chainF C) c.depth m) = true :=
    fun m hm => hcl _ (by rw [membersX_eq]; exact List.mem_map.2 ⟨m, hm, rfl⟩)
  simp only [membersX_eq, LatCert.members, List.length_map]
  refine ⟨hlen, fun j h₁ h₂ => ?_⟩
  simp only [List.getElem_map]
  have e : ms[j].1 = (c.tGens :: c.lat)[j].map P.code := by
    have := congrArg (fun l => l[j]?) hms
    simp only [List.getElem?_map, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
      Option.map_some, Option.some.injEq] at this
    exact this
  exact mem_rel hn hok hI e (hcl' _ (List.getElem_mem h₁))

@[expose] noncomputable def zipX (n : ℕ) (A B : List ℕ) (ws : List (List ℕ)) : Bool :=
  List.rec (motive := fun _ => List (List ℕ) → Bool) (fun _ => true)
    (fun b _ ih ws => List.rec (motive := fun _ => Bool) true
      (fun w ws' _ => CFSG.KC.Ord.andB (Nat.beq (CFSG.KC.LQT.W.evalWK n A w) b) (ih ws')) ws) B ws

theorem zipX_sound (A : List ℕ) : ∀ (B : List ℕ) (ws : List (List ℕ)), zipX n A B ws = true →
    ∀ p ∈ B.zip ws, CFSG.KC.LQT.W.evalWK n A p.2 = p.1
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | b :: B, w :: ws, h => by
    change CFSG.KC.Ord.andB (Nat.beq (CFSG.KC.LQT.W.evalWK n A w) b) (zipX n A B ws) = true at h
    rw [P.andB_iff, P.beq_iff] at h
    intro p hp
    rw [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h.1
    · exact zipX_sound A B ws h.2 p hp

theorem eqX_sound (hn : n ≤ 32) {C : List Lvl} {S : SetX} {H : Std.HashSet (RN n)}
    (hm : ∀ σ, memX n C (chainF C) S (P.code σ) = true ↔ RN.enc σ ∈ H)
    (A B : List (Perm (Fin n))) (ws : List (List ℕ)) {A' B' : List ℕ} (hA : A' = A.map P.code)
    (hB : B' = B.map P.code) (h : eqX n C (chainF C) S A' B' ws = true) :
    eqCert RN.enc H A B ws = true := by
  subst hA hB
  change CFSG.KC.Ord.andB _ (CFSG.KC.Ord.andB _ (zipX n (A.map P.code) (B.map P.code) ws)) =
    true at h
  rw [P.andB_iff, P.andB_iff, P.allL_map, P.beq_iff, LK.lenA_eq, LK.lenA_eq, List.length_map] at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold eqCert
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨fun g hg => Std.HashSet.contains_iff_mem.2 ((hm g).1 (h1 g hg)), h2⟩,
    fun p hp => ?_⟩
  obtain ⟨b, w⟩ := p
  have hz : (P.code b, w) ∈ (B.map P.code).zip ws := by
    rw [List.zip_map_left, List.mem_map]
    exact ⟨(b, w), hp, rfl⟩
  have := zipX_sound _ _ _ h3 _ hz
  rw [LK.evalWK_code hn, P.code_eq_iff hn] at this
  change evalW (A.map RN.enc) w = RN.enc b
  rw [← enc_evalW (rawIsEnc n), this]

theorem recSizeX (F : ℕ) (l : List (Mem × SetX)) :
    List.rec (motive := fun _ => List ℕ) [] (fun p _ ih => List.cons (sizeX F p.2) ih) l =
      l.map fun p => sizeX F p.2 :=
  LK.recMap _ l

theorem coverOK_of (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (c : LatCert (Perm (Fin n)))
    (hMin : ∀ σ, InC n C σ ↔ RN.enc σ ∈ bfsSet (c.mGens.map RN.enc) c.depth)
    (hMcl : closedH (c.mGens.map RN.enc) (bfsSet (c.mGens.map RN.enc) c.depth) = true)
    (hMsz : (bfsSet (c.mGens.map RN.enc) c.depth).size = chainF C)
    (hTcl : closedH (c.tGens.map RN.enc) (bfsSet (c.tGens.map RN.enc) c.depth) = true)
    (hTok : (bfsM n C (chainF C) (c.tGens.map P.code) c.depth).ok = true)
    (hT : ∀ g ∈ c.tGens, InC n C g)
    (h : coverC n C (chainF C) (bfsM n C (chainF C) (c.tGens.map P.code) c.depth) (repsCode c) =
      true) :
    c.coverOK RN.enc = true := by
  classical
  have hC := chainP_lvOK (chainP_of_ok hok hI)
  set ET := bfsM n C (chainF C) (c.tGens.map P.code) c.depth with hET
  have hR := repN hn hok hI c.tGens c.depth hTok
  rw [← hET] at hR
  have hKT := mem_closure_iff_H (rawIsEnc n) c.tGens c.depth hTcl
  have hKM := mem_closure_iff_H (rawIsEnc n) c.mGens c.depth hMcl
  set Ts : Finset (Perm (Fin n)) :=
    Finset.univ.filter fun τ => τ ∈ Subgroup.closure {g | g ∈ c.tGens} with hTs
  set Ms : Finset (Perm (Fin n)) :=
    Finset.univ.filter fun τ => τ ∈ Subgroup.closure {g | g ∈ c.mGens} with hMs
  have hTiff : ∀ σ, σ ∈ Ts ↔ RN.enc σ ∈ bfsSet (c.tGens.map RN.enc) c.depth := fun σ => by
    rw [hTs, Finset.mem_filter, hKT]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hMiff : ∀ σ, σ ∈ Ms ↔ InC n C σ := fun σ => by
    rw [hMs, Finset.mem_filter, hKM, hMin]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hsub : IsSubF Ts := by
    refine ⟨?_, fun a ha b hb => ?_, fun a ha => ?_⟩
    · rw [hTs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Subgroup.one_mem _⟩
    · rw [hTs, Finset.mem_filter] at ha hb ⊢
      exact ⟨Finset.mem_univ _, Subgroup.mul_mem _ ha.2 hb.2⟩
    · rw [hTs, Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ _, Subgroup.inv_mem _ ha.2⟩
  have hTM : Ts ⊆ Ms := fun σ hσ => by
    rw [hTs, Finset.mem_filter] at hσ
    rw [hMs, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hle : Subgroup.closure {g | g ∈ c.tGens} ≤ Subgroup.closure {g | g ∈ c.mGens} := by
      rw [Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, hKM, ← hMin]
      exact hT g hg
    exact hle hσ.2
  have hMmul : ∀ a ∈ Ms, ∀ b ∈ Ms, a * b ∈ Ms := fun a ha b hb => by
    rw [hMs, Finset.mem_filter] at ha hb ⊢
    exact ⟨Finset.mem_univ _, Subgroup.mul_mem _ ha.2 hb.2⟩
  have hcTs : Ts.card = ET.size := by
    rw [repM_size hR, ← card_closure_of_closedH (rawIsEnc n) c.tGens c.depth hTcl, hTs,
      ← natCard_sub]
  have hcMs : Ms.card = chainF C := by
    rw [← hMsz, ← card_closure_of_closedH (rawIsEnc n) c.mGens c.depth hMcl, hMs, ← natCard_sub]
  have hcode : ∀ ρ τ ρ' : Perm (Fin n), P.mul n (P.mul n (P.inv n (P.code ρ)) (P.code τ))
      (P.code ρ') = P.code (ρ⁻¹ * τ * ρ') := fun ρ τ ρ' => by
    rw [P.code_inv hn, P.code_mul hn, P.code_mul hn]
  unfold coverC at h
  rw [P.andB_iff, P.andB_iff, allA_eq_true, P.beq_iff] at h
  obtain ⟨c1, c2, c3⟩ := h
  have hrM : ∀ r ∈ c.reps.map Prod.fst, r ∈ Ms := fun r hr => by
    obtain ⟨rr, hrr, rfl⟩ := List.mem_map.1 hr
    have := c1 _ (by unfold repsCode; exact List.mem_map_of_mem hrr)
    exact (hMiff _).2 ((inC_iff hn hC _).1 this)
  have hd : (c.reps.map Prod.fst).Pairwise fun r r' => ∀ t ∈ Ts, r⁻¹ * t * r' ∉ Ts := by
    have c2' := (recPair (fun r r' : ℕ × ℕ × List (List ℕ) => P.allL ET.elems fun t =>
      CFSG.KC.Ord.notB (memM n C (chainF C) ET (P.mul n (P.mul n (P.inv n r.1) t) r'.1)))
      (repsCode c)).1 c2
    unfold repsCode at c2'
    rw [List.pairwise_map] at c2'
    rw [List.pairwise_map]
    refine c2'.imp fun {a b} hab t ht hin => ?_
    dsimp only at hab
    rw [repM_allL hR, LK.code_eq_P] at hab
    have := hab _ ((hTiff t).1 ht)
    rw [rnc_enc, hcode, P.notB_iff, memN hn hok hI hR] at this
    exact this ((hTiff _).1 hin)
  obtain ⟨El, hnd, hmem, hel, -, -, -⟩ := id hR
  have hEl : ∀ b ∈ El, ∃ σ : Perm (Fin n), RN.enc σ = b := fun b hb => by
    obtain ⟨σ, -, e⟩ := bfsSet_sound (rawIsEnc n) c.tGens c.depth b ((hmem b).2 hb)
    exact ⟨σ, e⟩
  have hterm : ∀ ρ : Perm (Fin n), CFSG.KC.Loop.strictN
      (lenA (filtL ET.elems fun t => memM n C (chainF C) ET
        (P.mul n (P.mul n (P.inv n (P.code ρ)) t) (P.code ρ))))
      (fun k => Bool.rec (motive := fun _ => ℕ) (Nat.add (chainF C) 1)
        (Nat.div (Nat.mul ET.size ET.size) k)
        (Nat.beq (Nat.mod (Nat.mul ET.size ET.size) k) 0)) = (dcos Ts ρ).card := by
    intro ρ
    rw [strictN_eq, LK.lenA_eq, filtL_eq', hel, List.filter_map, List.length_map,
      count_filter RN.enc_inj hnd (fun σ => (hTiff σ).trans (hmem _)) hEl]
    have hk : (Ts.filter fun a => (fun t => memM n C (chainF C) ET
        (P.mul n (P.mul n (P.inv n (P.code ρ)) t) (P.code ρ))) (rnc (RN.enc a)) = true) =
        Ts.filter fun t => ρ⁻¹ * t * ρ ∈ Ts := by
      refine Finset.filter_congr fun t _ => ?_
      dsimp only
      rw [rnc_enc, hcode, memN hn hok hI hR, hTiff]
    rw [Function.comp_def, hk]
    have hcd := card_dcos hsub ρ
    have hpos : 0 < (Ts.filter fun t => ρ⁻¹ * t * ρ ∈ Ts).card := by
      refine Finset.card_pos.2 ⟨1, Finset.mem_filter.2 ⟨hsub.one, ?_⟩⟩
      rw [mul_one, inv_mul_cancel]
      exact hsub.one
    rw [← hcTs]
    change Bool.rec (motive := fun _ => ℕ) (chainF C + 1)
      (Ts.card * Ts.card / (Ts.filter fun t => ρ⁻¹ * t * ρ ∈ Ts).card)
      (Nat.beq (Ts.card * Ts.card % (Ts.filter fun t => ρ⁻¹ * t * ρ ∈ Ts).card) 0) = _
    rw [← hcd, Nat.mul_mod_left, Nat.mul_div_cancel _ hpos]
    rfl
  have hs : ((c.reps.map Prod.fst).map fun r => (dcos Ts r).card).sum = Ms.card := by
    rw [hcMs, ← c3, recSum]
    unfold repsCode
    rw [List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun r _ => ?_
    exact (hterm r.1).symm
  have hcov := cover_of_count hsub hTM hMmul hrM hd hs
  unfold LatCert.coverOK
  dsimp only
  rw [toList_all_iff]
  intro x hx
  obtain ⟨σ, hσ, rfl⟩ := bfsSet_sound (rawIsEnc n) c.mGens c.depth x hx
  have hσM : σ ∈ Ms := by
    rw [hMs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hσ⟩
  obtain ⟨r, hr, hx'⟩ := hcov σ hσM
  obtain ⟨rr, hrr, rfl⟩ := List.mem_map.1 hr
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_dcos.1 hx'
  rw [Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_flatMap]
  refine ⟨rr, hrr, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨RN.enc a, Std.HashSet.mem_toList.2 ((hTiff a).1 ha), ?_⟩
  rw [List.mem_map]
  refine ⟨RN.enc b, Std.HashSet.mem_toList.2 ((hTiff b).1 hb), ?_⟩
  rw [RN.enc_mul, RN.enc_mul]

theorem latC_sound (hn : n ≤ 32) (C : List Lvl) (hI : chainInj n C = true)
    (MW : List (List (List ℕ))) (ms : List Mem) (c : LatCert (Perm (Fin n)))
    (h : latC n C c.depth (c.mGens.map P.code) MW (c.tGens.map P.code)
      (c.lat.map (List.map P.code)) ms (repsCode c) c.joins c.sizes c.msize = true) :
    c.check RN.enc = true := by
  unfold latC at h
  simp only [P.andB_iff] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  unfold closedOKC at h1
  rw [P.andB_iff, P.andB_iff, allA_eq_true] at h1
  obtain ⟨hok, hM, hcl⟩ := h1
  have hC := chainP_lvOK (chainP_of_ok hok hI)
  have hms := memsOK_iff h0
  obtain ⟨hlen, hrel⟩ := members_rel hn hok hI c ms hms hcl
  obtain ⟨hMin, hMcl, hMsz⟩ := grpM_spec hn hok hI c.mGens MW c.depth hM
  have hT : ∀ g ∈ c.tGens, InC n C g := by
    unfold tleC at h6
    rw [P.allL_map] at h6
    exact fun g hg => (inC_iff hn hC g).1 (h6 g hg)
  obtain ⟨m0, ms', rfl⟩ : ∃ m0 ms', ms = m0 :: ms' := by
    cases ms with
    | nil => simp at hms
    | cons m0 ms' => exact ⟨m0, ms', rfl⟩
  have hm0 : m0.1 = c.tGens.map P.code := by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at hms
    exact hms.1
  have hc0 : closedX n C (chainF C) c.depth m0 (mkX n C (chainF C) c.depth m0) = true :=
    hcl _ (by rw [membersX_eq]; exact List.mem_cons_self)
  have hTcl := (mem_rel hn hok hI hm0 hc0).2.2.2
  have hTok := ok_mem hn hok hI hm0 hc0
  unfold LatCert.check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, coverOK_of hn hok hI c hMin hMcl hMsz hTcl hTok hT h2⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    unfold LatCert.closedOK
    rw [Bool.and_eq_true, List.all_eq_true]
    refine ⟨hMcl, fun q hq => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    exact (hrel j (by omega) hj).2.2.2
  ·
    unfold repsC at h3
    rw [allA_eq_true] at h3
    unfold LatCert.repsOK
    dsimp only
    rw [List.all_eq_true]
    intro r hr
    have := h3 _ (by unfold repsCode; exact List.mem_map_of_mem hr)
    dsimp only at this
    rw [LK.getO_eq] at this
    rcases opt_rel hlen hrel r.2.1 with ⟨e1, e2⟩ | ⟨p, q, e1, e2, hR⟩
    · rw [e1] at this
      exact absurd this Bool.false_ne_true
    · rw [e1] at this
      rw [e2]
      change eqCert RN.enc q.2 (c.tGens ++ [r.1]) q.1 r.2.2 = true
      exact eqX_sound hn hR.2.1 _ _ _ (by rw [List.map_append]; rfl) hR.1 this
  ·
    unfold joinsC at h4
    rw [P.andB_iff, P.allN_iff, allA_eq_true, LK.lenA_eq] at h4
    obtain ⟨j1, j2⟩ := h4
    unfold LatCert.joinsOK
    dsimp only
    rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    refine ⟨fun a ha => ?_, fun j hj => ?_⟩
    · rw [List.mem_range, ← hlen] at ha
      have j1a := j1 a ha
      rw [P.allN_iff] at j1a
      rw [List.all_eq_true]
      intro b hb
      rw [List.mem_range, ← hlen] at hb
      have j1b := j1a b hb
      rw [LK.anyA_iff] at j1b
      obtain ⟨j, hj, e⟩ := j1b
      rw [P.andB_iff, P.beq_iff, P.beq_iff] at e
      rw [List.any_eq_true]
      exact ⟨j, hj, by simp [e.1, e.2]⟩
    · have := j2 j hj
      rw [LK.getO_eq, LK.getO_eq, LK.getO_eq] at this
      rcases opt_rel hlen hrel j.1 with ⟨a1, a2⟩ | ⟨pa, qa, a1, a2, ra⟩
      · rw [a1] at this
        exact absurd this Bool.false_ne_true
      rcases opt_rel hlen hrel j.2.1 with ⟨b1, b2⟩ | ⟨pb, qb, b1, b2, rb⟩
      · rw [a1, b1] at this
        exact absurd this Bool.false_ne_true
      rcases opt_rel hlen hrel j.2.2.1 with ⟨c1, c2⟩ | ⟨pc, qc, c1, c2, rc⟩
      · rw [a1, b1, c1] at this
        exact absurd this Bool.false_ne_true
      rw [a1, b1, c1] at this
      rw [a2, b2, c2]
      change eqCert RN.enc qc.2 (qa.1 ++ qb.1) qc.1 j.2.2.2 = true
      exact eqX_sound hn rc.2.1 _ _ _ (by rw [ra.1, rb.1, List.map_append]; rfl) rc.1 this
  ·
    unfold sizesC at h5
    rw [P.andB_iff, LK.eqL_iff, P.beq_iff, recSizeX] at h5
    obtain ⟨e1, e2⟩ := h5
    unfold LatCert.sizesOK
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
    refine ⟨?_, by rw [← e2]; exact hMsz⟩
    rw [← e1]
    refine List.ext_getElem (by rw [List.length_map, List.length_map, hlen]) fun j h₁ h₂ => ?_
    rw [List.getElem_map, List.getElem_map]
    exact (hrel j (by simpa using h₂) (by simpa using h₁)).2.2.1.symm
  ·
    unfold LatCert.tleOK
    rw [List.all_eq_true]
    exact fun g hg => Std.HashSet.contains_iff_mem.2 ((hMin g).1 (hT g hg))

open CFSG.QuasithinUnique.L246C127 in
theorem ctC_sound (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (ct : CTCert (Perm (Fin n)))
    (h : ctC n C (chainF C) ct.depth (ct.hGens.map P.code) (ct.nGens.map P.code) ct.expo = true) :
    ct.check RN.enc = true := by
  unfold ctC at h
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff, and_true] at h
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h
  have okH := (P.andB_iff.1 c1).1
  have okN := (P.andB_iff.1 c2).1
  have hRH := repN hn hok hI ct.hGens ct.depth okH
  have hRN := repN hn hok hI ct.nGens ct.depth okN
  have hinj := idxInjN hn hok hI (chainF C)
  have clH : closedH (ct.hGens.map RN.enc) (bfsSet (ct.hGens.map RN.enc) ct.depth) = true := by
    have := closedM_iff hinj (rnc_mul hn) rnc_one (ct.hGens.map RN.enc) hRH okH
    rw [map_rnc_enc] at this
    exact this.1 c1
  have clN : closedH (ct.nGens.map RN.enc) (bfsSet (ct.nGens.map RN.enc) ct.depth) = true := by
    have := closedM_iff hinj (rnc_mul hn) rnc_one (ct.nGens.map RN.enc) hRN okN
    rw [map_rnc_enc] at this
    exact this.1 c2
  rw [P.allL_map] at c3
  rw [repM_allL hRH] at c4 c5
  rw [P.beq_iff, repM_size hRN] at c6
  unfold CTCert.check
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨clH, clN⟩, ?_⟩, ?_⟩, ?_⟩, c6⟩
  · rw [List.all_eq_true]
    exact fun g hg => Std.HashSet.contains_iff_mem.2 ((memN hn hok hI hRH g).1 (c3 g hg))
  · rw [toList_all_iff]
    intro r hr
    have h4 := c4 r hr
    rw [P.allL_map] at h4
    rw [List.all_eq_true]
    intro g hg
    have h4g := h4 g hg
    rw [repM_anyL hRN] at h4g
    obtain ⟨r', hr', e⟩ := h4g
    rw [toList_any_iff]
    refine ⟨r', hr', ?_⟩
    rw [← rnc_enc, ← rnc_mul hn, ← rnc_mul hn, LK.rnc_beq hn] at e
    rw [beq_iff_eq]
    exact e
  · rw [toList_all_iff]
    intro r hr
    have h5 := c5 r hr
    rw [P.orB_iff, P.notB_iff, P.allL_map] at h5
    rw [Bool.or_eq_true]
    rcases h5 with h5 | h5
    · left
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      intro hall
      apply h5
      intro g hg
      rw [List.all_eq_true] at hall
      have := hall g hg
      rw [beq_iff_eq] at this
      rw [← rnc_enc, ← rnc_mul hn, ← rnc_mul hn, LK.rnc_beq hn]
      exact this
    · exact Or.inr (Std.HashSet.contains_iff_mem.2 ((repM_mem hinj hRN r).1 h5))

open CFSG.QuasithinUnique.L246C127 in
theorem memberC_sound (hn : n ≤ 32) (C : List Lvl) (hI : chainInj n C = true) (ms : List Mem)
    (c : LatCert (Perm (Fin n))) (cts : List (CTCert (Perm (Fin n))))
    (h : memberC n C c.depth (c.tGens.map P.code) (c.lat.map (List.map P.code)) ms c.msize
      (cts.map fun ct => (ct.depth, ct.hGens.map P.code, ct.nGens.map P.code, ct.expo)) = true) :
    memberOK c cts = true := by
  unfold memberC at h
  rw [P.andB_iff, P.andB_iff, allA_eq_true] at h
  obtain ⟨h0, hok, hall⟩ := h
  have hms := memsOK_iff h0
  obtain ⟨hlen, hrel⟩ := members_rel hn hok hI c ms hms fun p hp => (P.andB_iff.1 (hall p hp)).1
  unfold memberOK
  rw [List.all_eq_true]
  intro L hL
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
  have hj' : j < (c.members RN.enc).length := by simpa [LatCert.members] using hj
  have hjX : j < (membersX n C (chainF C) c.depth ms).length := by omega
  have hR := hrel j hjX hj'
  have hq : (c.members RN.enc)[j] =
      ((c.tGens :: c.lat)[j], elts RN.enc c.depth (c.tGens :: c.lat)[j]) := by
    simp only [LatCert.members, List.getElem_map]
  rw [hq] at hR
  have := (P.andB_iff.1 (hall _ (List.getElem_mem hjX))).2
  rw [P.orB_iff, P.beq_iff, hR.2.2.1, LK.anyA_iff] at this
  rw [Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
  rcases this with e | ⟨ct', hct', e⟩
  · exact Or.inl e
  · obtain ⟨ct, hct, rfl⟩ := List.mem_map.1 hct'
    dsimp only at e
    rw [P.andB_iff, LK.eqL_iff, hR.1] at e
    obtain ⟨e1, e2⟩ := e
    have hHL : ct.hGens = (c.tGens :: c.lat)[j] :=
      List.map_injective_iff.2 (fun a b h => P.code_inj hn h) e1
    refine Or.inr ⟨ct, hct, ?_⟩
    rw [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hHL, ctC_sound hn hok hI ct e2⟩

end CFSG.KC.LQT.CM

end
