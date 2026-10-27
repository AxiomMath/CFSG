module

public import CFSG.Certificates.Kernel.LocalQTSimsSound
import all CFSG.Certificates.Kernel.LocalQTChainGSound
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

variable {n : ℕ}

theorem recSumL (g : ℕ → ℕ) : ∀ m,
    Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.add acc (g j)) m =
      ∑ j ∈ Finset.range m, g j
  | 0 => rfl
  | m + 1 => by
    change Nat.add (Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.add acc (g j)) m) (g m) = _
    rw [recSumL g m, Finset.sum_range_succ]
    rfl

theorem letN_eq' (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.LQT.Syl.letN y k = k y := by
  cases y <;> rfl

theorem inC_nil (hn : n ≤ 32) (σ : Perm (Fin n)) : InC n [] σ ↔ σ = 1 := by
  change (sift n [] (P.code σ)).isSome = true ↔ _
  simp only [sift]
  rw [P.code_one]
  by_cases e : σ = 1
  · subst e
    simp
  · rw [if_neg fun h => e (P.code_inj hn h)]
    simp [e]

theorem img_mul_rep (hn : n ≤ 32) {prev : List ℕ} {lv : Lvl} {C : List Lvl}
    (hC : ChainP n prev (lv :: C)) {j : ℕ} (hj : j < n) (τ : Perm (Fin n))
    (hτ : P.code τ = getK lv.2.1 j) (e : getK lv.2.1 j ≠ 0) {σ : Perm (Fin n)}
    (hσ : InC n C σ) : P.img (P.code (τ * σ)) lv.1 = j := by
  have hfix := fix_of_inC hn hC.2 hσ lv.1 (List.mem_cons_self ..)
  have hb := (hC.1.2.1 j hj e).2
  rw [← hτ] at hb
  by_cases hbn : lv.1 < n
  · rw [img_one hn hbn, img_code_fix hn _ hbn] at hfix
    rw [img_code_fix hn _ hbn] at hb ⊢
    rw [Perm.mul_apply]
    have : σ ⟨lv.1, hbn⟩ = ⟨lv.1, hbn⟩ := Fin.ext hfix
    rw [this]
    exact hb
  · rw [img_ge hn (fc_code hn _) (not_lt.1 hbn)]
    rw [img_ge hn (fc_code hn _) (not_lt.1 hbn)] at hb
    exact hb

theorem cntFrom_sound (hn : n ≤ 32) (f : ℕ → Bool) : ∀ {prev : List ℕ} {C : List Lvl},
    ChainP n prev C → ∀ π : Perm (Fin n),
    CFSG.KC.LQT.PH.cntFrom n C f (P.code π) =
      (Finset.univ.filter fun σ => InC n C σ ∧ f (P.code (π * σ)) = true).card
  | prev, [], _, π => by
    change Bool.rec (motive := fun _ => ℕ) 0 1 (f (P.code π)) = _
    cases hf : f (P.code π) with
    | false =>
      refine (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun σ _ h => ?_)).symm
      obtain ⟨h1, h2⟩ := h
      rw [inC_nil hn] at h1
      subst h1
      rw [mul_one, hf] at h2
      exact Bool.false_ne_true h2
    | true =>
      refine (Finset.card_eq_one.2 ⟨1, Finset.ext fun σ => ?_⟩).symm
      rw [Finset.mem_filter, Finset.mem_singleton, inC_nil hn]
      constructor
      · exact fun h => h.2.1
      · rintro rfl
        exact ⟨Finset.mem_univ _, rfl, by rw [mul_one, hf]⟩
  | prev, lv :: C, hC, π => by
    have hlv := hC.1.1
    change Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.add acc
      (Bool.rec (motive := fun _ => ℕ)
        (CFSG.KC.LQT.Syl.letN (P.mul n (P.code π) (getK lv.2.1 j))
          (CFSG.KC.LQT.PH.cntFrom n C f)) 0 (Nat.beq (getK lv.2.1 j) 0))) n = _
    rw [recSumL, Finset.card_eq_sum_card_fiberwise (f := fun σ => P.img (P.code σ) lv.1)
      (t := Finset.range n) fun σ _ =>
        Finset.mem_coe.2 (Finset.mem_range.2 (img_lt hn (fc_code hn σ) hlv.1 lv.1))]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [Finset.filter_filter]
    by_cases e : getK lv.2.1 j = 0
    · have hb : Nat.beq (getK lv.2.1 j) 0 = true := P.beq_iff.2 e
      rw [hb]
      refine (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun σ _ h => ?_)).symm
      obtain ⟨⟨hσ, -⟩, hj'⟩ := h
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσ
      obtain ⟨j0, -, -, -, e0, himg, -⟩ := sift_cons_code hn hlv σ hk
      apply e0
      have : j0 = j := by rw [← himg]; exact hj'
      rw [this]
      exact e
    · obtain ⟨⟨τ, hτ⟩, -⟩ := hlv.2.1 j hj e
      have hb : Nat.beq (getK lv.2.1 j) 0 = false := by
        cases h : Nat.beq (getK lv.2.1 j) 0
        · rfl
        · exact absurd (P.beq_iff.1 h) e
      rw [hb]
      change CFSG.KC.LQT.Syl.letN (P.mul n (P.code π) (getK lv.2.1 j))
        (CFSG.KC.LQT.PH.cntFrom n C f) = _
      rw [letN_eq', ← hτ, P.code_mul hn, cntFrom_sound hn f hC.2 (π * τ)]
      refine Finset.card_bij' (fun σ' _ => τ * σ') (fun σ _ => τ⁻¹ * σ) ?_ ?_ ?_ ?_
      · intro σ' hσ'
        rw [Finset.mem_filter] at hσ' ⊢
        obtain ⟨-, hσ'C, hf⟩ := hσ'
        obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσ'C
        refine ⟨Finset.mem_univ _, ⟨?_, by rwa [← mul_assoc]⟩, ?_⟩
        · rw [InC, sift_mul_rep hn hC hj τ (hτ.trans rfl) e hk]
          rfl
        · exact img_mul_rep hn hC hj τ hτ e hσ'C
      · intro σ hσ
        rw [Finset.mem_filter] at hσ ⊢
        obtain ⟨-, ⟨hσC, hf⟩, hj'⟩ := hσ
        obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσC
        obtain ⟨j0, -, τ0, hτ0, -, himg, k', h', -⟩ := sift_cons_code hn hlv σ hk
        have hj0 : j0 = j := by rw [← himg]; exact hj'
        subst hj0
        have : τ0 = τ := P.code_inj hn (hτ0.trans hτ.symm)
        subst this
        refine ⟨Finset.mem_univ _, by rw [InC, h']; rfl, ?_⟩
        rwa [mul_assoc, mul_inv_cancel_left]
      · intro σ' _
        exact inv_mul_cancel_left τ σ'
      · intro σ _
        exact mul_inv_cancel_left τ σ

theorem incK_eq (hn : n ≤ 32) (K : ℕ) (lab : List ℕ) (σ : Perm (Fin n)) :
    incK n K lab (P.code σ) = ∑ q : Fin n, 2 ^ (8 * (K * getK lab q + getK lab (σ q))) := by
  change Nat.rec (motive := fun _ => ℕ) 0 (fun p acc => Nat.add acc
    ((fun p => Nat.shiftLeft 1 (Nat.mul 8 (Nat.add (Nat.mul K (getK lab p))
      (getK lab (P.img (P.code σ) p))))) p)) n = _
  rw [recSumL, Finset.sum_range]
  refine Finset.sum_congr rfl fun q _ => ?_
  change 1 <<< (8 * (K * getK lab q + getK lab (P.img (P.code σ) q))) = _
  rw [Nat.one_shiftLeft, img_code_fix hn σ q.isLt]

theorem incK_conj (hn : n ≤ 32) {K : ℕ} {lab : List ℕ} {t t' : Perm (Fin n)} (σ : Perm (Fin n))
    (ht : ∀ q : Fin n, getK lab (t q) = getK lab q)
    (ht' : ∀ q : Fin n, getK lab (t' q) = getK lab q) :
    incK n K lab (P.code (t * σ * t')) = incK n K lab (P.code σ) := by
  rw [incK_eq hn, incK_eq hn,
    ← Equiv.sum_comp t' (fun q => 2 ^ (8 * (K * getK lab q + getK lab (σ q))))]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Perm.mul_apply, ht, ht']

theorem lab_closure (hn : n ≤ 32) {lab : List ℕ} {G : List (Perm (Fin n))}
    (h : P.allL (G.map P.code) (fun g => P.allN n fun p =>
      Nat.beq (getK lab (P.img g p)) (getK lab p)) = true) :
    ∀ t ∈ Subgroup.closure {g | g ∈ G}, ∀ q : Fin n, getK lab (t q) = getK lab q := by
  rw [P.allL_map] at h
  intro t ht
  induction ht using Subgroup.closure_induction with
  | mem x hx =>
    intro q
    have := h x hx
    rw [P.allN_iff] at this
    have hq := P.beq_iff.1 (this q q.isLt)
    rw [img_code_fix hn x q.isLt] at hq
    exact hq
  | one => exact fun q => rfl
  | mul x y _ _ ihx ihy => exact fun q => by rw [Perm.mul_apply, ihx, ihy]
  | inv x _ ihx =>
    intro q
    rw [← ihx (x⁻¹ q), ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

abbrev MemRelG (n : ℕ) (m : MemG) (q : List (Perm (Fin n)) × Std.HashSet (RN n)) : Prop :=
  m.1 = q.1.map P.code ∧ (∀ σ, memG n m (P.code σ) = true ↔ RN.enc σ ∈ q.2) ∧
    chainF m.2.1 = q.2.size ∧ closedH (q.1.map RN.enc) q.2 = true

theorem memG_spec (hn : n ≤ 32) {d : ℕ} (m : MemG) (L : List (Perm (Fin n)))
    (hm : m.1 = L.map P.code) (hI : chainInj n m.2.1 = true) (hc : closedMG n d m = true) :
    (∀ σ, memG n m (P.code σ) = true ↔ InC n m.2.1 σ) ∧
      (∀ σ, InC n m.2.1 σ ↔ σ ∈ Subgroup.closure {g | g ∈ L}) ∧
      MemRelG n m (L, elts RN.enc d L) := by
  obtain ⟨M, D, W⟩ := m
  dsimp only at hm hI ⊢
  subst hm
  unfold closedMG at hc
  rw [P.andB_iff] at hc
  obtain ⟨hok, hg⟩ := hc
  have hC := chainP_lvOK (chainP_of_ok hok hI)
  obtain ⟨h1, h2⟩ := grpS_sound hn hok hI L hg
  obtain ⟨hmem, hsz, hcl⟩ := grp_spec hn hok hI L d h1 h2
  have hG : ∀ σ, memG n (L.map P.code, D, W) (P.code σ) = true ↔ InC n D σ :=
    fun σ => inC_iff hn hC σ
  refine ⟨hG, h1, rfl, fun σ => ?_, hsz.symm, hcl⟩
  rw [hG]
  change _ ↔ RN.enc σ ∈ bfsSet (L.map RN.enc) d
  rw [hmem]
  exact ⟨fun h => ⟨σ, h, rfl⟩, fun ⟨τ, hτ, e⟩ => (RN.enc_inj e) ▸ hτ⟩

theorem eqG_sound (hn : n ≤ 32) {m : MemG} {H : Std.HashSet (RN n)}
    (hm : ∀ σ, memG n m (P.code σ) = true ↔ RN.enc σ ∈ H)
    (A B : List (Perm (Fin n))) (ws : List (List ℕ)) {A' B' : List ℕ} (hA : A' = A.map P.code)
    (hB : B' = B.map P.code) (h : eqG n m A' B' ws = true) :
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

@[expose] noncomputable def memsGoA {α : Type} (Ls : List (List ℕ)) (ms : List (List ℕ × α)) :
    Bool :=
  List.rec (motive := fun _ => List (List ℕ × α) → Bool)
    (fun ms => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ms)
    (fun L _ ih ms => List.rec (motive := fun _ => Bool) false
      (fun m ms' _ => CFSG.KC.Ord.andB (eqL m.1 L) (ih ms')) ms) Ls ms

theorem memsGoA_iff {α : Type} : ∀ (Ls : List (List ℕ)) (ms : List (List ℕ × α)),
    memsGoA Ls ms = true ↔ ms.map Prod.fst = Ls
  | [], [] => by simp [memsGoA]
  | [], _ :: _ => by simp [memsGoA]
  | _ :: _, [] => by simp [memsGoA]
  | L :: Ls, m :: ms => by
    change CFSG.KC.Ord.andB (eqL m.1 L) (memsGoA Ls ms) = true ↔ _
    rw [P.andB_iff, LK.eqL_iff, memsGoA_iff Ls ms, List.map_cons, List.cons.injEq]

theorem memsOKG_iff {T : List (Perm (Fin n))} {lat : List (List (Perm (Fin n)))} {ms : List MemG}
    (h : memsOKG (T.map P.code) (lat.map (List.map P.code)) ms = true) :
    ms.map Prod.fst = (T :: lat).map (List.map P.code) := by
  rw [List.map_cons]
  exact (memsGoA_iff (T.map P.code :: lat.map (List.map P.code)) ms).1 h

theorem membersG_rel (hn : n ≤ 32) (c : LatCert (Perm (Fin n))) (ms : List MemG)
    (hms : ms.map Prod.fst = (c.tGens :: c.lat).map (List.map P.code))
    (hIm : ∀ m ∈ ms, chainInj n m.2.1 = true) (hcl : ∀ m ∈ ms, closedMG n c.depth m = true) :
    ms.length = (c.members RN.enc).length ∧
    ∀ j (h₁ : j < ms.length) (h₂ : j < (c.members RN.enc).length),
      MemRelG n ms[j] (c.members RN.enc)[j] := by
  have hlen : ms.length = (c.tGens :: c.lat).length := by
    have := congrArg List.length hms
    simpa using this
  simp only [LatCert.members, List.length_map]
  refine ⟨hlen, fun j h₁ h₂ => ?_⟩
  simp only [List.getElem_map]
  have e : ms[j].1 = (c.tGens :: c.lat)[j].map P.code := by
    have := congrArg (fun l => l[j]?) hms
    simp only [List.getElem?_map, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
      Option.map_some, Option.some.injEq] at this
    exact this
  exact (memG_spec hn _ _ e (hIm _ (List.getElem_mem h₁)) (hcl _ (List.getElem_mem h₁))).2.2

theorem coverOK_ofG (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (c : LatCert (Perm (Fin n))) {K : ℕ} {lab : List ℕ} {Tm : MemG}
    (hMin : ∀ σ, InC n C σ ↔ RN.enc σ ∈ bfsSet (c.mGens.map RN.enc) c.depth)
    (hMcl : closedH (c.mGens.map RN.enc) (bfsSet (c.mGens.map RN.enc) c.depth) = true)
    (hMsz : (bfsSet (c.mGens.map RN.enc) c.depth).size = chainF C)
    (hTm : Tm.1 = c.tGens.map P.code) (hTI : chainInj n Tm.2.1 = true)
    (hTc : closedMG n c.depth Tm = true) (hT : ∀ g ∈ c.tGens, InC n C g)
    (h : coverG n C (chainF C) Tm K lab (repsCode c) = true) :
    c.coverOK RN.enc = true := by
  classical
  have hC := chainP_lvOK (chainP_of_ok hok hI)
  obtain ⟨hTG, hTcl', hTrel⟩ := memG_spec hn Tm c.tGens hTm hTI hTc
  have hTok : chainOK n Tm.2.1 = true := (P.andB_iff.1 hTc).1
  have hTCP := chainP_of_ok hTok hTI
  have hKT := mem_closure_iff_H (rawIsEnc n) c.tGens c.depth hTrel.2.2.2
  have hKM := mem_closure_iff_H (rawIsEnc n) c.mGens c.depth hMcl
  set Ts : Finset (Perm (Fin n)) :=
    Finset.univ.filter fun τ => τ ∈ Subgroup.closure {g | g ∈ c.tGens} with hTs
  set Ms : Finset (Perm (Fin n)) :=
    Finset.univ.filter fun τ => τ ∈ Subgroup.closure {g | g ∈ c.mGens} with hMs
  have hTiff : ∀ σ, σ ∈ Ts ↔ RN.enc σ ∈ bfsSet (c.tGens.map RN.enc) c.depth := fun σ => by
    rw [hTs, Finset.mem_filter, hKT]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hTin : ∀ σ, σ ∈ Ts ↔ InC n Tm.2.1 σ := fun σ => by
    rw [hTs, Finset.mem_filter, hTcl']
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
  unfold coverG at h
  rw [P.andB_iff, P.andB_iff] at h
  obtain ⟨hA, hD, hN⟩ := h
  unfold coverA at hA
  rw [P.andB_iff, allA_eq_true] at hA
  obtain ⟨hlab, c1⟩ := hA
  unfold labOK at hlab
  rw [P.andB_iff, P.andB_iff, hTm] at hlab
  have hlabT := lab_closure hn hlab.2.2
  have hTC := chainP_lvOK hTCP
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
  have hcTs : Ts.card = chainF Tm.2.1 := by
    rw [← card_inC hn hTok hTI, hTs, ← natCard_sub]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => (hTcl' σ).symm)
  have hcMs : Ms.card = chainF C := by
    rw [← hMsz, ← card_closure_of_closedH (rawIsEnc n) c.mGens c.depth hMcl, hMs, ← natCard_sub]
  have hcode : ∀ ρ τ ρ' : Perm (Fin n), P.mul n (P.mul n (P.inv n (P.code ρ)) (P.code τ))
      (P.code ρ') = P.code (ρ⁻¹ * τ * ρ') := fun ρ τ ρ' => by
    rw [P.code_inv hn, P.code_mul hn, P.code_mul hn]
  have hrM : ∀ r ∈ c.reps.map Prod.fst, r ∈ Ms := fun r hr => by
    obtain ⟨rr, hrr, rfl⟩ := List.mem_map.1 hr
    have := c1 _ (by unfold repsCode; exact List.mem_map_of_mem hrr)
    exact (hMiff _).2 ((inC_iff hn hC _).1 this)
  have hd : (c.reps.map Prod.fst).Pairwise fun r r' => ∀ t ∈ Ts, r⁻¹ * t * r' ∉ Ts := by
    have c2' := (recPair (fun r r' : ℕ × ℕ × List (List ℕ) =>
      CFSG.KC.Ord.orB (CFSG.KC.Ord.notB (Nat.beq (incK n K lab r.1) (incK n K lab r'.1)))
        (allChain n Tm.2.1 fun t => CFSG.KC.Ord.notB
          (memG n Tm (P.mul n (P.mul n (P.inv n r.1) t) r'.1)))) (repsCode c)).1 hD
    unfold repsCode at c2'
    rw [List.pairwise_map] at c2'
    rw [List.pairwise_map]
    refine c2'.imp fun {a b} hab t ht hin => ?_
    dsimp only at hab
    rcases P.orB_iff.1 hab with h1 | h2
    · rw [P.notB_iff, P.beq_iff] at h1
      apply h1
      have eb : b.1 = t⁻¹ * a.1 * (a.1⁻¹ * t * b.1) := by group
      have htT : t⁻¹ ∈ Subgroup.closure {g | g ∈ c.tGens} :=
        Subgroup.inv_mem _ (Finset.mem_filter.1 ht).2
      have ht'T : a.1⁻¹ * t * b.1 ∈ Subgroup.closure {g | g ∈ c.tGens} := (Finset.mem_filter.1 hin).2
      change incK n K lab (P.code a.1) = incK n K lab (P.code b.1)
      rw [eb, incK_conj hn a.1 (hlabT _ htT) (hlabT _ ht'T)]
    · have := allChain_sound hn hTC _ h2 t ((hTin t).1 ht)
      rw [LK.code_eq_P, hcode, P.notB_iff, hTG, ← hTin] at this
      exact this hin
  have hterm : ∀ ρ : Perm (Fin n), CFSG.KC.Loop.strictN
      (CFSG.KC.LQT.PH.cntFrom n Tm.2.1
        (fun t => memG n Tm (P.mul n (P.mul n (P.inv n (P.code ρ)) t) (P.code ρ))) (P.one n))
      (fun k => Bool.rec (motive := fun _ => ℕ) (Nat.add (chainF C) 1)
        (Nat.div (Nat.mul (chainF Tm.2.1) (chainF Tm.2.1)) k)
        (Nat.beq (Nat.mod (Nat.mul (chainF Tm.2.1) (chainF Tm.2.1)) k) 0)) = (dcos Ts ρ).card := by
    intro ρ
    rw [strictN_eq, P.code_one, cntFrom_sound hn _ hTCP 1]
    have hk : (Finset.univ.filter fun σ => InC n Tm.2.1 σ ∧ memG n Tm
        (P.mul n (P.mul n (P.inv n (P.code ρ)) (P.code (1 * σ))) (P.code ρ)) = true) =
        Ts.filter fun t => ρ⁻¹ * t * ρ ∈ Ts := by
      ext σ
      rw [Finset.mem_filter, Finset.mem_filter, one_mul, hcode, hTG]
      exact ⟨fun h => ⟨(hTin σ).2 h.2.1, (hTin _).2 h.2.2⟩,
        fun h => ⟨Finset.mem_univ _, (hTin σ).1 h.1, (hTin _).1 h.2⟩⟩
    rw [hk]
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
    unfold coverN at hN
    rw [P.beq_iff] at hN
    rw [hcMs, ← hN, recSum]
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

theorem latG_sound (hn : n ≤ 32) (C : List Lvl) (MW : List (List (List ℕ))) (k : ℕ)
    (T : List (List ℕ)) (L : ℕ) (ms : List MemG) (K : ℕ) (lab : List ℕ)
    (hI : chainInj n C = true) (hIm : allA ms (fun m => chainInj n m.2.1) = true)
    (c : LatCert (Perm (Fin n)))
    (h : latG n C c.depth (c.mGens.map P.code) MW k T L (c.tGens.map P.code)
      (c.lat.map (List.map P.code)) ms K lab (repsCode c) c.joins c.sizes c.msize = true) :
    c.check RN.enc = true := by
  unfold latG at h
  simp only [P.andB_iff] at h
  obtain ⟨h0, hok, hM, h3, h4, h5, h6, h7, h8⟩ := h
  rw [allA_eq_true] at h3 hIm
  have hC := chainP_lvOK (chainP_of_ok hok hI)
  have hms := memsOKG_iff h0
  obtain ⟨hlen, hrel⟩ := membersG_rel hn c ms hms hIm h3
  obtain ⟨g1, g2⟩ := grpT_sound hn hok hI c.mGens hM
  obtain ⟨hmem, hMsz, hMcl⟩ := grp_spec hn hok hI c.mGens c.depth g1 g2
  have hMin : ∀ σ, InC n C σ ↔ RN.enc σ ∈ bfsSet (c.mGens.map RN.enc) c.depth := fun σ =>
    ⟨fun h => (hmem _).2 ⟨σ, h, rfl⟩, fun h => by
      obtain ⟨τ, hτ, e⟩ := (hmem _).1 h
      exact RN.enc_inj e ▸ hτ⟩
  have hT : ∀ g ∈ c.tGens, InC n C g := by
    unfold tleC at h8
    rw [P.allL_map] at h8
    exact fun g hg => (inC_iff hn hC g).1 (h8 g hg)
  obtain ⟨m0, ms', rfl⟩ : ∃ m0 ms', ms = m0 :: ms' := by
    cases ms with
    | nil => simp at hms
    | cons m0 ms' => exact ⟨m0, ms', rfl⟩
  have hm0 : m0.1 = c.tGens.map P.code := by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at hms
    exact hms.1
  change coverG n C (chainF C) m0 K lab (repsCode c) = true at h4
  unfold LatCert.check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, coverOK_ofG hn hok hI c hMin hMcl hMsz hm0 (hIm _ List.mem_cons_self)
    (h3 _ List.mem_cons_self) hT h4⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    unfold LatCert.closedOK
    rw [Bool.and_eq_true, List.all_eq_true]
    refine ⟨hMcl, fun q hq => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    exact (hrel j (by omega) hj).2.2.2
  ·
    unfold repsG at h5
    rw [allA_eq_true] at h5
    unfold LatCert.repsOK
    dsimp only
    rw [List.all_eq_true]
    intro r hr
    have := h5 _ (by unfold repsCode; exact List.mem_map_of_mem hr)
    dsimp only at this
    rw [LK.getO_eq] at this
    rcases opt_rel hlen hrel r.2.1 with ⟨e1, e2⟩ | ⟨p, q, e1, e2, hR⟩
    · rw [e1] at this
      exact absurd this Bool.false_ne_true
    · rw [e1] at this
      rw [e2]
      change eqCert RN.enc q.2 (c.tGens ++ [r.1]) q.1 r.2.2 = true
      exact eqG_sound hn hR.2.1 _ _ _ (by rw [List.map_append]; rfl) hR.1 this
  ·
    unfold joinsG at h6
    rw [P.andB_iff, P.allN_iff, allA_eq_true, LK.lenA_eq] at h6
    obtain ⟨j1, j2⟩ := h6
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
      exact eqG_sound hn rc.2.1 _ _ _ (by rw [ra.1, rb.1, List.map_append]; rfl) rc.1 this
  ·
    unfold sizesG at h7
    rw [P.andB_iff, LK.eqL_iff, P.beq_iff] at h7
    obtain ⟨e0, e2⟩ := h7
    have e1 : (m0 :: ms').map (fun m : MemG => chainF m.2.1) = c.sizes :=
      (LK.recMap (fun m : MemG => chainF m.2.1) _).symm.trans e0
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

theorem containsG_sound (hn : n ≤ 32) (ms : List MemG)
    (hIm : allA ms (fun m => chainInj n m.2.1) = true) (c : LatCert (Perm (Fin n)))
    (A : List (Perm (Fin n))) {d k s : ℕ}
    (h : containsG n d (c.tGens.map P.code) (c.lat.map (List.map P.code)) ms c.sizes
      (A.map P.code) k s = true) :
    (List.range k).all (fun j => c.sizes.getD j 0 != s ||
      A.all fun g => (elts (RN.enc : Perm (Fin n) → RN n) d ((c.tGens :: c.lat).getD j [])).contains
        (RN.enc g)) = true := by
  unfold containsG at h
  rw [P.andB_iff, P.allN_iff] at h
  obtain ⟨h0, hall⟩ := h
  rw [allA_eq_true] at hIm
  have hms := memsOKG_iff h0
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  have hj' := hall j hj
  rw [P.orB_iff, P.notB_iff, P.beq_iff, LK.getO_eq, getK_getD'] at hj'
  rw [Bool.or_eq_true]
  rcases hj' with e | e
  · left
    rw [bne_iff_ne]
    exact e
  · right
    rw [List.all_eq_true]
    intro g hg
    rw [Std.HashSet.contains_iff_mem]
    cases hp : ms[j]? with
    | none =>
      rw [hp] at e
      change P.allL (A.map P.code) (fun g => Nat.beq g (P.one n)) = true at e
      rw [P.allL_map] at e
      have hg1 := e g hg
      rw [P.beq_iff, P.code_one, P.code_eq_iff hn] at hg1
      subst hg1
      have hL : (c.tGens :: c.lat).getD j [] = [] := by
        have := congrArg List.length hms
        rw [List.getElem?_eq_none_iff] at hp
        simp only [List.length_map] at this
        exact List.getD_eq_default _ _ (by omega)
      rw [hL]
      have := mem_bfsSet_prod (G := Perm (Fin n)) RN.enc_mul RN.enc_one [] d []
        (fun _ h => absurd h List.not_mem_nil) (Nat.zero_le _)
      rw [List.prod_nil] at this
      exact this
    | some m =>
      rw [hp] at e
      obtain ⟨hc, hA⟩ := P.andB_iff.1 e
      have hjm : j < ms.length := by
        by_contra hh
        rw [List.getElem?_eq_none (by omega)] at hp
        exact absurd hp (by simp)
      have hmj : ms[j] = m := by
        rw [List.getElem?_eq_getElem hjm] at hp
        exact Option.some.inj hp
      have hlen : ms.length = (c.tGens :: c.lat).length := by
        have := congrArg List.length hms
        simpa using this
      have hm1 : m.1 = ((c.tGens :: c.lat)[j]'(by omega)).map P.code := by
        have := congrArg (fun l => l[j]?) hms
        simp only [List.getElem?_map, hp, List.getElem?_eq_getElem (show j < (c.tGens :: c.lat).length by omega),
          Option.map_some, Option.some.injEq] at this
        exact this
      have hR := (memG_spec hn m _ hm1 (hIm m (hmj ▸ List.getElem_mem hjm)) hc).2.2
      rw [P.allL_map] at hA
      have hgd : (c.tGens :: c.lat).getD j [] = (c.tGens :: c.lat)[j]'(by omega) := by
        rw [List.getD_eq_getElem]
      rw [hgd]
      exact (hR.2.1 g).1 (hA g hg)

end CFSG.KC.LQT.CM

end
