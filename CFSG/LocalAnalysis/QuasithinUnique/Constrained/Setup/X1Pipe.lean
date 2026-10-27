module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeCert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TwoExt

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm

section Counting

variable {P : Type*} [Group P] [Finite P] {R : Subgroup P} {a b : P} {N : ℕ}

theorem foldl_count (l : List ℕ) (p : ℕ → Bool) (c : ℕ) :
    l.foldl (fun c i => if p i then c + 1 else c) c = c + (l.filter p).length := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.filter_cons]
    by_cases h : p x = true
    · simp only [h, ite_true, ih, List.length_cons]
      omega
    · simp only [h, ih]
      simp

theorem blkSize_eq (N : ℕ) (b : Array Bool) :
    blkSize N b = ((List.range N).filter fun i => b.getD i false).length := by
  unfold blkSize
  rw [foldl_count]
  simp

theorem card_filter_range (N : ℕ) (q : ℕ → Bool) :
    Nat.card {i : ℕ // i < N ∧ q i = true} = ((List.range N).filter q).length := by
  have h1 : {i : ℕ | i < N ∧ q i = true} = ↑((List.range N).filter q).toFinset := by
    ext i
    simp [List.mem_range]
  have h2 : Nat.card {i : ℕ // i < N ∧ q i = true} = Set.ncard {i : ℕ | i < N ∧ q i = true} :=
    (Nat.card_coe_set_eq _).symm
  rw [h2, h1, Set.ncard_coe_finset, List.toFinset_card_of_nodup]
  exact (List.nodup_range).filter _

theorem card_eq_mul_blkSize (C : CosetCert R a b N)
    (hgen : Subgroup.closure ({a, b} : Set P) = ⊤) {V : Subgroup P} (hV : R ≤ V) (bl : Array Bool)
    (hb : ∀ i < N, bl.getD i false = true ↔ C.r i ∈ V) :
    Nat.card V = Nat.card R * blkSize N bl := by
  have h1 : Nat.card (R.subgroupOf V) * (R.subgroupOf V).index = Nat.card V :=
    Subgroup.card_mul_index _
  have h2 : Nat.card (R.subgroupOf V) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv
  have h3 : (R.subgroupOf V).index = Nat.card {i : ℕ // i < N ∧ bl.getD i false = true} := by
    rw [Subgroup.index_eq_card]
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun i => (QuotientGroup.mk (⟨C.r i.1, (hb i.1 i.2.1).1 i.2.2⟩ : V) :
        V ⧸ R.subgroupOf V)) ⟨?_, ?_⟩)
    · intro i j hij
      have hij' := QuotientGroup.eq.1 hij
      rw [Subgroup.mem_subgroupOf] at hij'
      have hcos : ((C.r j.1 : P) : P ⧸ R) = ((C.r i.1 : P) : P ⧸ R) :=
        coset_eq_of_mem (by simpa using hij')
      exact Subtype.ext (cosets_injective C hgen j.2.1 i.2.1 hcos).symm
    · intro q
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨i, hi, hgi⟩ := cosets_exhaust C hgen (v : P)
      have hri : C.r i ∈ V := (mem_iff_of_coset_eq hV hgi).1 v.2
      refine ⟨⟨i, hi, (hb i hi).2 hri⟩, ?_⟩
      apply QuotientGroup.eq.2
      rw [Subgroup.mem_subgroupOf]
      have := mem_of_coset_eq hgi
      simpa using this
  rw [← h1, h2, h3, blkSize_eq, ← card_filter_range N (fun i => bl.getD i false)]

theorem blkFull_iff (C : CosetCert R a b N) (hgen : Subgroup.closure ({a, b} : Set P) = ⊤)
    {V : Subgroup P} (hV : R ≤ V) (bl : Array Bool)
    (hb : ∀ i < N, bl.getD i false = true ↔ C.r i ∈ V) : blkFull N bl ↔ V = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro g _
    obtain ⟨i, hi, hgi⟩ := cosets_exhaust C hgen g
    exact (mem_iff_of_coset_eq hV hgi).2 ((hb i hi).1 (h i hi))
  · intro h i hi
    exact (hb i hi).2 (h ▸ Subgroup.mem_top _)

theorem blkSub_iff (C : CosetCert R a b N) (hgen : Subgroup.closure ({a, b} : Set P) = ⊤)
    {V W : Subgroup P} (hV : R ≤ V) (hW : R ≤ W) (bl bl' : Array Bool)
    (hb : ∀ i < N, bl.getD i false = true ↔ C.r i ∈ V)
    (hb' : ∀ i < N, bl'.getD i false = true ↔ C.r i ∈ W) : blkSub N bl bl' ↔ V ≤ W := by
  constructor
  · intro h g hg
    obtain ⟨i, hi, hgi⟩ := cosets_exhaust C hgen g
    have hri : C.r i ∈ V := (mem_iff_of_coset_eq hV hgi).1 hg
    exact (mem_iff_of_coset_eq hW hgi).2 ((hb' i hi).1 (h i hi ((hb i hi).2 hri)))
  · intro h i hi hbi
    exact (hb' i hi).2 (h ((hb i hi).1 hbi))

end Counting

section Shape

variable {P : Type*} [Group P] [Finite P] {R : Subgroup P} {a b : P} {N : ℕ}

theorem twoMaxOver_of_blocks (C : CosetCert R a b N)
    (hgen : Subgroup.closure ({a, b} : Set P) = ⊤) {m : ℕ} (V : ℕ → Subgroup P)
    (hRV : ∀ h < m, R ≤ V h) (hex : ∀ W : Subgroup P, R ≤ W → ∃ h < m, W = V h)
    (blocks : ℕ → Array Bool)
    (hbl : ∀ h < m, ∀ i < N, ((blocks h).getD i false = true ↔ C.r i ∈ V h))
    (hshape : ∃ h₁ < m, ∃ h₂ < m, ¬ blkFull N (blocks h₁) ∧ ¬ blkFull N (blocks h₂) ∧
      blkSize N (blocks h₁) ≠ blkSize N (blocks h₂) ∧
      (∀ h < m, blkSub N (blocks h₁) (blocks h) →
        blkSub N (blocks h) (blocks h₁) ∨ blkFull N (blocks h)) ∧
      (∀ h < m, blkSub N (blocks h₂) (blocks h) →
        blkSub N (blocks h) (blocks h₂) ∨ blkFull N (blocks h)) ∧
      (∀ h < m, ¬ blkFull N (blocks h) →
        blkSub N (blocks h) (blocks h₁) ∨ blkSub N (blocks h) (blocks h₂))) :
    TwoMaxOver P R := by
  obtain ⟨h₁, hh₁, h₂, hh₂, nf₁, nf₂, hsz, hup₁, hup₂, hlow⟩ := hshape
  have hfull : ∀ h < m, blkFull N (blocks h) ↔ V h = ⊤ := fun h hh =>
    blkFull_iff C hgen (hRV h hh) _ (hbl h hh)
  have hsub : ∀ h < m, ∀ k < m, blkSub N (blocks h) (blocks k) ↔ V h ≤ V k := fun h hh k hk =>
    blkSub_iff C hgen (hRV h hh) (hRV k hk) _ _ (hbl h hh) (hbl k hk)
  have hcard : ∀ h < m, Nat.card (V h) = Nat.card R * blkSize N (blocks h) := fun h hh =>
    card_eq_mul_blkSize C hgen (hRV h hh) _ (hbl h hh)
  have hcoatom : ∀ (h₀ : ℕ), h₀ < m → ¬ blkFull N (blocks h₀) →
      (∀ h < m, blkSub N (blocks h₀) (blocks h) →
        blkSub N (blocks h) (blocks h₀) ∨ blkFull N (blocks h)) → IsCoatom (V h₀) := by
    intro h₀ hh₀ nf hup
    refine ⟨fun h => nf ((hfull h₀ hh₀).2 h), fun W hW => ?_⟩
    obtain ⟨k, hk, rfl⟩ := hex W (le_trans (hRV h₀ hh₀) hW.le)
    rcases hup k hk ((hsub h₀ hh₀ k hk).2 hW.le) with h | h
    · exact absurd ((hsub k hk h₀ hh₀).1 h) (not_le_of_gt hW)
    · exact (hfull k hk).1 h
  have hc₁ := hcoatom h₁ hh₁ nf₁ hup₁
  have hc₂ := hcoatom h₂ hh₂ nf₂ hup₂
  have hRpos : 0 < Nat.card R := Nat.card_pos
  refine ⟨V h₁, V h₂, hRV h₁ hh₁, hRV h₂ hh₂, hc₁, hc₂, ?_, ?_⟩
  · rw [hcard h₁ hh₁, hcard h₂ hh₂]
    exact fun h => hsz (Nat.eq_of_mul_eq_mul_left hRpos h)
  · intro M hRM hMc
    obtain ⟨k, hk, rfl⟩ := hex M hRM
    have hnf : ¬ blkFull N (blocks k) := fun h => hMc.1 ((hfull k hk).1 h)
    have hbelow : ∀ h₀ < m, IsCoatom (V h₀) → V k ≤ V h₀ → V k = V h₀ := by
      intro h₀ hh₀ hc₀ hle
      rcases hle.lt_or_eq with hlt | heq
      · exact absurd (hMc.2 _ hlt) hc₀.1
      · exact heq
    rcases hlow k hk hnf with h | h
    · exact Or.inl (hbelow h₁ hh₁ hc₁ ((hsub k hk h₁ hh₁).1 h))
    · exact Or.inr (hbelow h₂ hh₂ hc₂ ((hsub k hk h₂ hh₂).1 h))

end Shape

section Omega

variable {P : Type} [Group P] {R : Subgroup P} {a b : P} {N : ℕ}

theorem omegaOf_actsOn (C : CosetCert R a b N) {par gen Aa Ab : Array ℕ}
    (htv : treeValid N par gen) (hr : ∀ x, C.r x = treeR a b par gen x)
    (hA : ∀ i, C.Aa i = arrImg Aa i) (hB : ∀ i, C.Ab i = arrImg Ab i) :
    ∀ fuel x, x < N → x ≤ fuel →
      ActsOn C (C.r x) (arrImg (omegaOf N Aa Ab par gen fuel x)) ∧
        N ≤ (omegaOf N Aa Ab par gen fuel x).size := by
  have hrange : ∀ x, x = 0 → ActsOn C (C.r x) (arrImg (Array.range N)) ∧
      N ≤ (Array.range N).size := by
    intro x hx
    subst hx
    exact ⟨by rw [C.r_zero]; exact actsOn_range C, by simp⟩
  have hAact : ActsOn C a (arrImg Aa) := by
    intro i hi
    have h1 := actsOn_a C i hi
    rw [hA i] at h1
    exact h1
  have hBact : ActsOn C b (arrImg Ab) := by
    intro i hi
    have h1 := actsOn_b C i hi
    rw [hB i] at h1
    exact h1
  intro fuel
  induction fuel with
  | zero =>
    intro x hx hxf
    have hx0 : x = 0 := by omega
    simp only [omegaOf]
    exact hrange x hx0
  | succ f ih =>
    intro x hx hxf
    simp only [omegaOf]
    by_cases hx0 : x = 0
    · simp only [hx0, ↓reduceIte]
      exact hrange 0 rfl
    · simp only [hx0, ↓reduceIte]
      have hxpos : 0 < x := Nat.pos_of_ne_zero hx0
      have hpar := (htv.2.2 x hx hxpos)
      obtain ⟨hact, hsz⟩ := ih (par.getD x 0) (lt_trans hpar.1 hx) (by omega)
      have hrx : C.r x = (if gen.getD x 0 = 0 then a else b) * C.r (par.getD x 0) := by
        rw [hr x, hr (par.getD x 0)]
        exact treeR_succ htv hx hxpos
      rw [hrx]
      by_cases hg : gen.getD x 0 = 0
      · simp only [hg, ↓reduceIte]
        exact ⟨actsOn_comp C hAact hact hsz, by simpa [compArr] using hsz⟩
      · simp only [hg, ↓reduceIte]
        exact ⟨actsOn_comp C hBact hact hsz, by simpa [compArr] using hsz⟩

end Omega

section Abstract

variable {P : Type} [Group P] [Finite P] {R : Subgroup P} {a b : P} {N : ℕ}

theorem blocksOf_getD (ROm : List (Array ℕ)) (N : ℕ) (Aa Ab par gen : Array ℕ)
    (xs : Array (List ℕ)) {h : ℕ} (hh : h < xs.size) :
    (blocksOf ROm N Aa Ab par gen xs).getD h #[] =
      bfsVis N (gensOm ROm N Aa Ab par gen (xs.getD h [])) 0 := by
  have e1 : (blocksOf ROm N Aa Ab par gen xs).getD h #[] =
      bfsVis N (gensOm ROm N Aa Ab par gen xs[h]) 0 := by
    unfold blocksOf
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hh]
    rfl
  have e2 : xs.getD h [] = xs[h] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hh]
    rfl
  rw [e1, e2]

theorem twoMaxOver_of_pipeline (C : CosetCert R a b N)
    (hgen : Subgroup.closure ({a, b} : Set P) = ⊤) {par gen Aa Ab repR : Array ℕ}
    {xs : Array (List ℕ)} (htv : treeValid N par gen) (hr : ∀ x, C.r x = treeR a b par gen x)
    (hA : ∀ i, C.Aa i = arrImg Aa i) (hB : ∀ i, C.Ab i = arrImg Ab i)
    (gsR : List (P × Array ℕ)) (ROm : List (Array ℕ)) (hROm : gsR.map Prod.snd = ROm)
    (hR : Subgroup.closure {g | g ∈ gsR.map Prod.fst} = R)
    (hgsR : ∀ p ∈ gsR, ActsOn C p.1 (arrImg p.2)) (hxs : xsOK N xs)
    (hbc : blocksClosed ROm N Aa Ab par gen xs (blocksOf ROm N Aa Ab par gen xs))
    (hrep : repsOK ROm N repR (repList N repR) (repOrbs ROm N (repList N repR)))
    (hclo : closureOK ROm N Aa Ab par gen xs (blocksOf ROm N Aa Ab par gen xs) (repList N repR))
    (hshape : shapeOK N (blocksOf ROm N Aa Ab par gen xs)) : TwoMaxOver P R := by
  subst hROm
  set ROm := gsR.map Prod.snd with hROm
  set blocksArr := blocksOf ROm N Aa Ab par gen xs with hblocksArr
  set reps := repList N repR with hreps
  obtain ⟨hxs0, hxs1, hxs2⟩ := hxs
  have hom : ∀ x < N, ActsOn C (C.r x) (arrImg (omegaOf N Aa Ab par gen x x)) := fun x hx =>
    (omegaOf_actsOn C htv hr hA hB x x hx le_rfl).1
  let ox : ℕ → Array ℕ := fun x => omegaOf N Aa Ab par gen x x
  let gens' : ℕ → List (P × Array ℕ) := fun h => gsR ++ (xs.getD h []).map fun x => (C.r x, ox x)
  have hgs' : ∀ h < xs.size, ∀ p ∈ gens' h, ActsOn C p.1 (arrImg p.2) := by
    intro h hh p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hgsR p hp
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
      exact hom x (hxs2 h hh x hx)
  have hsnd : ∀ h, (gens' h).map Prod.snd = gensOm ROm N Aa Ab par gen (xs.getD h []) := by
    intro h
    simp [gens', gensOm, ox, List.map_append, List.map_map, Function.comp_def, hROm]
  have hRV : ∀ h, R ≤ Subgroup.closure {g | g ∈ (gens' h).map Prod.fst} := by
    intro h
    rw [← hR]
    apply Subgroup.closure_mono
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    exact List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩
  have hsz : blocksArr.size = xs.size := hbc.1
  have hblk : ∀ h < xs.size, blocksArr.getD h #[] =
      bfsVis N ((gens' h).map Prod.snd) 0 ∧
      ClosedOK N ((gens' h).map Prod.snd) 0 (blocksArr.getD h #[]) := by
    intro h hh
    rw [hsnd h, hblocksArr, blocksOf_getD ROm N Aa Ab par gen xs hh]
    exact ⟨rfl, by rw [← blocksOf_getD ROm N Aa Ab par gen xs hh]; exact hbc.2 h hh⟩
  obtain ⟨hrlt, hrmem, hrcl, hrex⟩ := hrep
  have htab : ∀ t ∈ ROm, ∀ i < N, arrImg t i < N := tabs_lt_of_actsOn C hgsR
  have hrepR : ∀ i < N, repR.getD i 0 < N ∧ Reach ROm (repR.getD i 0) i := by
    intro i hi
    obtain ⟨p, hp, hp1, hp2⟩ := hrex i hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
    have hcl := hrcl _ hp
    simp only at hp1 hp2 hcl
    refine ⟨hrlt i hi, ?_⟩
    rw [← hp1]
    exact (bfsVis_iff ROm x N hcl htab (by rw [hp1]; exact hrlt i hi) i).1 ⟨hi, hp2⟩
  have hcl' : ∀ h : Fin xs.size, ∀ x ∈ reps, x < N → ∃ k : Fin xs.size,
      bfsVis N (((gens' h) ++ [(C.r x, ox x)]).map Prod.snd) 0 = blocksArr.getD k #[] ∧
      ClosedOK N (((gens' h) ++ [(C.r x, ox x)]).map Prod.snd) 0 (blocksArr.getD k #[]) := by
    intro h x hx _
    obtain ⟨k, hk, hk1, hk2⟩ := hclo h.1 h.2 x hx
    refine ⟨⟨k, hk⟩, ?_, ?_⟩
    · rw [List.map_append, hsnd]
      exact hk1
    · rw [List.map_append, hsnd]
      exact hk2
  have hinv := inventory_exhaustive C hgen gsR hR hgsR (m := xs.size) (fun h => gens' h.1)
    (fun h p hp => hgs' h.1 h.2 p hp) (fun h p hp => List.mem_append_left _ hp)
    ⟨⟨0, hxs0⟩, by show gens' 0 = gsR; simp only [gens', hxs1, List.map_nil, List.append_nil]⟩
    (fun h => blocksArr.getD h.1 #[])
    (fun h => hblk h.1 h.2) (fun i => repR.getD i 0) hrepR reps hrmem ox hom hcl'
  have hshape' : ∃ h₁ < xs.size, ∃ h₂ < xs.size, ¬ blkFull N (blocksArr.getD h₁ #[]) ∧
      ¬ blkFull N (blocksArr.getD h₂ #[]) ∧
      blkSize N (blocksArr.getD h₁ #[]) ≠ blkSize N (blocksArr.getD h₂ #[]) ∧
      (∀ h < xs.size, blkSub N (blocksArr.getD h₁ #[]) (blocksArr.getD h #[]) →
        blkSub N (blocksArr.getD h #[]) (blocksArr.getD h₁ #[]) ∨
          blkFull N (blocksArr.getD h #[])) ∧
      (∀ h < xs.size, blkSub N (blocksArr.getD h₂ #[]) (blocksArr.getD h #[]) →
        blkSub N (blocksArr.getD h #[]) (blocksArr.getD h₂ #[]) ∨
          blkFull N (blocksArr.getD h #[])) ∧
      (∀ h < xs.size, ¬ blkFull N (blocksArr.getD h #[]) →
        blkSub N (blocksArr.getD h #[]) (blocksArr.getD h₁ #[]) ∨
          blkSub N (blocksArr.getD h #[]) (blocksArr.getD h₂ #[])) := by
    have := hshape
    unfold shapeOK at this
    rw [hsz] at this
    exact this
  refine twoMaxOver_of_blocks C hgen (m := xs.size)
    (fun h => Subgroup.closure {g | g ∈ (gens' h).map Prod.fst}) (fun h _ => hRV h)
    (fun W hW => ?_) (fun h => blocksArr.getD h #[]) (fun h hh i hi => ?_) hshape'
  · obtain ⟨h, hh⟩ := hinv W hW
    exact ⟨h.1, h.2, hh⟩
  · exact block_iff C hgen (gens' h) (hgs' h hh) (hRV h) _ (hblk h hh).1 (hblk h hh).2 hi

end Abstract

section Pipeline

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]

theorem pipeline_twoMaxOver (hn : 0 < n) (a b : Γ)
    (hgen : Subgroup.closure ({a, b} : Set Γ) = ⊤)
    {N : ℕ} {ta tb tai tbi : Array ℕ} {prog qp : List (ℕ × ℕ)} {Aa Ab par gen repR : Array ℕ}
    {xs : Array (List ℕ)} (hta : ta = (tab n a).toArray) (htb : tb = (tab n b).toArray)
    {k m : ℕ} (hcard : Nat.card Γ = 2 ^ k * m) (hm : Odd m) (hNm : N = m)
    (hinv : invValid n ta tb tai tbi) (hslp : slpValidAux prog 2 = true)
    (hqp : qpOK n (slpTabsA ta tb prog) qp) (Ts : Array (List ℕ)) (rpar rcl : Array ℕ)
    (hE : BaseEnumOK n (List.range n) (qp.map fun p => (slpTabsA ta tb prog)[p.1]!)
      (qp.map fun p => (slpTabsA ta tb prog)[p.2]!) Ts rpar rcl)
    (hTs : Ts.size = 2 ^ k) (htv : treeValid N par gen)
    (hedge : edgeOK n N (ptsOf (List.range n) (qp.map fun p => (slpTabsA ta tb prog)[p.1]!)) Ts
      (keyMap n Ts) ta tb Aa Ab (treeTabs n N ta tb par gen)
      (treeInvTabs n N tai tbi par gen) = true)
    (hasz : aszOK N Aa Ab) (hxs : xsOK N xs) (ROm : List (Array ℕ))
    (hROm : qp.map (fun p => (slpTabsA Aa Ab prog)[p.1]!) = ROm)
    (hbc : blocksClosed ROm N Aa Ab par gen xs (blocksOf ROm N Aa Ab par gen xs))
    (hrep : repsOK ROm N repR (repList N repR) (repOrbs ROm N (repList N repR)))
    (hclo : closureOK ROm N Aa Ab par gen xs (blocksOf ROm N Aa Ab par gen xs) (repList N repR))
    (hshape : shapeOK N (blocksOf ROm N Aa Ab par gen xs)) :
    ∃ R : Subgroup Γ, IsPGroup 2 R ∧ ¬ 2 ∣ R.index ∧ TwoMaxOver Γ R := by
  obtain ⟨_, _, hs3, hs4, hinvq⟩ := hinv
  have hta' : tab n a = ta.toList := by rw [hta]
  have htb' : tab n b = tb.toList := by rw [htb]
  have htai' : tab n a⁻¹ = tai.toList :=
    tab_inv_of_inv a ta tai hta' hs3 (fun q hq => (hinvq q hq).1)
  have htbi' : tab n b⁻¹ = tbi.toList :=
    tab_inv_of_inv b tb tbi htb' hs4 (fun q hq => (hinvq q hq).2)
  have htai : tai = (tab n a⁻¹).toArray := by rw [htai']
  have htbi : tbi = (tab n b⁻¹).toArray := by rw [htbi']
  subst hta htb htai htbi
  set E := slpElts a b prog with hEdef
  set NT := slpTabsA (tab n a).toArray (tab n b).toArray prog with hNT
  have hsize : NT.size = prog.length + 2 := slpTabsA_size _ _ _
  have hspec := slp_tabs_spec (n := n) a b prog hslp
  let qs : List (Γ × Γ) := qp.map fun p => (E.getD p.1 1, E.getD p.2 1)
  have hqsinv : ∀ p ∈ qs, p.2 = p.1⁻¹ := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨h1, h2, h3⟩ := hqp q hq
    refine eq_inv_of_img (n := n) _ _ (fun i hi => ?_)
    have := h3 i hi
    rw [← hspec q.1 h1, ← hspec q.2 h2] at this
    exact this
  have hG1 : qs.map (fun p => (tab n p.1).toArray) = qp.map fun p => NT[p.1]! := by
    simp only [qs, List.map_map]
    apply List.map_congr_left
    intro q hq
    exact hspec q.1 (hqp q hq).1
  have hG2 : qs.map (fun p => (tab n p.2).toArray) = qp.map fun p => NT[p.2]! := by
    simp only [qs, List.map_map]
    apply List.map_congr_left
    intro q hq
    exact hspec q.2 (hqp q hq).2.1
  have hE' : BaseEnumOK n (List.range n) (qs.map fun p => (tab n p.1).toArray)
      (qs.map fun p => (tab n p.2).toArray) Ts rpar rcl := by
    rw [hG1, hG2]; exact hE
  obtain ⟨hmemR, hcardR, _⟩ := benum_data qs Ts rpar rcl hqsinv hE'
  set R := Subgroup.closure {x | x ∈ qs.map Prod.fst} with hRdef
  have hGt : genTabs n (qs.map Prod.fst) = qp.map fun p => NT[p.1]! := by
    rw [← hG1]
    simp only [genTabs, List.map_map, Function.comp_def]
  have hmem : ∀ y : Γ, memR n (ptsOf (List.range n) (qp.map fun p => NT[p.1]!)) Ts
      (keyMap n Ts) (tab n y).toArray = true → y ∈ R := by
    intro y hy
    rw [← hGt] at hy
    exact mem_R_of_memR qs Ts hn hmemR y hy
  have hcardR' : Nat.card R = 2 ^ k := by rw [hcardR, hTs]
  have hindex : R.index = m := by
    have h1 := R.card_mul_index
    rw [hcardR', hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hN : Nat.card (Γ ⧸ R) = N := by
    rw [← Subgroup.index_eq_card, hindex, hNm]
  have hN0 : 0 < N := by rw [hNm]; exact hm.pos
  obtain ⟨C, hr, hA, hB⟩ := exists_cert a b R hN hN0 htv _ Ts hmem hedge
  let gsR : List (Γ × Array ℕ) := qp.map fun q => (E.getD q.1 1, (slpTabsA Aa Ab prog)[q.1]!)
  have hfst : gsR.map Prod.fst = qs.map Prod.fst := by
    simp only [gsR, qs, List.map_map, Function.comp_def]
  have hsnd : gsR.map Prod.snd = ROm := by
    rw [← hROm]
    simp only [gsR, List.map_map, Function.comp_def]
  have hRg : Subgroup.closure {g | g ∈ gsR.map Prod.fst} = R := by rw [hfst]
  have hgsR : ∀ p ∈ gsR, ActsOn C p.1 (arrImg p.2) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have hlt : q.1 < (slpTabsA Aa Ab prog).size := by
      rw [slpTabsA_size, ← hsize]
      exact (hqp q hq).1
    exact (slp_actsOn C hA hB hasz prog hslp q.1 hlt).1
  refine ⟨R, IsPGroup.of_card hcardR', ?_,
    twoMaxOver_of_pipeline C hgen htv hr hA hB gsR ROm hsnd hRg hgsR hxs hbc hrep hclo hshape⟩
  rw [hindex]
  exact fun hd => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd)

end Pipeline

end CFSG.QuasithinUnique.Setup.X1
