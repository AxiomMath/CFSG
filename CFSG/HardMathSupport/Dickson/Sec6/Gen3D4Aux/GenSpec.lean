module

public import Certificates.Certificate17201
public import Certificates.Certificate17202
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterElem

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

open CFSG.Open CFSG.AGLEmbedding.ChevOuter

theorem gen_checkI : genCheckI = true :=
  Certificates.certificate17201

theorem gen_checkII : genCheckII = true :=
  Certificates.certificate17202

namespace Realization

variable {X : Type} [Group X] (R : Realization X)

@[expose] def Innr : Subgroup X := Subgroup.closure {x | ∃ k, k < 16 ∧ R.letter k = x}

@[expose] def FixedSet (c : ℕ) : Set X :=
  {x | x ∈ R.Innr ∧ ∃ S : Subgroup X, S ≤ R.Eg c ∧ Nat.card S = 9 ∧ ∀ s ∈ S, Commute s x}

theorem rep_prodP {alph : ℕ → Pr} {altX : ℕ → X} {w : List ℕ}
    (hw : ∀ s ∈ w, R.Rep (alph s) (altX s)) {acc : Pr} {α : X} (hacc : R.Rep acc α) :
    R.Rep (w.foldl (fun acc s => mulP acc (alph s)) acc) (α * (w.map altX).prod) := by
  induction w generalizing acc α with
  | nil => simpa using hacc
  | cons s w ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [← mul_assoc]
    exact ih (fun t ht => hw t (List.mem_cons_of_mem s ht))
      (R.rep_mul hacc (hw s List.mem_cons_self))

theorem rep_prodP' {alph : ℕ → Pr} {altX : ℕ → X} {w : List ℕ}
    (hw : ∀ s ∈ w, R.Rep (alph s) (altX s)) : R.Rep (prodP alph w) (w.map altX).prod := by
  have := R.rep_prodP hw R.rep_one
  rwa [one_mul] at this

theorem getD_mem_or {α : Type*} (a : Array α) (i : ℕ) (d : α) : a.getD i d ∈ a ∨ a.getD i d = d := by
  rw [Array.getD_eq_getD_getElem?]
  cases h : a[i]? with
  | none => exact Or.inr rfl
  | some x => exact Or.inl (Array.mem_of_getElem? h)

theorem wordElt_mem_Innr {w : List ℕ} (hw : ∀ l ∈ w, l < 16) : R.wordElt w ∈ R.Innr := by
  unfold wordElt
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have : R.elt l = R.letter l := by simp [elt, hw l hl]
  rw [this]
  exact Subgroup.subset_closure ⟨l, hw l hl, rfl⟩

variable [Finite X]

theorem ea_mem {c i : ℕ} (hi : i < 3) : R.ea c i ∈ R.Eg c := by
  interval_cases i <;> exact Subgroup.subset_closure (by simp)

theorem pool_fixed {c j : ℕ} (hc : c < 4) (hj : j < 3)
    (h : genPoolCheck c j = true) :
    R.wordElt (pEntry c j).2.2 ∈ R.FixedSet c ∧
      R.wordElt (invWord (pEntry c j).2.2) = (R.wordElt (pEntry c j).2.2)⁻¹ := by
  simp only [genPoolCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.or_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hu6, hv6⟩, hn16⟩, hu3⟩, hv3⟩, huv⟩, hind⟩, hun⟩, hvn⟩, hnn⟩ := h
  have heRep : ∀ s, s < 6 → R.Rep (eAlph c s)
      (if s % 2 = 0 then R.ea c (s / 2) else R.ea c (s / 2) ^ 2) := by
    intro s hs6
    have hi : s / 2 < 3 := by omega
    have hrep : R.Rep (eP c (s / 2)) (R.ea c (s / 2)) := by
      rw [eP_eq hc hi]
      exact R.rep_word _
    by_cases hev : s % 2 = 0
    · simp only [eAlph, hev, if_true]
      exact hrep
    · simp only [eAlph, hev, if_false]
      exact R.rep_pow hrep 2
  have heMem : ∀ s, s < 6 →
      (if s % 2 = 0 then R.ea c (s / 2) else R.ea c (s / 2) ^ 2) ∈ R.Eg c := by
    intro s hs6
    have hi : s / 2 < 3 := by omega
    by_cases hev : s % 2 = 0
    · simp only [hev, if_true]
      exact R.ea_mem hi
    · simp only [hev, if_false]
      exact Subgroup.pow_mem _ (R.ea_mem hi) 2
  have hu := R.rep_prodP' (alph := eAlph c) (w := (pEntry c j).1) fun s hs' => heRep s (hu6 s hs')
  have hv := R.rep_prodP' (alph := eAlph c) (w := (pEntry c j).2.1) fun s hs' =>
    heRep s (hv6 s hs')
  generalize huX : ((pEntry c j).1.map fun s =>
    if s % 2 = 0 then R.ea c (s / 2) else R.ea c (s / 2) ^ 2).prod = uX at hu
  generalize hvX : ((pEntry c j).2.1.map fun s =>
    if s % 2 = 0 then R.ea c (s / 2) else R.ea c (s / 2) ^ 2).prod = vX at hv
  have huE : uX ∈ R.Eg c := by
    rw [← huX]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨s, hs', rfl⟩ := List.mem_map.1 hx
    exact heMem s (hu6 s hs')
  have hvE : vX ∈ R.Eg c := by
    rw [← hvX]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨s, hs', rfl⟩ := List.mem_map.1 hx
    exact heMem s (hv6 s hs')
  have hn : R.Rep (nP c j) (R.wordElt (pEntry c j).2.2) := by
    rw [nP_eq hc hj]
    exact R.rep_word _
  have hninv : R.Rep (nInvP c j) (R.wordElt (invWord (pEntry c j).2.2)) := by
    rw [nInvP_eq hc hj]
    exact R.rep_word _
  have hnn' : R.wordElt (pEntry c j).2.2 * R.wordElt (invWord (pEntry c j).2.2) = 1 :=
    R.rep_ext (R.rep_mul hn hninv) R.rep_one hnn
  have hinv : R.wordElt (invWord (pEntry c j).2.2) = (R.wordElt (pEntry c j).2.2)⁻¹ :=
    eq_inv_of_mul_eq_one_right hnn'
  refine ⟨⟨R.wordElt_mem_Innr hn16, Subgroup.closure {uX, vX}, ?_, ?_, ?_⟩, hinv⟩
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact huE
    · exact hvE
  · have hu3' : uX ^ 3 = 1 := R.rep_ext (R.rep_pow hu 3) R.rep_one hu3
    have hv3' : vX ^ 3 = 1 := R.rep_ext (R.rep_pow hv 3) R.rep_one hv3
    have huv' : Commute uX vX := R.rep_ext (R.rep_mul hu hv) (R.rep_mul hv hu) huv
    have hind' : ∀ a b : ℕ, a < 3 → b < 3 → uX ^ a * vX ^ b = 1 → a = 0 ∧ b = 0 := by
      intro a b ha hb h1
      rcases hind a ha b hb with h | h
      · exact h
      · exact absurd (R.rep_id (h1 ▸ R.rep_mul (R.rep_pow hu a) (R.rep_pow hv b))) h
    obtain ⟨-, -, hcard⟩ := closure_pair uX vX hu3' hv3' huv' hind'
    rw [hcard]
    norm_num
  · have hu' : Commute uX (R.wordElt (pEntry c j).2.2) :=
      R.rep_ext (R.rep_mul hu hn) (R.rep_mul hn hu) hun
    have hv' : Commute vX (R.wordElt (pEntry c j).2.2) :=
      R.rep_ext (R.rep_mul hv hn) (R.rep_mul hn hv) hvn
    have hle : Subgroup.closure {uX, vX} ≤
        Subgroup.centralizer ({R.wordElt (pEntry c j).2.2} : Set X) := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm
      subst hm
      rcases hg with rfl | rfl
      · exact hu'.eq.symm
      · exact hv'.eq.symm
    intro s hs'
    have := Subgroup.mem_centralizer_iff.1 (hle hs') _ (Set.mem_singleton _)
    exact this.symm

theorem gen_spec {c : ℕ} (hc : c < 4) (h : genCheckClass c = true) :
    ∀ k, k < 16 → R.letter k ∈ Subgroup.closure (R.FixedSet c) := by
  simp only [genCheckClass, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨-, hlen⟩, hpool⟩, hr⟩, hslp⟩ := h
  simp only [genRCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  simp only [genSlpCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range] at hslp
  obtain ⟨⟨⟨hrlen, hrsym⟩, hr01⟩, hr23⟩ := hr
  set T := Subgroup.closure (R.FixedSet c) with hT
  have hpf : ∀ j, j < 3 → R.wordElt (pEntry c j).2.2 ∈ T ∧
      R.wordElt (invWord (pEntry c j).2.2) ∈ T := by
    intro j hj
    obtain ⟨h1, h2⟩ := R.pool_fixed hc hj (hpool j hj)
    refine ⟨Subgroup.subset_closure h1, ?_⟩
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure h1)
  have hpRep : ∀ s, s < 6 → R.Rep (pAlph c s) (if s % 2 = 0 then
      R.wordElt (pEntry c (s / 2)).2.2 else R.wordElt (invWord (pEntry c (s / 2)).2.2)) := by
    intro s hs6
    have hj : s / 2 < 3 := by omega
    by_cases hev : s % 2 = 0
    · simp only [pAlph, hev, if_true]
      rw [nP_eq hc hj]
      exact R.rep_word _
    · simp only [pAlph, hev, if_false]
      rw [nInvP_eq hc hj]
      exact R.rep_word _
  have hpMem : ∀ s, s < 6 → (if s % 2 = 0 then
      R.wordElt (pEntry c (s / 2)).2.2 else R.wordElt (invWord (pEntry c (s / 2)).2.2)) ∈ T := by
    intro s hs6
    have hj : s / 2 < 3 := by omega
    by_cases hev : s % 2 = 0
    · simp only [hev, if_true]
      exact (hpf _ hj).1
    · simp only [hev, if_false]
      exact (hpf _ hj).2
  have hrmem : ∀ i, i < 2 → ∀ s ∈ rWord c i, s < 6 := by
    intro i hi s hs'
    refine hrsym _ ?_ s hs'
    have : i < (genRW.getD c []).length := by omega
    show (genRW.getD c []).getD i [] ∈ genRW.getD c []
    rw [List.getD_eq_getElem _ _ this]
    exact List.getElem_mem this
  have hnegsym : ∀ w : List ℕ, (∀ s ∈ w, s < 6) → ∀ s ∈ negW w, s < 6 := by
    intro w hw s hs'
    simp only [negW, List.mem_map, List.mem_reverse] at hs'
    obtain ⟨t, ht, rfl⟩ := hs'
    have := hw t ht
    split_ifs <;> omega
  have hprodmem : ∀ w : List ℕ, (∀ s ∈ w, s < 6) → (w.map fun s => if s % 2 = 0 then
      R.wordElt (pEntry c (s / 2)).2.2 else R.wordElt (invWord (pEntry c (s / 2)).2.2)).prod ∈ T := by
    intro w hw
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨s, hs', rfl⟩ := List.mem_map.1 hx
    exact hpMem s (hw s hs')
  have hrRep : ∀ w : List ℕ, (∀ s ∈ w, s < 6) → ∃ x ∈ T, R.Rep (prodP (pAlph c) w) x := by
    intro w hw
    exact ⟨_, hprodmem w hw, R.rep_prodP' fun s hs' => hpRep s (hw s hs')⟩
  have hbase : ∀ p ∈ rBase c, ∃ x ∈ T, R.Rep p x := by
    intro p hp
    simp only [rBase, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at hp
    have h0 := hrmem 0 (by norm_num)
    have h1 := hrmem 1 (by norm_num)
    rcases hp with rfl | rfl | rfl | rfl
    · exact hrRep _ h0
    · exact hrRep _ (hnegsym _ h0)
    · exact hrRep _ h1
    · exact hrRep _ (hnegsym _ h1)
  have hone : ∃ x ∈ T, R.Rep oneP x := ⟨1, T.one_mem, R.rep_one⟩
  have hstep : ∀ (rules : List (ℕ × ℕ)) (tab : Array Pr), (∀ p ∈ tab, ∃ x ∈ T, R.Rep p x) →
      ∀ p ∈ rules.foldl slpStep tab, ∃ x ∈ T, R.Rep p x := by
    intro rules
    induction rules with
    | nil => intro tab h; exact h
    | cons r rs ih =>
      intro tab h
      apply ih
      intro p hp
      simp only [slpStep, Array.mem_push] at hp
      have hget : ∀ i, ∃ x ∈ T, R.Rep (tab.getD i oneP) x := fun i => by
        rcases getD_mem_or tab i oneP with hm | hm
        · exact h _ hm
        · rw [hm]; exact hone
      rcases hp with hp | rfl
      · exact h p hp
      · obtain ⟨x1, hx1, hr1⟩ := hget r.1
        obtain ⟨x2, hx2, hr2⟩ := hget r.2
        exact ⟨x1 * x2, T.mul_mem hx1 hx2, R.rep_mul hr1 hr2⟩
  have hsym : ∀ s, ∃ x ∈ T, R.Rep (sAlph c s) x := by
    intro s
    unfold sAlph
    rw [symTabs_eq hc]
    rcases getD_mem_or (symTab c) s oneP with hm | hm
    · exact hstep _ _ hbase _ hm
    · rw [hm]; exact hone
  choose xs hxsT hxsR using hsym
  intro k hk
  have hw := R.rep_prodP' (alph := sAlph c) (altX := xs) (w := tWord c k) fun s _ => hxsR s
  have hmemT : ((tWord c k).map xs).prod ∈ T := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
    exact hxsT s
  have hsymk : symP k = (letterArr k, 0) := by simp [symP, hk]
  have heq : R.letter k = ((tWord c k).map xs).prod :=
    R.rep_ext (R.rep_letter hk) hw (by rw [hsymk, hslp.2 k hk])
  rw [heq]
  exact hmemT

end Realization

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
