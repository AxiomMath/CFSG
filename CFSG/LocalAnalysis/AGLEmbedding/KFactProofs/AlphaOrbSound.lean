module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbDefs

public section

namespace CFSG.AGLEmbedding.R3

open scoped IsMulCommutative

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

section Pre

variable {X : Type} [Group X] {p n : ℕ}

@[expose] def preElt (a : Fin n → X) (c : Fin n → ZMod p) : X :=
  ((List.finRange n).map fun k => a k ^ (c k).val).prod

theorem pre_isMulCommutative {a : Fin n → X} (hcomm : ∀ i j, a i * a j = a j * a i) :
    IsMulCommutative (Subgroup.closure (Set.range a)) :=
  Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact hcomm i j)

theorem preElt_eq_prod {a : Fin n → X} [IsMulCommutative (Subgroup.closure (Set.range a))]
    (c : Fin n → ZMod p) :
    preElt a c = ((∏ k, (⟨a k, Subgroup.subset_closure ⟨k, rfl⟩⟩ :
      Subgroup.closure (Set.range a)) ^ (c k).val : Subgroup.closure (Set.range a)) : X) := by
  rw [Fin.prod_univ_def, SubmonoidClass.coe_list_prod, List.map_map]
  rfl

theorem preElt_zero (a : Fin n → X) : preElt a (0 : Fin n → ZMod p) = 1 := by
  simp [preElt]

theorem preElt_add [NeZero p] {a : Fin n → X} (hcomm : ∀ i j, a i * a j = a j * a i)
    (hpow : ∀ i, a i ^ p = 1) (c d : Fin n → ZMod p) :
    preElt a (c + d) = preElt a c * preElt a d := by
  have := pre_isMulCommutative hcomm
  simp only [preElt_eq_prod, ← Subgroup.coe_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  exact CoverCore.pow_val_add (Subtype.ext (hpow k)) _ _

theorem preElt_nsmul [NeZero p] {a : Fin n → X} (hcomm : ∀ i j, a i * a j = a j * a i)
    (hpow : ∀ i, a i ^ p = 1) (c : Fin n → ZMod p) (m : ℕ) :
    preElt a (m • c) = preElt a c ^ m := by
  induction m with
  | zero => rw [zero_smul, preElt_zero, pow_zero]
  | succ m ih => rw [succ_nsmul, preElt_add hcomm hpow, ih, pow_succ]

theorem preElt_list_sum [NeZero p] {a : Fin n → X} (hcomm : ∀ i j, a i * a j = a j * a i)
    (hpow : ∀ i, a i ^ p = 1) (v : Fin n → (Fin n → ZMod p)) :
    ∀ l : List (Fin n), (l.map fun k => preElt a (v k)).prod = preElt a (l.map v).sum
  | [] => by simp [preElt_zero]
  | k :: l => by
    simp only [List.map_cons, List.prod_cons, List.sum_cons, preElt_add hcomm hpow,
      preElt_list_sum hcomm hpow v l]

theorem pre_conj_elt [NeZero p] {a : Fin n → X} (hcomm : ∀ i j, a i * a j = a j * a i)
    (hpow : ∀ i, a i ^ p = 1) {g : X} {A : Matrix (Fin n) (Fin n) (ZMod p)}
    (hg : ∀ i, g * a i * g⁻¹ = preElt a (fun k => A k i)) (c : Fin n → ZMod p) :
    g * preElt a c * g⁻¹ = preElt a (A.mulVec c) := by
  have h1 : g * preElt a c * g⁻¹ = (MulAut.conj g) (preElt a c) := (MulAut.conj_apply g _).symm
  rw [h1, preElt, map_list_prod, List.map_map]
  set w : Fin n → (Fin n → ZMod p) := fun k => (c k).val • fun r => A r k with hw
  have h2 : ∀ k : Fin n, ((MulAut.conj g) ∘ fun k => a k ^ (c k).val) k = preElt a (w k) := by
    intro k
    rw [hw, preElt_nsmul hcomm hpow, ← hg k]
    simp [Function.comp_apply, MulAut.conj_apply]
  rw [List.map_congr_left (fun k _ => h2 k), preElt_list_sum hcomm hpow w]
  congr 1
  rw [← Fin.sum_univ_def]
  funext r
  have hw' : ∀ k, w k r = c k * A r k := by
    intro k
    rw [hw]
    show ((c k).val • fun r => A r k) r = _
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
  rw [Finset.sum_apply]
  simp only [hw', Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end Pre

@[expose] def vecOf (p n : ℕ) (c : List ℕ) : Fin n → ZMod p :=
  fun k => ((c.getD k.val 0 : ℕ) : ZMod p)

theorem vecOf_matVecL (p n : ℕ) (M c : List ℕ) :
    vecOf p n (matVecL p n M c) = (toMatL p n M).mulVec (vecOf p n c) := by
  funext k
  have hk : k.val < n := k.2
  simp only [vecOf, matVecL, Matrix.mulVec, dotProduct, toMatL]
  rw [getD_map_range _ n k.val hk, foldl_add_range, ZMod.natCast_mod, zero_add, Nat.cast_sum,
    Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by simp

theorem orbChk_good {X : Type} [Group X] {p : ℕ} [NeZero p] (m : NMod)
    (a : Fin m.basis.length → X) (gOf : NAct → X) (hcomm : ∀ i j, a i * a j = a j * a i)
    (hpow : ∀ i, a i ^ p = 1)
    (hg : ∀ g ∈ m.acts, ∀ i, gOf g * a i * (gOf g)⁻¹ =
      preElt a (fun k => actMatN p m.basis.length g k i)) (target : List (List ℕ)) :
    ∀ (orb : List (ℕ × ℕ)) (known : List (List ℕ)),
      (∀ c ∈ known, preElt a (vecOf p m.basis.length c) ≠ 1) →
      m.orbChk p target known orb = true →
      ∀ c ∈ target, preElt a (vecOf p m.basis.length c) ≠ 1
  | [], known, hk, h => by
    intro c hc
    simp only [NMod.orbChk, List.all_eq_true] at h
    exact hk c (List.mem_of_elem_eq_true (h c hc))
  | (j, par) :: rest, known, hk, h => by
    simp only [NMod.orbChk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hj, hpar⟩, hrest⟩ := h
    refine orbChk_good m a gOf hcomm hpow hg target rest _ ?_ hrest
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hk c hc
    · rw [List.mem_singleton] at hc
      subst hc
      have hgmem : m.acts.getD j default ∈ m.acts := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
        exact List.getElem_mem hj
      have hmem : known.getD par [] ∈ known := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpar, Option.getD_some]
        exact List.getElem_mem hpar
      rw [vecOf_matVecL, ← actMatN_eq_toMatL, ← pre_conj_elt hcomm hpow (hg _ hgmem)]
      intro heq
      apply hk _ hmem
      have h2 : gOf (m.acts.getD j default) *
          preElt a (vecOf p m.basis.length (known.getD par [])) = gOf (m.acts.getD j default) :=
        mul_inv_eq_one.1 heq
      simpa using h2

section Module

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {C : MCert} (hC : mcertCheck O sA sB C = true) {p : ℕ}

include Sp hC in
theorem wordUnit_word_eq_preElt [Fact p.Prime] {m : NMod} (hf : ∀ f ∈ m.facts p, f ∈ C.facts)
    (l : List ℕ) :
    wordUnit Sp hC (m.word l) =
      preElt (fun k : Fin m.basis.length => regUnit Sp hC (m.basis.getD k.val 0))
        (vecOf p m.basis.length l) := by
  have hpow : ∀ k : Fin m.basis.length, regUnit Sp hC (m.basis.getD k.val 0) ^ p = 1 :=
    fun k => regUnit_pow Sp hC (basis_ord_N hf k.2)
  unfold wordUnit NMod.word preElt
  rw [List.map_map]
  simp only [vecOf]
  rw [map_finRange_val m.basis.length
    (fun j => regUnit Sp hC (m.basis.getD j 0) ^ ((l.getD j 0 : ℕ) : ZMod p).val)]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have hjn : j < m.basis.length := List.mem_range.1 hj
  simp only [Function.comp_apply, ZMod.val_natCast]
  exact pow_eq_pow_mod _ (hpow ⟨j, hjn⟩)

include Sp hC in
theorem indep_O [Fact p.Prime] {m : NMod} (hf : ∀ f ∈ m.facts p, f ∈ C.facts)
    {orb : List (ℕ × ℕ)} (hw : m.wfO p orb = true) (cc : Fin m.basis.length → ZMod p)
    (h1 : ((List.finRange m.basis.length).map fun k =>
      regUnit Sp hC (m.basis.getD k.val 0) ^ (cc k).val).prod = 1) : cc = 0 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set a : Fin m.basis.length → (certMonoid c d sA sB)ˣ :=
    fun k => regUnit Sp hC (m.basis.getD k.val 0) with ha
  have hpow : ∀ i, a i ^ p = 1 := fun i => regUnit_pow Sp hC (basis_ord_N hf i.2)
  have hcomm : ∀ i j, a i * a j = a j * a i := by
    intro i j
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact comm_lt_N Sp hC hf i.2 j.2 h
    · rw [Fin.ext h]
    · exact (comm_lt_N Sp hC hf j.2 i.2 h).symm
  have hg : ∀ g ∈ m.acts, ∀ i : Fin m.basis.length,
      regUnit Sp hC g.reg * a i * (regUnit Sp hC g.reg)⁻¹ =
        preElt a (fun k => actMatN p m.basis.length g k i) := by
    intro g hgm i
    exact act_N Sp hC hf hgm i
  unfold NMod.wfO at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨-, -⟩, hchk⟩ := hw
  have htest : ∀ l ∈ m.indep.map (·.1), preElt a (vecOf p m.basis.length l) ≠ 1 := by
    intro l hl
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hl
    have hfne : MFact.ne (m.word q.1) [] q.2 ∈ C.facts := by
      apply hf
      simp only [NMod.facts, List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨q, hq, rfl⟩)
    have hne' := regUnit_ne Sp hC hfne (hasOrd_word_N hf q.1) (hasOrd_nil C)
    rw [wordUnit_nil, wordUnit_word_eq_preElt Sp hC hf] at hne'
    exact hne'
  have hgood := orbChk_good m a (fun g => regUnit Sp hC g.reg) hcomm hpow hg _ orb _ htest hchk
  by_contra hne
  obtain ⟨k0, hk0⟩ := Function.ne_iff.1 hne
  set l : List ℕ := List.ofFn fun k => (cc k).val with hl
  have hlen : l.length = m.basis.length := by simp [hl]
  have hlt : ∀ x ∈ l, x < p := by
    intro x hx
    simp only [hl, List.mem_ofFn'] at hx
    obtain ⟨k, rfl⟩ := hx
    exact ZMod.val_lt _
  have hmem : l ∈ allVecs p m.basis.length := (mem_allVecs p _ l).2 ⟨hlen, hlt⟩
  have hnz : ¬ (l.all (· == 0)) = true := by
    intro hall
    have := List.all_eq_true.1 hall (cc k0).val (by simp [hl])
    have h0 : (cc k0).val = 0 := by simpa using this
    exact hk0 ((ZMod.val_eq_zero _).1 h0)
  have htarget : l ∈ (allVecs p m.basis.length).filter fun c => !c.all (· == 0) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simpa using hnz⟩
  have hvec : vecOf p m.basis.length l = cc := by
    funext k
    simp [vecOf, hl]
  apply hgood l htarget
  rw [hvec]
  exact h1

@[expose] noncomputable def NMod.specO [Fact p.Prime] (m : NMod) {orb : List (ℕ × ℕ)}
    (hf : ∀ f ∈ m.facts p, f ∈ C.facts) (hw : m.wfO p orb = true) :
    ModuleSpec (certMonoid c d sA sB)ˣ p where
  n := m.basis.length
  m := m.acts.length
  a := fun i => regUnit Sp hC (m.basis.getD i.val 0)
  g := fun j => regUnit Sp hC (m.acts.get j).reg
  M := fun j => actMatN p m.basis.length (m.acts.get j)
  comm := fun i j => by
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact comm_lt_N Sp hC hf i.2 j.2 h
    · rw [Fin.ext h]
    · exact (comm_lt_N Sp hC hf j.2 i.2 h).symm
  pow := fun i => regUnit_pow Sp hC (basis_ord_N hf i.2)
  indep := fun cc h1 => indep_O Sp hC hf hw cc h1
  act := fun j i => act_N Sp hC hf (List.get_mem _ _) i

end Module

section Main

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {nregs : ℕ} {prog : List Op} {p : ℕ} {m : NMod} {tops : List Pc}
  {tidx : List ℕ} {orb : List (ℕ × ℕ)} {cf : ℕ → ℕ → ℕ → ℤ} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}
  {ct : ℕ → ℕ → ℕ → ℕ → ℤ}

include Sp in
theorem moduleDatum_of_modCheckV [Finite (NativeSporadic.seedMonoid c d 1 sA sB)ˣ] (hp : p.Prime)
    {N s : ℕ} (hN : Nat.card (NativeSporadic.seedMonoid c d 1 sA sB)ˣ = N)
    (hv : p ^ s ∣ N ∧ ¬ p ^ (s + 1) ∣ N)
    (h : modCheckV O sA sB nregs prog p m tops tidx s orb cf ci ct = true) :
    ModuleDatum (NativeSporadic.seedMonoid c d 1 sA sB)ˣ p := by
  have : Fact p.Prime := ⟨hp⟩
  unfold modCheckV at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, hw⟩, hpcwf⟩, hacts⟩, hwok⟩, hrank⟩, hfun⟩, halt⟩ := h
  let C : MCert := ⟨nregs, prog, m.modFactsW p tops⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have hf : ∀ f ∈ m.facts p, f ∈ C.facts := by
    intro f hf
    show f ∈ m.modFactsW p tops
    simp only [NMod.modFactsW, List.mem_append]
    exact Or.inl hf
  have hpcf : ∀ q ∈ tops ++ m.basisPc p, ∀ f ∈ q.facts p, f ∈ C.facts := by
    intro q hq f hqf
    show f ∈ m.modFactsW p tops
    unfold NMod.modFactsW
    refine List.mem_append.2 (Or.inr ?_)
    exact List.mem_flatMap.2 ⟨q, hq, hqf⟩
  let DS := NMod.specO Sp hC' m hf hw
  let P : Subgroup (certMonoid c d sA sB)ˣ :=
    Subgroup.closure {u | ∃ q ∈ tops ++ m.basisPc p, u = regUnit Sp hC' q.reg}
  have hPgrp : IsPGroup p P := chain_isPGroup Sp hC' (tops ++ m.basisPc p) hpcwf hpcf
  let qs : List (certMonoid c d sA sB)ˣ := tops.map fun q => regUnit Sp hC' q.reg
  let P' : Subgroup (certMonoid c d sA sB)ˣ := Subgroup.closure ((DS.span : Set _) ∪ {x | x ∈ qs})
  have hspanP : DS.span ≤ P := by
    rw [ModuleSpec.span, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨q, hq, hqreg⟩ : ∃ q ∈ m.basisPc p, q.reg = m.basis.getD i.val 0 :=
      ⟨_, List.mem_map.2 ⟨i.val, List.mem_range.2 i.2, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨q, List.mem_append.2 (Or.inr hq), by rw [hqreg]; rfl⟩
  have hqsP : ∀ x ∈ qs, x ∈ P := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure ⟨q, List.mem_append.2 (Or.inl hq), rfl⟩
  have hP'le : P' ≤ P := (Subgroup.closure_le P).2 (Set.union_subset hspanP hqsP)
  have hP'grp : IsPGroup p P' := IsPGroup.to_le hPgrp hP'le
  have hqsP' : ∀ x ∈ qs, x ∈ P' := fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hspanP' : DS.span ≤ P' := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hP'norm : P' ≤ Subgroup.normalizer (DS.span : Set _) := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact Subgroup.le_normalizer hx
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      obtain ⟨g, hg, hgq⟩ := List.any_eq_true.1 (List.all_eq_true.1 hacts q hq)
      have hgq' : g.reg = q.reg := beq_iff_eq.1 hgq
      obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hg
      have := DS.g_mem_normalizer j
      show regUnit Sp hC' q.reg ∈ _
      rw [← hgq']
      exact this
  unfold NMod.wOK at hwok
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwok
  obtain ⟨hidx, hchk⟩ := hwok
  obtain ⟨hcodes, hs⟩ := pairwise_codes_of_wChk hchk
  set L : List (List ℕ) :=
    wordsL p m.basis.length (tidx.map fun i => (m.acts.getD i default).mat) with hL
  have hget : ∀ i (hi : i < m.acts.length), m.acts.getD i default = m.acts.get ⟨i, hi⟩ := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rfl
  have hgen : ∀ A ∈ tidx.map (fun i => (m.acts.getD i default).mat),
      ∃ q ∈ P', ActsBy DS q (toMatL p DS.n A) := by
    intro A hA
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hA
    obtain ⟨hi1, hi2⟩ := hidx i hi
    obtain ⟨q, hq, hqreg⟩ := List.any_eq_true.1 hi2
    have hqreg' : q.reg = (m.acts.getD i default).reg := beq_iff_eq.1 hqreg
    refine ⟨DS.g ⟨i, hi1⟩, ?_, ?_⟩
    · have hgreg : DS.g ⟨i, hi1⟩ = regUnit Sp hC' (m.acts.get ⟨i, hi1⟩).reg := rfl
      rw [hgreg, ← hget i hi1, ← hqreg']
      exact hqsP' _ (List.mem_map.2 ⟨q, hq, rfl⟩)
    · have := actsBy_g DS ⟨i, hi1⟩
      rw [hget i hi1]
      exact this
  have hall := exists_mem_wordsL DS P' _ hgen
  have hex : ∀ a : Fin L.length, ∃ g ∈ P', ActsBy DS g (toMatL p DS.n (L.get a)) :=
    fun a => hall _ (List.get_mem L a)
  choose g hgP hgA using hex
  have hlen : ∀ a : Fin L.length, (L.get a).length = DS.n * DS.n ∧ ∀ x ∈ L.get a, x < p :=
    fun a => wordsL_spec p DS.n hp.one_lt _ _ (List.get_mem L a)
  have hdiff : ∀ a b : Fin L.length, a.val < b.val →
      toMatL p DS.n (L.get a) ≠ toMatL p DS.n (L.get b) := by
    intro a b hab hM
    have hcode := List.pairwise_iff_getElem.1 hcodes a.val b.val a.2 b.2 hab
    apply hcode
    have := toMatL_inj p DS.n (hlen a).1 (hlen b).1 (hlen a).2 (hlen b).2 hM
    show codeL p (L.get a) = codeL p (L.get b)
    rw [this]
  have hdist : ∀ a b : Fin L.length, a ≠ b →
      toMatL p DS.n (L.get a) ≠ toMatL p DS.n (L.get b) := by
    intro a b hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hdiff a b hlt
    · exact (hdiff b a hlt).symm
  have hlow : L.length * p ^ m.basis.length ≤ Nat.card P' := by
    have h := card_ge_of_actsBy DS P' hspanP' g (fun a => toMatL p DS.n (L.get a)) hgP hgA hdist
    rw [DS.card_span hp] at h
    exact h
  have hN0 : N ≠ 0 := by
    rw [← hN]
    exact Nat.card_pos.ne'
  obtain ⟨k, hk⟩ := hP'grp.exists_card_eq
  have hdvd : Nat.card P' ∣ N := hN ▸ Subgroup.card_subgroup_dvd_card P'
  have hs1 : s ≤ k := by
    have : p ^ s ≤ p ^ k := by
      rw [← hk]
      exact hs.trans hlow
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
  have hs2 : k ≤ s := by
    by_contra hlt
    apply hv.2
    exact (Nat.pow_dvd_pow p (not_le.1 hlt)).trans (hk ▸ hdvd)
  have hkeq : k = s := le_antisymm hs2 hs1
  have hfact : N.factorization p = s := by
    have h1 := (hp.pow_dvd_iff_le_factorization hN0).1 hv.1
    have h2 : ¬ s + 1 ≤ N.factorization p :=
      fun h => hv.2 ((hp.pow_dvd_iff_le_factorization hN0).2 h)
    omega
  have hcard : Nat.card P' = p ^ (Nat.card (certMonoid c d sA sB)ˣ).factorization p := by
    rw [hN, hfact, hk, hkeq]
  exact ⟨DS, hrank, fun B hB hinv => noAlt_of_altOK halt B hB hinv,
    fun v hv' => noFun_of_funOK hfun v hv', Sylow.ofCard P' hcard, hP'norm⟩

end Main

end CFSG.AGLEmbedding.R3
