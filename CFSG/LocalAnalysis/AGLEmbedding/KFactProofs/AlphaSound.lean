module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaLinear
public import CFSG.LocalAnalysis.AGLEmbedding.CoverCore
public import CFSG.RankThree.Asc83Table.MatCert

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

theorem map_finRange_val {α : Type*} (n : ℕ) (h : ℕ → α) :
    (List.finRange n).map (fun k : Fin n => h k.val) = (List.range n).map h := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  rfl

theorem mem_allVecs (p : ℕ) : ∀ (n : ℕ) (l : List ℕ),
    l ∈ allVecs p n ↔ l.length = n ∧ ∀ x ∈ l, x < p
  | 0, l => by
    simp only [allVecs, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.1 h
  | n + 1, l => by
    simp only [allVecs, List.mem_flatMap, List.mem_range, List.mem_map, mem_allVecs p n]
    constructor
    · rintro ⟨a, ha, l', ⟨hl', hlt⟩, rfl⟩
      refine ⟨by simp [hl'], fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact hlt x hx
    · rintro ⟨hlen, hlt⟩
      cases l with
      | nil => simp at hlen
      | cons a l' =>
        refine ⟨a, hlt a (by simp), l',
          ⟨by simpa using hlen, fun x hx => hlt x (by simp [hx])⟩, rfl⟩

section Module

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {C : MCert} (hC : mcertCheck O sA sB C = true) {p : ℕ}

omit [Inhabited M] in
theorem basis_ord_N {m : NMod} (hf : ∀ f ∈ m.facts p, f ∈ C.facts) {i : ℕ}
    (hi : i < m.basis.length) : MFact.ord (m.basis.getD i 0) p ∈ C.facts := by
  apply hf
  simp only [NMod.facts, List.mem_append, List.mem_map]
  refine Or.inl (Or.inl (Or.inl ⟨m.basis.getD i 0, ?_, rfl⟩))
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

omit [Inhabited M] in
theorem hasOrd_word_N {m : NMod} (hf : ∀ f ∈ m.facts p, f ∈ C.facts) (l : List ℕ) :
    HasOrd C (m.word l) := by
  intro q hq
  simp only [NMod.word, List.mem_map, List.mem_range] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  exact ⟨p, basis_ord_N hf hk⟩

omit [Inhabited M] in
theorem hasOrd_col_N {m : NMod} (hf : ∀ f ∈ m.facts p, f ∈ C.facts) (g : NAct) (i : ℕ) :
    HasOrd C (m.col g i) := by
  intro q hq
  simp only [NMod.col, List.mem_map, List.mem_range] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  exact ⟨p, basis_ord_N hf hk⟩

include Sp hC in
theorem comm_lt_N {m : NMod} (hf : ∀ f ∈ m.facts p, f ∈ C.facts) {i j : ℕ}
    (hi : i < m.basis.length) (hj : j < m.basis.length) (hij : i < j) :
    regUnit Sp hC (m.basis.getD i 0) * regUnit Sp hC (m.basis.getD j 0) =
      regUnit Sp hC (m.basis.getD j 0) * regUnit Sp hC (m.basis.getD i 0) := by
  have hmem : MFact.eq [(m.basis.getD i 0, 1), (m.basis.getD j 0, 1)]
      [(m.basis.getD j 0, 1), (m.basis.getD i 0, 1)] ∈ C.facts := by
    apply hf
    simp only [NMod.facts, List.mem_append, NMod.commFacts, List.mem_flatMap, List.mem_map,
      List.mem_filter, List.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨i, hi, j, ⟨hj, by simpa using hij⟩, rfl⟩))
  have hoi := basis_ord_N hf hi
  have hoj := basis_ord_N hf hj
  have hord : ∀ a b : ℕ, MFact.ord a p ∈ C.facts → MFact.ord b p ∈ C.facts →
      HasOrd C [(a, 1), (b, 1)] := by
    intro a b ha hb q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨p, ha⟩
    · exact ⟨p, hb⟩
  have h2 := regUnit_eq Sp hC hmem (hord _ _ hoi hoj) (hord _ _ hoj hoi)
  simpa [wordUnit] using h2

include Sp hC in
theorem indep_N [Fact p.Prime] {m : NMod} (hf : ∀ f ∈ m.facts p, f ∈ C.facts)
    (hw : m.wf p = true) (cc : Fin m.basis.length → ZMod p)
    (h1 : ((List.finRange m.basis.length).map fun k =>
      regUnit Sp hC (m.basis.getD k.val 0) ^ (cc k).val).prod = 1) : cc = 0 := by
  by_contra hne
  set l : List ℕ := List.ofFn fun k => (cc k).val with hl
  have hlen : l.length = m.basis.length := by simp [hl]
  have hlt : ∀ x ∈ l, x < p := by
    intro x hx
    simp only [hl, List.mem_ofFn'] at hx
    obtain ⟨k, rfl⟩ := hx
    exact ZMod.val_lt _
  have hmem : l ∈ allVecs p m.basis.length := (mem_allVecs p _ l).2 ⟨hlen, hlt⟩
  unfold NMod.wf at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
  have h2 := hw.2 l hmem
  rcases Bool.or_eq_true_iff.1 h2 with h3 | h3
  · apply hne
    funext k
    have hk : (cc k).val = 0 := by
      have := List.all_eq_true.1 h3 (cc k).val (by simp [hl])
      simpa using this
    exact (ZMod.val_eq_zero _).1 hk
  · obtain ⟨q, hq, hql⟩ := List.any_eq_true.1 h3
    have hql' : q.1 = l := beq_iff_eq.1 hql
    have hfne : MFact.ne (m.word l) [] q.2 ∈ C.facts := by
      apply hf
      simp only [NMod.facts, List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨q, hq, by rw [hql']⟩)
    have hne' := regUnit_ne Sp hC hfne (hasOrd_word_N hf l) (hasOrd_nil C)
    apply hne'
    rw [wordUnit_nil]
    rw [← h1]
    unfold wordUnit NMod.word
    rw [List.map_map, ← map_finRange_val]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    simp [hl]

include Sp hC in
theorem act_N [Fact p.Prime] {m : NMod} (hf : ∀ f ∈ m.facts p, f ∈ C.facts) {g : NAct}
    (hg : g ∈ m.acts) (i : Fin m.basis.length) :
    regUnit Sp hC g.reg * regUnit Sp hC (m.basis.getD i.val 0) * (regUnit Sp hC g.reg)⁻¹ =
      ((List.finRange m.basis.length).map fun k => regUnit Sp hC (m.basis.getD k.val 0) ^
        (actMatN p m.basis.length g k i).val).prod := by
  have hord : MFact.ord g.reg g.ord ∈ C.facts := by
    apply hf
    simp only [NMod.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨g, hg, by simp⟩
  have hconj : MFact.conj g.reg [(m.basis.getD i.val 0, 1)] (m.col g i.val) ∈ C.facts := by
    apply hf
    simp only [NMod.facts, List.mem_append, List.mem_flatMap]
    refine Or.inr ⟨g, hg, ?_⟩
    simp only [List.mem_cons, List.mem_map, List.mem_range]
    exact Or.inr ⟨i.val, i.2, rfl⟩
  have hu : HasOrd C [(m.basis.getD i.val 0, 1)] := by
    intro q hq
    simp only [List.mem_singleton] at hq
    rw [hq]
    exact ⟨p, basis_ord_N hf i.2⟩
  have h := regUnit_conj Sp hC hconj hord hu (hasOrd_col_N hf g i.val)
  have hpow : ∀ k : Fin m.basis.length, regUnit Sp hC (m.basis.getD k.val 0) ^ p = 1 :=
    fun k => regUnit_pow Sp hC (basis_ord_N hf k.2)
  simp only [wordUnit, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    pow_one] at h
  refine h.trans ?_
  unfold NMod.col
  rw [List.map_map, ← map_finRange_val]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, actMatN, ZMod.val_natCast]
  exact pow_eq_pow_mod _ (hpow k)

@[expose] noncomputable def NMod.spec [Fact p.Prime] (m : NMod) (hf : ∀ f ∈ m.facts p, f ∈ C.facts)
    (hw : m.wf p = true) : ModuleSpec (certMonoid c d sA sB)ˣ p where
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
  indep := fun cc h1 => indep_N Sp hC hf hw cc h1
  act := fun j i => act_N Sp hC hf (List.get_mem _ _) i

end Module


section Main

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {nregs : ℕ} {prog : List Op} {p : ℕ} {m : NMod}
  {cf : ℕ → ℕ → ℕ → ℤ} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ} {ct : ℕ → ℕ → ℕ → ℕ → ℤ}
  {q : List ℕ} {a₁ b₁ : ℕ}

include Sp in
theorem abelianSylowDatum_of_absCheck (hp : p.Prime)
    (h : absCheck O sA sB nregs prog p m cf ci ct q a₁ b₁ = true)
    (hq : IsUnit (qMat p m.basis.length q).det)
    (hX : ¬ p ^ (m.basis.length + 1) ∣ Nat.card (NativeSporadic.seedMonoid c d 1 sA sB)ˣ) :
    AbelianSylowDatum (NativeSporadic.seedMonoid c d 1 sA sB)ˣ p := by
  have : Fact p.Prime := ⟨hp⟩
  unfold absCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hC, hw⟩, hn4⟩, ha⟩, hb⟩, hfun⟩, halt⟩ := h
  have hf : ∀ f ∈ m.facts p, f ∈ (⟨nregs, prog, m.facts p⟩ : MCert).facts := fun f hf => hf
  let D := NMod.spec Sp hC m hf hw
  refine ⟨D, hn4, fun v hv => noFun_of_funOK hfun v hv, fun B hB hinv hne =>
    nondeg_of_altOK ha hb halt hq B hB hinv hne, ?_⟩
  intro hdvd
  apply hX
  have h1 := Subgroup.card_mul_index D.span
  rw [D.card_span hp] at h1
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k, ?_⟩
  have hn : D.n = m.basis.length := rfl
  rw [← h1, hk, hn]
  ring

end Main

end CFSG.AGLEmbedding.R3
