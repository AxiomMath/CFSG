module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalGenUMatDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalGenU
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMGenSound

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.SectionRank
  CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint

private theorem MGenU.conj_mem_closure {G : Type*} [Group G] {S : Set G} {g : G}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure S) {y : G} (hy : y ∈ Subgroup.closure S) :
    g * y * g⁻¹ ∈ Subgroup.closure S := by
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  | mul x y _ _ ihx ihy =>
    have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ih =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ih

private theorem MGenU.mem_normalizer_closure {G : Type*} [Group G] {S : Set G} {g : G}
    (h₁ : ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure S)
    (h₂ : ∀ x ∈ S, g⁻¹ * x * g ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact MGenU.conj_mem_closure h₁ hy
  · intro hy
    have h := MGenU.conj_mem_closure (g := g⁻¹) (by simpa using h₂) hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at h

private theorem MGenU.isPGroup_closure_of_sq_comm {G : Type*} [Group G] {S : Set G}
    (hsq : ∀ x ∈ S, x * x = 1) (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    IsPGroup 2 (Subgroup.closure S) := by
  haveI : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm x hx y hy
  have key : ∀ x ∈ Subgroup.closure S, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hsq x hx
    | one => exact mul_one 1
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := setLike_mul_comm hx hy
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = x * x * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, mul_one]
    | inv x _ ih =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [ih, inv_one]
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  have h := key g.1 g.2
  rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
  exact h

private theorem MGenU.exists_mem_zip {α β : Type*} {l : List α} {l' : List β}
    (h : l.length ≤ l'.length) {x : α} (hx : x ∈ l) : ∃ q ∈ l.zip l', q.1 = x := by
  rw [← List.map_fst_zip h] at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  exact ⟨q, hq, rfl⟩

private theorem MGenU.conj_pair {G : Type*} [Group G] {x u P P' : G} (h₁ : x * u = P * x)
    (h₂ : u * x = x * P') : x * u * x⁻¹ = P ∧ x⁻¹ * u * x = P' :=
  ⟨by rw [mul_inv_eq_iff_eq_mul]; exact h₁, by rw [mul_assoc, h₂, inv_mul_cancel_left]⟩

@[expose] def MGenU.regs {G : Type*} [Group G] (a b : G) (c : MGenU) : List G :=
  c.base.g.regs a b ++ c.ks.map fun k => evalPW a b k.1

@[expose] def MGenU.uEval {G : Type*} [Group G] (a b : G) (c : MGenU) (idx : List ℕ) : G :=
  (idx.map fun j => evalPW a b (c.us.getD j [])).prod

@[expose] def MGenU.uSet {G : Type*} [Group G] (a b : G) (c : MGenU) : Set G :=
  {x | ∃ u ∈ c.us, x = evalPW a b u}

@[expose] def MGenU.nsSet {G : Type*} [Group G] (a b : G) (c : MGenU) : Set G :=
  {x | ∃ n ∈ c.base.g.ns, x = evalPW a b n.1}

@[expose] def MGenU.msSet {G : Type*} [Group G] (a b : G) (c : MGenU) : Set G :=
  {x | ∃ m ∈ c.base.g.ms, x = evalPW a b m.1}

@[expose] def MGenU.ksSet {G : Type*} [Group G] (a b : G) (c : MGenU) : Set G :=
  {x | ∃ k ∈ c.ks, x = evalPW a b k.1}

structure MGenU.Holds {G : Type*} [Group G] (a b : G) (c : MGenU) : Prop where
  base : c.base.g.holdsBase a b
  u_sq : ∀ u ∈ c.us, evalPW a b u * evalPW a b u = 1
  u_comm : ∀ u ∈ c.us, ∀ v ∈ c.us, evalPW a b u * evalPW a b v = evalPW a b v * evalPW a b u
  u_ne : evalPW a b (c.us.getD 0 []) ≠ 1
  z_conj : ∀ q ∈ c.us.zip c.uz,
    evalPW a b c.base.g.z * evalPW a b q.1 * (evalPW a b c.base.g.z)⁻¹ = c.uEval a b q.2.1 ∧
    (evalPW a b c.base.g.z)⁻¹ * evalPW a b q.1 * evalPW a b c.base.g.z = c.uEval a b q.2.2
  k_conj : ∀ k ∈ c.ks, ∀ q ∈ c.us.zip k.2,
    evalPW a b k.1 * evalPW a b q.1 * (evalPW a b k.1)⁻¹ = c.uEval a b q.2.1 ∧
    (evalPW a b k.1)⁻¹ * evalPW a b q.1 * evalPW a b k.1 = c.uEval a b q.2.2
  gen_a : a = evalIdx (c.regs a b) c.base.g.wa
  gen_b : b = evalIdx (c.regs a b) c.base.g.wb

theorem MGenU.evalPW_getD_mem {G : Type*} [Group G] (a b : G) (c : MGenU) (j : ℕ) :
    evalPW a b (c.us.getD j []) ∈ Subgroup.closure (c.uSet a b) := by
  by_cases hj : j < c.us.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact Subgroup.subset_closure ⟨_, List.getElem_mem hj, rfl⟩
  · rw [List.getD_eq_default _ _ (not_lt.1 hj)]
    exact Subgroup.one_mem _

theorem MGenU.uEval_mem {G : Type*} [Group G] (a b : G) (c : MGenU) (idx : List ℕ) :
    c.uEval a b idx ∈ Subgroup.closure (c.uSet a b) := by
  induction idx with
  | nil =>
    have e : c.uEval a b [] = 1 := by simp [MGenU.uEval]
    rw [e]
    exact Subgroup.one_mem _
  | cons j idx ih =>
    have e : c.uEval a b (j :: idx) = evalPW a b (c.us.getD j []) * c.uEval a b idx := by
      simp [MGenU.uEval]
    rw [e]
    exact Subgroup.mul_mem _ (MGenU.evalPW_getD_mem a b c j) ih

theorem MGenU.genUW_of_holds {G : Type} [Group G] {a b : G} {c : MGenU}
    (hp : c.base.g.p.Prime) (huz : c.uz.length = c.us.length)
    (hks : ∀ k ∈ c.ks, k.2.length = c.us.length) (hu0 : c.u0 < c.base.g.ms.length)
    (hmu : (c.base.g.ms.getD c.u0 ([], 0)).1 = c.us.getD 0 [])
    (h : MGenU.Holds a b c) (htop : Subgroup.closure ({a, b} : Set G) = ⊤) :
    GenUW G c.base.g.p := by
  haveI : Fact c.base.g.p.Prime := ⟨hp⟩
  have hzN : evalPW a b c.base.g.z ∈
      Subgroup.normalizer (Subgroup.closure (c.uSet a b) : Set G) := by
    refine MGenU.mem_normalizer_closure ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨q, hq, rfl⟩ := MGenU.exists_mem_zip huz.ge hu
      rw [(h.z_conj q hq).1]
      exact MGenU.uEval_mem a b c _
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨q, hq, rfl⟩ := MGenU.exists_mem_zip huz.ge hu
      rw [(h.z_conj q hq).2]
      exact MGenU.uEval_mem a b c _
  have hkN : ∀ k ∈ c.ks, evalPW a b k.1 ∈
      Subgroup.normalizer (Subgroup.closure (c.uSet a b) : Set G) := by
    intro k hk
    refine MGenU.mem_normalizer_closure ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨q, hq, rfl⟩ := MGenU.exists_mem_zip (hks k hk).ge hu
      rw [(h.k_conj k hk q hq).1]
      exact MGenU.uEval_mem a b c _
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨q, hq, rfl⟩ := MGenU.exists_mem_zip (hks k hk).ge hu
      rw [(h.k_conj k hk q hq).2]
      exact MGenU.uEval_mem a b c _
  refine ⟨evalPW a b c.base.g.z, c.nsSet a b, c.msSet a b, c.ksSet a b,
    Subgroup.closure (c.uSet a b), ?_, ?_, ?_, ?_, hzN, ?_, ?_, ?_⟩
  · exact orderOf_eq_prime h.base.1 h.base.2.1
  · rintro x ⟨n, hn, rfl⟩
    obtain ⟨h4, h5⟩ := h.base.2.2.2.1 n hn
    exact mem_normalizer_zpowers_of _ _ n.2.1 n.2.2 h4 h5
  · rintro x ⟨m, hm, rfl⟩
    obtain ⟨w, hw, hcomm⟩ := h.base.2.2.2.2 m hm
    obtain ⟨hw1, hw2, hw3⟩ := h.base.2.2.1 w hw
    exact ⟨evalPW a b w, hw1, hw2, hw3, hcomm⟩
  · exact MGenU.isPGroup_closure_of_sq_comm
      (by rintro _ ⟨u, hu, rfl⟩; exact h.u_sq u hu)
      (by rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩; exact h.u_comm u hu v hv)
  · intro hbot
    apply h.u_ne
    have hmem : evalPW a b (c.us.getD 0 []) ∈ Subgroup.closure (c.uSet a b) ⊓
        Subgroup.closure (c.nsSet a b ∪ c.msSet a b) := by
      refine Subgroup.mem_inf.2 ⟨MGenU.evalPW_getD_mem a b c 0,
        Subgroup.subset_closure (Or.inr ⟨c.base.g.ms.getD c.u0 ([], 0), ?_, ?_⟩)⟩
      · rw [List.getD_eq_getElem _ _ hu0]
        exact List.getElem_mem hu0
      · rw [hmu]
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  · rintro x ⟨k, hk, rfl⟩
    exact hkN k hk
  · have hregs : ∀ x ∈ c.regs a b,
        x ∈ Subgroup.closure (c.nsSet a b ∪ c.msSet a b ∪ c.ksSet a b) := by
      intro x hx
      simp only [MGenU.regs, PGen.regs, List.mem_append, List.mem_map] at hx
      rcases hx with (⟨n, hn, rfl⟩ | ⟨m, hm, rfl⟩) | ⟨k, hk, rfl⟩
      · exact Subgroup.subset_closure (Or.inl (Or.inl ⟨n, hn, rfl⟩))
      · exact Subgroup.subset_closure (Or.inl (Or.inr ⟨m, hm, rfl⟩))
      · exact Subgroup.subset_closure (Or.inr ⟨k, hk, rfl⟩)
    have ha : a ∈ Subgroup.closure (c.nsSet a b ∪ c.msSet a b ∪ c.ksSet a b) := by
      have h' := evalIdx_mem (c.regs a b) _ hregs c.base.g.wa
      rwa [← h.gen_a] at h'
    have hb : b ∈ Subgroup.closure (c.nsSet a b ∪ c.msSet a b ∪ c.ksSet a b) := by
      have h' := evalIdx_mem (c.regs a b) _ hregs c.base.g.wb
      rwa [← h.gen_b] at h'
    have hle : Subgroup.closure ({a, b} : Set G) ≤
        Subgroup.closure (c.nsSet a b ∪ c.msSet a b ∪ c.ksSet a b) := by
      rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨ha, hb⟩
    rw [htop] at hle
    exact top_le_iff.1 hle

theorem MGenU.baseFacts_subset (c : MGenU) {f : MFact} (hf : f ∈ c.base.baseFacts) :
    f ∈ c.facts := by
  simp [MGenU.facts, hf]

theorem MGenU.mem_facts_sq (c : MGenU) {u : PW} (hu : u ∈ c.us) :
    MFact.eq (pwToWord u ++ pwToWord u) [] ∈ c.facts := by
  have h : MFact.eq (pwToWord u ++ pwToWord u) [] ∈ c.sqFacts := by
    simp only [MGenU.sqFacts, List.mem_map]
    exact ⟨u, hu, rfl⟩
  simp [MGenU.facts, h]

theorem MGenU.mem_facts_comm (c : MGenU) {u v : PW} (hu : u ∈ c.us) (hv : v ∈ c.us) :
    MFact.eq (pwToWord u ++ pwToWord v) (pwToWord v ++ pwToWord u) ∈ c.facts := by
  have h : MFact.eq (pwToWord u ++ pwToWord v) (pwToWord v ++ pwToWord u) ∈ c.commFacts := by
    simp only [MGenU.commFacts, List.mem_flatMap, List.mem_map]
    exact ⟨u, hu, v, hv, rfl⟩
  simp [MGenU.facts, h]

theorem MGenU.mem_facts_ne (c : MGenU) :
    MFact.ne (pwToWord (c.us.getD 0 [])) [] c.ut ∈ c.facts := by
  simp [MGenU.facts]

theorem MGenU.mem_facts_z (c : MGenU) {q : PW × (List ℕ × List ℕ)} (hq : q ∈ c.us.zip c.uz) :
    MFact.eq (pwToWord c.base.g.z ++ pwToWord q.1) (c.uProd q.2.1 ++ pwToWord c.base.g.z) ∈
      c.facts ∧
    MFact.eq (pwToWord q.1 ++ pwToWord c.base.g.z) (pwToWord c.base.g.z ++ c.uProd q.2.2) ∈
      c.facts := by
  have h1 : MFact.eq (pwToWord c.base.g.z ++ pwToWord q.1)
      (c.uProd q.2.1 ++ pwToWord c.base.g.z) ∈ c.zFacts := by
    simp only [MGenU.zFacts, List.mem_flatMap]
    exact ⟨q, hq, by simp⟩
  have h2 : MFact.eq (pwToWord q.1 ++ pwToWord c.base.g.z)
      (pwToWord c.base.g.z ++ c.uProd q.2.2) ∈ c.zFacts := by
    simp only [MGenU.zFacts, List.mem_flatMap]
    exact ⟨q, hq, by simp⟩
  exact ⟨by simp [MGenU.facts, h1], by simp [MGenU.facts, h2]⟩

theorem MGenU.mem_facts_k (c : MGenU) {k : PW × List (List ℕ × List ℕ)} (hk : k ∈ c.ks)
    {q : PW × (List ℕ × List ℕ)} (hq : q ∈ c.us.zip k.2) :
    MFact.eq (pwToWord k.1 ++ pwToWord q.1) (c.uProd q.2.1 ++ pwToWord k.1) ∈ c.facts ∧
    MFact.eq (pwToWord q.1 ++ pwToWord k.1) (pwToWord k.1 ++ c.uProd q.2.2) ∈ c.facts := by
  have h1 : MFact.eq (pwToWord k.1 ++ pwToWord q.1)
      (c.uProd q.2.1 ++ pwToWord k.1) ∈ c.kFacts := by
    simp only [MGenU.kFacts, List.mem_flatMap]
    exact ⟨k, hk, q, hq, by simp⟩
  have h2 : MFact.eq (pwToWord q.1 ++ pwToWord k.1)
      (pwToWord k.1 ++ c.uProd q.2.2) ∈ c.kFacts := by
    simp only [MGenU.kFacts, List.mem_flatMap]
    exact ⟨k, hk, q, hq, by simp⟩
  exact ⟨by simp [MGenU.facts, h1], by simp [MGenU.facts, h2]⟩

theorem MGenU.mem_facts_e1 (c : MGenU) :
    MFact.eq [(0, 1)] (c.idxWord c.base.g.wa) ∈ c.facts := by
  simp [MGenU.facts]

theorem MGenU.mem_facts_e2 (c : MGenU) :
    MFact.eq [(1, 1)] (c.idxWord c.base.g.wb) ∈ c.facts := by
  simp [MGenU.facts]

theorem MGenU.hasOrd_uProd {C : MCert} {e0 e1 : ℕ} (h0 : MFact.ord 0 e0 ∈ C.facts)
    (h1 : MFact.ord 1 e1 ∈ C.facts) (c : MGenU) (idx : List ℕ) : HasOrd C (c.uProd idx) := by
  induction idx with
  | nil => exact hasOrd_nil _
  | cons j idx ih =>
    show HasOrd C (pwToWord (c.us.getD j []) ++ c.uProd idx)
    exact hasOrd_append (hasOrd_pwToWord h0 h1 _) ih

theorem MGenU.hasOrd_reg {C : MCert} {e0 e1 : ℕ} (h0 : MFact.ord 0 e0 ∈ C.facts)
    (h1 : MFact.ord 1 e1 ∈ C.facts) (c : MGenU) (i : ℕ) : HasOrd C (c.regW i) := by
  unfold MGenU.regW
  split_ifs
  · exact hasOrd_regW h0 h1 c.base.g i
  · exact hasOrd_pwToWord h0 h1 _

theorem MGenU.hasOrd_idxWord {C : MCert} {e0 e1 : ℕ} (h0 : MFact.ord 0 e0 ∈ C.facts)
    (h1 : MFact.ord 1 e1 ∈ C.facts) (c : MGenU) (w : List (ℕ × ℕ)) :
    HasOrd C (c.idxWord w) := by
  induction w with
  | nil => exact hasOrd_nil _
  | cons q w ih =>
    obtain ⟨i, e⟩ := q
    show HasOrd C (wordPow (c.regW i) e ++ c.idxWord w)
    exact hasOrd_append (hasOrd_wordPow (MGenU.hasOrd_reg h0 h1 c i) e) ih

section Cert

variable {M V : Type} {O : Ops M V} {pf d : ℕ} (Sp : OpsSpec O pf d) [Inhabited M] {sA sB : String}

theorem MGenU.wordUnit_uProd {C : MCert} (hC : mcertCheck O sA sB C = true) (c : MGenU)
    (idx : List ℕ) :
    wordUnit Sp hC (c.uProd idx) = c.uEval (regUnit Sp hC 0) (regUnit Sp hC 1) idx := by
  induction idx with
  | nil => exact wordUnit_nil Sp hC
  | cons j idx ih =>
    show wordUnit Sp hC (pwToWord (c.us.getD j []) ++ c.uProd idx) = _
    rw [wordUnit_append Sp hC, wordUnit_pwToWord Sp hC, ih]
    simp [MGenU.uEval]

theorem MGenU.wordUnit_reg {C : MCert} (hC : mcertCheck O sA sB C = true) (c : MGenU) (i : ℕ) :
    wordUnit Sp hC (c.regW i) = (c.regs (regUnit Sp hC 0) (regUnit Sp hC 1)).getD i 1 := by
  have hlen : (c.base.g.regs (regUnit Sp hC 0) (regUnit Sp hC 1)).length =
      c.base.g.ns.length + c.base.g.ms.length := by
    simp only [PGen.regs, List.length_append, List.length_map]
  unfold MGenU.regW MGenU.regs
  by_cases hi : i < c.base.g.ns.length + c.base.g.ms.length
  · have hl : i < (c.base.g.regs (regUnit Sp hC 0) (regUnit Sp hC 1)).length := by
      rw [hlen]; exact hi
    rw [if_pos hi, wordUnit_regW Sp hC c.base.g i, List.getD_append _ _ _ _ hl]
  · have hl : (c.base.g.regs (regUnit Sp hC 0) (regUnit Sp hC 1)).length ≤ i := by
      rw [hlen]; omega
    rw [if_neg hi, wordUnit_pwToWord Sp hC, List.getD_append_right _ _ _ _ hl, hlen,
      ← Nat.sub_sub]
    exact (getD_map_evalPW (regUnit Sp hC 0) (regUnit Sp hC 1) c.ks (fun k => k.1) ([], [])
      rfl (i - c.base.g.ns.length - c.base.g.ms.length)).symm

theorem MGenU.wordUnit_idxWord {C : MCert} (hC : mcertCheck O sA sB C = true) (c : MGenU)
    (w : List (ℕ × ℕ)) :
    wordUnit Sp hC (c.idxWord w) = evalIdx (c.regs (regUnit Sp hC 0) (regUnit Sp hC 1)) w := by
  induction w with
  | nil => exact wordUnit_nil Sp hC
  | cons q w ih =>
    obtain ⟨i, e⟩ := q
    show wordUnit Sp hC (wordPow (c.regW i) e ++ c.idxWord w) = _
    rw [wordUnit_append Sp hC, wordUnit_wordPow Sp hC, MGenU.wordUnit_reg Sp hC c i, ih]
    rfl

theorem MGenU.holds_of_facts {C : MCert} (hC : mcertCheck O sA sB C = true) (c : MGenU)
    (htts : c.base.tts.length = c.base.g.ts.length)
    (hms : ∀ m ∈ c.base.g.ms, m.2 < c.base.g.ts.length)
    (hf : ∀ f ∈ c.facts, f ∈ C.facts) :
    MGenU.Holds (regUnit Sp hC 0) (regUnit Sp hC 1) c := by
  have hfb : ∀ f ∈ c.base.baseFacts, f ∈ C.facts := fun f hf' =>
    hf f (MGenU.baseFacts_subset c hf')
  have h0 : MFact.ord 0 c.base.oa ∈ C.facts := hfb _ (mem_base_ord0 c.base)
  have h1 : MFact.ord 1 c.base.ob ∈ C.facts := hfb _ (mem_base_ord1 c.base)
  have hw : ∀ w : PW, HasOrd C (pwToWord w) := hasOrd_pwToWord h0 h1
  refine ⟨MGen.holdsBase_of_facts Sp hC c.base htts hms hfb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have e := regUnit_eq Sp hC (hf _ (MGenU.mem_facts_sq c hu))
      (hasOrd_append (hw _) (hw _)) (hasOrd_nil _)
    rw [wordUnit_append Sp hC, wordUnit_pwToWord Sp hC, wordUnit_nil Sp hC] at e
    exact e
  · intro u hu v hv
    have e := regUnit_eq Sp hC (hf _ (MGenU.mem_facts_comm c hu hv))
      (hasOrd_append (hw _) (hw _)) (hasOrd_append (hw _) (hw _))
    rw [wordUnit_append Sp hC, wordUnit_append Sp hC, wordUnit_pwToWord Sp hC,
      wordUnit_pwToWord Sp hC] at e
    exact e
  · have e := regUnit_ne Sp hC (hf _ (MGenU.mem_facts_ne c)) (hw _) (hasOrd_nil _)
    rw [wordUnit_pwToWord Sp hC, wordUnit_nil Sp hC] at e
    exact e
  · intro q hq
    obtain ⟨f1, f2⟩ := MGenU.mem_facts_z c hq
    have e1 := regUnit_eq Sp hC (hf _ f1) (hasOrd_append (hw _) (hw _))
      (hasOrd_append (MGenU.hasOrd_uProd h0 h1 c _) (hw _))
    have e2 := regUnit_eq Sp hC (hf _ f2) (hasOrd_append (hw _) (hw _))
      (hasOrd_append (hw _) (MGenU.hasOrd_uProd h0 h1 c _))
    rw [wordUnit_append Sp hC, wordUnit_append Sp hC, wordUnit_pwToWord Sp hC,
      wordUnit_pwToWord Sp hC, MGenU.wordUnit_uProd Sp hC] at e1 e2
    exact MGenU.conj_pair e1 e2
  · intro k hk q hq
    obtain ⟨f1, f2⟩ := MGenU.mem_facts_k c hk hq
    have e1 := regUnit_eq Sp hC (hf _ f1) (hasOrd_append (hw _) (hw _))
      (hasOrd_append (MGenU.hasOrd_uProd h0 h1 c _) (hw _))
    have e2 := regUnit_eq Sp hC (hf _ f2) (hasOrd_append (hw _) (hw _))
      (hasOrd_append (hw _) (MGenU.hasOrd_uProd h0 h1 c _))
    rw [wordUnit_append Sp hC, wordUnit_append Sp hC, wordUnit_pwToWord Sp hC,
      wordUnit_pwToWord Sp hC, MGenU.wordUnit_uProd Sp hC] at e1 e2
    exact MGenU.conj_pair e1 e2
  · have e := regUnit_eq Sp hC (hf _ (MGenU.mem_facts_e1 c)) (hasOrd_single0 h0)
      (MGenU.hasOrd_idxWord h0 h1 c _)
    rw [wordUnit_single0 Sp hC, MGenU.wordUnit_idxWord Sp hC c] at e
    exact e
  · have e := regUnit_eq Sp hC (hf _ (MGenU.mem_facts_e2 c)) (hasOrd_single1 h1)
      (MGenU.hasOrd_idxWord h0 h1 c _)
    rw [wordUnit_single1 Sp hC, MGenU.wordUnit_idxWord Sp hC c] at e
    exact e

end Cert

theorem MGenU.genUW_of_check {M V : Type} {O : Ops M V} {pf d : ℕ} (Sp : OpsSpec O pf d)
    [Inhabited M] (sA sB : String) (c : MGenU) (h : c.check O sA sB = true) :
    GenUW (NativeSporadic.seedMonoid pf d 1 sA sB)ˣ c.base.g.p := by
  unfold MGenU.check at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hwf, hC⟩ := h
  simp only [MGenU.wf, decide_eq_true_eq] at hwf
  obtain ⟨hp, htts, hms, -, huz, hks, hu0, hmu, -, -, -, -⟩ := hwf
  have hf : ∀ f ∈ c.facts, f ∈ (⟨2, [], c.facts⟩ : MCert).facts := fun f hf => hf
  have hholds := MGenU.holds_of_facts Sp hC c htts hms hf
  have h0 : MFact.ord 0 c.base.oa ∈ (⟨2, [], c.facts⟩ : MCert).facts :=
    MGenU.baseFacts_subset c (mem_base_ord0 c.base)
  have h1 : MFact.ord 1 c.base.ob ∈ (⟨2, [], c.facts⟩ : MCert).facts :=
    MGenU.baseFacts_subset c (mem_base_ord1 c.base)
  have hS : certMonoid pf d sA sB = Submonoid.closure
      ({LocalWitness.valHom (certMonoid pf d sA sB) (regUnit Sp hC 0),
        LocalWitness.valHom (certMonoid pf d sA sB) (regUnit Sp hC 1)} :
        Set (Matrix (Fin d) (Fin d) (ZMod pf))) := by
    rw [valHom_regUnit_zero Sp hC rfl rfl h0, valHom_regUnit_one Sp hC rfl rfl h1]
    rfl
  have hcl : Subgroup.closure ({regUnit Sp hC 0, regUnit Sp hC 1} :
      Set (certMonoid pf d sA sB)ˣ) = ⊤ :=
    closure_units_eq_top (certMonoid pf d sA sB) _ _ hS
  exact MGenU.genUW_of_holds hp huz hks hu0 hmu hholds hcl

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
