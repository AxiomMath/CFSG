module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeSound

public section

namespace CFSG.AGLEmbedding.R3

section Abstract

variable {X : Type*} [Group X] {p : ℕ} [Fact p.Prime]

@[expose] def ChainTests (B : Subgroup X) : List X → List X → Prop
  | [], [] => True
  | q :: qs, z :: zs => (∀ b ∈ B, z * b = b * z) ∧ (∀ r ∈ qs, z * r = r * z) ∧
      z * q ≠ q * z ∧ ChainTests B qs zs
  | _, _ => False

theorem card_chain_ge [Finite X] (B : Subgroup X) :
    ∀ (qs zs : List X), ChainTests B qs zs →
      IsPGroup p (Subgroup.closure ((B : Set X) ∪ {x | x ∈ qs})) →
      p ^ qs.length * Nat.card B ≤ Nat.card (Subgroup.closure ((B : Set X) ∪ {x | x ∈ qs}))
  | [], [], _, _ => by
    simp only [List.length_nil, pow_zero, one_mul, List.not_mem_nil, Set.ofPred_false,
      Set.union_empty, Subgroup.closure_eq]
    exact le_rfl
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim
  | q :: qs, z :: zs, ⟨hzB, hzq, hne, hrest⟩, hP => by
    set T' := Subgroup.closure ((B : Set X) ∪ {x | x ∈ qs}) with hT'
    set T := Subgroup.closure ((B : Set X) ∪ {x | x ∈ q :: qs}) with hT
    have hle : T' ≤ T := by
      apply Subgroup.closure_mono
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (List.mem_cons_of_mem q hx)
    have hq : q ∈ T := Subgroup.subset_closure (Or.inr (by simp))
    have hqn : q ∉ T' := by
      intro hq'
      have hcomm : ∀ y ∈ T', z * y = y * z := by
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem x hx =>
          rcases hx with hx | hx
          · exact hzB x hx
          · exact hzq x hx
        | one => simp
        | mul x y _ _ ihx ihy =>
          exact (Commute.mul_right (show Commute z x from ihx) (show Commute z y from ihy))
        | inv x _ ihx =>
          exact (Commute.inv_right (show Commute z x from ihx))
      exact hne (hcomm q hq')
    have hne' : T' ≠ T := fun h => hqn (h ▸ hq)
    have ih := card_chain_ge B qs zs hrest (IsPGroup.to_le hP hle)
    have hdvd : Nat.card T' ∣ Nat.card T := Subgroup.card_dvd_of_le hle
    have hlt : Nat.card T' < Nat.card T := by
      refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) fun h => hne' ?_
      exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq h.symm)
    obtain ⟨a, ha⟩ := hP.exists_card_eq
    obtain ⟨b, hb⟩ := (IsPGroup.to_le hP hle).exists_card_eq
    have hba : b < a := by
      rw [ha, hb] at hlt
      exact (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).1 hlt
    have : p * Nat.card T' ≤ Nat.card T := by
      rw [ha, hb, ← pow_succ']
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hba
    calc p ^ (q :: qs).length * Nat.card B = p * (p ^ qs.length * Nat.card B) := by
          rw [List.length_cons, pow_succ]; ring
      _ ≤ p * Nat.card T' := Nat.mul_le_mul_left p ih
      _ ≤ Nat.card T := this

end Abstract

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

section Module

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {C : MCert} (hC : mcertCheck O sA sB C = true) {p : ℕ}

include Sp hC in
theorem chainTests_N {m : NMod} (hf : ∀ f ∈ m.facts p, f ∈ C.facts)
    (B : Subgroup (certMonoid c d sA sB)ˣ)
    (hBz : ∀ vec : List ℕ, wordUnit Sp hC (m.word vec) ∈ B)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    ∀ (qs : List Pc) (ts : List NTest), qs.length = ts.length →
      (∀ q ∈ qs, MFact.ord q.reg q.ord ∈ C.facts) →
      (∀ f ∈ m.testFacts qs ts, f ∈ C.facts) →
      ChainTests B (qs.map fun q => regUnit Sp hC q.reg)
        (ts.map fun T => wordUnit Sp hC (m.word T.vec))
  | [], [], _, _, _ => trivial
  | [], _ :: _, h, _, _ => absurd h (by simp)
  | _ :: _, [], h, _, _ => absurd h (by simp)
  | q :: qs, T :: ts, hlen, hq, htf => by
    simp only [List.map_cons, ChainTests]
    have hqord : ∀ r ∈ q :: qs, HasOrd C [(r.reg, 1)] := by
      intro r hr a ha
      simp only [List.mem_singleton] at ha
      rw [ha]
      exact ⟨r.ord, hq r hr⟩
    have hz := hasOrd_word_N hf T.vec
    refine ⟨fun b hb => hBc _ (hBz _) b hb, ?_, ?_, ?_⟩
    · intro r hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      have hfact : MFact.eq (m.word T.vec ++ [(r'.reg, 1)]) ([(r'.reg, 1)] ++ m.word T.vec) ∈
          C.facts := by
        apply htf
        simp only [NMod.testFacts, List.mem_append, List.mem_map]
        exact Or.inl (Or.inl ⟨r', hr', rfl⟩)
      have := regUnit_eq Sp hC hfact (hasOrd_append hz (hqord r' (List.mem_cons_of_mem q hr')))
        (hasOrd_append (hqord r' (List.mem_cons_of_mem q hr')) hz)
      rw [wordUnit_append, wordUnit_append] at this
      simpa [wordUnit] using this
    · have hfact : MFact.ne (m.word T.vec ++ [(q.reg, 1)]) ([(q.reg, 1)] ++ m.word T.vec) T.t ∈
          C.facts := by
        apply htf
        simp [NMod.testFacts]
      have := regUnit_ne Sp hC hfact (hasOrd_append hz (hqord q List.mem_cons_self))
        (hasOrd_append (hqord q List.mem_cons_self) hz)
      rw [wordUnit_append, wordUnit_append] at this
      simpa [wordUnit] using this
    · refine chainTests_N hf B hBz hBc qs ts (by simpa using hlen)
        (fun r hr => hq r (List.mem_cons_of_mem q hr)) (fun f hf' => htf f ?_)
      simp only [NMod.testFacts, List.mem_append]
      exact Or.inr hf'

end Module

section Main

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {nregs : ℕ} {prog : List Op} {p : ℕ} {m : NMod} {tops : List Pc}
  {tests : List NTest} {cf : ℕ → ℕ → ℕ → ℤ} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}
  {ct : ℕ → ℕ → ℕ → ℕ → ℤ}

include Sp in
theorem moduleDatum_of_modCheck [Finite (NativeSporadic.seedMonoid c d 1 sA sB)ˣ] (hp : p.Prime)
    {N : ℕ} (hN : Nat.card (NativeSporadic.seedMonoid c d 1 sA sB)ˣ = N)
    (hv : p ^ (tops.length + m.basis.length) ∣ N ∧
      ¬ p ^ (tops.length + m.basis.length + 1) ∣ N)
    (h : modCheck O sA sB nregs prog p m tops tests cf ci ct = true) :
    ModuleDatum (NativeSporadic.seedMonoid c d 1 sA sB)ˣ p := by
  have : Fact p.Prime := ⟨hp⟩
  unfold modCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, hw⟩, hpcwf⟩, hlen⟩, hacts⟩, hrank⟩, hfun⟩, halt⟩ := h
  let C : MCert := ⟨nregs, prog, m.modFacts p tops tests⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have hf : ∀ f ∈ m.facts p, f ∈ C.facts := by
    intro f hf
    show f ∈ m.modFacts p tops tests
    simp only [NMod.modFacts, List.mem_append]
    exact Or.inl (Or.inl hf)
  have hpcf : ∀ q ∈ tops ++ m.basisPc p, ∀ f ∈ q.facts p, f ∈ C.facts := by
    intro q hq f hqf
    show f ∈ m.modFacts p tops tests
    unfold NMod.modFacts
    refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ?_)))
    exact List.mem_flatMap.2 ⟨q, hq, hqf⟩
  let DS := NMod.spec Sp hC' m hf hw
  let P : Subgroup (certMonoid c d sA sB)ˣ :=
    Subgroup.closure {u | ∃ q ∈ tops ++ m.basisPc p, u = regUnit Sp hC' q.reg}
  have hPgrp : IsPGroup p P := chain_isPGroup Sp hC' (tops ++ m.basisPc p) hpcwf hpcf
  let qs : List (certMonoid c d sA sB)ˣ := tops.map fun q => regUnit Sp hC' q.reg
  let zs : List (certMonoid c d sA sB)ˣ := tests.map fun T => wordUnit Sp hC' (m.word T.vec)
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
  have hBz : ∀ vec : List ℕ, wordUnit Sp hC' (m.word vec) ∈ DS.span := by
    intro vec
    refine CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' _ _ fun a ha => ?_
    simp only [NMod.word, List.mem_map, List.mem_range] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    exact DS.a_mem_span ⟨k, hk⟩
  have hBc : ∀ x ∈ DS.span, ∀ y ∈ DS.span, x * y = y * x :=
    fun x hx y hy => DS.mul_comm_of_mem hx hy
  have hqord : ∀ q ∈ tops, MFact.ord q.reg q.ord ∈ C.facts := by
    intro q hq
    exact hpcf q (List.mem_append.2 (Or.inl hq)) _ (by simp [Pc.facts])
  have htf : ∀ f ∈ m.testFacts tops tests, f ∈ C.facts := by
    intro f hf'
    show f ∈ m.modFacts p tops tests
    unfold NMod.modFacts
    exact List.mem_append.2 (Or.inr hf')
  have htests : ChainTests DS.span qs zs :=
    chainTests_N Sp hC' hf DS.span hBz hBc tops tests hlen.symm hqord htf
  have hlow : p ^ tops.length * p ^ m.basis.length ≤ Nat.card P' := by
    have h := card_chain_ge DS.span qs zs htests hP'grp
    have hlen' : qs.length = tops.length := List.length_map _
    rw [hlen', DS.card_span hp] at h
    exact h
  have hN0 : N ≠ 0 := by
    rw [← hN]
    exact Nat.card_pos.ne'
  obtain ⟨k, hk⟩ := hP'grp.exists_card_eq
  have hdvd : Nat.card P' ∣ N := hN ▸ Subgroup.card_subgroup_dvd_card P'
  have hs1 : tops.length + m.basis.length ≤ k := by
    have : p ^ (tops.length + m.basis.length) ≤ p ^ k := by
      rw [← hk, pow_add]
      exact hlow
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
  have hs2 : k ≤ tops.length + m.basis.length := by
    by_contra hlt
    apply hv.2
    exact (Nat.pow_dvd_pow p (not_le.1 hlt)).trans (hk ▸ hdvd)
  have hkeq : k = tops.length + m.basis.length := le_antisymm hs2 hs1
  have hfact : N.factorization p = tops.length + m.basis.length := by
    have h1 := (hp.pow_dvd_iff_le_factorization hN0).1 hv.1
    have h2 : ¬ tops.length + m.basis.length + 1 ≤ N.factorization p :=
      fun h => hv.2 ((hp.pow_dvd_iff_le_factorization hN0).2 h)
    omega
  have hcard : Nat.card P' = p ^ (Nat.card (certMonoid c d sA sB)ˣ).factorization p := by
    rw [hN, hfact, hk, hkeq]
  exact ⟨DS, hrank, fun B hB hinv => noAlt_of_altOK halt B hB hinv,
    fun v hv' => noFun_of_funOK hfun v hv', Sylow.ofCard P' hcard, hP'norm⟩

end Main

end CFSG.AGLEmbedding.R3
