module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.SylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbSound
import all CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

@[expose] def SylowModuleData (X : Type) [Group X] [Finite X] (p n : ℕ)
    (tmats : List (List ℕ)) : Prop :=
  ∃ (D : ModuleSpec X p) (P : Subgroup X), D.n = n ∧ D.NoAlt ∧ D.NoFun ∧
    Nat.card P = p ^ (Nat.card X).factorization p ∧ D.span ≤ P ∧
    P ≤ Subgroup.normalizer (D.span : Set X) ∧
    (∀ x ∈ P, (∀ a ∈ D.span, x * a = a * x) → x ∈ D.span) ∧
    ∀ A ∈ tmats, ∃ q ∈ P, ActsBy D q (toMatL p D.n A)

@[expose] def SylowModuleCover (X : Type) [Group X] [Finite X] (p n : ℕ)
    (Lm : List (List ℕ)) : Prop :=
  ∃ (D : ModuleSpec X p) (P : Subgroup X), D.n = n ∧ D.NoAlt ∧ D.NoFun ∧
    Nat.card P = p ^ (Nat.card X).factorization p ∧ D.span ≤ P ∧
    P ≤ Subgroup.normalizer (D.span : Set X) ∧
    (∀ x ∈ P, (∀ a ∈ D.span, x * a = a * x) → x ∈ D.span) ∧
    (Lm.map (toMatL p D.n)).Nodup ∧
    (∀ A ∈ Lm, ∃ q ∈ P, ActsBy D q (toMatL p D.n A)) ∧
    ∀ x ∈ P, ∃ A ∈ Lm, ActsBy D x (toMatL p D.n A)

theorem actsBy_mul_span {X : Type} [Group X] {p : ℕ} [Fact p.Prime] (D : ModuleSpec X p)
    {q α : X} {A : Matrix (Fin D.n) (Fin D.n) (ZMod p)} (hq : ActsBy D q A)
    (hα : α ∈ D.span) : ActsBy D (q * α) A := by
  intro i
  have hc : α * D.a i = D.a i * α := D.mul_comm_of_mem hα (D.a_mem_span i)
  have : q * α * D.a i * (q * α)⁻¹ = q * D.a i * q⁻¹ := by
    calc q * α * D.a i * (q * α)⁻¹ = q * (α * D.a i) * α⁻¹ * q⁻¹ := by group
      _ = q * (D.a i * α) * α⁻¹ * q⁻¹ := by rw [hc]
      _ = q * D.a i * q⁻¹ := by group
  rw [this]
  exact hq i

section Main

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {nregs : ℕ} {prog : List Op} {p : ℕ} {m : NMod} {tops : List Pc}
  {cf : ℕ → ℕ → ℕ → ℤ} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ} {ct : ℕ → ℕ → ℕ → ℕ → ℤ}

include Sp in
theorem exists_spec_of_modCheck {tests : List NTest} (hp : p.Prime)
    (h : modCheck O sA sB nregs prog p m tops tests cf ci ct = true) :
    ∃ D : ModuleSpec (NativeSporadic.seedMonoid c d 1 sA sB)ˣ p,
      D.n = m.basis.length ∧ D.NoAlt ∧ D.NoFun := by
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
  exact ⟨NMod.spec Sp hC' m hf hw, rfl, fun B hB hinv => noAlt_of_altOK halt B hB hinv,
    fun v hv' => noFun_of_funOK hfun v hv'⟩


include Sp in
theorem sylowData_of_modCheckE {gs : List NGrp} [Finite (NativeSporadic.seedMonoid c d 1 sA sB)ˣ]
    (hp : p.Prime) {N s : ℕ} (hN : Nat.card (NativeSporadic.seedMonoid c d 1 sA sB)ˣ = N)
    (hv : p ^ s ∣ N ∧ ¬ p ^ (s + 1) ∣ N) (hs : p ^ s ≤ gs.length * p ^ m.basis.length)
    (h : modCheckE O sA sB nregs prog p m tops gs cf ci ct = true) :
    SylowModuleData (NativeSporadic.seedMonoid c d 1 sA sB)ˣ p m.basis.length
      ((m.acts.filter fun g => tops.any (·.reg == g.reg)).map (·.mat)) := by
  have : Fact p.Prime := ⟨hp⟩
  unfold modCheckE at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hC, hw⟩, hpcwf⟩, hentries⟩, hacts⟩, hgrp⟩, hrank⟩, hfun⟩, halt⟩ := h
  let C : MCert := ⟨nregs, prog, m.modFactsE p tops gs⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have hf : ∀ f ∈ m.facts p, f ∈ C.facts := by
    intro f hf
    show f ∈ m.modFactsE p tops gs
    simp only [NMod.modFactsE, List.mem_append]
    exact Or.inl (Or.inl hf)
  have hpcf : ∀ q ∈ tops ++ m.basisPc p, ∀ f ∈ q.facts p, f ∈ C.facts := by
    intro q hq f hqf
    show f ∈ m.modFactsE p tops gs
    unfold NMod.modFactsE
    refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ?_)))
    exact List.mem_flatMap.2 ⟨q, hq, hqf⟩
  have hgf : ∀ g ∈ gs, MFact.eq [((m.acts.getD g.idx default).reg, 1)] g.w ∈ C.facts := by
    intro g hg
    show _ ∈ m.modFactsE p tops gs
    unfold NMod.modFactsE
    refine List.mem_append.2 (Or.inr ?_)
    exact List.mem_map.2 ⟨g, hg, rfl⟩
  let DS := NMod.spec Sp hC' m hf hw
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
  unfold NMod.grpOK at hgrp
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hgrp
  obtain ⟨hgrp1, hgrp2⟩ := hgrp
  have hidx : ∀ a : Fin gs.length, (gs.get a).idx < m.acts.length := fun a =>
    (hgrp1 _ (List.get_mem _ _)).1
  let J : Fin gs.length → Fin DS.m := fun a => ⟨(gs.get a).idx, hidx a⟩
  have hget : ∀ a : Fin gs.length,
      m.acts.getD (gs.get a).idx default = m.acts.get (J a) := by
    intro a
    have hi := hidx a
    show m.acts.getD (gs.get a).idx default = m.acts.get ⟨(gs.get a).idx, hi⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rfl
  have hJ : ∀ a, DS.g (J a) ∈ P' := by
    intro a
    have hmem := List.get_mem gs a
    have hfact := hgf _ hmem
    have hwq := (hgrp1 _ hmem).2
    rw [hget a] at hfact
    have hu : HasOrd C [((m.acts.get (J a)).reg, 1)] := by
      intro x hx
      simp only [List.mem_singleton] at hx
      rw [hx]
      have hord : MFact.ord (m.acts.get (J a)).reg (m.acts.get (J a)).ord ∈ C.facts := by
        apply hf
        simp only [NMod.facts, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨m.acts.get (J a), List.get_mem _ _, by simp⟩
      exact ⟨_, hord⟩
    have hwo : HasOrd C (gs.get a).w := by
      intro x hx
      obtain ⟨q, hq, hqx⟩ := List.any_eq_true.1 (hwq x hx)
      have : x.1 = q.reg := (beq_iff_eq.1 hqx).symm
      refine ⟨q.ord, ?_⟩
      rw [this]
      exact hpcf q (List.mem_append.2 (Or.inl hq)) _ (by simp [Pc.facts])
    have heq := regUnit_eq Sp hC' hfact hu hwo
    have hgreg : DS.g (J a) = regUnit Sp hC' (m.acts.get (J a)).reg := rfl
    rw [hgreg]
    have e : wordUnit Sp hC' [((m.acts.get (J a)).reg, 1)] =
        regUnit Sp hC' (m.acts.get (J a)).reg := by simp [wordUnit]
    rw [e] at heq
    rw [heq]
    refine CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' P' _ fun x hx => ?_
    obtain ⟨q, hq, hqx⟩ := List.any_eq_true.1 (hwq x hx)
    have : x.1 = q.reg := (beq_iff_eq.1 hqx).symm
    rw [this]
    exact hqsP' _ (List.mem_map.2 ⟨q, hq, rfl⟩)
  have hentries' : ∀ (g : NAct), g ∈ m.acts → ∀ i, g.mat.getD i 0 < p := by
    intro g hg i
    by_cases hi : i < g.mat.length
    · have := List.all_eq_true.1 (List.all_eq_true.1 hentries g hg) (g.mat.getD i 0)
        (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      simpa using this
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 hi)]
      exact hp.pos
  have hdiff : ∀ a b : Fin gs.length, a.val < b.val → DS.M (J a) ≠ DS.M (J b) := by
    intro a b hab hM
    have h1 := hgrp2 a.val (List.mem_range.2 a.2) b.val (List.mem_range.2 b.2)
    have h1' : m.matDiffer (gs.getD a.val default).idx (gs.getD b.val default).idx = true := by
      simpa [not_le.2 hab] using h1
    have hga : gs.getD a.val default = gs.get a := by
      simp [List.getD_eq_getElem?_getD]
    have hgb : gs.getD b.val default = gs.get b := by
      simp [List.getD_eq_getElem?_getD]
    rw [hga, hgb] at h1'
    unfold NMod.matDiffer at h1'
    rw [hget a, hget b] at h1'
    simp only [List.any_eq_true, List.mem_range, bne_iff_ne] at h1'
    obtain ⟨k, hk, l, hl, hkl⟩ := h1'
    apply hkl
    have hent := congrFun (congrFun hM ⟨k, hk⟩) ⟨l, hl⟩
    have ea := hentries' (m.acts.get (J a)) (List.get_mem _ _) (m.basis.length * k + l)
    have eb := hentries' (m.acts.get (J b)) (List.get_mem _ _) (m.basis.length * k + l)
    have hent' := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hent
    rwa [Nat.mod_eq_of_lt ea, Nat.mod_eq_of_lt eb] at hent'
  have hdist : ∀ a b : Fin gs.length, a ≠ b → DS.M (J a) ≠ DS.M (J b) := by
    intro a b hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hdiff a b hlt
    · exact (hdiff b a hlt).symm
  have hcore := sylow_selfCentralizing DS P' hspanP' hP'grp hN hv hs (fun a => DS.g (J a))
    (fun a => DS.M (J a)) hJ (fun a => actsBy_g DS (J a)) hdist
  refine ⟨DS, P', rfl, fun B hB hinv => noAlt_of_altOK halt B hB hinv,
    fun v hv' => noFun_of_funOK hfun v hv', hcore.1, hspanP', hP'norm, hcore.2.1, ?_⟩
  intro A hA
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hA
  obtain ⟨hgm, hgt⟩ := List.mem_filter.1 hg
  obtain ⟨q, hq, hqreg⟩ := List.any_eq_true.1 hgt
  obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hgm
  refine ⟨DS.g j, ?_, ?_⟩
  · have hgreg : DS.g j = regUnit Sp hC' (m.acts.get j).reg := rfl
    rw [hgreg, ← beq_iff_eq.1 hqreg]
    exact hqsP' _ (List.mem_map.2 ⟨q, hq, rfl⟩)
  · exact actsBy_g DS j

include Sp in
theorem sylowCover_of_modCheckV {tidx : List ℕ} {orb : List (ℕ × ℕ)}
    [Finite (NativeSporadic.seedMonoid c d 1 sA sB)ˣ]
    (hp : p.Prime) {N s : ℕ} (hN : Nat.card (NativeSporadic.seedMonoid c d 1 sA sB)ˣ = N)
    (hv : p ^ s ∣ N ∧ ¬ p ^ (s + 1) ∣ N)
    (h : modCheckV O sA sB nregs prog p m tops tidx s orb cf ci ct = true) :
    SylowModuleCover (NativeSporadic.seedMonoid c d 1 sA sB)ˣ p m.basis.length
      (wordsL p m.basis.length (tidx.map fun i => (m.acts.getD i default).mat)) := by
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
  have hcore := sylow_selfCentralizing DS P' hspanP' hP'grp hN hv hs (fun a => g a)
    (fun a => toMatL p DS.n (L.get a)) hgP hgA hdist
  refine ⟨DS, P', rfl, fun B hB hinv => noAlt_of_altOK halt B hB hinv,
    fun v hv' => noFun_of_funOK hfun v hv', hcore.1, hspanP', hP'norm, hcore.2.1, ?_, ?_, ?_⟩
  · rw [List.Nodup, List.pairwise_map, List.pairwise_iff_getElem]
    intro a b ha hb hab
    exact hdiff ⟨a, ha⟩ ⟨b, hb⟩ hab
  · intro A hA
    obtain ⟨a, rfl⟩ := List.mem_iff_get.1 hA
    exact ⟨g a, hgP a, hgA a⟩
  · intro x hx
    obtain ⟨a, α, hα, rfl⟩ := hcore.2.2 x hx
    exact ⟨L.get a, List.get_mem L a, actsBy_mul_span DS (hgA a) hα⟩

end Main

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
