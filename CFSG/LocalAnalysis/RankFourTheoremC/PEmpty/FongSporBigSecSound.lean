module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMSecProps
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalGenW
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigSecDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.SectionRank
  CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint

namespace SClaim

theorem mem_facts_of_kFacts (c : SClaim) {k : ℕ} (hk : k < c.simple.par.length) {f : MFact}
    (hf : f ∈ c.kFacts k) : f ∈ c.facts := by
  unfold facts
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hf⟩)))

theorem mem_facts_of_repFacts (c : SClaim) {i : ℕ} (hi : i < c.simple.reps.length) {f : MFact}
    (hf : f ∈ c.repFacts i) : f ∈ c.facts := by
  unfold facts
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hf⟩))

theorem ord_mem_kFacts (c : SClaim) (k : ℕ) :
    MFact.ord (c.sr k) (c.sord.getD k 1) ∈ c.kFacts k := by
  simp [kFacts]

theorem eq_zero_mem_kFacts (c : SClaim) : MFact.eq [(c.sr 0, 1)] [] ∈ c.kFacts 0 := by
  simp [kFacts]

theorem eq_par_mem_kFacts (c : SClaim) {k : ℕ} (hk : k ≠ 0) :
    MFact.eq [(c.sr k, 1)]
      [(c.sr (c.simple.par.getD k 0), 1), (c.gReg (c.simple.gen.getD k false), 1)] ∈
      c.kFacts k := by
  simp [kFacts, hk]

theorem suc1_mem_kFacts (c : SClaim) (k : ℕ) :
    MFact.eq [(c.sr k, 1), (c.rg1, 1)] [(c.sr (c.simple.suc1.getD k 0), 1)] ∈ c.kFacts k := by
  simp [kFacts]

theorem suc2_mem_kFacts (c : SClaim) (k : ℕ) :
    MFact.eq [(c.sr k, 1), (c.rg2, 1)] [(c.sr (c.simple.suc2.getD k 0), 1)] ∈ c.kFacts k := by
  simp [kFacts]

theorem cls_none_mem_kFacts (c : SClaim) {k : ℕ} (h : c.simple.cls.getD k none = none) :
    MFact.eq [(c.sr k, 1)] [] ∈ c.kFacts k := by
  unfold kFacts
  rw [h]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem cls_some_mem_kFacts (c : SClaim) {k u i : ℕ} (h : c.simple.cls.getD k none = some (u, i)) :
    MFact.eq [(c.sr k, 1), (c.sr u, 1)]
      [(c.sr u, 1), (c.sr (c.simple.reps.getD i 0), 1)] ∈ c.kFacts k := by
  unfold kFacts
  rw [h]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem rep1_mem_repFacts (c : SClaim) (i : ℕ) :
    MFact.eq [(c.rg1, 1)] ((c.simple.nc.getD i ([], [])).1.map fun l => (c.sr l, 1)) ∈
      c.repFacts i := by
  simp [repFacts]

theorem rep2_mem_repFacts (c : SClaim) (i : ℕ) :
    MFact.eq [(c.rg2, 1)] ((c.simple.nc.getD i ([], [])).2.map fun l => (c.sr l, 1)) ∈
      c.repFacts i := by
  simp [repFacts]

end SClaim

section Sound

variable {M V : Type} {O : Ops M V} {pf d : ℕ}

theorem SClaim.secW_of_check (Sp : OpsSpec O pf d) [Inhabited M] (sA sB : String) (c : SClaim)
    (h : c.check O sA sB = true) :
    SecW (NativeSporadic.seedMonoid pf d 1 sA sB)ˣ c.p := by
  unfold SClaim.check at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hwf, hC⟩ := h
  unfold SClaim.wf at hwf
  rw [Bool.and_eq_true] at hwf
  obtain ⟨hp, hwfB⟩ := hwf
  have hp' : c.p.Prime := of_decide_eq_true hp
  haveI : Fact c.p.Prime := ⟨hp'⟩
  obtain ⟨hn0, hK, hreps, hnc, hk3, hkz⟩ := PSimple.wfB_spec hwfB
  generalize hCg : (⟨c.nregs, c.prog, c.facts⟩ : MCert) = C at hC
  have hCf : C.facts = c.facts := by rw [← hCg]
  have hmem : ∀ f ∈ c.facts, f ∈ C.facts := fun f hf => by rw [hCf]; exact hf
  have fz : MFact.ord c.rz c.p ∈ C.facts := hmem _ (by simp [SClaim.facts])
  have fzne : MFact.ne [(c.rz, 1)] [] c.zt ∈ C.facts := hmem _ (by simp [SClaim.facts])
  have ft2 : MFact.ord c.rt 2 ∈ C.facts := hmem _ (by simp [SClaim.facts])
  have ftne : MFact.ne [(c.rt, 1)] [] c.tt ∈ C.facts := hmem _ (by simp [SClaim.facts])
  have fzt : MFact.eq [(c.rz, 1), (c.rt, 1)] [(c.rt, 1), (c.rz, 1)] ∈ C.facts :=
    hmem _ (by simp [SClaim.facts])
  have f1t : MFact.eq [(c.rg1, 1), (c.rt, 1)] [(c.rt, 1), (c.rg1, 1)] ∈ C.facts :=
    hmem _ (by simp [SClaim.facts])
  have f2t : MFact.eq [(c.rg2, 1), (c.rt, 1)] [(c.rt, 1), (c.rg2, 1)] ∈ C.facts :=
    hmem _ (by simp [SClaim.facts])
  have hrg1 : MFact.ord c.rg1 c.simple.o1 ∈ C.facts := hmem _ (by simp [SClaim.facts])
  have hrg2 : MFact.ord c.rg2 c.simple.o2 ∈ C.facts := hmem _ (by simp [SClaim.facts])
  have fnab : MFact.ne [(c.rg1, 1), (c.rg2, 1)] [(c.rg2, 1), (c.rg1, 1)] c.tg ∈ C.facts :=
    hmem _ (by simp [SClaim.facts])
  have fcube : MFact.eq [(c.sr c.simple.k3, 3)] [] ∈ C.facts := hmem _ (by simp [SClaim.facts])
  have fne3 : MFact.ne [(c.sr c.simple.k3, 1)] [] c.t3 ∈ C.facts := hmem _ (by simp [SClaim.facts])
  have fkz : MFact.eq [(c.sr c.simple.kz, 1)] [(c.rz, 1)] ∈ C.facts :=
    hmem _ (by simp [SClaim.facts])
  have hrs : ∀ j, j < c.simple.par.length → MFact.ord (c.sr j) (c.sord.getD j 1) ∈ C.facts :=
    fun j hj => hmem _ (SClaim.mem_facts_of_kFacts c hj (SClaim.ord_mem_kFacts c j))
  have hcons : ∀ {r e : ℕ} {w : Word}, (∃ e', MFact.ord r e' ∈ C.facts) → HasOrd C w →
      HasOrd C ((r, e) :: w) := by
    intro r e w hr hw q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hr
    · exact hw q hq
  have hs0 : regUnit Sp hC (c.sr 0) = 1 := by
    have hf := hmem _ (SClaim.mem_facts_of_kFacts c hn0 (SClaim.eq_zero_mem_kFacts c))
    have e := regUnit_eq Sp hC hf (hcons ⟨_, hrs 0 hn0⟩ (hasOrd_nil _)) (hasOrd_nil _)
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have hpar : ∀ k, 0 < k → k < c.simple.par.length →
      regUnit Sp hC (c.sr k) = regUnit Sp hC (c.sr (c.simple.par.getD k 0)) *
        (if c.simple.gen.getD k false then regUnit Sp hC c.rg2 else regUnit Sp hC c.rg1) := by
    intro k hk0 hk
    have hk0' : k ≠ 0 := by omega
    have hf := hmem _ (SClaim.mem_facts_of_kFacts c hk (SClaim.eq_par_mem_kFacts c hk0'))
    have hpk : c.simple.par.getD k 0 < c.simple.par.length := by
      rcases (hK k hk).1 with h' | h' <;> omega
    have hgen : ∃ e', MFact.ord (c.gReg (c.simple.gen.getD k false)) e' ∈ C.facts := by
      unfold SClaim.gReg
      split_ifs
      · exact ⟨_, hrg2⟩
      · exact ⟨_, hrg1⟩
    have e := regUnit_eq Sp hC hf (hcons ⟨_, hrs k hk⟩ (hasOrd_nil _))
      (hcons ⟨_, hrs _ hpk⟩ (hcons hgen (hasOrd_nil _)))
    simp only [wordUnit_cons Sp hC, wordUnit_nil Sp hC, pow_one, mul_one] at e
    rw [e]
    unfold SClaim.gReg
    split_ifs <;> rfl
  have hg1 : regUnit Sp hC c.rg1 ^ c.simple.o1 = 1 := regUnit_pow Sp hC hrg1
  have hg2 : regUnit Sp hC c.rg2 ^ c.simple.o2 = 1 := regUnit_pow Sp hC hrg2
  have hsuc : ∀ k, k < c.simple.par.length →
      regUnit Sp hC (c.sr k) * regUnit Sp hC c.rg1 = regUnit Sp hC (c.sr (c.simple.suc1.getD k 0)) ∧
      regUnit Sp hC (c.sr k) * regUnit Sp hC c.rg2 =
        regUnit Sp hC (c.sr (c.simple.suc2.getD k 0)) := by
    intro k hk
    obtain ⟨-, hs1, hs2, -⟩ := hK k hk
    have f1 := hmem _ (SClaim.mem_facts_of_kFacts c hk (SClaim.suc1_mem_kFacts c k))
    have f2 := hmem _ (SClaim.mem_facts_of_kFacts c hk (SClaim.suc2_mem_kFacts c k))
    have e1 := regUnit_eq Sp hC f1
      (hcons ⟨_, hrs k hk⟩ (hcons ⟨_, hrg1⟩ (hasOrd_nil _)))
      (hcons ⟨_, hrs _ hs1⟩ (hasOrd_nil _))
    have e2 := regUnit_eq Sp hC f2
      (hcons ⟨_, hrs k hk⟩ (hcons ⟨_, hrg2⟩ (hasOrd_nil _)))
      (hcons ⟨_, hrs _ hs2⟩ (hasOrd_nil _))
    simp only [wordUnit_cons Sp hC, wordUnit_nil Sp hC, pow_one, mul_one] at e1 e2
    exact ⟨e1, e2⟩
  have hcls : ∀ k, k < c.simple.par.length → match c.simple.cls.getD k none with
      | none => regUnit Sp hC (c.sr k) = 1
      | some (u, i) => regUnit Sp hC (c.sr k) * regUnit Sp hC (c.sr u) =
          regUnit Sp hC (c.sr u) * regUnit Sp hC (c.sr (c.simple.reps.getD i 0)) := by
    intro k hk
    rcases hcl : c.simple.cls.getD k none with _ | ⟨u, i⟩
    · have hf := hmem _ (SClaim.mem_facts_of_kFacts c hk (SClaim.cls_none_mem_kFacts c hcl))
      have e := regUnit_eq Sp hC hf (hcons ⟨_, hrs k hk⟩ (hasOrd_nil _)) (hasOrd_nil _)
      simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
    · obtain ⟨hu, hi⟩ := (hK k hk).2.2.2 u i hcl
      have hr : c.simple.reps.getD i 0 < c.simple.par.length := by
        rw [List.getD_eq_getElem _ _ hi]
        exact hreps _ (List.getElem_mem hi)
      have hf := hmem _ (SClaim.mem_facts_of_kFacts c hk (SClaim.cls_some_mem_kFacts c hcl))
      have e := regUnit_eq Sp hC hf
        (hcons ⟨_, hrs k hk⟩ (hcons ⟨_, hrs u hu⟩ (hasOrd_nil _)))
        (hcons ⟨_, hrs u hu⟩ (hcons ⟨_, hrs _ hr⟩ (hasOrd_nil _)))
      simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have hncp : ∀ i, i < c.simple.reps.length →
      (((c.simple.nc.getD i ([], [])).1.map fun l => regUnit Sp hC (c.sr l)).prod =
        regUnit Sp hC c.rg1) ∧
      (((c.simple.nc.getD i ([], [])).2.map fun l => regUnit Sp hC (c.sr l)).prod =
        regUnit Sp hC c.rg2) := by
    intro i hi
    obtain ⟨hl1, hl2⟩ := hnc i hi
    have f1 := hmem _ (SClaim.mem_facts_of_repFacts c hi (SClaim.rep1_mem_repFacts c i))
    have f2 := hmem _ (SClaim.mem_facts_of_repFacts c hi (SClaim.rep2_mem_repFacts c i))
    have hw1 : HasOrd C ((c.simple.nc.getD i ([], [])).1.map fun l => (c.sr l, 1)) := by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
      exact ⟨_, hrs x (hl1 x hx)⟩
    have hw2 : HasOrd C ((c.simple.nc.getD i ([], [])).2.map fun l => (c.sr l, 1)) := by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
      exact ⟨_, hrs x (hl2 x hx)⟩
    have e1 := regUnit_eq Sp hC f1 (hcons ⟨_, hrg1⟩ (hasOrd_nil _)) hw1
    have e2 := regUnit_eq Sp hC f2 (hcons ⟨_, hrg2⟩ (hasOrd_nil _)) hw2
    simp only [wordUnit, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pow_one,
      mul_one, List.map_map, Function.comp_def] at e1 e2
    exact ⟨e1.symm, e2.symm⟩
  have hnab : regUnit Sp hC c.rg1 * regUnit Sp hC c.rg2 ≠
      regUnit Sp hC c.rg2 * regUnit Sp hC c.rg1 := by
    have e := regUnit_ne Sp hC fnab
      (hcons ⟨_, hrg1⟩ (hcons ⟨_, hrg2⟩ (hasOrd_nil _)))
      (hcons ⟨_, hrg2⟩ (hcons ⟨_, hrg1⟩ (hasOrd_nil _)))
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have h3 : regUnit Sp hC (c.sr c.simple.k3) ^ 3 = 1 := by
    have e := regUnit_eq Sp hC fcube
      (hcons ⟨_, hrs _ hk3⟩ (hasOrd_nil _)) (hasOrd_nil _)
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have h3' : regUnit Sp hC (c.sr c.simple.k3) ≠ 1 := by
    have e := regUnit_ne Sp hC fne3
      (hcons ⟨_, hrs _ hk3⟩ (hasOrd_nil _)) (hasOrd_nil _)
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have hzo : HasOrd C [(c.rz, 1)] := hcons ⟨_, fz⟩ (hasOrd_nil _)
  have hz : regUnit Sp hC (c.sr c.simple.kz) = regUnit Sp hC c.rz := by
    have e := regUnit_eq Sp hC fkz
      (hcons ⟨_, hrs _ hkz⟩ (hasOrd_nil _)) hzo
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have hS := PSimple.sound_of_props c.simple hwfB (fun k => regUnit Sp hC (c.sr k))
    (regUnit Sp hC c.rg1) (regUnit Sp hC c.rg2) (regUnit Sp hC c.rz) hs0 hpar hg1 hg2 hsuc hcls
    hncp hnab h3 h3' hz
  obtain ⟨hS1, hS2, hS3, hS4⟩ := hS
  have hto : ∃ e, MFact.ord c.rt e ∈ C.facts := ⟨_, ft2⟩
  have hzoo : ∃ e, MFact.ord c.rz e ∈ C.facts := ⟨_, fz⟩
  have hx1 : ∃ e, MFact.ord c.rg1 e ∈ C.facts := ⟨_, hrg1⟩
  have hx2 : ∃ e, MFact.ord c.rg2 e ∈ C.facts := ⟨_, hrg2⟩
  have ht2 : regUnit Sp hC c.rt * regUnit Sp hC c.rt = 1 := by
    rw [← pow_two]
    exact regUnit_pow Sp hC ft2
  have htne : regUnit Sp hC c.rt ≠ 1 := by
    have e := regUnit_ne Sp hC ftne (hcons hto (hasOrd_nil _)) (hasOrd_nil _)
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have hzt : regUnit Sp hC c.rz * regUnit Sp hC c.rt = regUnit Sp hC c.rt * regUnit Sp hC c.rz := by
    have e := regUnit_eq Sp hC fzt (hcons hzoo (hcons hto (hasOrd_nil _)))
      (hcons hto (hcons hzoo (hasOrd_nil _)))
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have hxt : regUnit Sp hC c.rg1 * regUnit Sp hC c.rt = regUnit Sp hC c.rt * regUnit Sp hC c.rg1 := by
    have e := regUnit_eq Sp hC f1t (hcons hx1 (hcons hto (hasOrd_nil _)))
      (hcons hto (hcons hx1 (hasOrd_nil _)))
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have hyt : regUnit Sp hC c.rg2 * regUnit Sp hC c.rt = regUnit Sp hC c.rt * regUnit Sp hC c.rg2 := by
    have e := regUnit_eq Sp hC f2t (hcons hx2 (hcons hto (hasOrd_nil _)))
      (hcons hto (hcons hx2 (hasOrd_nil _)))
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  refine ⟨regUnit Sp hC c.rz, ∅, {regUnit Sp hC c.rg1, regUnit Sp hC c.rg2},
    Subgroup.closure ({regUnit Sp hC c.rg1, regUnit Sp hC c.rg2} : Set _), ?_, ?_, ?_, ?_, hS1,
    hS2, hS3, hS4⟩
  · have hzpow := regUnit_pow Sp hC fz
    have hne := regUnit_ne Sp hC fzne hzo (hasOrd_nil _)
    simp only [wordUnit, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, pow_one,
      mul_one] at hne
    exact orderOf_eq_prime hzpow hne
  · intro n hn
    exact absurd hn (Set.notMem_empty n)
  · intro m hm
    rcases hm with rfl | hm
    · exact ⟨regUnit Sp hC c.rt, ht2, htne, hzt, hxt⟩
    · rw [Set.mem_singleton_iff] at hm
      subst hm
      exact ⟨regUnit Sp hC c.rt, ht2, htne, hzt, hyt⟩
  · rw [Set.empty_union]

end Sound

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
