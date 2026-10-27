module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMGenSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMSecProps
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSecOf

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.SectionRank
  CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint

namespace MSec

theorem mem_simpleFacts_ord1 (c : MSec) : MFact.ord c.rg1 c.simple.o1 ∈ c.simpleFacts := by
  simp [simpleFacts]

theorem mem_simpleFacts_ord2 (c : MSec) : MFact.ord c.rg2 c.simple.o2 ∈ c.simpleFacts := by
  simp [simpleFacts]

theorem mem_simpleFacts_idx1 (c : MSec) :
    MFact.eq [(c.rg1, 1)] (c.base.g.idxWord c.h1) ∈ c.simpleFacts := by
  simp [simpleFacts]

theorem mem_simpleFacts_idx2 (c : MSec) :
    MFact.eq [(c.rg2, 1)] (c.base.g.idxWord c.h2) ∈ c.simpleFacts := by
  simp [simpleFacts]

theorem mem_simpleFacts_ne (c : MSec) :
    MFact.ne [(c.rg1, 1), (c.rg2, 1)] [(c.rg2, 1), (c.rg1, 1)] c.tg ∈ c.simpleFacts := by
  simp [simpleFacts]

theorem mem_simpleFacts_cube (c : MSec) :
    MFact.eq [(c.sr c.simple.k3, 3)] [] ∈ c.simpleFacts := by
  simp [simpleFacts]

theorem mem_simpleFacts_ne3 (c : MSec) :
    MFact.ne [(c.sr c.simple.k3, 1)] [] c.t3 ∈ c.simpleFacts := by
  simp [simpleFacts]

theorem mem_simpleFacts_kz (c : MSec) :
    MFact.eq [(c.sr c.simple.kz, 1)] (pwToWord c.base.g.z) ∈ c.simpleFacts := by
  simp [simpleFacts]

theorem mem_simpleFacts_of_kFacts (c : MSec) {k : ℕ} (hk : k < c.simple.par.length) {f : MFact}
    (hf : f ∈ c.kFacts k) : f ∈ c.simpleFacts := by
  unfold simpleFacts
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hf⟩)))

theorem mem_simpleFacts_of_repFacts (c : MSec) {i : ℕ} (hi : i < c.simple.reps.length) {f : MFact}
    (hf : f ∈ c.repFacts i) : f ∈ c.simpleFacts := by
  unfold simpleFacts
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hf⟩))

theorem ord_mem_kFacts (c : MSec) (k : ℕ) :
    MFact.ord (c.sr k) (c.sord.getD k 1) ∈ c.kFacts k := by
  simp [kFacts]

theorem eq_zero_mem_kFacts (c : MSec) : MFact.eq [(c.sr 0, 1)] [] ∈ c.kFacts 0 := by
  simp [kFacts]

theorem eq_par_mem_kFacts (c : MSec) {k : ℕ} (hk : k ≠ 0) :
    MFact.eq [(c.sr k, 1)]
      [(c.sr (c.simple.par.getD k 0), 1), (c.gReg (c.simple.gen.getD k false), 1)] ∈
      c.kFacts k := by
  simp [kFacts, hk]

theorem suc1_mem_kFacts (c : MSec) (k : ℕ) :
    MFact.eq [(c.sr k, 1), (c.rg1, 1)] [(c.sr (c.simple.suc1.getD k 0), 1)] ∈ c.kFacts k := by
  simp [kFacts]

theorem suc2_mem_kFacts (c : MSec) (k : ℕ) :
    MFact.eq [(c.sr k, 1), (c.rg2, 1)] [(c.sr (c.simple.suc2.getD k 0), 1)] ∈ c.kFacts k := by
  simp [kFacts]

theorem cls_none_mem_kFacts (c : MSec) {k : ℕ} (h : c.simple.cls.getD k none = none) :
    MFact.eq [(c.sr k, 1)] [] ∈ c.kFacts k := by
  unfold kFacts
  rw [h]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem cls_some_mem_kFacts (c : MSec) {k u i : ℕ} (h : c.simple.cls.getD k none = some (u, i)) :
    MFact.eq [(c.sr k, 1), (c.sr u, 1)]
      [(c.sr u, 1), (c.sr (c.simple.reps.getD i 0), 1)] ∈ c.kFacts k := by
  unfold kFacts
  rw [h]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem rep1_mem_repFacts (c : MSec) (i : ℕ) :
    MFact.eq [(c.rg1, 1)] ((c.simple.nc.getD i ([], [])).1.map fun l => (c.sr l, 1)) ∈
      c.repFacts i := by
  simp [repFacts]

theorem rep2_mem_repFacts (c : MSec) (i : ℕ) :
    MFact.eq [(c.rg2, 1)] ((c.simple.nc.getD i ([], [])).2.map fun l => (c.sr l, 1)) ∈
      c.repFacts i := by
  simp [repFacts]

end MSec

section Sound

variable {M V : Type} {O : Ops M V} {pf d : ℕ} (Sp : OpsSpec O pf d) [Inhabited M] {sA sB : String}

include Sp in
theorem MSec.secW_of_check (c : MSec) (h : c.check O sA sB = true) :
    SecW (NativeSporadic.seedMonoid pf d 1 sA sB)ˣ c.base.g.p := by
  unfold MSec.check at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hwf, hC⟩ := h
  unfold MSec.wf at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨hp, htts⟩, hms⟩, -⟩, -⟩, hwfB⟩ := hwf
  obtain ⟨hn0, hK, hreps, hnc, hk3, hkz⟩ := PSimple.wfB_spec hwfB
  generalize hCg : (⟨c.nregs, c.prog, c.facts⟩ : MCert) = C at hC
  have hCf : C.facts = c.facts := by rw [← hCg]
  have hmemb : ∀ f ∈ c.base.baseFacts, f ∈ C.facts := fun f hf => by
    rw [hCf]
    exact List.mem_append_left _ hf
  have hmems : ∀ f ∈ c.simpleFacts, f ∈ C.facts := fun f hf => by
    rw [hCf]
    exact List.mem_append_right _ hf
  have hb := MGen.holdsBase_of_facts Sp hC c.base htts hms hmemb
  have h0 : MFact.ord 0 c.base.oa ∈ C.facts := hmemb _ (mem_base_ord0 c.base)
  have h1 : MFact.ord 1 c.base.ob ∈ C.facts := hmemb _ (mem_base_ord1 c.base)
  have hrg1 : MFact.ord c.rg1 c.simple.o1 ∈ C.facts := hmems _ (MSec.mem_simpleFacts_ord1 c)
  have hrg2 : MFact.ord c.rg2 c.simple.o2 ∈ C.facts := hmems _ (MSec.mem_simpleFacts_ord2 c)
  have hrs : ∀ j, j < c.simple.par.length → MFact.ord (c.sr j) (c.sord.getD j 1) ∈ C.facts :=
    fun j hj => hmems _ (MSec.mem_simpleFacts_of_kFacts c hj (MSec.ord_mem_kFacts c j))
  have hcons : ∀ {r e : ℕ} {w : Word}, (∃ e', MFact.ord r e' ∈ C.facts) → HasOrd C w →
      HasOrd C ((r, e) :: w) := by
    intro r e w hr hw q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hr
    · exact hw q hq
  have hs0 : regUnit Sp hC (c.sr 0) = 1 := by
    have hf := hmems _ (MSec.mem_simpleFacts_of_kFacts c hn0 (MSec.eq_zero_mem_kFacts c))
    have e := regUnit_eq Sp hC hf (hcons ⟨_, hrs 0 hn0⟩ (hasOrd_nil _)) (hasOrd_nil _)
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have hpar : ∀ k, 0 < k → k < c.simple.par.length →
      regUnit Sp hC (c.sr k) = regUnit Sp hC (c.sr (c.simple.par.getD k 0)) *
        (if c.simple.gen.getD k false then regUnit Sp hC c.rg2 else regUnit Sp hC c.rg1) := by
    intro k hk0 hk
    have hk0' : k ≠ 0 := by omega
    have hf := hmems _ (MSec.mem_simpleFacts_of_kFacts c hk (MSec.eq_par_mem_kFacts c hk0'))
    have hpk : c.simple.par.getD k 0 < c.simple.par.length := by
      rcases (hK k hk).1 with h' | h' <;> omega
    have hgen : ∃ e', MFact.ord (c.gReg (c.simple.gen.getD k false)) e' ∈ C.facts := by
      unfold MSec.gReg
      split_ifs
      · exact ⟨_, hrg2⟩
      · exact ⟨_, hrg1⟩
    have e := regUnit_eq Sp hC hf (hcons ⟨_, hrs k hk⟩ (hasOrd_nil _))
      (hcons ⟨_, hrs _ hpk⟩ (hcons hgen (hasOrd_nil _)))
    simp only [wordUnit_cons Sp hC, wordUnit_nil Sp hC, pow_one, mul_one] at e
    rw [e]
    unfold MSec.gReg
    split_ifs <;> rfl
  have hg1 : regUnit Sp hC c.rg1 ^ c.simple.o1 = 1 := regUnit_pow Sp hC hrg1
  have hg2 : regUnit Sp hC c.rg2 ^ c.simple.o2 = 1 := regUnit_pow Sp hC hrg2
  have hsuc : ∀ k, k < c.simple.par.length →
      regUnit Sp hC (c.sr k) * regUnit Sp hC c.rg1 = regUnit Sp hC (c.sr (c.simple.suc1.getD k 0)) ∧
      regUnit Sp hC (c.sr k) * regUnit Sp hC c.rg2 =
        regUnit Sp hC (c.sr (c.simple.suc2.getD k 0)) := by
    intro k hk
    obtain ⟨-, hs1, hs2, -⟩ := hK k hk
    have f1 := hmems _ (MSec.mem_simpleFacts_of_kFacts c hk (MSec.suc1_mem_kFacts c k))
    have f2 := hmems _ (MSec.mem_simpleFacts_of_kFacts c hk (MSec.suc2_mem_kFacts c k))
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
    · have hf := hmems _ (MSec.mem_simpleFacts_of_kFacts c hk (MSec.cls_none_mem_kFacts c hcl))
      have e := regUnit_eq Sp hC hf (hcons ⟨_, hrs k hk⟩ (hasOrd_nil _)) (hasOrd_nil _)
      simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
    · obtain ⟨hu, hi⟩ := (hK k hk).2.2.2 u i hcl
      have hr : c.simple.reps.getD i 0 < c.simple.par.length := by
        rw [List.getD_eq_getElem _ _ hi]
        exact hreps _ (List.getElem_mem hi)
      have hf := hmems _ (MSec.mem_simpleFacts_of_kFacts c hk (MSec.cls_some_mem_kFacts c hcl))
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
    have f1 := hmems _ (MSec.mem_simpleFacts_of_repFacts c hi (MSec.rep1_mem_repFacts c i))
    have f2 := hmems _ (MSec.mem_simpleFacts_of_repFacts c hi (MSec.rep2_mem_repFacts c i))
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
    have e := regUnit_ne Sp hC (hmems _ (MSec.mem_simpleFacts_ne c))
      (hcons ⟨_, hrg1⟩ (hcons ⟨_, hrg2⟩ (hasOrd_nil _)))
      (hcons ⟨_, hrg2⟩ (hcons ⟨_, hrg1⟩ (hasOrd_nil _)))
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have h3 : regUnit Sp hC (c.sr c.simple.k3) ^ 3 = 1 := by
    have e := regUnit_eq Sp hC (hmems _ (MSec.mem_simpleFacts_cube c))
      (hcons ⟨_, hrs _ hk3⟩ (hasOrd_nil _)) (hasOrd_nil _)
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have h3' : regUnit Sp hC (c.sr c.simple.k3) ≠ 1 := by
    have e := regUnit_ne Sp hC (hmems _ (MSec.mem_simpleFacts_ne3 c))
      (hcons ⟨_, hrs _ hk3⟩ (hasOrd_nil _)) (hasOrd_nil _)
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have hz : regUnit Sp hC (c.sr c.simple.kz) =
      evalPW (regUnit Sp hC 0) (regUnit Sp hC 1) c.base.g.z := by
    have e := regUnit_eq Sp hC (hmems _ (MSec.mem_simpleFacts_kz c))
      (hcons ⟨_, hrs _ hkz⟩ (hasOrd_nil _)) (hasOrd_pwToWord h0 h1 _)
    rw [wordUnit_pwToWord Sp hC] at e
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have hS := PSimple.sound_of_props c.simple hwfB (fun k => regUnit Sp hC (c.sr k))
    (regUnit Sp hC c.rg1) (regUnit Sp hC c.rg2)
    (evalPW (regUnit Sp hC 0) (regUnit Sp hC 1) c.base.g.z) hs0 hpar hg1 hg2 hsuc hcls hncp hnab
    h3 h3' hz
  have hi1 : regUnit Sp hC c.rg1 =
      evalIdx (c.base.g.regs (regUnit Sp hC 0) (regUnit Sp hC 1)) c.h1 := by
    have e := regUnit_eq Sp hC (hmems _ (MSec.mem_simpleFacts_idx1 c))
      (hcons ⟨_, hrg1⟩ (hasOrd_nil _)) (hasOrd_idxWord h0 h1 c.base.g c.h1)
    rw [MGen.wordUnit_idxWord Sp hC c.base c.h1] at e
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  have hi2 : regUnit Sp hC c.rg2 =
      evalIdx (c.base.g.regs (regUnit Sp hC 0) (regUnit Sp hC 1)) c.h2 := by
    have e := regUnit_eq Sp hC (hmems _ (MSec.mem_simpleFacts_idx2 c))
      (hcons ⟨_, hrg2⟩ (hasOrd_nil _)) (hasOrd_idxWord h0 h1 c.base.g c.h2)
    rw [MGen.wordUnit_idxWord Sp hC c.base c.h2] at e
    simpa [wordUnit_cons Sp hC, wordUnit_nil Sp hC] using e
  rw [hi1, hi2] at hS
  exact secW_of_parts (regUnit Sp hC 0) (regUnit Sp hC 1) c.base.g c.h1 c.h2 hp hb hS

end Sound

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
