module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMGenDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalGenW
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermSecDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.SectionRank
  CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint

theorem getD_map_evalPW {G : Type*} [Group G] (a b : G) {X : Type*} (l : List X) (k : X → PW)
    (x0 : X) (hk : k x0 = []) (i : ℕ) :
    (l.map fun x => evalPW a b (k x)).getD i 1 = evalPW a b (k (l.getD i x0)) := by
  by_cases hi : i < l.length
  · have hi' : i < (l.map fun x => evalPW a b (k x)).length := by simpa using hi
    rw [List.getD_eq_getElem (hn := hi'), List.getElem_map, List.getD_eq_getElem (hn := hi)]
  · have hi' : l.length ≤ i := by omega
    have hi'' : (l.map fun x => evalPW a b (k x)).length ≤ i := by simpa using hi'
    rw [List.getD_eq_default (hn := hi''), List.getD_eq_default (hn := hi'), hk]
    rfl

section General

variable {M V : Type} {O : Ops M V} {pf d : ℕ} (Sp : OpsSpec O pf d) [Inhabited M] {sA sB : String}

theorem wordUnit_pwToWord {C : MCert} (hC : mcertCheck O sA sB C = true) (w : PW) :
    wordUnit Sp hC (pwToWord w) = evalPW (regUnit Sp hC 0) (regUnit Sp hC 1) w := by
  induction w with
  | nil => rfl
  | cons q w ih =>
    obtain ⟨b, e⟩ := q
    have h1 : pwToWord ((b, e) :: w) = (if b then 1 else 0, e) :: pwToWord w := rfl
    rw [h1, wordUnit_cons, ih]
    cases b <;> rfl

theorem wordUnit_mwordPow {C : MCert} (hC : mcertCheck O sA sB C = true) (w : PW) (k : ℕ) :
    wordUnit Sp hC (mwordPow (pwToWord w) k) =
      evalPW (regUnit Sp hC 0) (regUnit Sp hC 1) w ^ k := by
  rw [← wordUnit_pwToWord Sp hC w]
  exact wordUnit_wordPow Sp hC (pwToWord w) k

theorem wordUnit_regW {C : MCert} (hC : mcertCheck O sA sB C = true) (c : PGen) (i : ℕ) :
    wordUnit Sp hC (c.regW i) = (c.regs (regUnit Sp hC 0) (regUnit Sp hC 1)).getD i 1 := by
  unfold PGen.regW PGen.regs
  by_cases hi : i < c.ns.length
  · have hi' : i < (c.ns.map fun n => evalPW (regUnit Sp hC 0) (regUnit Sp hC 1) n.1).length := by
      simp only [List.length_map]; exact hi
    rw [if_pos hi, wordUnit_pwToWord Sp hC, List.getD_append (h := hi')]
    exact (getD_map_evalPW (regUnit Sp hC 0) (regUnit Sp hC 1) c.ns (fun n => n.1) ([], 0, 0)
      rfl i).symm
  · have hl : (c.ns.map fun n => evalPW (regUnit Sp hC 0) (regUnit Sp hC 1) n.1).length ≤ i := by
      simp only [List.length_map]; omega
    rw [if_neg hi, wordUnit_pwToWord Sp hC, List.getD_append_right (h := hl), List.length_map]
    exact (getD_map_evalPW (regUnit Sp hC 0) (regUnit Sp hC 1) c.ms (fun m => m.1) ([], 0) rfl
      (i - c.ns.length)).symm

theorem MGen.wordUnit_idxWord {C : MCert} (hC : mcertCheck O sA sB C = true) (c : MGen)
    (w : List (ℕ × ℕ)) :
    wordUnit Sp hC (c.g.idxWord w) = evalIdx (c.g.regs (regUnit Sp hC 0) (regUnit Sp hC 1)) w := by
  induction w with
  | nil => exact wordUnit_nil Sp hC
  | cons q w ih =>
    obtain ⟨i, e⟩ := q
    show wordUnit Sp hC (wordPow (c.g.regW i) e ++ c.g.idxWord w) = _
    rw [wordUnit_append Sp hC, wordUnit_wordPow Sp hC, wordUnit_regW Sp hC c.g i, ih]
    rfl

theorem wordUnit_single0 {C : MCert} (hC : mcertCheck O sA sB C = true) :
    wordUnit Sp hC [(0, 1)] = regUnit Sp hC 0 := by
  rw [wordUnit_cons, wordUnit_nil]
  simp

theorem wordUnit_single1 {C : MCert} (hC : mcertCheck O sA sB C = true) :
    wordUnit Sp hC [(1, 1)] = regUnit Sp hC 1 := by
  rw [wordUnit_cons, wordUnit_nil]
  simp

theorem hasOrd_pwToWord {C : MCert} {e0 e1 : ℕ} (h0 : MFact.ord 0 e0 ∈ C.facts)
    (h1 : MFact.ord 1 e1 ∈ C.facts) (w : PW) : HasOrd C (pwToWord w) := by
  intro q hq
  simp only [pwToWord, List.mem_map] at hq
  obtain ⟨⟨b, e⟩, -, rfl⟩ := hq
  cases b
  · exact ⟨e0, h0⟩
  · exact ⟨e1, h1⟩

theorem hasOrd_mwordPow {C : MCert} {e0 e1 : ℕ} (h0 : MFact.ord 0 e0 ∈ C.facts)
    (h1 : MFact.ord 1 e1 ∈ C.facts) (w : PW) (k : ℕ) : HasOrd C (mwordPow (pwToWord w) k) :=
  hasOrd_wordPow (hasOrd_pwToWord h0 h1 w) k

theorem hasOrd_regW {C : MCert} {e0 e1 : ℕ} (h0 : MFact.ord 0 e0 ∈ C.facts)
    (h1 : MFact.ord 1 e1 ∈ C.facts) (c : PGen) (i : ℕ) : HasOrd C (c.regW i) := by
  unfold PGen.regW
  split_ifs <;> exact hasOrd_pwToWord h0 h1 _

theorem hasOrd_idxWord {C : MCert} {e0 e1 : ℕ} (h0 : MFact.ord 0 e0 ∈ C.facts)
    (h1 : MFact.ord 1 e1 ∈ C.facts) (c : PGen) (w : List (ℕ × ℕ)) : HasOrd C (c.idxWord w) := by
  induction w with
  | nil => exact hasOrd_nil _
  | cons q w ih =>
    obtain ⟨i, e⟩ := q
    show HasOrd C (wordPow (c.regW i) e ++ c.idxWord w)
    exact hasOrd_append (hasOrd_wordPow (hasOrd_regW h0 h1 c i) e) ih

theorem hasOrd_single0 {C : MCert} {e0 : ℕ} (h0 : MFact.ord 0 e0 ∈ C.facts) :
    HasOrd C [(0, 1)] := by
  intro q hq
  rw [List.mem_singleton] at hq
  subst hq
  exact ⟨e0, h0⟩

theorem hasOrd_single1 {C : MCert} {e1 : ℕ} (h1 : MFact.ord 1 e1 ∈ C.facts) :
    HasOrd C [(1, 1)] := by
  intro q hq
  rw [List.mem_singleton] at hq
  subst hq
  exact ⟨e1, h1⟩

theorem mem_base_ord0 (c : MGen) : MFact.ord 0 c.oa ∈ c.baseFacts := by
  simp [MGen.baseFacts]

theorem mem_base_ord1 (c : MGen) : MFact.ord 1 c.ob ∈ c.baseFacts := by
  simp [MGen.baseFacts]

theorem mem_base_zeq (c : MGen) : MFact.eq (mwordPow (pwToWord c.g.z) c.g.p) [] ∈ c.baseFacts := by
  simp [MGen.baseFacts]

theorem mem_base_zne (c : MGen) : MFact.ne (pwToWord c.g.z) [] c.zt ∈ c.baseFacts := by
  simp [MGen.baseFacts]

theorem mem_base_ts (c : MGen) {w : PW} {t : ℕ} (hwt : (w, t) ∈ c.g.ts.zip c.tts) :
    MFact.eq (pwToWord w ++ pwToWord w) [] ∈ c.baseFacts ∧
    MFact.ne (pwToWord w) [] t ∈ c.baseFacts ∧
    MFact.eq (pwToWord c.g.z ++ pwToWord w) (pwToWord w ++ pwToWord c.g.z) ∈ c.baseFacts := by
  have key : ∀ f ∈ [MFact.eq (pwToWord w ++ pwToWord w) [], MFact.ne (pwToWord w) [] t,
      MFact.eq (pwToWord c.g.z ++ pwToWord w) (pwToWord w ++ pwToWord c.g.z)],
      f ∈ c.baseFacts := by
    intro f hf
    have hT : f ∈ (c.g.ts.zip c.tts).flatMap fun q =>
        [MFact.eq (pwToWord q.1 ++ pwToWord q.1) [], MFact.ne (pwToWord q.1) [] q.2,
          MFact.eq (pwToWord c.g.z ++ pwToWord q.1) (pwToWord q.1 ++ pwToWord c.g.z)] :=
      List.mem_flatMap.2 ⟨(w, t), hwt, hf⟩
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
      (List.mem_append.2 (Or.inr hT)))))
  exact ⟨key _ (by simp), key _ (by simp), key _ (by simp)⟩

theorem mem_base_ns (c : MGen) {n : PW × ℕ × ℕ} (hn : n ∈ c.g.ns) :
    MFact.eq (pwToWord n.1 ++ pwToWord c.g.z) (mwordPow (pwToWord c.g.z) n.2.1 ++ pwToWord n.1) ∈
      c.baseFacts ∧
    MFact.eq (pwToWord n.1 ++ mwordPow (pwToWord c.g.z) n.2.2) (pwToWord c.g.z ++ pwToWord n.1) ∈
      c.baseFacts := by
  have key : ∀ f ∈ [MFact.eq (pwToWord n.1 ++ pwToWord c.g.z)
        (mwordPow (pwToWord c.g.z) n.2.1 ++ pwToWord n.1),
      MFact.eq (pwToWord n.1 ++ mwordPow (pwToWord c.g.z) n.2.2)
        (pwToWord c.g.z ++ pwToWord n.1)], f ∈ c.baseFacts := by
    intro f hf
    have hN : f ∈ c.g.ns.flatMap fun n' =>
        [MFact.eq (pwToWord n'.1 ++ pwToWord c.g.z)
            (mwordPow (pwToWord c.g.z) n'.2.1 ++ pwToWord n'.1),
          MFact.eq (pwToWord n'.1 ++ mwordPow (pwToWord c.g.z) n'.2.2)
            (pwToWord c.g.z ++ pwToWord n'.1)] :=
      List.mem_flatMap.2 ⟨n, hn, hf⟩
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hN)))
  exact ⟨key _ (by simp), key _ (by simp)⟩

theorem mem_base_ms (c : MGen) {m : PW × ℕ} (hm : m ∈ c.g.ms) :
    MFact.eq (pwToWord m.1 ++ pwToWord (c.g.ts.getD m.2 []))
      (pwToWord (c.g.ts.getD m.2 []) ++ pwToWord m.1) ∈ c.baseFacts := by
  have hM : MFact.eq (pwToWord m.1 ++ pwToWord (c.g.ts.getD m.2 []))
      (pwToWord (c.g.ts.getD m.2 []) ++ pwToWord m.1) ∈ c.g.ms.flatMap fun m' =>
        [MFact.eq (pwToWord m'.1 ++ pwToWord (c.g.ts.getD m'.2 []))
          (pwToWord (c.g.ts.getD m'.2 []) ++ pwToWord m'.1)] :=
    List.mem_flatMap.2 ⟨m, hm, by simp⟩
  exact List.mem_append.2 (Or.inr hM)

theorem MGen.holdsBase_of_facts {C : MCert} (hC : mcertCheck O sA sB C = true) (c : MGen)
    (htts : c.tts.length = c.g.ts.length) (hms : ∀ m ∈ c.g.ms, m.2 < c.g.ts.length)
    (hf : ∀ f ∈ c.baseFacts, f ∈ C.facts) :
    c.g.holdsBase (regUnit Sp hC 0) (regUnit Sp hC 1) := by
  have h0 : MFact.ord 0 c.oa ∈ C.facts := hf _ (mem_base_ord0 c)
  have h1 : MFact.ord 1 c.ob ∈ C.facts := hf _ (mem_base_ord1 c)
  unfold PGen.holdsBase
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have e := regUnit_eq Sp hC (hf _ (mem_base_zeq c))
      (hasOrd_mwordPow h0 h1 c.g.z c.g.p) (hasOrd_nil _)
    rw [wordUnit_mwordPow Sp hC, wordUnit_nil Sp hC] at e
    exact e
  · have e := regUnit_ne Sp hC (hf _ (mem_base_zne c)) (hasOrd_pwToWord h0 h1 _) (hasOrd_nil _)
    rw [wordUnit_pwToWord Sp hC, wordUnit_nil Sp hC] at e
    exact e
  · intro w hw
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    have hjt : j < c.tts.length := by rw [htts]; exact hj
    have hzlt : j < (c.g.ts.zip c.tts).length := by
      rw [List.length_zip]; exact lt_min hj hjt
    have hzip : (c.g.ts[j], c.tts[j]) ∈ c.g.ts.zip c.tts := by
      have h := List.getElem_mem hzlt
      rwa [List.getElem_zip] at h
    obtain ⟨f1, f2, f3⟩ := mem_base_ts c hzip
    refine ⟨?_, ?_, ?_⟩
    · have e := regUnit_eq Sp hC (hf _ f1)
        (hasOrd_append (hasOrd_pwToWord h0 h1 _) (hasOrd_pwToWord h0 h1 _)) (hasOrd_nil _)
      rw [wordUnit_append Sp hC, wordUnit_pwToWord Sp hC, wordUnit_nil Sp hC] at e
      exact e
    · have e := regUnit_ne Sp hC (hf _ f2) (hasOrd_pwToWord h0 h1 _) (hasOrd_nil _)
      rw [wordUnit_pwToWord Sp hC, wordUnit_nil Sp hC] at e
      exact e
    · have e := regUnit_eq Sp hC (hf _ f3)
        (hasOrd_append (hasOrd_pwToWord h0 h1 _) (hasOrd_pwToWord h0 h1 _))
        (hasOrd_append (hasOrd_pwToWord h0 h1 _) (hasOrd_pwToWord h0 h1 _))
      rw [wordUnit_append Sp hC, wordUnit_append Sp hC, wordUnit_pwToWord Sp hC,
        wordUnit_pwToWord Sp hC] at e
      exact e
  · intro n hn
    obtain ⟨f1, f2⟩ := mem_base_ns c hn
    have e1 := regUnit_eq Sp hC (hf _ f1)
      (hasOrd_append (hasOrd_pwToWord h0 h1 _) (hasOrd_pwToWord h0 h1 _))
      (hasOrd_append (hasOrd_mwordPow h0 h1 _ _) (hasOrd_pwToWord h0 h1 _))
    have e2 := regUnit_eq Sp hC (hf _ f2)
      (hasOrd_append (hasOrd_pwToWord h0 h1 _) (hasOrd_mwordPow h0 h1 _ _))
      (hasOrd_append (hasOrd_pwToWord h0 h1 _) (hasOrd_pwToWord h0 h1 _))
    rw [wordUnit_append Sp hC, wordUnit_append Sp hC, wordUnit_pwToWord Sp hC,
      wordUnit_pwToWord Sp hC, wordUnit_mwordPow Sp hC] at e1
    rw [wordUnit_append Sp hC, wordUnit_append Sp hC, wordUnit_pwToWord Sp hC,
      wordUnit_pwToWord Sp hC, wordUnit_mwordPow Sp hC] at e2
    exact ⟨by rw [mul_inv_eq_iff_eq_mul]; exact e1, by rw [mul_inv_eq_iff_eq_mul]; exact e2⟩
  · intro m hm
    have hmem : c.g.ts.getD m.2 [] ∈ c.g.ts := by
      rw [List.getD_eq_getElem (hn := hms m hm)]
      exact List.getElem_mem _
    refine ⟨c.g.ts.getD m.2 [], hmem, ?_⟩
    have e := regUnit_eq Sp hC (hf _ (mem_base_ms c hm))
      (hasOrd_append (hasOrd_pwToWord h0 h1 _) (hasOrd_pwToWord h0 h1 _))
      (hasOrd_append (hasOrd_pwToWord h0 h1 _) (hasOrd_pwToWord h0 h1 _))
    rw [wordUnit_append Sp hC, wordUnit_append Sp hC, wordUnit_pwToWord Sp hC,
      wordUnit_pwToWord Sp hC] at e
    exact e

theorem certRegs_zero {C : MCert} (h2 : C.nregs = 2) (hp : C.prog = []) :
    (certRegs O sA sB C)[0]! = O.decode sA := by
  simp [certRegs, Ops.regsOf, Ops.run, Ops.initRegs, h2, hp, Array.getElem!_eq_getD,
    Array.getD_getElem?]

theorem certRegs_one {C : MCert} (h2 : C.nregs = 2) (hp : C.prog = []) :
    (certRegs O sA sB C)[1]! = O.decode sB := by
  simp [certRegs, Ops.regsOf, Ops.run, Ops.initRegs, h2, hp, Array.getElem!_eq_getD,
    Array.getD_getElem?]

theorem valHom_regUnit_zero {C : MCert} (hC : mcertCheck O sA sB C = true) (h2 : C.nregs = 2)
    (hp : C.prog = []) {e : ℕ} (hf : MFact.ord 0 e ∈ C.facts) :
    LocalWitness.valHom (certMonoid pf d sA sB) (regUnit Sp hC 0) =
      NativeSporadic.decode pf d 1 sA := by
  rw [val_regUnit Sp hC hf, certRegs_zero h2 hp, Sp.toMat_decode]

theorem valHom_regUnit_one {C : MCert} (hC : mcertCheck O sA sB C = true) (h2 : C.nregs = 2)
    (hp : C.prog = []) {e : ℕ} (hf : MFact.ord 1 e ∈ C.facts) :
    LocalWitness.valHom (certMonoid pf d sA sB) (regUnit Sp hC 1) =
      NativeSporadic.decode pf d 1 sB := by
  rw [val_regUnit Sp hC hf, certRegs_one h2 hp, Sp.toMat_decode]

end General

theorem mem_closure_units {N : Type*} [Monoid N] (S : Submonoid N) (G₀ : Set Sˣ) {x : N}
    (hx : x ∈ Submonoid.closure (LocalWitness.valHom S '' G₀)) :
    ∃ w ∈ Subgroup.closure G₀, LocalWitness.valHom S w = x := by
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g, Subgroup.subset_closure hg, rfl⟩
  | one => exact ⟨1, Subgroup.one_mem _, map_one _⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨w₁, hw₁, rfl⟩ := ihx
    obtain ⟨w₂, hw₂, rfl⟩ := ihy
    exact ⟨w₁ * w₂, Subgroup.mul_mem _ hw₁ hw₂, map_mul _ _ _⟩

theorem closure_units_eq_top {N : Type*} [Monoid N] (S : Submonoid N) (a b : Sˣ)
    (hS : S = Submonoid.closure ({LocalWitness.valHom S a, LocalWitness.valHom S b} : Set N)) :
    Subgroup.closure ({a, b} : Set Sˣ) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have hu : (u.val : N) ∈ Submonoid.closure (LocalWitness.valHom S '' ({a, b} : Set Sˣ)) := by
    rw [Set.image_pair, ← hS]
    exact u.val.2
  obtain ⟨w, hw, hwu⟩ := mem_closure_units S {a, b} hu
  have hwu' : w = u := LocalWitness.valHom_injective S hwu
  rw [← hwu']
  exact hw

theorem baseFacts_subset (c : MGen) {f : MFact} (hf : f ∈ c.baseFacts) : f ∈ c.facts :=
  List.mem_append.2 (Or.inl hf)

theorem mem_facts_e1 (c : MGen) : MFact.eq [(0, 1)] (c.g.idxWord c.g.wa) ∈ c.facts :=
  List.mem_append.2 (Or.inr (by simp))

theorem mem_facts_e2 (c : MGen) : MFact.eq [(1, 1)] (c.g.idxWord c.g.wb) ∈ c.facts :=
  List.mem_append.2 (Or.inr (by simp))

theorem MGen.genW_of_check {M V : Type} {O : Ops M V} {pf d : ℕ} (Sp : OpsSpec O pf d)
    [Inhabited M] (sA sB : String) (c : MGen) (h : c.check O sA sB = true) :
    GenW (NativeSporadic.seedMonoid pf d 1 sA sB)ˣ c.g.p := by
  unfold MGen.check at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hwf, hC⟩ := h
  simp only [MGen.wf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf
  obtain ⟨⟨⟨⟨hp, hlen⟩, hms⟩, -⟩, -⟩ := hwf
  have hf : ∀ f ∈ c.baseFacts, f ∈ (⟨2, [], c.facts⟩ : MCert).facts :=
    fun f hf => baseFacts_subset c hf
  have hB := MGen.holdsBase_of_facts Sp hC c hlen hms hf
  have h0 : MFact.ord 0 c.oa ∈ (⟨2, [], c.facts⟩ : MCert).facts := hf _ (mem_base_ord0 c)
  have h1 : MFact.ord 1 c.ob ∈ (⟨2, [], c.facts⟩ : MCert).facts := hf _ (mem_base_ord1 c)
  have hholds : c.g.holds (regUnit Sp hC 0) (regUnit Sp hC 1) := by
    unfold PGen.holds
    refine ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, hB.2.2.2.2, ?_, ?_⟩
    · have e := regUnit_eq Sp hC (mem_facts_e1 c) (hasOrd_single0 h0)
        (hasOrd_idxWord h0 h1 c.g c.g.wa)
      rw [wordUnit_single0 Sp hC, MGen.wordUnit_idxWord Sp hC c] at e
      exact e
    · have e := regUnit_eq Sp hC (mem_facts_e2 c) (hasOrd_single1 h1)
        (hasOrd_idxWord h0 h1 c.g c.g.wb)
      rw [wordUnit_single1 Sp hC, MGen.wordUnit_idxWord Sp hC c] at e
      exact e
  have hS : certMonoid pf d sA sB = Submonoid.closure
      ({LocalWitness.valHom (certMonoid pf d sA sB) (regUnit Sp hC 0),
        LocalWitness.valHom (certMonoid pf d sA sB) (regUnit Sp hC 1)} :
        Set (Matrix (Fin d) (Fin d) (ZMod pf))) := by
    rw [valHom_regUnit_zero Sp hC rfl rfl h0, valHom_regUnit_one Sp hC rfl rfl h1]
    rfl
  have hcl : Subgroup.closure ({regUnit Sp hC 0, regUnit Sp hC 1} :
      Set (certMonoid pf d sA sB)ˣ) = ⊤ :=
    closure_units_eq_top (certMonoid pf d sA sB) _ _ hS
  have hG : GenW ↥(Subgroup.closure ({regUnit Sp hC 0, regUnit Sp hC 1} :
      Set (certMonoid pf d sA sB)ˣ)) c.g.p :=
    genW_exists_of_holds (regUnit Sp hC 0) (regUnit Sp hC 1) c.g hp hholds
  exact GenW.of_mulEquiv ((MulEquiv.subgroupCongr hcl).trans Subgroup.topEquiv) hG

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
