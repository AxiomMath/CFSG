module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeSound

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding CFSG.SectionRank.LocalWitness

section Sub

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {C : MCert} (hC : mcertCheck O sA sB C = true) {p : ℕ}

theorem wordUnit_mem_gens (gs : List TGen) {w : Word}
    (hw : w.all (fun a => gs.any (·.reg == a.1)) = true) :
    wordUnit Sp hC w ∈ Subgroup.closure {u | ∃ g ∈ gs, u = regUnit Sp hC g.reg} := by
  refine CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC _ w fun a ha => ?_
  obtain ⟨g, hg, hga⟩ := List.any_eq_true.1 (List.all_eq_true.1 hw a ha)
  simp only [beq_iff_eq] at hga
  exact Subgroup.subset_closure ⟨g, hg, by rw [hga]⟩

theorem hasOrd_of_gens (gs : List TGen) (hgs : ∀ g ∈ gs, MFact.ord g.reg g.ord ∈ C.facts)
    {w : Word} (hw : w.all (fun a => gs.any (·.reg == a.1)) = true) : HasOrd C w := by
  intro a ha
  obtain ⟨g, hg, hga⟩ := List.any_eq_true.1 (List.all_eq_true.1 hw a ha)
  simp only [beq_iff_eq] at hga
  exact ⟨g.ord, hga ▸ hgs g hg⟩

include Sp hC in
theorem tc_sub [Finite (certMonoid c d sA sB)ˣ] (hp : p.Prime) (pcs : List Pc) (s : TSub)
    (hpcf : ∀ q ∈ pcs, ∀ f ∈ q.facts p, f ∈ C.facts) (hf : ∀ f ∈ s.facts p, f ∈ C.facts)
    (hgw : ∀ u ∈ s.gens, u.w.all (fun a => pcs.any (·.reg == a.1)) = true)
    (hv0 : s.genWord s.v0 = true) (hv1 : s.genWord s.v1 = true)
    (hv2 : s.v2.all (fun a => pcs.any (·.reg == a.1)) = true)
    (hindep : ∀ v ∈ nonzeroTriples p, ∃ q ∈ s.indep,
      q.1 = v.1 ∧ q.2.1 = v.2.1 ∧ q.2.2.1 = v.2.2)
    (hacts : ∀ g ∈ s.acts, (∀ c ∈ g.imgs, s.gens.any (·.reg == c.1) = true ∧
        s.genWord c.2 = true) ∧ ∀ u ∈ s.gens, g.imgs.any (·.1 == u.reg) = true) :
    ∃ U : Subgroup (certMonoid c d sA sB)ˣ,
      U ≤ Subgroup.closure {u | ∃ q ∈ pcs, u = regUnit Sp hC q.reg} ∧ 2 ≤ Open.pRank p U ∧
      3 ≤ Open.pRank p (U ⊔ (Subgroup.closure {u | ∃ q ∈ pcs, u = regUnit Sp hC q.reg} ⊓
        Subgroup.centralizer (U : Set (certMonoid c d sA sB)ˣ))) ∧
      ∀ g ∈ s.acts,
        regUnit Sp hC g.reg ∈ Subgroup.normalizer (U : Set (certMonoid c d sA sB)ˣ) := by
  have : Fact p.Prime := ⟨hp⟩
  set P : Subgroup (certMonoid c d sA sB)ˣ :=
    Subgroup.closure {u | ∃ q ∈ pcs, u = regUnit Sp hC q.reg} with hPdef
  set U : Subgroup (certMonoid c d sA sB)ˣ :=
    Subgroup.closure {u | ∃ g ∈ s.gens, u = regUnit Sp hC g.reg} with hUdef
  have hgord : ∀ g ∈ s.gens, MFact.ord g.reg g.ord ∈ C.facts := by
    intro g hg
    apply hf
    simp only [TSub.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨g, hg, by simp⟩)))
  have hgeq : ∀ g ∈ s.gens, MFact.eq [(g.reg, 1)] g.w ∈ C.facts := by
    intro g hg
    apply hf
    simp only [TSub.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨g, hg, by simp⟩)))
  have hc0 : MFact.ord s.c0 p ∈ C.facts := hf _ (by simp [TSub.facts])
  have hc1 : MFact.ord s.c1 p ∈ C.facts := hf _ (by simp [TSub.facts])
  have hc2 : MFact.ord s.c2 p ∈ C.facts := hf _ (by simp [TSub.facts])
  have e0 : MFact.eq [(s.c0, 1)] s.v0 ∈ C.facts := hf _ (by simp [TSub.facts])
  have e1 : MFact.eq [(s.c1, 1)] s.v1 ∈ C.facts := hf _ (by simp [TSub.facts])
  have e2 : MFact.eq [(s.c2, 1)] s.v2 ∈ C.facts := hf _ (by simp [TSub.facts])
  have f01 : MFact.eq [(s.c0, 1), (s.c1, 1)] [(s.c1, 1), (s.c0, 1)] ∈ C.facts :=
    hf _ (by simp [TSub.facts])
  have f02 : MFact.eq [(s.c0, 1), (s.c2, 1)] [(s.c2, 1), (s.c0, 1)] ∈ C.facts :=
    hf _ (by simp [TSub.facts])
  have f12 : MFact.eq [(s.c1, 1), (s.c2, 1)] [(s.c2, 1), (s.c1, 1)] ∈ C.facts :=
    hf _ (by simp [TSub.facts])
  have hcomm_gen : ∀ g ∈ s.gens, MFact.eq [(s.c2, 1), (g.reg, 1)] [(g.reg, 1), (s.c2, 1)] ∈
      C.facts := by
    intro g hg
    apply hf
    simp only [TSub.facts, List.mem_append, List.mem_flatMap, List.mem_map]
    exact Or.inl (Or.inl (Or.inr ⟨g, hg, rfl⟩))
  have hOrdC : ∀ w : Word, (∀ q ∈ w, q.1 = s.c0 ∨ q.1 = s.c1 ∨ q.1 = s.c2) → HasOrd C w := by
    intro w hw q hq
    rcases hw q hq with h | h | h
    · exact ⟨p, h ▸ hc0⟩
    · exact ⟨p, h ▸ hc1⟩
    · exact ⟨p, h ▸ hc2⟩
  have hUP : U ≤ P := by
    refine (Subgroup.closure_le P).2 ?_
    rintro _ ⟨g, hg, rfl⟩
    have hu : HasOrd C [(g.reg, 1)] := fun a ha => by
      simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨g.ord, hgord g hg⟩
    have := regUnit_eq Sp hC (hgeq g hg) hu (hasOrd_of_chain pcs hpcf (hgw g hg))
    have e : wordUnit Sp hC [(g.reg, 1)] = regUnit Sp hC g.reg := by simp [wordUnit]
    rw [e] at this
    rw [this]
    exact wordUnit_mem_chain Sp hC pcs (hgw g hg)
  have hc0U : regUnit Sp hC s.c0 ∈ U := by
    have hu : HasOrd C [(s.c0, 1)] := fun a ha => by
      simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨p, hc0⟩
    have := regUnit_eq Sp hC e0 hu (hasOrd_of_gens s.gens hgord hv0)
    have e : wordUnit Sp hC [(s.c0, 1)] = regUnit Sp hC s.c0 := by simp [wordUnit]
    rw [e] at this
    rw [this]
    exact wordUnit_mem_gens Sp hC s.gens hv0
  have hc1U : regUnit Sp hC s.c1 ∈ U := by
    have hu : HasOrd C [(s.c1, 1)] := fun a ha => by
      simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨p, hc1⟩
    have := regUnit_eq Sp hC e1 hu (hasOrd_of_gens s.gens hgord hv1)
    have e : wordUnit Sp hC [(s.c1, 1)] = regUnit Sp hC s.c1 := by simp [wordUnit]
    rw [e] at this
    rw [this]
    exact wordUnit_mem_gens Sp hC s.gens hv1
  have hc2P : regUnit Sp hC s.c2 ∈ P := by
    have hu : HasOrd C [(s.c2, 1)] := fun a ha => by
      simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨p, hc2⟩
    have := regUnit_eq Sp hC e2 hu (hasOrd_of_chain pcs hpcf hv2)
    have e : wordUnit Sp hC [(s.c2, 1)] = regUnit Sp hC s.c2 := by simp [wordUnit]
    rw [e] at this
    rw [this]
    exact wordUnit_mem_chain Sp hC pcs hv2
  have hc2C : regUnit Sp hC s.c2 ∈ Subgroup.centralizer (U : Set (certMonoid c d sA sB)ˣ) := by
    have hle : U ≤ Subgroup.centralizer ({regUnit Sp hC s.c2} : Set (certMonoid c d sA sB)ˣ) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      have hu : HasOrd C [(s.c2, 1), (g.reg, 1)] := fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact ⟨p, hc2⟩
        · exact ⟨g.ord, hgord g hg⟩
      have hu' : HasOrd C [(g.reg, 1), (s.c2, 1)] := fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact ⟨g.ord, hgord g hg⟩
        · exact ⟨p, hc2⟩
      have := regUnit_eq Sp hC (hcomm_gen g hg) hu hu'
      simpa [wordUnit] using this
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := Subgroup.mem_centralizer_iff.1 (hle hx) (regUnit Sp hC s.c2) rfl
    exact this.symm
  have hbOrd : ∀ w : Word, (∀ q ∈ w, q.1 = s.c0 ∨ q.1 = s.c1 ∨ q.1 = s.c2) → HasOrd C w := hOrdC
  have hindep3 : ∀ cc : Fin 3 → ZMod p,
      ((List.finRange 3).map fun k => ![regUnit Sp hC s.c0, regUnit Sp hC s.c1,
        regUnit Sp hC s.c2] k ^ (cc k).val).prod = 1 → cc = 0 := by
    intro cc hcc
    by_contra hne
    have hv : ((cc 0).val, (cc 1).val, (cc 2).val) ∈ nonzeroTriples p := by
      rw [mem_nonzeroTriples]
      refine ⟨ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ?_⟩
      rintro ⟨h0, h1, h2⟩
      apply hne
      ext k
      fin_cases k
      · exact (ZMod.val_eq_zero _).1 h0
      · exact (ZMod.val_eq_zero _).1 h1
      · exact (ZMod.val_eq_zero _).1 h2
    obtain ⟨q, hq, hq0, hq1, hq2⟩ := hindep _ hv
    have hfne : MFact.ne [(s.c0, q.1), (s.c1, q.2.1), (s.c2, q.2.2.1)] [] q.2.2.2 ∈ C.facts :=
      hf _ (by
        simp only [TSub.facts, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨q, hq, rfl⟩))
    have := regUnit_ne Sp hC hfne (hOrdC _ (by simp)) (hasOrd_nil C)
    apply this
    rw [wordUnit_nil, hq0, hq1, hq2]
    simp only [wordUnit, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    simp only [List.finRange_succ, List.map_cons, List.prod_cons, List.finRange_zero, List.map_nil,
      List.prod_nil, mul_one] at hcc
    simpa [mul_assoc] using hcc
  have c01 := regUnit_eq Sp hC f01 (hOrdC _ (by simp)) (hOrdC _ (by simp))
  have c02 := regUnit_eq Sp hC f02 (hOrdC _ (by simp)) (hOrdC _ (by simp))
  have c12 := regUnit_eq Sp hC f12 (hOrdC _ (by simp)) (hOrdC _ (by simp))
  simp only [wordUnit, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    pow_one] at c01 c02 c12
  have hcomm3 : ∀ i j : Fin 3, ![regUnit Sp hC s.c0, regUnit Sp hC s.c1, regUnit Sp hC s.c2] i *
      ![regUnit Sp hC s.c0, regUnit Sp hC s.c1, regUnit Sp hC s.c2] j =
      ![regUnit Sp hC s.c0, regUnit Sp hC s.c1, regUnit Sp hC s.c2] j *
      ![regUnit Sp hC s.c0, regUnit Sp hC s.c1, regUnit Sp hC s.c2] i := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact c01 | exact c01.symm | exact c02 | exact c02.symm | exact c12 |
        exact c12.symm
  have hpow3 : ∀ i : Fin 3, ![regUnit Sp hC s.c0, regUnit Sp hC s.c1, regUnit Sp hC s.c2] i ^ p
      = 1 := by
    intro i
    fin_cases i
    · exact regUnit_pow Sp hC hc0
    · exact regUnit_pow Sp hC hc1
    · exact regUnit_pow Sp hC hc2
  have hr3 : 3 ≤ Open.pRank p
      (U ⊔ (P ⊓ Subgroup.centralizer (U : Set (certMonoid c d sA sB)ˣ))) := by
    refine le_pRank_of_indep hp _ hcomm3 hpow3 hindep3 ?_
    intro i
    fin_cases i
    · exact Subgroup.mem_sup_left hc0U
    · exact Subgroup.mem_sup_left hc1U
    · exact Subgroup.mem_sup_right ⟨hc2P, hc2C⟩
  have hindep2 : ∀ cc : Fin 2 → ZMod p,
      ((List.finRange 2).map fun k => ![regUnit Sp hC s.c0, regUnit Sp hC s.c1] k ^
        (cc k).val).prod = 1 → cc = 0 := by
    intro cc hcc
    have h3 := hindep3 ![cc 0, cc 1, 0] (by
      simp only [List.finRange_succ, List.map_cons, List.prod_cons, List.finRange_zero,
        List.map_nil, List.prod_nil, mul_one] at hcc ⊢
      simpa using hcc)
    ext k
    fin_cases k
    · simpa using congrFun h3 0
    · simpa using congrFun h3 1
  have hr2 : 2 ≤ Open.pRank p U := by
    refine le_pRank_of_indep hp _ (fun i j => ?_) (fun i => ?_) hindep2 ?_
    · fin_cases i <;> fin_cases j <;>
        first | rfl | exact c01 | exact c01.symm
    · fin_cases i
      · exact regUnit_pow Sp hC hc0
      · exact regUnit_pow Sp hC hc1
    · intro i
      fin_cases i
      · exact hc0U
      · exact hc1U
  refine ⟨U, hUP, hr2, hr3, ?_⟩
  intro g hg
  obtain ⟨himgs, hcover⟩ := hacts g hg
  have hgo : MFact.ord g.reg g.ord ∈ C.facts := by
    apply hf
    simp only [TSub.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨g, hg, by simp⟩
  have hgpow : regUnit Sp hC g.reg ^ g.ord = 1 := regUnit_pow Sp hC hgo
  have hgpos : 0 < g.ord := (reg_pow Sp hC hgo).2.1
  refine mem_normalizer_closure_of_conj hgpos hgpow ?_
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨cc, hcc, hcu⟩ := List.any_eq_true.1 (hcover u hu)
  simp only [beq_iff_eq] at hcu
  have hcf : MFact.conj g.reg [(cc.1, 1)] cc.2 ∈ C.facts := by
    apply hf
    simp only [TSub.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨g, hg, List.mem_cons_of_mem _ (List.mem_map.2 ⟨cc, hcc, rfl⟩)⟩
  obtain ⟨hcg, hcw⟩ := himgs cc hcc
  have hu1 : HasOrd C [(cc.1, 1)] := fun a ha => by
    simp only [List.mem_singleton] at ha
    rw [ha]
    obtain ⟨u', hu', hu'r⟩ := List.any_eq_true.1 hcg
    simp only [beq_iff_eq] at hu'r
    exact ⟨u'.ord, hu'r ▸ hgord u' hu'⟩
  have := regUnit_conj Sp hC hcf hgo hu1 (hasOrd_of_gens s.gens hgord hcw)
  have e : wordUnit Sp hC [(cc.1, 1)] = regUnit Sp hC u.reg := by simp [wordUnit, hcu]
  rw [e] at this
  rw [this]
  exact wordUnit_mem_gens Sp hC s.gens hcw

end Sub

section Split

variable {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : ℕ) (prog : List Op)

theorem mcertCheck_append (F G : List MFact)
    (h₁ : mcertCheck O sA sB ⟨nregs, prog, F⟩ = true)
    (h₂ : mcertCheck O sA sB ⟨nregs, prog, G⟩ = true) :
    mcertCheck O sA sB ⟨nregs, prog, F ++ G⟩ = true := by
  simp only [mcertCheck, Bool.and_eq_true, List.all_append] at h₁ h₂ ⊢
  exact ⟨h₁.1, h₁.2, h₂.2⟩

theorem tcCheck_of_head_tail (D : TSpec) (m : ℕ)
    (h₁ : tcCheckHead O sA sB nregs prog D m = true)
    (h₂ : tcCheckTail O sA sB nregs prog D m = true) :
    tcCheck O sA sB nregs prog D = true := by
  unfold tcCheckHead at h₁
  unfold tcCheckTail at h₂
  simp only [Bool.and_eq_true] at h₁
  obtain ⟨⟨⟨⟨⟨hm, hrA⟩, hrB⟩, hAeq⟩, hBeq⟩, hwf⟩ := h₁
  have h := mcertCheck_append O sA sB nregs prog _ _ hm h₂
  rw [List.take_append_drop] at h
  unfold tcCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h, hrA⟩, hrB⟩, hAeq⟩, hBeq⟩, hwf⟩

end Split

section Main

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {nregs : ℕ} {prog : List Op} {D : TSpec}

include Sp in
theorem tcGenDatum_of_check [Finite (NativeSporadic.seedMonoid c d 1 sA sB)ˣ] (hp : D.p.Prime)
    (h : tcCheck O sA sB nregs prog D = true) :
    TCGenDatum (NativeSporadic.seedMonoid c d 1 sA sB)ˣ D.p := by
  have : Fact D.p.Prime := ⟨hp⟩
  unfold tcCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hC, hrA⟩, hrB⟩, hAeq⟩, hBeq⟩, hwf⟩ := h
  let C : MCert := ⟨nregs, prog, D.facts⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have fordA : MFact.ord D.rA D.oA ∈ D.facts := by simp [TSpec.facts]
  have fordB : MFact.ord D.rB D.oB ∈ D.facts := by simp [TSpec.facts]
  have feA : MFact.eq [(D.rA, 1)] D.wA ∈ D.facts := by simp [TSpec.facts]
  have feB : MFact.eq [(D.rB, 1)] D.wB ∈ D.facts := by simp [TSpec.facts]
  have hpcf : ∀ q ∈ D.pc, ∀ f ∈ q.facts D.p, f ∈ D.facts := by
    intro q hq f hf
    simp only [TSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inr ⟨q, hq, hf⟩))
  have hsubf : ∀ s ∈ D.subs, ∀ f ∈ s.facts D.p, f ∈ D.facts := by
    intro s hs f hf
    simp only [TSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨s, hs, hf⟩)
  have hactord : ∀ s ∈ D.subs, ∀ g ∈ s.acts, MFact.ord g.reg g.ord ∈ D.facts := by
    intro s hs g hg
    apply hsubf s hs
    simp only [TSub.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨g, hg, by simp⟩
  unfold TSpec.wf at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨⟨⟨-, hpcwf⟩, hsubwf⟩, hderwf⟩, hseedwf⟩ := hwf
  let P : Subgroup (certMonoid c d sA sB)ˣ :=
    Subgroup.closure {u | ∃ q ∈ D.pc, u = regUnit Sp hC' q.reg}
  have hP : IsPGroup D.p P := chain_isPGroup Sp hC' D.pc hpcwf hpcf
  have hsubs : ∀ s ∈ D.subs, ∃ U : Subgroup (certMonoid c d sA sB)ˣ, U ≤ P ∧
      2 ≤ Open.pRank D.p U ∧
      3 ≤ Open.pRank D.p (U ⊔ (P ⊓ Subgroup.centralizer (U : Set (certMonoid c d sA sB)ˣ))) ∧
      ∀ g ∈ s.acts, regUnit Sp hC' g.reg ∈
        Subgroup.normalizer (U : Set (certMonoid c d sA sB)ˣ) := by
    intro s hs
    have hsw := List.all_eq_true.1 hsubwf s hs
    simp only [Bool.and_eq_true] at hsw
    obtain ⟨⟨⟨⟨⟨hgw, hv0⟩, hv1⟩, hv2⟩, hind⟩, hact⟩ := hsw
    refine tc_sub Sp hC' hp D.pc s hpcf (hsubf s hs)
      (fun u hu => List.all_eq_true.1 hgw u hu) hv0 hv1 hv2 ?_ ?_
    · intro v hv
      obtain ⟨q, hq, hqv⟩ := List.any_eq_true.1 (List.all_eq_true.1 hind v hv)
      simp only [Bool.and_eq_true, beq_iff_eq] at hqv
      exact ⟨q, hq, hqv.1.1, hqv.1.2, hqv.2⟩
    · intro g hg
      have hg' := List.all_eq_true.1 hact g hg
      simp only [Bool.and_eq_true] at hg'
      refine ⟨fun cc hcc => ?_, fun u hu => List.all_eq_true.1 hg'.2 u hu⟩
      have := List.all_eq_true.1 hg'.1 cc hcc
      simp only [Bool.and_eq_true] at this
      exact this
  have hex : ∀ i : Fin D.subs.length, ∃ U : Subgroup (certMonoid c d sA sB)ˣ, U ≤ P ∧
      2 ≤ Open.pRank D.p U ∧
      3 ≤ Open.pRank D.p (U ⊔ (P ⊓ Subgroup.centralizer (U : Set (certMonoid c d sA sB)ˣ))) ∧
      ∀ g ∈ (D.subs.get i).acts, regUnit Sp hC' g.reg ∈
        Subgroup.normalizer (U : Set (certMonoid c d sA sB)ˣ) :=
    fun i => hsubs _ (List.get_mem _ _)
  choose U hUP hr2 hr3 hnorm using hex
  let S : Set (certMonoid c d sA sB)ˣ :=
    {g | ∃ s ∈ D.subs, ∃ a ∈ s.acts, g = regUnit Sp hC' a.reg}
  have hact : ∀ r ∈ D.actRegs, regUnit Sp hC' r ∈ Subgroup.closure S ∧
      ∃ o, MFact.ord r o ∈ C.facts := by
    intro r hr
    obtain ⟨s, hs, hr'⟩ := List.mem_flatMap.1 hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr'
    exact ⟨Subgroup.subset_closure ⟨s, hs, g, hg, rfl⟩, g.ord, hactord s hs g hg⟩
  have hderf : ∀ e ∈ D.der, ∀ f ∈ e.facts, f ∈ D.facts := by
    intro e he f hf
    simp only [TSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨e, he, hf⟩
  have hderG := der_mem Sp hC' (Subgroup.closure S) D.der D.actRegs hderf hact hderwf
  have hseedG : ∀ q ∈ D.wA ++ D.wB, regUnit Sp hC' q.1 ∈ Subgroup.closure S ∧
      ∃ o, MFact.ord q.1 o ∈ C.facts := by
    intro q hq
    rcases List.mem_append.1 (List.contains_iff_mem.1 (List.all_eq_true.1 hseedwf q hq)) with h | h
    · exact hact q.1 h
    · obtain ⟨e, he, hq1⟩ := List.mem_map.1 h
      rw [← hq1]
      exact hderG e he
  have hOrdGens : ∀ w : Word, (∀ q ∈ w, q ∈ D.wA ++ D.wB) → HasOrd C w :=
    fun w hw q hq => (hseedG q (hw q hq)).2
  have hΓreg : ∀ q ∈ D.wA ++ D.wB, regUnit Sp hC' q.1 ∈ Subgroup.closure S :=
    fun q hq => (hseedG q hq).1
  have hrA' : D.rA < C.nregs := hrA
  have hrB' : D.rB < C.nregs := hrB
  have hvalA : valHom (certMonoid c d sA sB) (regUnit Sp hC' D.rA) =
      NativeSporadic.decode c d 1 sA := by
    rw [val_regUnit Sp hC' fordA, Sp.toMat_eq (reg_ok Sp hC' hrA').1 (Sp.decode_wf sA) hAeq,
      Sp.toMat_decode]
  have hvalB : valHom (certMonoid c d sA sB) (regUnit Sp hC' D.rB) =
      NativeSporadic.decode c d 1 sB := by
    rw [val_regUnit Sp hC' fordB, Sp.toMat_eq (reg_ok Sp hC' hrB').1 (Sp.decode_wf sB) hBeq,
      Sp.toMat_decode]
  have htop := CFSG.RankThree.PartOne.CTP.Fus.closure_pair_units_eq_top (certMonoid c d sA sB) rfl
    (regUnit Sp hC' D.rA) (regUnit Sp hC' D.rB) hvalA hvalB
  have hAw : regUnit Sp hC' D.rA = wordUnit Sp hC' D.wA := by
    have := regUnit_eq Sp hC' feA (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oA, fordA⟩)
      (hOrdGens D.wA fun q hq => List.mem_append.2 (Or.inl hq))
    simpa [wordUnit] using this
  have hBw : regUnit Sp hC' D.rB = wordUnit Sp hC' D.wB := by
    have := regUnit_eq Sp hC' feB (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oB, fordB⟩)
      (hOrdGens D.wB fun q hq => List.mem_append.2 (Or.inr hq))
    simpa [wordUnit] using this
  have hgen : Subgroup.closure S = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← htop, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [hAw]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' _ D.wA fun q hq =>
        hΓreg q (List.mem_append.2 (Or.inl hq))
    · rw [hBw]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' _ D.wB fun q hq =>
        hΓreg q (List.mem_append.2 (Or.inr hq))
  refine ⟨D.subs.length, U, P, S, hP, hUP, fun i => ⟨hr2 i, hr3 i⟩, hgen, ?_⟩
  rintro _ ⟨s, hs, a, ha, rfl⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hs
  exact ⟨i, hnorm i a ha⟩

end Main

end CFSG.AGLEmbedding.R3
