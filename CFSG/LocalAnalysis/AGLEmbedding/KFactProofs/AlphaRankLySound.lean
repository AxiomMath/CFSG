module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRankLyDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyFiveSlp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeSound

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding CFSG.SectionRank.LocalWitness
  CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
  CFSG.Sporadic.LySchreier.Native

section Main

variable {nregs : ℕ} {prog : List Op} {D : RLySpec} {tabs : List RLin}

theorem rankLiftDatum_of_ly5check
    (hp : D.p.Prime)
    (h : rlLyCheck (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2
      [(pairAt asArr 2).1, (pairAt asArr 3).1, (pairAt asArr 4).1, (pairAt asArr 5).1,
        (pairAt asArr 6).1] (fun X => !stabOK X) nregs prog D tabs = true) :
    RankLiftDatum NativeSporadic.Ly D.p := by
  have : Fact D.p.Prime := ⟨hp⟩
  set Sp := specP 5 111 with hSp
  unfold rlLyCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hC0, -⟩, -⟩, hlen⟩, -⟩, hall⟩, hstab⟩, hwf⟩, hlin⟩ := h
  let C : MCert := ⟨nregs, prog, D.facts⟩
  have hC' : mcertCheck (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C = true :=
    hC0
  have hpcf : ∀ q ∈ D.pc, ∀ f ∈ q.facts D.p, f ∈ C.facts := by
    intro q hq f hf
    simp only [C, RLySpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl ⟨q, hq, hf⟩))
  have hmodf : ∀ m ∈ D.mods, ∀ f ∈ m.facts D.p, f ∈ C.facts := by
    intro m hm f hf
    simp only [C, RLySpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inr ⟨m, hm, hf⟩))
  have hderf : ∀ e ∈ D.ders, ∀ f ∈ e.facts, f ∈ C.facts := by
    intro e he f hf
    simp only [C, RLySpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨e, he, hf⟩)
  have hgenf : ∀ f ∈ D.gen.facts, f ∈ C.facts := by
    intro f hf
    simp only [C, RLySpec.facts, List.mem_append]
    exact Or.inr hf
  unfold RLySpec.wf at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨⟨⟨-, hpcwf⟩, hmodwf⟩, hderwf⟩, hgenwf⟩ := hwf
  unfold RLySpec.linOK at hlin
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hlin
  obtain ⟨hlenT, hlinall⟩ := hlin
  let P : Subgroup NativeSporadic.Ly :=
    Subgroup.closure {u | ∃ q ∈ D.pc, u = regUnit Sp hC' q.reg}
  have hP : IsPGroup D.p P := chain_isPGroup Sp hC' D.pc hpcwf hpcf
  have hactord : ∀ m ∈ D.mods, ∀ g ∈ m.nm.acts, MFact.ord g.reg g.ord ∈ C.facts := by
    intro m hm g hg
    apply hmodf m hm
    simp only [RMod.facts, List.mem_append, NMod.facts, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨g, hg, by simp⟩)
  have hmods : ∀ i : Fin D.mods.length, ∃ DS : ModuleSpec NativeSporadic.Ly D.p,
      ((3 ≤ DS.n ∧ DS.NoAlt) ∨ (2 ≤ DS.n ∧ DS.NoAlt ∧ DS.NoFun)) ∧ DS.span ≤ P ∧
      ∀ g ∈ (D.mods.get i).nm.acts, regUnit Sp hC' g.reg ∈ Set.range DS.g := by
    intro i
    set m : RMod := D.mods.get i with hmdef
    have hm : m ∈ D.mods := List.get_mem _ _
    have hgetD : D.mods.getD i.val default = m := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2, Option.getD_some]
      rfl
    have hlin1 := hlinall i.val i.2
    rw [hgetD] at hlin1
    obtain ⟨halt, hfunor⟩ := hlin1
    have hmw := List.all_eq_true.1 hmodwf m hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hmw
    obtain ⟨⟨⟨hwfm, hrank⟩, hwlen⟩, hwords⟩ := hmw
    have hf : ∀ f ∈ m.nm.facts D.p, f ∈ C.facts := by
      intro f hf
      apply hmodf m hm
      simp only [RMod.facts, List.mem_append]
      exact Or.inl hf
    let DS := NMod.spec Sp hC' m.nm hf hwfm
    have hDSn : DS.n = m.nm.basis.length := rfl
    refine ⟨DS, ?_, ?_, ?_⟩
    · have hNA : DS.NoAlt := fun B hB hinv => noAlt_of_altOK halt B hB hinv
      rcases Bool.or_eq_true_iff.1 hfunor with h3 | hfun
      · left
        exact ⟨by rw [hDSn]; exact of_decide_eq_true h3, hNA⟩
      · right
        exact ⟨by rw [hDSn]; exact hrank, hNA, fun v hv => noFun_of_funOK hfun v hv⟩
    · rw [ModuleSpec.span, Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      have hk : k.val < m.nm.basis.length := k.2
      have hkw : k.val < m.ws.length := by rw [hwlen]; exact hk
      have hword : (m.ws.getD k.val []).all (fun a => D.pc.any (·.reg == a.1)) = true := by
        apply List.all_eq_true.1 hwords
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkw, Option.getD_some]
        exact List.getElem_mem hkw
      have hfeq : MFact.eq [(m.nm.basis.getD k.val 0, 1)] (m.ws.getD k.val []) ∈ C.facts := by
        apply hmodf m hm
        simp only [RMod.facts, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨k.val, hk, rfl⟩
      have hb : MFact.ord (m.nm.basis.getD k.val 0) D.p ∈ C.facts := basis_ord_N hf hk
      have hu : HasOrd C [(m.nm.basis.getD k.val 0, 1)] := fun a ha => by
        simp only [List.mem_singleton] at ha; rw [ha]; exact ⟨D.p, hb⟩
      have := regUnit_eq Sp hC' hfeq hu (hasOrd_of_chain D.pc hpcf hword)
      have e : wordUnit Sp hC' [(m.nm.basis.getD k.val 0, 1)] =
          regUnit Sp hC' (m.nm.basis.getD k.val 0) := by simp [wordUnit]
      rw [e] at this
      show regUnit Sp hC' (m.nm.basis.getD k.val 0) ∈ P
      rw [this]
      exact wordUnit_mem_chain Sp hC' D.pc hword
    · intro g hg
      obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hg
      exact ⟨j, rfl⟩
  choose Dm hDm hDmP hDmR using hmods
  refine ⟨D.mods.length, Dm, P, hP, hDmP, hDm, ?_⟩
  set T : Subgroup NativeSporadic.Ly := Subgroup.closure (⋃ i, Set.range (Dm i).g) with hT
  have hav : ∀ r ∈ D.actRegs, regUnit Sp hC' r ∈ T ∧ ∃ o, MFact.ord r o ∈ C.facts := by
    intro r hr
    simp only [RLySpec.actRegs, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨m, hm, g, hg, rfl⟩ := hr
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hm
    exact ⟨Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, hDmR i g hg⟩),
      g.ord, hactord _ (List.get_mem _ _) g hg⟩
  have hders := der_mem Sp hC' T D.ders D.actRegs hderf hav hderwf
  have hw : ∀ q ∈ D.gen.words, regUnit Sp hC' q.1 ∈ T ∧ ∃ o, MFact.ord q.1 o ∈ C.facts := by
    intro q hq
    have := List.contains_iff_mem.1 (List.all_eq_true.1 hgenwf q hq)
    rcases List.mem_append.1 this with h1 | h1
    · obtain ⟨e, he, heq⟩ := List.mem_map.1 h1
      rw [← heq]
      exact hders e he
    · exact hav _ h1
  have hel : ∀ j < 5, (opsP 5 111).eq (certRegs (opsP 5 111) NativeSporadic.LySeed1
      NativeSporadic.LySeed2 C)[(D.gen.els.getD j default).reg]! (pairAt asArr (j + 2)).1 =
        true := by
    intro j hj
    have := List.all_eq_true.1 hall j (List.mem_range.2 hj)
    interval_cases j <;> exact this
  have hs : stabOK (certRegs (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C)[
      D.gen.rs]! = false := by
    simpa using hstab
  exact ly_gen_top5 hC' D.gen hgenf hlen hel hs hw

end Main

end CFSG.AGLEmbedding.R3
