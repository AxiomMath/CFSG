module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyThreeSlp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding CFSG.SectionRank.LocalWitness
  CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
  CFSG.Sporadic.LySchreier.Native

section Main

variable {nregs : ℕ} {prog : List Op} {Dz : LZSpec} {Dc : LCSpec}

theorem tcGenDatum_of_lycheck
    (hp : Dz.p.Prime)
    (h : lyCheck (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2
      (evalWordM seedM (seedMInv (powM 5 111 matB 4)) (seedWord 0))
      (evalWordM seedM (seedMInv (powM 5 111 matB 4)) (seedWord 1)) nregs prog Dz Dc = true) :
    TCGenDatum NativeSporadic.Ly Dz.p := by
  have : Fact Dz.p.Prime := ⟨hp⟩
  set Sp := specP 5 111 with hSp
  unfold lyCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hC0, hAeq⟩, hBeq⟩, hc0⟩, hc1⟩, -⟩, -⟩, hzwf⟩, -⟩ := h
  let C : MCert := ⟨nregs, prog, Dz.facts ++ Dc.facts⟩
  have hC' : mcertCheck (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C = true :=
    hC0
  have hpcf : ∀ q ∈ Dz.pc, ∀ f ∈ q.facts Dz.p, f ∈ C.facts := by
    intro q hq f hf
    simp only [C, LZSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl ⟨q, hq, hf⟩))
  have hsubf : ∀ s ∈ Dz.subs, ∀ f ∈ s.facts Dz.p, f ∈ C.facts := by
    intro s hs f hf
    simp only [C, LZSpec.facts, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inr ⟨s, hs, hf⟩))
  have hgenf : ∀ f ∈ Dz.gen.facts, f ∈ C.facts := by
    intro f hf
    simp only [C, LZSpec.facts, List.mem_append]
    exact Or.inl (Or.inr hf)
  have hactord : ∀ s ∈ Dz.subs, ∀ g ∈ s.acts, MFact.ord g.reg g.ord ∈ C.facts := by
    intro s hs g hg
    apply hsubf s hs
    simp only [TSub.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨g, hg, by simp⟩
  unfold LZSpec.wf at hzwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hzwf
  obtain ⟨⟨⟨-, hpcwf⟩, hsubwf⟩, hgenwf⟩ := hzwf
  let P : Subgroup NativeSporadic.Ly :=
    Subgroup.closure {u | ∃ q ∈ Dz.pc, u = regUnit Sp hC' q.reg}
  have hP : IsPGroup Dz.p P := chain_isPGroup Sp hC' Dz.pc hpcwf hpcf
  have hsubs : ∀ s ∈ Dz.subs, ∃ U : Subgroup NativeSporadic.Ly, U ≤ P ∧
      2 ≤ Open.pRank Dz.p U ∧
      3 ≤ Open.pRank Dz.p (U ⊔ (P ⊓ Subgroup.centralizer (U : Set NativeSporadic.Ly))) ∧
      ∀ g ∈ s.acts, regUnit Sp hC' g.reg ∈
        Subgroup.normalizer (U : Set NativeSporadic.Ly) := by
    intro s hs
    have hsw := List.all_eq_true.1 hsubwf s hs
    unfold TSub.lyWf at hsw
    simp only [Bool.and_eq_true] at hsw
    obtain ⟨⟨⟨⟨⟨hgw, hv0⟩, hv1⟩, hv2⟩, hind⟩, hact⟩ := hsw
    refine tc_sub Sp hC' hp Dz.pc s hpcf (hsubf s hs)
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
  have hex : ∀ i : Fin Dz.subs.length, ∃ U : Subgroup NativeSporadic.Ly, U ≤ P ∧
      2 ≤ Open.pRank Dz.p U ∧
      3 ≤ Open.pRank Dz.p (U ⊔ (P ⊓ Subgroup.centralizer (U : Set NativeSporadic.Ly))) ∧
      ∀ g ∈ (Dz.subs.get i).acts, regUnit Sp hC' g.reg ∈
        Subgroup.normalizer (U : Set NativeSporadic.Ly) :=
    fun i => hsubs _ (List.get_mem _ _)
  choose U hUP hr2 hr3 hnorm using hex
  let S : Set NativeSporadic.Ly :=
    {g | ∃ s ∈ Dz.subs, ∃ a ∈ s.acts, g = regUnit Sp hC' a.reg}
  have hact : ∀ r ∈ Dz.actRegs, regUnit Sp hC' r ∈ Subgroup.closure S ∧
      ∃ o, MFact.ord r o ∈ C.facts := by
    intro r hr
    obtain ⟨s, hs, hr'⟩ := List.mem_flatMap.1 hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr'
    exact ⟨Subgroup.subset_closure ⟨s, hs, g, hg, rfl⟩, g.ord, hactord s hs g hg⟩
  have hgen : Subgroup.closure S = ⊤ :=
    ly_gen_top hC' Dz.gen hgenf hAeq hBeq hc0 hc1 fun q hq =>
      hact q.1 (List.contains_iff_mem.1 (List.all_eq_true.1 hgenwf q hq))
  refine ⟨Dz.subs.length, U, P, S, hP, hUP, fun i => ⟨hr2 i, hr3 i⟩, hgen, ?_⟩
  rintro _ ⟨s, hs, a, ha, rfl⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hs
  exact ⟨i, hnorm i a ha⟩

end Main

end CFSG.AGLEmbedding.R3
