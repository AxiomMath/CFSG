module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaPRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRankLyDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaSound

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

section Main

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {aMats : List M} {stab : M → Bool} {nregs : ℕ} {prog : List Op}
  {D : RLySpec} {tabs : List RLin}

include Sp in
theorem exists_moduleSpec_of_rlLyCheck (hp : D.p.Prime)
    (h : rlLyCheck O sA sB aMats stab nregs prog D tabs = true) {m : RMod} (hm : m ∈ D.mods) :
    ∃ DS : ModuleSpec (NativeSporadic.seedMonoid c d 1 sA sB)ˣ D.p,
      DS.n = m.nm.basis.length := by
  have : Fact D.p.Prime := ⟨hp⟩
  unfold rlLyCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hC0, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hwf⟩, -⟩ := h
  let C : MCert := ⟨nregs, prog, D.facts⟩
  have hC' : mcertCheck O sA sB C = true := hC0
  have hf : ∀ f ∈ m.nm.facts D.p, f ∈ C.facts := by
    intro f hf
    simp only [C, RLySpec.facts, List.mem_append, List.mem_flatMap]
    have hfm : f ∈ RMod.facts D.p m := by
      simp only [RMod.facts, List.mem_append]
      exact Or.inl hf
    exact Or.inl (Or.inl (Or.inr ⟨m, hm, hfm⟩))
  have hwfm : m.nm.wf D.p = true := by
    unfold RLySpec.wf at hwf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨⟨⟨-, -⟩, hmodwf⟩, -⟩, -⟩ := hwf
    have hmw := List.all_eq_true.1 hmodwf m hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hmw
    exact hmw.1.1.1
  exact ⟨NMod.spec Sp hC' m.nm hf hwfm, rfl⟩

include Sp in
theorem three_le_pRank_of_rlLyCheck [Finite (NativeSporadic.seedMonoid c d 1 sA sB)ˣ]
    (hp : D.p.Prime) (h : rlLyCheck O sA sB aMats stab nregs prog D tabs = true) {m : RMod}
    (hm : m ∈ D.mods) (h3 : 3 ≤ m.nm.basis.length) :
    3 ≤ Open.pRank D.p (⊤ : Subgroup (NativeSporadic.seedMonoid c d 1 sA sB)ˣ) := by
  obtain ⟨DS, hDS⟩ := exists_moduleSpec_of_rlLyCheck Sp hp h hm
  exact (by rw [hDS]; exact h3 : 3 ≤ DS.n).trans (DS.n_le_pRank hp)

end Main

end CFSG.AGLEmbedding.R3
