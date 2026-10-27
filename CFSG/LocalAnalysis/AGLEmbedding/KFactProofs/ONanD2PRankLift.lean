module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaPRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRankDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaSound

public section

namespace CFSG.AGLEmbedding

theorem AbelianSylowDatum.three_le_pRank {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hX : p ^ 3 ∣ Nat.card X) (h : AbelianSylowDatum X p) :
    3 ≤ Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨D, -, -, -, hidx⟩ := h
  have h1 := Subgroup.card_mul_index D.span
  rw [D.card_span hp] at h1
  rw [← h1] at hX
  have hcop : Nat.Coprime (p ^ 3) D.span.index :=
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd hp).2 hidx)
  have h3 : p ^ 3 ∣ p ^ D.n := hcop.dvd_of_dvd_mul_right hX
  have hn : 3 ≤ D.n := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h3
  exact hn.trans (D.n_le_pRank hp)

namespace R3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

section Main

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {nregs : ℕ} {prog : List Op}

include Sp in
theorem exists_moduleSpec_of_nmodCheck {p : ℕ} {m : NMod} (hp : p.Prime)
    (h : mcertCheck O sA sB ⟨nregs, prog, m.facts p⟩ = true) (hw : m.wf p = true) :
    ∃ DS : ModuleSpec (NativeSporadic.seedMonoid c d 1 sA sB)ˣ p, DS.n = m.basis.length := by
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨NMod.spec Sp h m (fun f hf => hf) hw, rfl⟩

include Sp in
theorem three_le_pRank_of_nmodCheck [Finite (NativeSporadic.seedMonoid c d 1 sA sB)ˣ] {p : ℕ}
    {m : NMod} (hp : p.Prime) (h : mcertCheck O sA sB ⟨nregs, prog, m.facts p⟩ = true)
    (hw : m.wf p = true) (h3 : 3 ≤ m.basis.length) :
    3 ≤ Open.pRank p (⊤ : Subgroup (NativeSporadic.seedMonoid c d 1 sA sB)ˣ) := by
  obtain ⟨DS, hDS⟩ := exists_moduleSpec_of_nmodCheck Sp hp h hw
  exact (by rw [hDS]; exact h3 : 3 ≤ DS.n).trans (DS.n_le_pRank hp)

variable {D : RSpec} {tabs : List RLin}

include Sp in
theorem exists_moduleSpec_of_rlCheck (hp : D.p.Prime)
    (h : rlCheck O sA sB nregs prog D tabs = true) {m : RMod} (hm : m ∈ D.mods) :
    ∃ DS : ModuleSpec (NativeSporadic.seedMonoid c d 1 sA sB)ˣ D.p,
      DS.n = m.nm.basis.length := by
  have : Fact D.p.Prime := ⟨hp⟩
  unfold rlCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hC, -⟩, -⟩, -⟩, -⟩, hwf⟩, -⟩ := h
  let C : MCert := ⟨nregs, prog, D.facts⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have hf : ∀ f ∈ m.nm.facts D.p, f ∈ C.facts := by
    intro f hf
    simp only [C, RSpec.facts, List.mem_append, List.mem_flatMap]
    have hfm : f ∈ RMod.facts D.p m := by
      simp only [RMod.facts, List.mem_append]
      exact Or.inl hf
    exact Or.inl (Or.inr ⟨m, hm, hfm⟩)
  have hwfm : m.nm.wf D.p = true := by
    unfold RSpec.wf at hwf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨⟨⟨-, -⟩, hmodwf⟩, -⟩, -⟩ := hwf
    have hmw := List.all_eq_true.1 hmodwf m hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hmw
    exact hmw.1.1.1
  exact ⟨NMod.spec Sp hC' m.nm hf hwfm, rfl⟩

include Sp in
theorem three_le_pRank_of_rlCheck [Finite (NativeSporadic.seedMonoid c d 1 sA sB)ˣ]
    (hp : D.p.Prime) (h : rlCheck O sA sB nregs prog D tabs = true) {m : RMod}
    (hm : m ∈ D.mods) (h3 : 3 ≤ m.nm.basis.length) :
    3 ≤ Open.pRank D.p (⊤ : Subgroup (NativeSporadic.seedMonoid c d 1 sA sB)ˣ) := by
  obtain ⟨DS, hDS⟩ := exists_moduleSpec_of_rlCheck Sp hp h hm
  exact (by rw [hDS]; exact h3 : 3 ≤ DS.n).trans (DS.n_le_pRank hp)

end Main

end R3

end CFSG.AGLEmbedding
