module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubReduce
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubSmall
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubSymp
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLAType

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

structure LeviSubInputs : Prop where
  psu : ∀ {S : Type} [Group S] [Finite S] {n f : ℕ}, 4 ≤ n →
    StatedClassicalModel S .PSU n 2 f → LeviSubAt S
  pomegaPlus : ∀ {S : Type} [Group S] [Finite S] {n f : ℕ},
    StatedClassicalModel S .POmegaPlus n 2 f → LeviSubAt S
  pomegaMinus : ∀ {S : Type} [Group S] [Finite S] {n f : ℕ},
    StatedClassicalModel S .POmegaMinus n 2 f → LeviSubAt S
  g2 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .G2 2 f → LeviSubAt S
  f4 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .F4 2 f → LeviSubAt S
  e6 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .E6 2 f → LeviSubAt S
  e7 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .E7 2 f → LeviSubAt S
  e8 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .E8 2 f → LeviSubAt S
  twistedE6 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .twistedE6 2 f → LeviSubAt S
  trialityD4 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .trialityD4 2 f → LeviSubAt S
  twistedF4 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ReeTitsModel S .twistedF4 2 f → LeviSubAt S

theorem leviSubAt_of_psu
    (h4 : ∀ {S : Type} [Group S] [Finite S] {n f : ℕ}, 4 ≤ n →
      StatedClassicalModel S .PSU n 2 f → LeviSubAt S)
    {S : Type} [Group S] [Finite S] {n f : ℕ} (hm : StatedClassicalModel S .PSU n 2 f) :
    LeviSubAt S := by
  by_cases hn : 4 ≤ n
  · exact h4 hn hm
  · have h3 : n = 3 := by
      obtain ⟨⟨-, -, h3n, -⟩, -⟩ := hm
      omega
    subst h3
    intro K₀ p hB
    have hf : 2 ≤ f := by
      obtain ⟨⟨-, hf1, -, hne⟩, -⟩ := hm
      by_contra hlt
      have hf1' : f = 1 := by omega
      subst hf1'
      exact hne (by simp)
    exact absurd (CFSG.Quasithin.GoldMLA.fusionIsBenderGroup_of_isPSU3 hf hm) hB

theorem kFactParabolicLeviSub_of_inputs
    (h : LeviSubInputs) : KFactParabolicLeviSub :=
  kFactParabolicLeviSub_of_families
    { psl := fun hm => leviSubAt_of_psl hm, psu := fun hm => leviSubAt_of_psu h.psu hm
      psp := fun hm => leviSubAt_of_psp hm, pomegaPlus := h.pomegaPlus
      pomegaMinus := h.pomegaMinus, g2 := h.g2, f4 := h.f4, e6 := h.e6, e7 := h.e7, e8 := h.e8
      twistedE6 := h.twistedE6, trialityD4 := h.trialityD4, twistedF4 := h.twistedF4
      tits := fun hm => leviSubAt_tits hm
      alt6 := fun e => leviSubAt_of_alt6 e
      u33 := fun hm => leviSubAt_u33 hm }

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
