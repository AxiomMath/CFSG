module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25RankOne

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

structure LeviSubFamilies : Prop where
  psl : ∀ {S : Type} [Group S] [Finite S] {n f : ℕ},
    StatedClassicalModel S .PSL n 2 f → LeviSubAt S
  psu : ∀ {S : Type} [Group S] [Finite S] {n f : ℕ},
    StatedClassicalModel S .PSU n 2 f → LeviSubAt S
  psp : ∀ {S : Type} [Group S] [Finite S] {n f : ℕ},
    StatedClassicalModel S .PSp n 2 f → LeviSubAt S
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
  tits : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ReeTitsModel S .Tits 2 f → LeviSubAt S
  alt6 : ∀ {S : Type} [Group S] [Finite S],
    Nonempty (S ≃* alternatingGroup (Fin 6)) → LeviSubAt S
  u33 : ∀ {S : Type} [Group S] [Finite S],
    StatedClassicalModel S .PSU 3 3 1 → LeviSubAt S

theorem leviSubAt_of_families
    (F : LeviSubFamilies) {S : Type} [Group S] [Finite S]
    (hS : IsChevSimple 2 S) : LeviSubAt S := by
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases hS with ⟨t, n, f, hm⟩ | ⟨e⟩ | h33
  · rcases hm with ⟨htc, hcl⟩ | ⟨-, htc, hce⟩ | ⟨-, htc, hrt⟩ | ⟨-, rfl, hsz⟩
    · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact F.psl hcl
      · exact F.psu hcl
      · exact F.psp hcl
      · obtain ⟨⟨-, -, -, hne⟩, -⟩ := hcl
        exact absurd rfl hne
      · exact F.pomegaPlus hcl
      · exact F.pomegaMinus hcl
    · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact F.g2 hce
      · exact F.f4 hce
      · exact F.e6 hce
      · exact F.e7 hce
      · exact F.e8 hce
      · exact F.twistedE6 hce
      · exact F.trialityD4 hce
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at htc
      rcases htc with rfl | rfl | rfl
      · obtain ⟨⟨-, -, -, hp3, -⟩, -⟩ := hrt
        omega
      · exact F.twistedF4 hrt
      · exact F.tits hrt
    · intro K₀ p hB
      exact absurd (CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isSz hsz) hB
  · exact F.alt6 e
  · exact F.u33 h33

theorem kFactParabolicLeviSub_of_families
    (F : LeviSubFamilies) : KFactParabolicLeviSub :=
  kFactParabolicLeviSub_of_leviSubAt fun _ _ _ hS => leviSubAt_of_families F hS

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
