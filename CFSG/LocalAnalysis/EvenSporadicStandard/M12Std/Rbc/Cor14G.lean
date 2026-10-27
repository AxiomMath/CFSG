module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Cor14GChain
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Cor14GCit
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.ConeTop
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Layer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.TopStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitCompBInner
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.UseAt

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

variable {G : Type} [Group G] [Finite G]

section Certified

open _root_.Certificates


theorem Out.false_of_isCompIn_rankOne
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hMcard : Nat.card MonsterY443Derived = monsterOrder)
    {L : Subgroup G} {t : G} (hO : Out G L t) {z : G} (hz : orderOf z = 2) {X : Subgroup G}
    (hzX : z ∈ X) (hX : IsCompIn X (centralizer ({z} : Set G))) (hrk : CFSG.pRank 2 ↥X = 1) :
    False := by
  haveI := hO.std.simple
  rcases oddLie_or_m11_of_rankOne hCIT hO.std.nonabelian hz hzX hX hrk with h | h
  · exact hO.false_of_noM12List hMcard (Or.inr (Or.inl h))
  · exact hO.false_of_isSporadic_m11 h

section Main

theorem exists_inCG_of_isCompIn
    (hUG : Balance.UHered G)
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hMcard : Nat.card MonsterY443Derived = monsterOrder)
    {X₀ : Subgroup G} {u : G} (hO : Out G X₀ u)
    {T₀ K : Subgroup G} (hT₀ : IsPGroup 2 T₀) (hT₀1 : T₀ ≠ ⊥)
    (hK : IsCompIn K (centralizer (T₀ : Set G))) :
    ∃ m U TU sU, InCG G m U TU sU ∧ U 0 = K := by
  have hG := hO.std.simple
  have hna := hO.std.nonabelian
  have hKp := hO.std.kProper
  have hFS : FStarSimple (⊤ : Subgroup G) := @fStarSimple_top G _ _ hG hna
  have hodd : CFSG.oddCore G = ⊥ := hFS.oddCore_eq_bot
  have h15 : FS79Lemma15At G := fs79Lemma15At_of_uhered G hUG
  obtain ⟨a, L, T, s, hlinks, hL0, hinLF, hT⟩ := exists_tLinks_to_inLF h15 hKp hodd hT₀ hT₀1 hK
  obtain ⟨X, hXcone, hmax, hup1, hup2⟩ := exists_coneTop hinLF
  obtain ⟨c, L', T', s', hlinks', hL'0, hL'c, hT'⟩ := exists_tLinks_extend hlinks hT hXcone
  have hstd : StdBare X := by
    by_cases hrk : CFSG.pRank 2 ↥X = 1
    · obtain ⟨z, hzX, hz, hXz⟩ :=
        isCompIn_of_coneTop_rankOne h15 hKp hodd hinLF hXcone hup1 hup2 hrk
      exact (Out.false_of_isCompIn_rankOne hCIT hMcard hO hz hzX hXz hrk).elim
    · exact fs79Thm13UseAt_of_lemma15At h15 hKp ⊤ hFS (fun _ _ => le_top) X hmax hrk
  obtain ⟨z, hz, hXz⟩ := hmax.1
  subst hL'c
  obtain ⟨m, U, TU, sU, hC, hU0⟩ :=
    exists_inCG_of_tLinks_of_isCompIn hG hna hlinks' hT' hz hXz hstd
  exact ⟨m, U, TU, sU, hC, hU0.trans (hL'0.trans hL0)⟩

end Main

end Certified

end CFSG.EvenSporadicStandard.M12Std.Rbc
