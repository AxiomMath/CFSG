module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcD4Class
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcE6Lane
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExc

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T

section Exc


theorem ssTw_pgroup_e6class {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 6)
    (hc : (componentRoots (rootCharHom a) i).ncard = 72)
    {ℓ : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hℓ5 : 5 ≤ ℓ) :
    ∃ V : Subgroup ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i), IsPGroup ℓ V ∧
      8 ≤ Nat.card V := by
  cases τ with
  | G2 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | D4 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | E6 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E7 =>
    obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_six (by decide)
      (by decide) hTp i hr hc
    exact ssTw_pgroup_e6 S hT i v hv hℓ hℓ5
  | E8 =>
    obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_six (by decide)
      (by decide) hTp i hr hc
    exact ssTw_pgroup_e6 S hT i v hv hℓ hℓ5


theorem ssexc_not_L34_exc {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup τ L 3)
    (h2 : (2 : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .exc)
    (hq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ¬ IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨r, e, hr, hchar, hr5, he, hqe⟩ := ssexc_char_ge_five S h2
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  haveI : Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    ssTw_finite_rationalComponent S i
  obtain ⟨hnin, hA | ⟨hr4, hc24, -⟩⟩ := exc_kind hk
  · obtain ⟨V, hV, h8⟩ := ssTw_pgroup_e6class S Nat.prime_three S.natCast_ne_zero hT hTp h1 i
      hA.1 hA.2 hr hr5
    exact not_isLThreeFour_of_pGroup hq.1 hr hr5 hV h8
  · obtain ⟨V, hV, h8⟩ := ssTw_pgroup_d4class S Nat.prime_three S.natCast_ne_zero hT hTp h1 i hr4
      hc24 hnin hr hr5
    exact not_isLThreeFour_of_pGroup hq.1 hr hr5 hV h8

theorem ssExcExc_holds (τ : Tag) : SsExcExc τ := by
  intro L _ _ S h2 a hT hTp h1 i hk hq
  exact ssexc_not_L34_exc S h2 hT hTp h1 i hk hq

end Exc

end CFSG.HardMathSupport.Dickson.Sec6
