module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFixed
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFix
import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
open CFSG.StandardType (GGLabelRigidInput)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem i167COrth_fixed_gen (hD : COrthLabelDict) (hRig : GGLabelRigidInput) (hb : CatDistinct.OrderBridge)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {N : ℕ} (hdim : Module.finrank F V = 2 * N) (hN : 4 ≤ N)
    {g : ↥(orthDerived Q)} (hg : orderOf g = p) {J : Subgroup ↥(orthDerived Q)}
    (hJ : IsComponentOf J (Subgroup.centralizer ({g} : Set ↥(orthDerived Q))))
    (hJp : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J)) (hJt : Type167J p J)
    (hWitt : J ≤ (supportedFixedDerived Q (g : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) →
      Module.finrank F V = Module.finrank F (fixedSpace (g : V ≃ₗ[F] V)) + 2 ∧
        (IsPlusType Q ↔ ¬ IsPlusType (Q.comp (fixedSpace (g : V ≃ₗ[F] V)).subtype))) :
    (p = 3 ∧ ∃ n : ℕ, Even n ∧ catalogIs (PSimple 3 J) (isOmMA n 2) ∧
        catalogIs ↥(orthDerived Q) (isOmPA (n + 1) 2)) ∨
      ∃ n k : ℕ, Odd n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs (PSimple p J) (isOmPA n (2 ^ k)) ∧
        catalogIs ↥(orthDerived Q) (isOmMA (n + 1) (2 ^ k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rcases comp_cases_orthDerived_gen hQ hp hp2 hpq hg hJ with
    ⟨h, hh, hne, hq, hJs⟩ | ⟨G, -, hGle, -, hGdim, hJG⟩
  · exact (i167COrth_fixed_special hD hRig hQ hp hp2 hpq hg hh hne hq hJs hJ.2.2 hJp hJt).elim
  · have hJle : J ≤ (supportedFixedDerived Q (g : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) := by
      intro j hj
      rw [hJG] at hj
      exact Subgroup.mem_subgroupOf.2 (hGle (Subgroup.mem_subgroupOf.1 hj))
    obtain ⟨hdimW', hiff⟩ := hWitt hJle
    have hdimW : Module.finrank F (fixedSpace (g : V ≃ₗ[F] V)) = 2 * m := by omega
    have hGeq : G = supportedFixedDerived Q (g : V ≃ₗ[F] V) := hGdim.resolve_left (by omega)
    exact i167COrth_fixed_space hD hRig hb hQ hp hp2 hpq (by omega) hdim hg hdimW hiff
      (by rw [hJG, hGeq]) hJ.2.2 hJp hJt

end CFSG.LocalAnalysis.GLTheoremA.I167

end
