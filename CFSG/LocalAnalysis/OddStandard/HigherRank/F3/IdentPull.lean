module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.F3.Ident

open Subgroup CFSG
open scoped commutatorElement

theorem exists_perfect_pullback {S J Y : Type} [Group S] [Finite S] [Group J] [Finite J]
    [Group Y] (π : S →* Y) (φ : J →* Y) (hπ : Function.Surjective π) (hk : π.ker ≤ center S)
    (hJ : Group.IsPerfect J) :
    ∃ (P : Type) (_ : Group P) (_ : Finite P) (ρ : P →* J) (σ : P →* S),
      Group.IsPerfect P ∧ Function.Surjective ρ ∧ ρ.ker ≤ center P ∧
        ∀ p : P, π (σ p) = φ (ρ p) := by
  let F : Subgroup (S × J) := (π.comp (MonoidHom.fst S J)).eqLocus (φ.comp (MonoidHom.snd S J))
  let P : Type := ↥(Quasithin.perfectCore F)
  let ρ : P →* J := (MonoidHom.snd S J).comp (Quasithin.perfectCore F).subtype
  let σ : P →* S := (MonoidHom.fst S J).comp (Quasithin.perfectCore F).subtype
  have hperfect : Group.IsPerfect P :=
    Subgroup.isPerfect_iff.mpr (Quasithin.perfectCore_perfect F)
  have hFtop : F.map (MonoidHom.snd S J) = ⊤ := by
    rw [eq_top_iff]
    intro j _
    obtain ⟨s, hs⟩ := hπ (φ j)
    exact Subgroup.mem_map.mpr ⟨(s, j), hs, rfl⟩
  have htop : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = ⊤ := by
    rw [← commutator_def]
    exact hJ.commutator_eq_top
  have hρrange : ρ.range = ⊤ := by
    dsimp only [ρ]
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Quasithin.map_perfectCore, hFtop,
      Quasithin.perfectCore_eq_self_of_perfect htop]
  refine ⟨P, inferInstance, inferInstance, ρ, σ, hperfect,
    MonoidHom.range_eq_top.mp hρrange, ?_, ?_⟩
  ·
    intro p hp
    have hj : (p : S × J).2 = 1 := by
      show ρ p = 1
      exact MonoidHom.mem_ker.mp hp
    have hpF : (p : S × J) ∈ F := Quasithin.perfectCore_le F p.2
    have heq : π (p : S × J).1 = φ (p : S × J).2 := hpF
    have hs : (p : S × J).1 ∈ center S := by
      apply hk
      rw [MonoidHom.mem_ker, heq, hj, map_one]
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    apply Prod.ext
    · show (q : S × J).1 * (p : S × J).1 = (p : S × J).1 * (q : S × J).1
      exact Subgroup.mem_center_iff.mp hs (q : S × J).1
    · show (q : S × J).2 * (p : S × J).2 = (p : S × J).2 * (q : S × J).2
      rw [hj, mul_one, one_mul]
  ·
    intro p
    exact Quasithin.perfectCore_le F p.2

end CFSG.OddStandard.HigherRank.F3.Ident
