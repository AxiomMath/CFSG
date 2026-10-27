module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sec
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

structure Cfg55E (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S T Tstar : Subgroup G)
    (p : ℕ) (H P : Subgroup G) (g : G) (X Y : Subgroup G) : Prop where
  ctx : Stage2Ctx G z k S
  c51 : Ctx51 k z S T Tstar p H P
  hnot : ¬ Concl51 k S p H P
  l52 : L52 k S T Tstar p H P
  s53 : Step53 p H P g X Y
  two : ¬ TypeOneCase G k

theorem H_ne_top_of_ctx51 {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S T Tstar : Subgroup G} {p : ℕ} {H P : Subgroup G} (ctx : Stage2Ctx G z k S)
    (c51 : Ctx51 k z S T Tstar p H P) : H ≠ ⊤ := by
  intro hH
  have hp : Fact p.Prime := ⟨c51.prime⟩
  have hF : Fs H = Op p H := c51.fstar
  have hsimple : IsSimpleGroup G := ctx.std.kps.1
  have hnab : ∃ a b : G, a * b ≠ b * a := ctx.std.kps.2.1
  subst hH
  have hgen : generalizedFitting ↥(⊤ : Subgroup G) = pCore p ↥(⊤ : Subgroup G) :=
    Subgroup.map_injective (⊤ : Subgroup G).subtype_injective hF
  let e : ↥(⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  have hsimple' : IsSimpleGroup ↥(⊤ : Subgroup G) := (e.isSimpleGroup_congr).2 hsimple
  rcases hsimple'.eq_bot_or_eq_top_of_normal (pCore p ↥(⊤ : Subgroup G)) with hbot | htop
  · have hc := centralizer_generalizedFitting_le ↥(⊤ : Subgroup G)
    rw [hgen, hbot] at hc
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(⊤ : Subgroup G))
    apply hx
    have hx' : x ∈ Subgroup.centralizer (((⊥ : Subgroup ↥(⊤ : Subgroup G)) :
        Subgroup ↥(⊤ : Subgroup G)) : Set ↥(⊤ : Subgroup G)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have : y = 1 := hy
      rw [this]
      simp
    exact Subgroup.mem_bot.mp (hc hx')
  · have hP' : IsPGroup p ↥(⊤ : Subgroup G) := by
      intro y
      have hy : y ∈ pCore p ↥(⊤ : Subgroup G) := by rw [htop]; trivial
      obtain ⟨m, hm⟩ := (pCore_isPGroup (p := p) (G := ↥(⊤ : Subgroup G))) ⟨y, hy⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have hnil : Group.IsNilpotent ↥(⊤ : Subgroup G) := hP'.isNilpotent
    have hsol : Group.IsSolvable ↥(⊤ : Subgroup G) := @IsNilpotent.to_isSolvable _ _ hnil
    have hcomm := hsimple'.comm_iff_isSolvable.mpr hsol
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (by
      have := congrArg e (hcomm (e.symm a) (e.symm b))
      simpa using this)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
