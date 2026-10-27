module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.RuTypeF4

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Quasithin
open scoped MatrixGroups commutatorElement

theorem toGL_surjective_SL32 :
    Function.Surjective (Matrix.SpecialLinearGroup.toGL : SL(3, ZMod 2) → GL (Fin 3) (ZMod 2)) :=
  fun A => by
  refine ⟨⟨A, ?_⟩, Units.ext rfl⟩
  have h : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  have := congrArg Units.val h
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this

theorem pCore_two_SL32 : CFSG.Open.pCore 2 SL(3, ZMod 2) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : SL(3, ZMod 2) ≃* GL (Fin 3) (ZMod 2) := MulEquiv.ofBijective
    Matrix.SpecialLinearGroup.toGL ⟨Matrix.SpecialLinearGroup.toGL_injective, toGL_surjective_SL32⟩
  have : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := GHarris.isSimpleGroup_GL32_gh
  have : IsSimpleGroup SL(3, ZMod 2) := e.isSimpleGroup
  rcases (CFSG.LieType.BorelTits.pCore_normal (G := SL(3, ZMod 2)) 2).eq_bot_or_eq_top with h | h
  · exact h
  exfalso
  have hp := CFSG.LieType.BorelTits.pCore_isPGroup (G := SL(3, ZMod 2)) 2
  rw [h] at hp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hp.of_equiv Subgroup.topEquiv)
  rw [Nat.card_congr e.toEquiv, GHarris.card_GL32_gh] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 168)
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

variable {G : Type} [Group G]

theorem pCoreOf_eq_of_SL32 {L S : Subgroup G} (θ : L →* SL(3, ZMod 2))
    (hθ : Function.Surjective θ) (hker : θ.ker = S.subgroupOf L) (hSL : S ≤ L)
    (hS : IsPGroup 2 S) : pCoreOf 2 L = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCoreOf 2 hSL (hker ▸ θ.normal_ker) hS)
  have h1 : (CFSG.Open.pCore 2 L).map θ = ⊥ :=
    le_bot_iff.mp ((CFSG.LieType.BorelTits.map_pCore_le 2 θ hθ).trans pCore_two_SL32.le)
  have h2 : CFSG.Open.pCore 2 L ≤ S.subgroupOf L := hker ▸ (Subgroup.map_eq_bot_iff _).mp h1
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (h2 hx)

end CFSG.ComponentClassification.GMS78
