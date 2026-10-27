module

public import CFSG.LieType.BorelExponent.Defs
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.ClassicalGroups.Orthogonal.BorelQuotientAbelian
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LieType.BorelExponent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise


theorem pow_card_sub_one_mem_posUnipotentSub {τ : Tag} {K : Type} [Field K] [Finite K]
    [CharP K 2] {b : adjointGroup τ K}
    (hb : b ∈ Subgroup.normalizer (posUnipotentSub τ K : Set (adjointGroup τ K))) :
    b ^ (Nat.card K - 1) ∈ posUnipotentSub τ K := by
  rw [CFSG.ClassicalGroups.Orthogonal.normalizer_posUnipotentSub_eq_borelSub] at hb
  have hbB : (b : ModGL τ K) ∈ borelGroup τ K := hb
  have hstr := triangular_borel_structure.{0, 0} τ K
  have hset : ((borelGroup τ K : Set (Module.End K (RootModule τ K))ˣ)) =
      SetLike.coe (posUnipotent τ K) * SetLike.coe (torusGroup τ K) := hstr.2.2.2.2.2.1
  have hbB' : (b : ModGL τ K) ∈ SetLike.coe (posUnipotent τ K) * SetLike.coe (torusGroup τ K) := by
    rw [← hset]
    exact hbB
  obtain ⟨u, hu, h, hh, hbuh⟩ := Set.mem_mul.1 hbB'
  show ((b ^ (Nat.card K - 1) : adjointGroup τ K) : ModGL τ K) ∈ posUnipotent τ K
  rw [Subgroup.coe_pow, ← hbuh]
  exact mul_pow_mem_of_le_normalizer hstr.2.2.1
    (fun h hh => pow_card_sub_one_eq_one_of_mem_diagonalGroup (hstr.2.1 h hh)) hu hh

theorem hasBorelExponent_of_untwistedChevalleyModel {τ : Tag} {X : Type} [Group X] [Finite X]
    {f : ℕ} (hmodel : UntwistedChevalleyModel X τ (2 ^ f)) : HasBorelExponent X (2 ^ f - 1) := by
  obtain ⟨K, hK, hfin, hcard, ⟨e⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  let e' : X ≃* ↥(adjointGroup τ K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have : Finite ↥(adjointGroup τ K) := Finite.of_equiv X e'.toEquiv
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index (τ := τ) (K := K) 2
    (posUnipotent_le_adjointGroup (K := K)) (card_posUnipotent (τ := τ) (K := K))
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (posUnipotentSub τ K) ⊤ := by
    refine ⟨le_top, hUp, ?_⟩
    rw [show ((posUnipotentSub τ K).subgroupOf ⊤).index = (posUnipotentSub τ K).index from
      Subgroup.relIndex_top_right _]
    exact hUi
  refine HasBorelExponent.of_mulEquiv e'.symm (hasBorelExponent_of_isSylowTwoOf hU ?_)
  intro x hx
  have h := pow_card_sub_one_mem_posUnipotentSub hx
  rwa [hcard] at h

theorem borelExponentAt_F4 : BorelExponentAt .F4 := by
  intro X _ _ m f _ hLie
  obtain ⟨-, hmodel⟩ := (LieModel.chevalleyExceptional_iff (t := .F4) (by decide)).1 hLie
  exact hasBorelExponent_of_untwistedChevalleyModel hmodel.2

theorem borelExponentAt_E6 : BorelExponentAt .E6 := by
  intro X _ _ m f _ hLie
  obtain ⟨-, hmodel⟩ := (LieModel.chevalleyExceptional_iff (t := .E6) (by decide)).1 hLie
  exact hasBorelExponent_of_untwistedChevalleyModel hmodel.2

theorem borelExponentAt_E7 : BorelExponentAt .E7 := by
  intro X _ _ m f _ hLie
  obtain ⟨-, hmodel⟩ := (LieModel.chevalleyExceptional_iff (t := .E7) (by decide)).1 hLie
  exact hasBorelExponent_of_untwistedChevalleyModel hmodel.2

theorem borelExponentAt_E8 : BorelExponentAt .E8 := by
  intro X _ _ m f _ hLie
  obtain ⟨-, hmodel⟩ := (LieModel.chevalleyExceptional_iff (t := .E8) (by decide)).1 hLie
  exact hasBorelExponent_of_untwistedChevalleyModel hmodel.2

end CFSG.LieType.BorelExponent

end
