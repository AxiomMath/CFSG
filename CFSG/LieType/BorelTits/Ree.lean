module

public import CFSG.LieType.Ree.ReePerfect
public import CFSG.LieType.BorelTits.DerivedQuotient
public import CFSG.LieType.BorelTits.Classical

public section

namespace CFSG.LieType.BorelTits

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem holds_reeDerivedQuotient (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime]
    (a : ℕ) (ha : 1 ≤ a) (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    Holds (DerivedCentralQuotient (reeFixedGroup t.tag K t.perm (fun i => if i ∈ t.longSet
      then t.prime ^ a else t.prime ^ (a + 1)))) t.prime := by
  have : Fact t.prime.Prime := ⟨by cases t <;> decide⟩
  obtain ⟨S, hS⟩ := exists_sylow_reeFixed t K a
  have hSle : (S : Subgroup (reeFixed t K a)) ≤ commutator (reeFixed t K a) := by
    intro x hx
    rw [hS] at hx
    obtain ⟨y, hy, hyx⟩ := reeFixed_U_le_derived t K a ha hK x hx x.2
    rwa [Subtype.ext hyx] at hy
  exact holds_derivedCentralQuotient _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed t K a)).trans
      ((reeFixed t K a).equivMapOfInjective _ Subtype.val_injective).symm)
    (holds_reeFixed t K a) S hSle

theorem holds_of_reeTitsModel {G : Type} [Group G]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {p f : ℕ} (h : ReeTitsModel G t p f)
    (ht : t ≠ .Tits) : Holds G p := by
  obtain ⟨hadm, a, hf, hmodel⟩ := h
  cases t
  all_goals try exact hmodel.elim
  ·
    obtain ⟨-, -, -, hp, -, h3⟩ := hadm
    subst hp
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hc : CharP K 3 := charP_of_natCard_eq hK
    have : CharP K ReeTag.G2.prime := hc
    exact (holds_reeDerivedQuotient .G2 K a (by omega) (by rw [hK, hf]; rfl)).of_mulEquiv e.symm
  ·
    obtain ⟨-, -, -, hp, -, h3⟩ := hadm
    subst hp
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
    have : Fact (Nat.Prime 2) := ⟨by decide⟩
    have hc : CharP K 2 := charP_of_natCard_eq hK
    have : CharP K ReeTag.F4.prime := hc
    exact (holds_reeDerivedQuotient .F4 K a (by omega) (by rw [hK, hf]; rfl)).of_mulEquiv e.symm
  · exact absurd rfl ht

end CFSG.LieType.BorelTits
