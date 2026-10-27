module

public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TenArith

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise

set_option linter.unusedSectionVars false


structure E8TenFrame (K L : Type) [Field K] [Field L] [Algebra K L] (ℓ f p : ℕ)
    [Fact ℓ.Prime] [CharP L ℓ] : Type where
  n : ModGL .E8 L
  hnm : n ∈ monomialSubgroup .E8 L
  hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = ((-1 : ℤ) • weylMatrix e8F5U) *ᵥ u
  g0 : ModGL .E8 L
  hg0C : g0 ∈ adjointGroup .E8 L
  hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n
  hperf : ∀ P : Subgroup (ModGL .E8 L), Finite P → P ≤ adjointGroup .E8 L →
    (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
      P ≤ (adjEmb .E8 K L).range
  hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
    (fixedCharTuples (e8FiveM (-1)) (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E8 L)
  hconj : ∀ A : Subgroup (adjointGroup .E8 K), IsPGroup p A → ∃ c : adjointGroup .E8 K,
    ∀ x ∈ A, g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))

theorem exists_e8TenFrame (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 10)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    Nonempty (E8TenFrame K L ℓ f p) := by
  classical
  obtain ⟨hp7', hpq, hΦ10, -⟩ := e8Ten_arith hp hp7 he
  have hp5 : 5 < p := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  have hcm := canonicalRep_mem_monomialSubgroup L (e8F5C ^ 21)
  set n : ModGL .E8 L := canonicalRep (coxeterSystem .E8) L (e8F5C ^ 21) with hn
  have hπ : weylQuotientHom .E8 L ⟨n, hcm⟩ = e8F5C ^ 21 :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep (e8F5C ^ 21))
  have hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hcm⟩ • u = ((-1 : ℤ) • weylMatrix e8F5U) *ᵥ u :=
    fun u => by
      rw [hπ, ← weylMatrix_mulVec, weylMatrix_e8F5C_21, neg_one_smul]
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hcm
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hT : twistedTorusOf n Φ =
      (fixedCharTuples (e8FiveM (-1)) Fr).map (rootDiagUnitHom .E8 L) := by
    have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
    rw [show e8FiveM (-1) = (-1 : ℤ) • weylMatrix e8F5U from rfl, ← h]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hcm _ rfl Fr
  set G4 := fixedBlockTuples (e8FiveM (-1)) Fr
    (e8FiveCols 4 (-1) '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG4
  set G0 := fixedBlockTuples (e8FiveM (-1)) Fr
    (e8FiveCols 0 (-1) '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG0
  set N : ℕ := (((Nat.card K : ℤ) ^ 4 + (-1) * (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
    (-1) * (Nat.card K : ℤ) + 1).natAbs) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .E8 L) := (G4 ⊔ G0).map (rootDiagUnitHom .E8 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e8Five_card_sup (-1) (Or.inr rfl) Fr hFr hℓ hℓq hq2
  have hN : N ≠ 0 := by
    refine pow_ne_zero 2 (Int.natAbs_ne_zero.2 ?_)
    have := e8FiveP_eval_ne_zero (-1) (Or.inr rfl) hq2
    rwa [e8FiveP_eval] at this
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p = p ^ N.factorization p :=
    e8Five_ordProj K (-1) (Or.inr rfl) hp hp5 (m := 10) (Or.inr rfl) he hpq
      (e8Five_hΦ_neg _ hΦ10)
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E8 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp (by omega) n hnC Z0 hZ0le hN hZ0card hord
  refine ⟨⟨n, hcm, hnW, g0, hg0C, hg0, hperf, hT, fun A hA => ?_⟩⟩
  obtain ⟨c, hc⟩ := hconj A hA
  exact ⟨c, fun x hx => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc x hx))⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
