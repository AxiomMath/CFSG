module

public import CFSG.RankThree.PartOne.KE.E8TwelveData
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TwelveArith

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise

set_option linter.unusedSectionVars false


structure E8TwelveFrame (K L : Type) [Field K] [Field L] [Algebra K L] (ℓ f p : ℕ)
    [Fact ℓ.Prime] [CharP L ℓ] : Type where
  n : ModGL .E8 L
  hnm : n ∈ monomialSubgroup .E8 L
  hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8T12WW
  g0 : ModGL .E8 L
  hg0C : g0 ∈ adjointGroup .E8 L
  hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n
  hperf : ∀ P : Subgroup (ModGL .E8 L), Finite P → P ≤ adjointGroup .E8 L →
    (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
      P ≤ (adjEmb .E8 K L).range
  hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
    (fixedCharTuples e8T12V (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E8 L)
  hconj : ∀ A : Subgroup (adjointGroup .E8 K), IsPGroup p A → ∃ c : adjointGroup .E8 K,
    ∀ x ∈ A, g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))

theorem exists_e8TwelveFrame (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 12)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    Nonempty (E8TwelveFrame K L ℓ f p) := by
  classical
  obtain ⟨hp7', hpq, hΦ, hpf⟩ := e8Twelve_arith hp hp7 he
  have hp3 : 3 < p := by omega
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
  have hcm := canonicalRep_mem_monomialSubgroup L ((coxeterSystem .E8).wordProd e8T12WW)
  set n : ModGL .E8 L :=
    canonicalRep (coxeterSystem .E8) L ((coxeterSystem .E8).wordProd e8T12WW) with hn
  have hπ : weylQuotientHom .E8 L ⟨n, hcm⟩ = (coxeterSystem .E8).wordProd e8T12WW :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hcm
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hnWv : ∀ u, weylQuotientHom .E8 L ⟨n, hcm⟩ • u = e8T12V *ᵥ u := fun u => by
    rw [hπ]
    exact e8T12_weylImage u
  have hT : twistedTorusOf n Φ = (fixedCharTuples e8T12V Fr).map (rootDiagUnitHom .E8 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnWv Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hcm _ rfl Fr
  set G1 := fixedBlockTuples e8T12V Fr
    (e8T12Bas e8T12B1List e8T12B2List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG1
  set G2 := fixedBlockTuples e8T12V Fr
    (e8T12Bas e8T12B2List e8T12B1List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG2
  set N : ℕ := (Nat.card K ^ 4 - Nat.card K ^ 2 + 1) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .E8 L) := (G1 ⊔ G2).map (rootDiagUnitHom .E8 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e8T12_card_sup Fr hFr hℓ hℓq hq2
  have h24 : Nat.card K ^ 2 ≤ Nat.card K ^ 4 :=
    Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) hq2) (by norm_num)
  have hN : N ≠ 0 := pow_ne_zero 2 (by omega)
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p = p ^ N.factorization p :=
    e8T12_ordProj hp hp3 hpq he
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E8 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp hp3 n hnC Z0 hZ0le hN hZ0card hord
  refine ⟨⟨n, hcm, hπ, g0, hg0C, hg0, hperf, hT, fun A hA => ?_⟩⟩
  obtain ⟨c, hc⟩ := hconj A hA
  exact ⟨c, fun x hx => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc x hx))⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
