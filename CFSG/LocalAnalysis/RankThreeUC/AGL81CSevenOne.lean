module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

@[expose] def SevenOneOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ L : Subgroup X,
    CFSG.IsComponent L → L.Normal →
      ∃ n : ℕ, derivedSeries X n ≤ L ⊔ centralizer (L : Set X)

@[expose] def SevenOneThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ L : Subgroup X, CFSG.IsComponent L → L.Normal →
      (CFSG.Open.pRank p L = 1 ∨ CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 ∨
        CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) →
      ∃ N : Subgroup X, N.Normal ∧ L ⊔ centralizer (L : Set X) ≤ N ∧
        (∃ k : ℕ, (L ⊔ centralizer (L : Set X)).relIndex N = p ^ k) ∧ ¬ p ∣ N.index

@[expose] def SevenOneFourChev : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ L : Subgroup X, CFSG.IsComponent L → L.Normal → CFSG.Open.pRank p L ≤ 1 →
      (∃ x : X, (∃ k : ℕ, orderOf x = p ^ k) ∧ x ∉ L ⊔ centralizer (L : Set X)) →
      ∃ d : TauCeti.ValidLieTypeIndex,
        Nonempty (↥L ⧸ center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def SevenOneFourField : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ L : Subgroup X, CFSG.IsComponent L → L.Normal → CFSG.Open.pRank p L = 1 →
    ∀ x : X, x ∉ L ⊔ centralizer (L : Set X) → x ^ p ∈ L ⊔ centralizer (L : Set X) →
      ∃ l ∈ L, (x * l) ^ p ∈ centralizer (L : Set X) ∧
        ∃ z ∈ L, orderOf z = p ∧ x * l * z = z * (x * l)

@[expose] def SevenOneFourSplit : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ L : Subgroup X, CFSG.IsComponent L → L.Normal → CFSG.Open.pRank p L = 1 →
      ∃ W : Subgroup X, centralizer (L : Set X) ≤ W ∧ W ⊓ L ≤ centralizer (L : Set X) ∧
        oPPrimeHull p (⊤ : Subgroup X) ≤ L ⊔ W ∧
        (∃ g ∈ W, (∃ k : ℕ, g ^ (p ^ k) ∈ centralizer (L : Set X)) ∧
          ∀ w ∈ W, ∃ n : ℕ, w * (g ^ n)⁻¹ ∈ centralizer (L : Set X)) ∧
        ∀ w ∈ W, w ^ p ∈ centralizer (L : Set X) → ∃ z ∈ L, orderOf z = p ∧ w * z = z * w

@[expose] def SevenOneSeven : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ L : Subgroup X,
    CFSG.IsComponent L → L.Normal → CFSG.Open.pRank 3 L = 3 →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 →
      ¬ 3 ∣ (L ⊔ centralizer (L : Set X)).index ∨
        IsPSLType 2 (GaloisField 3 3) (↥L ⧸ center ↥L)

@[expose] def KFactCenterRankFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ L : Subgroup X,
    CFSG.IsComponent L → ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card (center ↥L) →
      3 ≤ CFSG.Open.pRank p L

theorem not_dvd_card_center_of_pRank_eq_one (h72 : KFactOmegaNotCentral) {X : Type} [Group X]
    [Finite X] (hX : CFSG.Open.IsKGroup X) {L : Subgroup X} (hL : CFSG.IsComponent L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : CFSG.Open.pRank p L = 1) :
    ¬ p ∣ Nat.card (center ↥L) := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥L)) p hdvd
  let z : X := ((z₀ : ↥L) : X)
  have hzval : z = ((z₀ : ↥L) : X) := rfl
  have hzL : z ∈ L := by rw [hzval]; exact (z₀ : ↥L).2
  have hzord : orderOf z = p := by
    rw [hzval, orderOf_submonoid, orderOf_submonoid]
    exact hz₀
  have hzcent : z ∈ Subgroup.centralizer (L : Set X) := by
    rw [hzval, Subgroup.mem_centralizer_iff]
    intro y hy
    have hcomm := Subgroup.mem_center_iff.mp z₀.2 (⟨y, hy⟩ : ↥L)
    simpa using congrArg (fun w : ↥L => (w : X)) hcomm
  have hcenter_dvd : Nat.card (center ↥L) ∣ Nat.card ↥L :=
    Subgroup.card_subgroup_dvd_card (center ↥L)
  have hpL : p ∣ Nat.card ↥L := dvd_trans hdvd hcenter_dvd
  obtain ⟨e, heL, heord, hnc⟩ := h72 X hX L hL p hp hp2 hpL
  have hzpow : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hAab : CFSG.Open.IsElemAbelian p (Subgroup.zpowers z) :=
    CFSG.Open.isElemAbelian_zpowers hzpow
  have hAcard : Nat.card (Subgroup.zpowers z) = p ^ 1 := by
    rw [Nat.card_zpowers, hzord, pow_one]
  have hAC : Subgroup.zpowers z ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.zpowers_le.mpr hzcent
  obtain ⟨hEab, hEcard⟩ := isElemAbelian_sup_zpowers hp hAab hAcard hAC heL heord hnc
  have hE_le : Subgroup.zpowers z ⊔ Subgroup.zpowers e ≤ L :=
    sup_le (Subgroup.zpowers_le.mpr hzL) (Subgroup.zpowers_le.mpr heL)
  have h2 : 2 ≤ CFSG.Open.pRank p L := by
    refine CFSG.SectionRank.le_pRank hp.one_lt hE_le hEab ?_
    simpa using hEcard
  omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
