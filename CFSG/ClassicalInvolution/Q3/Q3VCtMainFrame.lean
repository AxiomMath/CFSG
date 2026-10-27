module

public import CFSG.ClassicalInvolution.Q3.Q3VCtMainSub
public import CFSG.ClassicalInvolution.Q3.Q3VCtFrFinal

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint CFSG.Assembly.LowTwoRank

private theorem statedLieAdmissible_psp_three {n : ℕ} (hn : 2 ≤ n) :
    StatedLieAdmissible .PSp n 3 1 :=
  ⟨Nat.prime_three, le_rfl, hn, fun h => by simp at h⟩

theorem weakCT_symplectic_of_spFrame {n p f : ℕ} (hadm : StatedLieAdmissible .PSp n p f)
    (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    {X : Type} [Group X] (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (fr : SpFrame F n U) :
    ∃ Ψ : StatedSp n F →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      IsQuasisimple X ∧ Subgroup.center X = (Subgroup.center (StatedSp n F)).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .PSp n p f ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n F).rootGroup k).map Ψ = U k :=
  weakCT_symplectic_of_family hadm hn hF U hgen hcomm fr.ρ (fun k => ⟨fr.ρ_inj k, fr.ρ_range k⟩)
    fr.ψ (fun i h => fr.ψ_zero i _ h rfl) fr.ψ_one fr.ψ4
    (fr.ψ4_long _ (by simp only; omega)) (fr.ψ4_short _ (by simp only; omega))

theorem weakCT_symplectic_subgroup_of_spFrame {n p f : ℕ}
    (hadm : StatedLieAdmissible .PSp n p f) (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) {G : Type} [Group G] (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (fr : SpFrame F n U) :
    ∃ Ψ : StatedSp n F →* G, Ψ.ker ≤ Subgroup.center (StatedSp n F) ∧
      Ψ.range = ⨆ k, U k ∧ IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .PSp n p f ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n F).rootGroup k).map Ψ = U k :=
  weakCT_symplectic_subgroup_of_family hadm hn hF U hcomm fr.ρ
    (fun k => ⟨fr.ρ_inj k, fr.ρ_range k⟩) fr.ψ (fun i h => fr.ψ_zero i _ h rfl) fr.ψ_one fr.ψ4
    (fr.ψ4_long _ (by simp only; omega)) (fr.ψ4_short _ (by simp only; omega))

theorem weakCT3_of_spFrame3 {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X] (U : Fin n → Subgroup X)
    (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (fr : SpFrame3 n U) :
    ∃ Ψ : StatedSp n (GaloisField 3 1) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 3 1)) ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (StatedSp n (GaloisField 3 1))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .PSp n 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n (GaloisField 3 1)).rootGroup k).map Ψ =
        U k :=
  weakCT_symplectic_of_spFrame (statedLieAdmissible_psp_three (by omega)) hn
    (Q3Z.natCard_galoisField_three.trans (pow_one 3).symm) U hgen hcomm fr

theorem weakCT3_of_spFrame3_subgroup {n : ℕ} (hn : 3 ≤ n) {G : Type} [Group G]
    (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (fr : SpFrame3 n U) :
    ∃ Ψ : StatedSp n (GaloisField 3 1) →* G,
      Ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 3 1)) ∧ Ψ.range = ⨆ k, U k ∧
      IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .PSp n 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n (GaloisField 3 1)).rootGroup k).map Ψ =
        U k :=
  weakCT_symplectic_subgroup_of_spFrame (statedLieAdmissible_psp_three (by omega)) hn
    (Q3Z.natCard_galoisField_three.trans (pow_one 3).symm) U hcomm fr

theorem weakCT3_symplectic (hC : Q3Z.V6Collapse) {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    ∃ Ψ : StatedSp n (GaloisField 3 1) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 3 1)) ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (StatedSp n (GaloisField 3 1))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .PSp n 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n (GaloisField 3 1)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨fr⟩ := exists_spFrame3 hC hn U hcomm hpair hsp
  exact weakCT3_of_spFrame3 hn U hgen hcomm fr

theorem weakCT3_symplectic_subgroup (hC : Q3Z.V6Collapse) {n : ℕ} (hn : 3 ≤ n) {G : Type}
    [Group G] (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    ∃ Ψ : StatedSp n (GaloisField 3 1) →* G,
      Ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 3 1)) ∧ Ψ.range = ⨆ k, U k ∧
      IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .PSp n 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n (GaloisField 3 1)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨fr⟩ := exists_spFrame3 hC hn U hcomm hpair hsp
  exact weakCT3_of_spFrame3_subgroup hn U hcomm fr

theorem weakCT3_symplectic_of_check (hVC : Q3Z.V6CollapseCheck) {n : ℕ} (hn : 3 ≤ n) {X : Type}
    [Group X] (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    ∃ Ψ : StatedSp n (GaloisField 3 1) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 3 1)) ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (StatedSp n (GaloisField 3 1))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .PSp n 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n (GaloisField 3 1)).rootGroup k).map Ψ =
        U k :=
  weakCT3_symplectic (Q3Z.v6Collapse_of_check hVC) hn U hgen hcomm hpair hsp

theorem weakCT3_symplectic_subgroup_of_check (hVC : Q3Z.V6CollapseCheck) {n : ℕ} (hn : 3 ≤ n)
    {G : Type} [Group G] (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    ∃ Ψ : StatedSp n (GaloisField 3 1) →* G,
      Ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 3 1)) ∧ Ψ.range = ⨆ k, U k ∧
      IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .PSp n 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n (GaloisField 3 1)).rootGroup k).map Ψ =
        U k :=
  weakCT3_symplectic_subgroup (Q3Z.v6Collapse_of_check hVC) hn U hcomm hpair hsp

end CFSG.ClassicalInvolution.Q3.Q3V
