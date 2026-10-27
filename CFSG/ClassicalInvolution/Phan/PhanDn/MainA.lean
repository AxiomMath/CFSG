module

public import CFSG.LocalAnalysis.StandardType.PhanDLift
public import CFSG.ClassicalInvolution.Phan.PhanDn.Dictionary
public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamilyGood
public import CFSG.ClassicalInvolution.Phan.PhanDn.SpinModel
public import CFSG.ClassicalInvolution.Phan.PhanDn.PointFibration
public import CFSG.ClassicalInvolution.Phan.PhanDn.Quadrangles
public import CFSG.ClassicalInvolution.Phan.PhanDn.Triangles
public import CFSG.ClassicalInvolution.Phan.PhanDn.Pentagons

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

section

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem cycleTrivial_solidWalks (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) {n : ℕ} (hn : 4 ≤ n) :
    CycleTrivial (solidWalks σ n) :=
  cycleTrivial_solidWalks_of_nullLen (n := n) hσ hK hq hn
    (nullLen_three (n := n) hσ hK hq)
    (nullLen_four_of_nullLen_three (n := n) hσ hK hq hn (nullLen_three (n := n) hσ hK hq))

theorem simplyTwoConnected_dChamberSystem (hσ : IsUnitaryInvolution σ) [Finite K] [CharP K 2]
    {q : ℕ} (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) {m : ℕ} (hm : 2 ≤ m) :
    (dChamberSystem σ m).SimplyTwoConnected :=
  simplyTwoConnected_dChamberSystem_of_cycleTrivial hσ hK hq
    (fun _ hn => cycleTrivial_solidWalks hσ hK hq hn) hm

theorem dChamberSystemConnected_holds :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ), Nat.card K = (2 ^ f) ^ 2 →
      4 ≤ 2 ^ f → ∀ m : ℕ, 3 ≤ m →
        (dChamberSystem (unitaryInvolution K 2 f) m).Connected := by
  intro K _ _ _ f hK hq m hm
  exact connected_dChamberSystem (K := K) (σ := unitaryInvolution K 2 f) (q := 2 ^ f) (m := m)
    (isUnitaryInvolution_unitaryInvolution (p := 2) (f := f) hK) hK hq (by omega)

theorem dChamberSystemSimplyTwoConnected_holds :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ), Nat.card K = (2 ^ f) ^ 2 →
      4 ≤ 2 ^ f → ∀ m : ℕ, 3 ≤ m →
        (dChamberSystem (unitaryInvolution K 2 f) m).SimplyTwoConnected := by
  intro K _ _ _ f hK hq m hm
  exact simplyTwoConnected_dChamberSystem (K := K) (σ := unitaryInvolution K 2 f) (q := 2 ^ f)
    (m := m) (isUnitaryInvolution_unitaryInvolution (p := 2) (f := f) hK) hK hq (by omega)

end

theorem phanDUniversal_of_dChamberSystem : PhanDUniversal := by
  have hconn := dChamberSystemConnected_holds
  have hsc := dChamberSystemSimplyTwoConnected_holds
  intro K _ _ f _ hK hq n hn
  have hf : f ≠ 0 := by rintro rfl; norm_num at hq
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  let _ : Algebra (GaloisField 2 f) K := Classical.choice (Aniso.nonempty_algebra hF hK)
  let E := quadExt_of_card_of_char_two (F := GaloisField 2 f) f hF hK
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 3 ≤ m := by omega
  have hU : (stdFamilyΩ E m hm hK hq).IsUniversal :=
    isUniversal_stdFamilyΩ_of_dChamberSystem E hm hK hq (stdFamilyΩ_good E m hm hK hq)
      (hconn K f hK hq m hm) (hsc K f hK hq m hm)
  exact ⟨fun he => ⟨_, hU.map (omegaEquivLieUniversalPlus E he (by omega))⟩,
    fun ho => ⟨_, hU.map (omegaEquivLieUniversalMinus E ho (by omega))⟩⟩

theorem phanDInput2_of_dChamberSystem :
    CFSG.ClassicalInvolution.Phan.PhanDInput2 :=
  phanDInput2_of_phanDUniversal phanDUniversal_of_dChamberSystem

theorem phanDInput2_holds : CFSG.ClassicalInvolution.Phan.PhanDInput2 :=
  phanDInput2_of_dChamberSystem

end CFSG.ClassicalInvolution.PhanDn

end
