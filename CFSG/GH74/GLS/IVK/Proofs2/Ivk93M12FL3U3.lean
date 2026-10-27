module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Leaves
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12FL2
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovL3U3

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint
open CFSG.GH74.KGroups.L3Eps (tInv tInv_mul_self tInv_ne_one exists_projectiveSL_equiv)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

namespace Ivk93M12FL3U3

theorem false_of_quasisimple_le_centralizer {J : Type} [Group J] {y : J}
    (hsol : Group.IsSolvable ↥(centralizer ({y} : Set J))) {S : Subgroup J}
    (hS : CFSG.IsQuasisimple ↥S) (hle : S ≤ centralizer ({y} : Set J)) : False := by
  have : Group.IsSolvable ↥S :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hS this

end Ivk93M12FL3U3

theorem ivk93m12_l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93M12Empty (fun X _ => LieModel X .PSL 3 p f) := by
  intro p f hp hp2 hf J _ _ hJ y hD
  have hy2 : orderOf y = 2 := hD.central.1
  have hyy : y * y = 1 := by rw [← sq, ← hy2]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy2; omega
  by_cases hq3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := ivk93cov_eq_three hp hf hq3
    have h1 := CFSG.GH74.twoRank_le_two_of_lieModel_PSL_three_three hJ
    have h2 := Ivk93M12TwoRank.three_le_twoRank hD
    omega
  · have h5 := ivk93cov_five_le_pow hp hp2 hf hq3
    have hst := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hst
    have hodd : Odd (Nat.card F) := by
      rw [hF]
      exact (hp.odd_of_ne_two hp2).pow
    have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
    have h5' : 5 ≤ Nat.card F := by
      rw [hF]
      exact h5
    have hex2 : e y * e y = 1 := by rw [← map_mul, hyy, map_one]
    have hex1 : e y ≠ 1 := fun h1 => hy1 (e.injective (h1.trans (map_one e).symm))
    obtain ⟨g, hg⟩ := Generic.S3.singleInv_projectiveSL h2 (e y) tInv hex2 hex1 tInv_mul_self
      (tInv_ne_one h2)
    let e' : J ≃* projectiveSL 3 F := e.trans (MulAut.conj g)
    have he' : e' y = tInv := by
      show MulAut.conj g (e y) = tInv
      rw [MulAut.conj_apply]
      exact hg
    obtain ⟨S, hSq, -, hSle, -, -⟩ := ivk93cov_l3_data h2 (by omega) e' he'
    exact Ivk93M12FL3U3.false_of_quasisimple_le_centralizer hD.solvable hSq hSle

theorem u33_no_data : ∀ (J : Type) [Group J] [Finite J], LieModel J .PSU 3 3 1 →
    ∀ y : J, Ivk93M12Data J y → False := by
  intro J _ _ hJ y hD
  have h1 := CFSG.GH74.twoRank_le_two_of_lieModel_PSU_three_three hJ
  have h2 := Ivk93M12TwoRank.three_le_twoRank hD
  omega

theorem ivk93m12_u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93M12Empty (fun X _ => LieModel X .PSU 3 p f) := by
  intro p f hp hp2 hf J _ _ hJ y hD
  by_cases hq3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := ivk93cov_eq_three hp hf hq3
    exact u33_no_data J hJ y hD
  · have hy2 : orderOf y = 2 := hD.central.1
    have hyy : y * y = 1 := by rw [← sq, ← hy2]; exact pow_orderOf_eq_one y
    have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy2; omega
    have h5 := ivk93cov_five_le_pow hp hp2 hf hq3
    have hst := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
    obtain ⟨S, hInv⟩ := ((Generic.S3.libData_uni hp hp2 h5) J hst).1 y hyy hy1
    exact Ivk93M12FL3U3.false_of_quasisimple_le_centralizer hD.solvable hInv.quasisimple
      hInv.le_centralizer

end CFSG.GH74.GLS.IVK.Proofs2
