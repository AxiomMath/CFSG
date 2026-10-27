module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294SporData
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294SporJ3Check
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294SporJ3Sylow
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.Sporadic.Bridge.J3Surj
public import Certificates.Certificate452000
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem j3Native_sylow_central :
    ∃ P Z : Subgroup NativeSporadic.J3, Nat.card P = 3 ^ 5 ∧ Z ≤ P ∧
      (∀ z ∈ Z, ∀ g ∈ P, Commute z g) ∧ Nat.card Z = 3 ^ 2 := by
  obtain ⟨P, Z, hP, hZP, hZc, hZ⟩ := sylowCentral_of_check (spec2 80) (fun _ => trivial)
    j3SylowCentralData Certificates.certificate452000
  exact ⟨P, Z, hP.trans (by norm_num [j3SylowCentralData]), hZP, hZc, hZ⟩

private theorem factorization_three_j3 : (50232960 : ℕ).factorization 3 = 5 := by
  rw [show (50232960 : ℕ) = 3 ^ 5 * 206720 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem j3ThreeCentralizer_native
    (x : NativeSporadic.J3) (hx : orderOf x = 3) :
    3 ^ 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set NativeSporadic.J3)) := by
  obtain ⟨P, Z, hP, hZP, hZc, hZ⟩ := j3Native_sylow_central
  have hfin : Finite NativeSporadic.J3 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.J3.card_J3]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine pow_three_dvd_card_centralizer_of_sylow_central (p := 3) ?_ ?_ hZP hZc hZ hx
  · rw [hP, CFSG.Sporadic.J3.card_J3, factorization_three_j3]
  · rw [hP]
    exact pow_dvd_pow 3 (by norm_num)

theorem three_dvd_card_centralizer_of_carrier (s : TauCeti.SporadicName)
    (hbr : Nonempty (NativeSporadic.Carrier s ≃* s.Group))
    (h : ∀ a : NativeSporadic.Carrier s, orderOf a = 3 →
      3 ^ 3 ∣ Nat.card (Subgroup.centralizer ({a} : Set (NativeSporadic.Carrier s))))
    (x : (TauCeti.CFSGIndex.sporadic s).Group) (hx : orderOf x = 3) :
    3 ^ 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set (TauCeti.CFSGIndex.sporadic s).Group)) := by
  obtain ⟨e⟩ := hbr
  have hx' : orderOf (e.symm x) = 3 := by rw [MulEquiv.orderOf_eq, hx]
  have hcard := sylowCentral_card_centralizer_mulEquiv e (e.symm x)
  rw [MulEquiv.apply_symm_apply] at hcard
  rw [hcard]
  exact h _ hx'

theorem j3ThreeCentralizer_holds :
    J3ThreeCentralizer := by
  intro _ x hx
  exact three_dvd_card_centralizer_of_carrier .J3
    CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv j3ThreeCentralizer_native x hx

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
