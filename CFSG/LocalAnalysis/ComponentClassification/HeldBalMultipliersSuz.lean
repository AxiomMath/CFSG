module

public import CFSG.LocalAnalysis.ComponentClassification.HeldBalCentre
public import CFSG.Sporadic.Recognition.SuzMultiplier
public import Certificates.Certificate15030
public import Certificates.Certificate15031
public import Certificates.Certificate15033
public import Certificates.Certificate15034
public import Certificates.Certificate15035
import CFSG.RankThree.PerfectCover.HopfCentralCovers

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

theorem card_sylow_two_le_two_of_card {G : Type*} [Group G] [Finite G]
    (hc : Nat.card G = 3 ∨ Nat.card G = 6) (S : Sylow 2 G) : Nat.card S ≤ 2 := by
  have hS : Nat.card S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card (S : Subgroup G)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (S.isPGroup' : IsPGroup 2 S)
  rw [hk] at hS ⊢
  rcases hc with h | h <;> rw [h] at hS
  · have : k = 0 := by
      by_contra hk0
      have := (dvd_pow_self 2 hk0).trans hS
      omega
    subst this
    simp
  · have : k ≤ 1 := by
      by_contra hk1
      have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := h4.trans hS
      omega
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      _ = 2 := by norm_num

theorem centreTwoPartLe_suz_of_card
    (hcard : Nat.card (CFSG.Open.griessHopfMultiplier Blueprint.NativeSporadic.Suz) = 3 ∨
      Nat.card (CFSG.Open.griessHopfMultiplier Blueprint.NativeSporadic.Suz) = 6) :
    CentreTwoPartLe Blueprint.NativeSporadic.Suz 2 := by
  have hfin : Finite (CFSG.Open.griessHopfMultiplier Blueprint.NativeSporadic.Suz) :=
    Nat.finite_of_card_ne_zero (by rcases hcard with h | h <;> omega)
  intro L _ _ hq e S
  exact (RankThree.PerfectCover.hopf_central_cover_consequences
    Blueprint.NativeSporadic.Suz).1 (fun S' => card_sylow_two_le_two_of_card hcard S') L hq e S

open CFSG.CosetTable CFSG.Sporadic.Recognition.SuzMultiplier in
theorem centreTwoPartLe_suz_of_checks
    (hTab : suzTabCheck = true) (hRho0 : suzRho0Check = true)
    (hL0 : SuzIndexP1) (hL1 : SuzIndexP2) (hL2 : SuzCardP2) :
    CentreTwoPartLe Blueprint.NativeSporadic.Suz 2 :=
  centreTwoPartLe_suz_of_card (card_griessHopfMultiplier_Suz hTab hRho0 hL0 hL1 hL2)

theorem centreTwoPartLe_suz_cert :
    CentreTwoPartLe Blueprint.NativeSporadic.Suz 2 :=
  centreTwoPartLe_suz_of_checks Certificates.certificate15030
    Certificates.certificate15031 Certificates.certificate15033
    Certificates.certificate15034 Certificates.certificate15035

end CFSG.ComponentClassification.GrSLit
