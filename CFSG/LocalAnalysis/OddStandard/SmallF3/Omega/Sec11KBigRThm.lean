module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
import CFSG.ClassicalInvolution.QuaternionStructure.Witness
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigRTr
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigREven
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigRQuat
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115cA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem s900_witness_of_semidihedral [Finite G] {X P : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    (hP : IsSylow2Of P X) (hPsd : Nonempty (↥P ≃* CFSG.Open.SemidihedralGroup n))
    (hXP : oddCoreIn X ⊔ P ≠ X) {z : G} (hzX : z ∈ X) (hz2 : orderOf z = 2)
    (hXH : X ≤ centralizer ({z} : Set G))
    (hXn : ∀ h ∈ centralizer ({z} : Set G), ∀ x ∈ X, h * x * h⁻¹ ∈ X) :
    ∃ J : Subgroup G, z ∈ J ∧ CFSG.Open.IsSubnormal J (centralizer ({z} : Set G)) ∧
      ∃ Sy : Sylow 2 J, (∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((Sy : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
      CFSG.Open.classicalInvolutionWitness J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzc : ∀ x ∈ X, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hXH hx)
  have huniq : ∀ s ∈ oTwoRes X, orderOf s = 2 → s = z :=
    s900_oTwoRes_unique_inv hn hP hPsd hzX hz2 hzc
  have h2 : 2 ∣ Nat.card (oTwoRes X) := s900_oTwoRes_even hP hXP
  have hgen : oTwoRes (oTwoRes X) = oTwoRes X := s900_oTwoRes_idem X
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(oTwoRes X)) := inferInstance
  obtain ⟨J, hJE, hJn, hw, S', hS'⟩ :=
    CFSG.ClassicalInvolution.exists_witness_of_not_isPGroup (oTwoRes X) S
      (s900_sylow_quaternion hgen h2 huniq S) (s900_not_isPGroup_quot hgen h2)
  have hEH : oTwoRes X ≤ centralizer ({z} : Set G) := (sec11c_oTwoRes_le X).trans hXH
  have hEn : ((oTwoRes X).subgroupOf (centralizer ({z} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hEH]
    intro e h he hh
    exact sec11c_conj_mem_oTwoRes (hXn h hh) he
  have hzJ : z ∈ J := by
    obtain ⟨r, -, ⟨eq⟩⟩ := hS'
    have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
    have hcard : Nat.card (S' : Subgroup J) = 2 * (2 * 2 ^ (r - 2)) := by
      rw [Nat.card_congr eq.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      ring
    have h2J : 2 ∣ Nat.card J :=
      (Dvd.intro _ hcard.symm).trans (Subgroup.card_subgroup_dvd_card _)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2J
    have hxz : (x : G) = z := huniq _ (hJE x.2) (by rw [Subgroup.orderOf_coe, hx])
    exact hxz ▸ x.2
  exact ⟨J, hzJ, .step hJE hJn (.step hEH hEn (.refl _)), S', hS', hw⟩

end CFSG.OddStandard.SmallF3.Omega
