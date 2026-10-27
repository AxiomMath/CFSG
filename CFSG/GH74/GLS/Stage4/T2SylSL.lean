module

public import CFSG.GH74.GLS.Stage4.T2CentSL
public import CFSG.GH74.GLS.IVK.Lifted.SL2TwoOrder
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup
public import CFSG.GH74.GLS.Stage4.T2SL2C

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open CFSG.GH74.GLS.IVK.Lifted (comm_of_commute_matrix nonscalar_of_not_mem_center two_power_order_sl2_le)
open CFSG.ABGLocalTools (isCyclic_of_isPGroup_two_of_comm)

theorem t2C_cent_sylow_sl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (P : Subgroup (SL2 F)) (hP : IsPGroup 2 ↥P) (hPidx : ¬ 2 ∣ P.index)
    (x : SL2 F) (hx : ∀ p ∈ P, x * p = p * x) : x = 1 ∨ x = negOne F := by
  by_contra hxne
  rw [not_or] at hxne
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hxc : x ∉ Subgroup.center (SL2 F) := fun h =>
    ((t2C_center_sl2 x).1 h).elim hxne.1 hxne.2
  have hns := nonscalar_of_not_mem_center x hxc
  have hcomm : ∀ a b : ↥P, a * b = b * a := by
    intro a b
    apply Subtype.ext
    have key : ∀ y : ↥P, ((y : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) =
        (x : Matrix (Fin 2) (Fin 2) F) * ((y : SL2 F) : Matrix (Fin 2) (Fin 2) F) := by
      intro y
      have := congrArg (fun z : SL2 F => (z : Matrix (Fin 2) (Fin 2) F)) (hx y y.2).symm
      simpa [Matrix.SpecialLinearGroup.coe_mul] using this
    exact comm_of_commute_matrix _ hns a b (key a) (key b)
  have huniq : ∀ u v : ↥P, orderOf u = 2 → orderOf v = 2 → u = v := by
    have hinv : ∀ u : ↥P, orderOf u = 2 → (u : SL2 F) = negOne F := by
      intro u hu
      have hu2 : u * u = 1 := by
        have h := pow_orderOf_eq_one u
        rw [hu, pow_two] at h
        exact h
      have hu1 : u ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hu
        omega
      refine eq_negOne_of_involution h2 ?_ ?_
      · exact congrArg Subtype.val hu2
      · intro h
        exact hu1 (Subtype.ext h)
    intro u v hu hv
    exact Subtype.ext ((hinv u hu).trans (hinv v hv).symm)
  have hcyc : IsCyclic ↥P := isCyclic_of_isPGroup_two_of_comm hP hcomm huniq
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hidx : P.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hval : (Nat.card (SL2 F)).factorization 2 = n := by
    rw [← Subgroup.card_mul_index P, hn, Nat.factorization_mul (by positivity) hidx]
    simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hPidx]
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgord : orderOf g = 2 ^ n := by
    rw [← hn]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hle := two_power_order_sl2_le hodd (g : SL2 F) (k := n)
    (by rw [Subgroup.orderOf_coe, hgord])
  rw [hval, pow_succ] at hle
  have hpos : 0 < 2 ^ n := by positivity
  omega

end CFSG.GH74.GLS.Stage4.Rest
