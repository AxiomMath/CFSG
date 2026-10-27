module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.QuotientAEmpty
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.FStarBar
public import CFSG.ClassicalInvolution.Q3.TA3SmallDescent

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

structure Q8Bridge (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (N : Subgroup Y) [N.Normal] : Prop where
  central : N ≤ Subgroup.center Y
  two : IsPGroup 2 ↥N
  not_mem : t ∉ N
  q8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)
  quot : Q8Quot R S t N
  simple : IsSimpleGroup ↥(genFittingFStar (Y ⧸ N))
  nonab : ∃ a b : ↥(genFittingFStar (Y ⧸ N)), a * b ≠ b * a
  aEmpty : AEmpty (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
    (tightCore (R.map (QuotientGroup.mk' N)))

variable {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem q8Bridge_of_centTwin (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hE2 : ¬ TightInO2 t) (hQ : TightFStarQuasisimple Y) {c y : Y}
    (hcZ : c ∈ Subgroup.center Y) (hc1 : c ≠ 1) (hy : y * t * y⁻¹ = t * c) :
    Q8Bridge R S t (TA3.fstarCenter Y) := by
  have hNc : TA3.fstarCenter Y ≤ Subgroup.center Y := TA3.fstarCenter_le_center hd hc hE2
  have hN2 : IsPGroup 2 ↥(TA3.fstarCenter Y) := TA3.isPGroup_fstarCenter hc
  have htN : t ∉ TA3.fstarCenter Y := TA3.not_mem_fstarCenter hc hE2
  have hcN : c ∈ TA3.fstarCenter Y := by
    have hcC : c ∈ Subgroup.centralizer (genFittingFStar Y : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp hcZ g
    have hcF : c ∈ genFittingFStar Y := CFSG.Adapters.generalized_fitting_self_centralizing Y hcC
    refine ⟨⟨c, hcF⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcZ g)
  obtain ⟨hFs, hFn⟩ := fstar_quot_quasisimple hQ hNc
  exact ⟨hNc, hN2, htN, hc.1, q8Quot_of_twin hd hc hNc hN2 htN hcN hc1 hy, hFs, hFn,
    aEmpty_map' hd hc.1 hNc hN2 htN⟩

theorem q8Bridge_of_twisted (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hE2 : ¬ TightInO2 t) (htw : TightTwisted Y t)
    (hall : ∀ c ∈ Subgroup.center Y, orderOf c = 2 → ∃ y : Y, y * t * y⁻¹ = t * c) :
    Q8Bridge R S t (genFittingFitting Y) := by
  obtain ⟨L, hLc, hLn, hlayer, htL, -, hFc, hFL⟩ := htw
  have hN2 : IsPGroup 2 ↥(genFittingFitting Y) := isPGroup_two_genFittingFitting hc.2.2
  have htN : t ∉ genFittingFitting Y := fun h' => hE2 ⟨_, genFittingFitting_normal, hN2, h'⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : genFittingFitting Y ≠ ⊥ := fun h1 => hFL (h1 ▸ bot_le)
  obtain ⟨m, hm⟩ := hN2.exists_card_eq
  have hm0 : m ≠ 0 := by
    intro h1
    rw [h1, pow_zero] at hm
    exact hne (Subgroup.card_eq_one.mp hm)
  have hdvd : 2 ∣ Nat.card ↥(genFittingFitting Y) := by
    rw [hm]
    exact dvd_pow_self 2 hm0
  obtain ⟨c, hc2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(genFittingFitting Y)) 2 hdvd
  have hc2' : orderOf (c : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hc2
  have hc1 : (c : Y) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hc2'
    exact absurd hc2' (by norm_num)
  obtain ⟨y, hy⟩ := hall (c : Y) (hFc c.2) hc2'
  obtain ⟨hFs, hFn⟩ := fstar_quot_twisted hLc hLn hlayer hFc
  exact ⟨hFc, hN2, htN, hc.1, q8Quot_of_twin hd hc hFc hN2 htN c.2 hc1 hy, hFs, hFn,
    aEmpty_map' hd hc.1 hFc hN2 htN⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
