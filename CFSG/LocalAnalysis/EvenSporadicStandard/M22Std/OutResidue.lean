module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutRest4
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Input

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std
  CFSG.EvenSporadicStandard.M23Std

@[expose] def OuterFusion (X : Type) [Group X] (z : X) : Prop :=
  ∃ b ∈ (commutator ↥(centralizer ({z} : Set X))).map (centralizer ({z} : Set X)).subtype,
    b * b = 1 ∧ b ≠ 1 ∧ IsConj z (z * b)

theorem not_mem_fusionZStar {X : Type} [Group X] [Finite X] {z : X} (h : OuterFusion X z) :
    z ∉ fusionZStar X := by
  intro hz
  obtain ⟨b, -, hb2, hb1, hconj⟩ := h
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hzc : QuotientGroup.mk' (fusionOddCore X) z ∈ Subgroup.center (X ⧸ fusionOddCore X) := hz
  have h1 : QuotientGroup.mk' (fusionOddCore X) (z * b) =
      QuotientGroup.mk' (fusionOddCore X) z := by
    rw [← hc, map_mul, map_mul, map_inv]
    have := Subgroup.mem_center_iff.1 hzc (QuotientGroup.mk' (fusionOddCore X) c)
    calc QuotientGroup.mk' (fusionOddCore X) c * QuotientGroup.mk' (fusionOddCore X) z *
          (QuotientGroup.mk' (fusionOddCore X) c)⁻¹ =
        QuotientGroup.mk' (fusionOddCore X) z * QuotientGroup.mk' (fusionOddCore X) c *
          (QuotientGroup.mk' (fusionOddCore X) c)⁻¹ := by rw [this]
      _ = QuotientGroup.mk' (fusionOddCore X) z := by group
  have h2 : QuotientGroup.mk' (fusionOddCore X) b = 1 := by
    have : QuotientGroup.mk' (fusionOddCore X) z * QuotientGroup.mk' (fusionOddCore X) b =
        QuotientGroup.mk' (fusionOddCore X) z * 1 := by rw [← map_mul, h1, mul_one]
    exact mul_left_cancel this
  have hbO : b ∈ fusionOddCore X := (QuotientGroup.eq_one_iff b).1 h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
  have hdvd : orderOf b ∣ Nat.card (fusionOddCore X) := Subgroup.orderOf_dvd_natCard _ hbO
  rw [hb] at hdvd
  exact (Nat.not_even_iff_odd.2 (natCard_fusionOddCore_odd X)) (even_iff_two_dvd.2 hdvd)

@[expose] def Fin77aOuterSit
    (P : (X : Type) → [Group X] → [Finite X] → X → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (L : Subgroup G) (z t : G)
    (T₁ : Subgroup (centralizer ({z} : Set G))) (F : Subgroup (L ⧸ center L))
    (tb : L ⧸ center L) (Q : Sylow 2 G) (x : G) (L1 : Subgroup G),
    OuterSituation G L z t T₁ F tb Q x L1 →
    ∀ hz : z ∈ normalizer (L1 : Set G), Nonempty (centralizer
      ({(QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)} : Set (Xbar L1)) ≃*
        Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) →
    P (Xbar L1) (QuotientGroup.mk ⟨z, hz⟩)

end CFSG.EvenSporadicStandard.M22Std
