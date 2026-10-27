module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeKlein
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  Subgroup


theorem babyNoPureFourAt_three_of_zero (h : BabyNoPureFourAt 0) : BabyNoPureFourAt 3 := by
  intro t ht D hDt hD hDcard
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨r, s, hr, hs, hrst⟩ :
      ∃ r s : NativeSporadic.B, BabyInv 0 r ∧ BabyInv 0 s ∧ r * s = t := by
    obtain ⟨r₀, hr₀⟩ : ∃ r₀ : NativeSporadic.B, BabyInv 0 r₀ :=
      ⟨_, babyInv_zero_map_d BThreeFi23.phiB BThreeFi23.phiB_injective⟩
    obtain ⟨-, -, hcard₀⟩ := CFSG.Monster.Existence.babyTableIV r₀ hr₀
    obtain ⟨s₀, hs₀, hrs₀⟩ :
        ({s | BabyInv 0 s ∧ BabyOrbit 1 r₀ s} : Set NativeSporadic.B).Nonempty := by
      apply Set.nonempty_of_ncard_ne_zero
      rw [hcard₀ 1]
      norm_num [babyOrbitSize]
    obtain ⟨c, hc⟩ :=
      isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 3 t (r₀ * s₀) ht hrs₀)
    refine ⟨c⁻¹ * r₀ * c, c⁻¹ * s₀ * c, hr₀.of_isConj (isConj_iff.2 ⟨c⁻¹, by rw [inv_inv]⟩),
      hs₀.of_isConj (isConj_iff.2 ⟨c⁻¹, by rw [inv_inv]⟩), ?_⟩
    calc c⁻¹ * r₀ * c * (c⁻¹ * s₀ * c) = c⁻¹ * (r₀ * s₀) * c := by group
      _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [hc]
      _ = t := by group
  have hrs3 : BabyInv 3 (r * s) := by rw [hrst]; exact ht
  have hrs : BabyOrbit 1 r s := hrs3
  obtain ⟨-, hconj, hcard⟩ := CFSG.Monster.Existence.babyTableIV r hr
  have horb : ({y | ∃ g ∈ centralizer ({r} : Set NativeSporadic.B), g * s * g⁻¹ = y} :
      Set NativeSporadic.B) = {y | BabyInv 0 y ∧ BabyOrbit 1 r y} := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hgr : g * r = r * g := (mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 hg
      refine ⟨hs.of_isConj (isConj_iff.2 ⟨g, rfl⟩), ?_⟩
      show BabyInv 3 (r * (g * s * g⁻¹))
      refine hrs3.of_isConj (isConj_iff.2 ⟨g, ?_⟩)
      have e : g * r * g⁻¹ = r := by rw [hgr]; group
      calc g * (r * s) * g⁻¹ = (g * r * g⁻¹) * (g * s * g⁻¹) := by group
        _ = r * (g * s * g⁻¹) := by rw [e]
    · rintro ⟨hy, hyo⟩
      exact hconj 1 s y hs hy hrs hyo
  have hmul := CFSG.EvenSporadicStandard.Solomon78.card_inf_centralizer_mul_ncard_conj
    (centralizer ({r} : Set NativeSporadic.B)) s
  rw [horb, hcard 1, hr.2] at hmul
  have hcardK : Nat.card (centralizer ({t} : Set NativeSporadic.B)) = 2 * Nat.card
      (centralizer ({r} : Set NativeSporadic.B) ⊓ centralizer ({s} : Set NativeSporadic.B) :
        Subgroup NativeSporadic.B) := by
    rw [ht.2]
    norm_num [babyOrbitSize, babyCentOrder] at hmul ⊢
    omega
  set K : Subgroup NativeSporadic.B :=
    centralizer ({r} : Set NativeSporadic.B) ⊓ centralizer ({s} : Set NativeSporadic.B) with hK
  have hKt : K ≤ centralizer ({t} : Set NativeSporadic.B) := by
    intro g hg
    have h1 : g * r = r * g :=
      (mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 (mem_inf.1 hg).1
    have h2 : g * s = s * g :=
      (mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 (mem_inf.1 hg).2
    rw [mem_centralizer_singleton_iff (G := NativeSporadic.B), ← hrst]
    calc g * (r * s) = r * g * s := by rw [← mul_assoc, h1]
      _ = r * s * g := by rw [mul_assoc, h2, ← mul_assoc]
  have hidx : (K.subgroupOf (centralizer ({t} : Set NativeSporadic.B))).index = 2 := by
    have hc := card_mul_index (K.subgroupOf (centralizer ({t} : Set NativeSporadic.B)))
    rw [Nat.card_congr (subgroupOfEquivOfLe hKt).toEquiv, hcardK] at hc
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [hc, mul_comm])
  have hDr : D ≤ centralizer ({r} : Set NativeSporadic.B) := by
    intro x hx
    obtain ⟨y, rfl⟩ : ∃ y : centralizer ({t} : Set NativeSporadic.B), (y : NativeSporadic.B) = x :=
      ⟨⟨x, hDt hx⟩, rfl⟩
    have hy3 : y ^ 3 = 1 := Subtype.ext (by rw [coe_pow, coe_one]; exact hD.2 _ hx)
    have h4 : (y ^ 2) ^ 2 = y := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hy3, one_mul]
    have hyK : y ∈ K.subgroupOf (centralizer ({t} : Set NativeSporadic.B)) := by
      rw [← h4]
      exact pow_mem (sq_mem_of_index_two hidx y) 2
    exact (mem_inf.1 (mem_subgroupOf.1 hyK)).1
  exact h r hr D hDr hD hDcard

end CFSG.LocalAnalysis.GLTheoremA.H1017
