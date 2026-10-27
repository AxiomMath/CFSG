module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Order
public import CFSG.LieType.SeitzGeneration.ExcHighThree.ConjClass

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

section Index


theorem tw_index_eq_three {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (p ^ f)) :
    ((twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))
        ≤ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr) ∧
    (((twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))).subgroupOf
        (twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)).Normal ∧
    (((twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))).subgroupOf
        (twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)).index = 3 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨hfinR, -, hder, ⟨kk, hk⟩, -, hRcard, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order hp hf K hK σ.toRingHom hσ
      (AlgebraicClosure K) Fr hFr
  set L := AlgebraicClosure K with hL
  set R := twistedFixedGroup TwistTag.E6 L Fr with hR
  set C := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K L)) with hC
  have hle : C ≤ R := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C.subgroupOf R).Normal := by
    have e : C.subgroupOf R = ⁅(⊤ : Subgroup R), ⊤⁆ := by
      have h1 : ⁅R, R⁆ = Subgroup.map R.subtype ⁅(⊤ : Subgroup R), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  refine ⟨hle, hnormal, ?_⟩
  have hCcard : Nat.card C = ordTwistedE6 (p ^ f) := by
    have h1 : Nat.card C = Nat.card (twistedE6RootGroup K σ) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    rw [h1]
    exact card_twistedE6RootGroup_eq hp hf σ hK hσ
  have hsub : Nat.card (C.subgroupOf R) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hmul : Nat.card C * 3 ^ kk = Nat.card R := by
    rw [← hsub, ← hk]
    exact Subgroup.card_mul_index _
  have h3q : 3 ∣ p ^ f + 1 := by omega
  have hgcd : Nat.gcd 3 (p ^ f + 1) = 3 := Nat.gcd_eq_left h3q
  have hsq : (p ^ f) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have h3N : 3 ∣ (p ^ f) ^ 36 * ((p ^ f) ^ 12 - 1) * ((p ^ f) ^ 9 + 1) * ((p ^ f) ^ 8 - 1) *
      ((p ^ f) ^ 6 - 1) * ((p ^ f) ^ 5 + 1) * ((p ^ f) ^ 2 - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    have hpos : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos f)
    omega
  have hCpos : 0 < Nat.card C := by
    haveI : Finite (Module.End K (RootModule TwistTag.E6.tag K)) := Module.finite_of_finite K
    haveI : Finite (ModGL TwistTag.E6.tag K) := inferInstance
    have h1 : Nat.card C = Nat.card (twistedE6RootGroup K σ) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    rw [h1]
    exact Nat.card_pos
  have hC3 : Nat.card C * 3 = Nat.card R := by
    rw [hRcard, hCcard]
    unfold ordTwistedE6
    rw [hgcd]
    exact Nat.div_mul_cancel h3N
  have h33 : 3 ^ kk = 3 := Nat.eq_of_mul_eq_mul_left hCpos (hmul.trans hC3.symm)
  rw [hk, h33]

theorem tw_class_correction {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (p ^ f))
    {c0 h : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hc0 : c0 ∈ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)
    (hh : h ∈ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)
    (hc0C : c0 ∉ (twistedE6RootGroup K σ).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K)))) :
    ∃ j : ℤ, c0 ^ j * h ∈ (twistedE6RootGroup K σ).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  classical
  obtain ⟨-, hnormal, hidx⟩ := tw_index_eq_three hp hf hK σ hσ hq Fr hFr
  set R := twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr with hR
  set C := (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) with hC
  haveI := hnormal
  set N : Subgroup R := C.subgroupOf R with hN
  let mk : R →* R ⧸ N := QuotientGroup.mk' N
  have hcard : Nat.card (⊤ : Subgroup (R ⧸ N)) ∣ 3 := by
    rw [Subgroup.card_top, ← Subgroup.index_eq_card, hidx]
  have hy1 : mk ⟨c0, hc0⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨c0, hc0⟩ : R) ∈ N := (QuotientGroup.eq_one_iff _).1 h1
    exact hc0C (Subgroup.mem_subgroupOf.1 h2)
  obtain ⟨j, hj⟩ := exists_zpow_eq_of_card_dvd_three (⊤ : Subgroup (R ⧸ N)) hcard
    (y := mk ⟨c0, hc0⟩) (x := (mk ⟨h, hh⟩)⁻¹) (Subgroup.mem_top _) hy1 (Subgroup.mem_top _)
  refine ⟨j, ?_⟩
  have h1 : mk ((⟨c0, hc0⟩ : R) ^ j * ⟨h, hh⟩) = 1 := by
    rw [map_mul, map_zpow, hj, inv_mul_cancel]
  have h2 : ((⟨c0, hc0⟩ : R) ^ j * ⟨h, hh⟩) ∈ N := (QuotientGroup.eq_one_iff _).1 h1
  have h3 := Subgroup.mem_subgroupOf.1 h2
  simpa using h3

end Index

end CFSG.LieType.SeitzGeneration.ExcHighThree
