module

public import CFSG.FeitThompson.Local.MaximalNormalizedPSubgroupSingletonTrivial
public import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
import CFSG.FeitThompson.Foundations.PGroupFixedPointCongruence

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise MulAction

variable {G : Type*} [Group G] {A Q : Subgroup G} {q : ℕ}

theorem pointwise_smul_eq_map (σ : MulAut G) (Q : Subgroup G) :
    (σ • Q : Subgroup G) = Q.map (σ : G →* G) :=
  Subgroup.toSubmonoid_inj.mp rfl

theorem conj_smul_eq_self_iff_mem_normalizer {g : G} {Q : Subgroup G} :
    (MulAut.conj g • Q : Subgroup G) = Q ↔ g ∈ normalizer (Q : Set G) := by
  rw [pointwise_smul_eq_map, mem_normalizer_iff_map_conj_eq]

theorem normalizer_pointwise_smul (σ : MulAut G) (Q : Subgroup G) :
    normalizer ((σ • Q : Subgroup G) : Set G) = (σ • normalizer (Q : Set G) : Subgroup G) := by
  rw [pointwise_smul_eq_map, pointwise_smul_eq_map,
    Subgroup.map_normalizer_eq_of_bijective _ σ.bijective]

theorem isPGroup_pointwise_smul (σ : MulAut G) (h : IsPGroup q Q) :
    IsPGroup q (σ • Q : Subgroup G) :=
  h.of_equiv (Subgroup.equivSMul σ Q)

theorem le_normalizer_pointwise_smul {σ : MulAut G} (hσ : σ • A = A)
    (h : A ≤ normalizer (Q : Set G)) : A ≤ normalizer ((σ • Q : Subgroup G) : Set G) := by
  rw [normalizer_pointwise_smul, ← hσ]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 h

theorem mem_maximalNormalizedPSubgroups_of_le_normalizer {P : Subgroup G} (hAP : A ≤ P)
    (hQ : Q ∈ maximalNormalizedPSubgroups A q) (hPQ : P ≤ normalizer (Q : Set G)) :
    Q ∈ maximalNormalizedPSubgroups P q :=
  mem_maximalNormalizedPSubgroups_of_forall (isPGroup_of_mem hQ) hPQ
    fun _ hR hRP hQR => eq_of_mem_of_le hQ hR (hAP.trans hRP) hQR

def conjPerm (A : Subgroup G) (q : ℕ) (g : ↥(normalizer (A : Set G))) :
    Equiv.Perm ↥(maximalNormalizedPSubgroups A q) where
  toFun Q := ⟨MulAut.conj (g : G) • (Q : Subgroup G),
    smul_mem_maximalNormalizedPSubgroups (conj_smul_eq_self_iff_mem_normalizer.2 g.2) Q.2⟩
  invFun Q := ⟨(MulAut.conj (g : G))⁻¹ • (Q : Subgroup G),
    smul_mem_maximalNormalizedPSubgroups
      (by rw [inv_smul_eq_iff, conj_smul_eq_self_iff_mem_normalizer.2 g.2]) Q.2⟩
  left_inv Q := Subtype.ext (inv_smul_smul _ _)
  right_inv Q := Subtype.ext (smul_inv_smul _ _)

@[simp]
theorem coe_conjPerm_apply (g : ↥(normalizer (A : Set G)))
    (Q : ↥(maximalNormalizedPSubgroups A q)) :
    ((conjPerm A q g Q : Subgroup G)) = MulAut.conj (g : G) • (Q : Subgroup G) := (rfl)

def conjPermHom (A : Subgroup G) (q : ℕ) :
    ↥(normalizer (A : Set G)) →* Equiv.Perm ↥(maximalNormalizedPSubgroups A q) where
  toFun := conjPerm A q
  map_one' := Equiv.ext fun Q => Subtype.ext (by
    rw [coe_conjPerm_apply,
      show ((1 : ↥(normalizer (A : Set G))) : G) = 1 from rfl, map_one, one_smul]
    rfl)
  map_mul' g h := Equiv.ext fun Q => Subtype.ext (by
    rw [Equiv.Perm.mul_apply, coe_conjPerm_apply, coe_conjPerm_apply, coe_conjPerm_apply,
      show ((g * h : ↥(normalizer (A : Set G))) : G) = (g : G) * (h : G) from rfl, map_mul,
      mul_smul])

@[simp]
theorem coe_conjPermHom_apply (g : ↥(normalizer (A : Set G)))
    (Q : ↥(maximalNormalizedPSubgroups A q)) :
    ((conjPermHom A q g Q : Subgroup G)) = MulAut.conj (g : G) • (Q : Subgroup G) := (rfl)

theorem conjPermHom_eq_one_of_mem (g : ↥(normalizer (A : Set G))) (hg : (g : G) ∈ A) :
    conjPermHom A q g = 1 :=
  Equiv.ext fun Q => Subtype.ext (by
    rw [coe_conjPermHom_apply, Equiv.Perm.one_apply]
    exact conj_smul_eq_self_iff_mem_normalizer.2 (le_normalizer_of_mem Q.2 hg))

def conjPermRange (A : Subgroup G) (q : ℕ) {H : Subgroup G} (hH : H ≤ normalizer (A : Set G)) :
    Subgroup (Equiv.Perm ↥(maximalNormalizedPSubgroups A q)) :=
  ((conjPermHom A q).comp (Subgroup.inclusion hH)).range

theorem conjPermHom_mem_conjPermRange {H : Subgroup G} (hH : H ≤ normalizer (A : Set G)) {h : G}
    (hh : h ∈ H) : (conjPermHom A q ⟨h, hH hh⟩) ∈ conjPermRange A q hH :=
  ⟨⟨h, hh⟩, rfl⟩

theorem coe_conjPermRange_smul {H : Subgroup G} (hH : H ≤ normalizer (A : Set G)) {h : G}
    (hh : h ∈ H) (Q : ↥(maximalNormalizedPSubgroups A q)) :
    (((⟨conjPermHom A q ⟨h, hH hh⟩, conjPermHom_mem_conjPermRange hH hh⟩ :
        ↥(conjPermRange A q hH)) • Q : ↥(maximalNormalizedPSubgroups A q)) : Subgroup G) =
      MulAut.conj h • (Q : Subgroup G) := (rfl)

theorem natCard_conjPermRange_dvd [Finite G] {H : Subgroup G} (hH : H ≤ normalizer (A : Set G)) :
    Nat.card ↥(conjPermRange A q hH) ∣ Nat.card H :=
  Subgroup.card_range_dvd _

theorem natCard_conjPermRange_dvd_relIndex {A P : Subgroup G}
    (hPA : P ≤ normalizer (A : Set G)) (q : ℕ) :
    Nat.card ↥(conjPermRange A q hPA) ∣ A.relIndex P :=
  calc Nat.card ↥(conjPermRange A q hPA)
      = ((conjPermHom A q).comp (Subgroup.inclusion hPA)).ker.index :=
        (Subgroup.index_ker _).symm
    _ ∣ (A.subgroupOf P).index :=
        Subgroup.index_dvd_of_le fun _ hx => conjPermHom_eq_one_of_mem _ hx
    _ = A.relIndex P := rfl

variable [Finite G]

theorem exists_mem_maximalNormalizedPSubgroups_le_normalizer
    {A P : Subgroup G} {q r : ℕ}
    (hAP : A ≤ P) (hA : (A.subgroupOf P).Normal) (hindex : A.relIndex P = r)
    (hrπ : r ∈ subgroupPrimeSupport A)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂) :
    ∃ Q ∈ maximalNormalizedPSubgroups A q, P ≤ normalizer (Q : Set G) := by
  have hr : r.Prime := prime_of_mem_subgroupPrimeSupport hrπ
  have : Fact r.Prime := ⟨hr⟩
  have hPnorm : P ≤ normalizer (A : Set G) := (normal_subgroupOf_iff_le_normalizer hAP).1 hA
  have hK : constrainedCentralizerCore A ≤ normalizer (A : Set G) :=
    (constrainedCentralizerCore_le_centralizer A).trans (centralizer_le_normalizer _)
  obtain ⟨Q₀, hQ₀⟩ := maximalNormalizedPSubgroups_nonempty A q
  have horb : orbit ↥(conjPermRange A q hK)
      (⟨Q₀, hQ₀⟩ : ↥(maximalNormalizedPSubgroups A q)) = Set.univ := by
    refine Set.eq_univ_of_forall fun Q => ?_
    obtain ⟨k, hk, hkeq⟩ := hconj Q₀ hQ₀ Q.1 Q.2
    have hk' : k⁻¹ ∈ constrainedCentralizerCore A := (constrainedCentralizerCore A).inv_mem hk
    refine ⟨⟨conjPermHom A q ⟨k⁻¹, hK hk'⟩, conjPermHom_mem_conjPermRange hK hk'⟩,
      Subtype.ext ?_⟩
    rw [coe_conjPermRange_smul]
    exact hkeq
  have hdvd : Nat.card ↥(maximalNormalizedPSubgroups A q) ∣
      Nat.card (constrainedCentralizerCore A) := by
    have h1 := natCard_orbit_dvd_natCard
      (P := ↥(conjPermRange A q hK)) (⟨Q₀, hQ₀⟩ : ↥(maximalNormalizedPSubgroups A q))
    rw [horb, Nat.card_univ] at h1
    exact h1.trans (natCard_conjPermRange_dvd hK)
  have hnd : ¬ r ∣ Nat.card ↥(maximalNormalizedPSubgroups A q) := fun h =>
    (mem_subgroupPrimeSupportCompl_iff.1
      (isPiSubgroup_iff.1 (isPiSubgroup_constrainedCentralizerCore A) r
        (Nat.mem_primeFactors.2 ⟨hr, h.trans hdvd, Nat.card_pos.ne'⟩))).2 hrπ
  have hPr : IsPGroup r ↥(conjPermRange A q hPnorm) := by
    rcases (Nat.dvd_prime hr).1 (hindex ▸ natCard_conjPermRange_dvd_relIndex hPnorm q) with h | h
    · exact IsPGroup.of_card (n := 0) (by simpa using h)
    · exact IsPGroup.of_card (n := 1) (by simpa using h)
  obtain ⟨Q, hQ⟩ := hPr.nonempty_fixed_point_of_prime_not_dvd_card _ hnd
  refine ⟨Q, Q.2, fun g hg => ?_⟩
  rw [← conj_smul_eq_self_iff_mem_normalizer, ← coe_conjPermRange_smul hPnorm hg Q]
  exact congrArg Subtype.val (mem_fixedPoints.1 hQ
    ⟨conjPermHom A q ⟨g, hPnorm hg⟩, conjPermHom_mem_conjPermRange hPnorm hg⟩)

theorem exists_mem_maximalNormalizedPSubgroups_inter_le_normalizer
    {A P : Subgroup G} {q r : ℕ}
    (hAP : A ≤ P) (hA : (A.subgroupOf P).Normal) (hindex : A.relIndex P = r)
    (hrπ : r ∈ subgroupPrimeSupport A)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂) :
    ∃ Q ∈ maximalNormalizedPSubgroups A q,
      P ≤ normalizer (Q : Set G) ∧ Q ∈ maximalNormalizedPSubgroups P q := by
  obtain ⟨Q, hQ, hPQ⟩ :=
    exists_mem_maximalNormalizedPSubgroups_le_normalizer hAP hA hindex hrπ hconj
  exact ⟨Q, hQ, hPQ, mem_maximalNormalizedPSubgroups_of_le_normalizer hAP hQ hPQ⟩

end

end CFSG.FeitThompson
