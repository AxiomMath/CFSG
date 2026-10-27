module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylowTransport
public import CFSG.LocalAnalysis.SignalizerFunctor.SylowFixedIntersections
public import CFSG.LocalAnalysis.SignalizerFunctor.WeakClosureConjugation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.SignalizerFunctor.Helpers CFSG.BenderSuzuki.External

variable {K : Type*} [Group K]

theorem involution_cyclic_actor_is_two_group (t : K) (ht : orderOf t = 2) :
    IsPGroup 2 (Subgroup.zpowers t) := by
  apply IsPGroup.of_card (n := 1)
  rw [Nat.card_zpowers, ht]
  rfl

theorem involution_normalized_odd_subgroup_invariant_sylow [Finite K]
    (p : ℕ) (hp : p.Prime) (Y : Subgroup K) (t : K) (ht : orderOf t = 2)
    (hYodd : Odd (Nat.card Y))
    (hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (Y : Set K)) :
    ∃ P : Sylow p Y, t ∈ Subgroup.normalizer
      (((P : Subgroup Y).map Y.subtype : Subgroup K) : Set K) := by
  let T := Subgroup.zpowers t
  let _action := conjugationAction T Y hnorm
  have hbot : IsPGroup p (⊥ : Subgroup Y) := by
    apply IsPGroup.of_card (n := 0)
    simp
  obtain ⟨P, _, hfixed⟩ := invariant_sylow_containing 2 p Nat.prime_two hp
    (involution_cyclic_actor_is_two_group t ht) (Nat.coprime_two_left.mpr hYodd)
    (⊥ : Subgroup Y) hbot (by
      intro a y hy
      have hyone := Subgroup.mem_bot.mp hy
      rw [hyone, smul_one]
      exact Subgroup.one_mem _)
  refine ⟨P, ?_⟩
  have hTnorm : T ≤ Subgroup.normalizer
      (((P : Subgroup Y).map Y.subtype : Subgroup K) : Set K) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro a ha y ⟨x, hx, rfl⟩
    have hpres := (invariant_sylow_subgroup_iff p P).mp hfixed (⟨a, ha⟩ : T) x hx
    exact Subgroup.mem_map_of_mem Y.subtype hpres
  exact hTnorm (Subgroup.mem_zpowers t)

theorem involution_normalized_odd_sylow_fixed_intersection [Finite K]
    (p : ℕ) (hp : p.Prime) (Y : Subgroup K) (t : K) (ht : orderOf t = 2)
    (hYodd : Odd (Nat.card Y))
    (hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (Y : Set K))
    (P : Sylow p Y)
    (hPnorm : t ∈ Subgroup.normalizer
      (((P : Subgroup Y).map Y.subtype : Subgroup K) : Set K)) :
    ∃ R : Sylow p (Y ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K),
      (R : Subgroup (Y ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K)).map
        (Y ⊓ Subgroup.centralizer ({t} : Set K)).subtype =
          (P : Subgroup Y).map Y.subtype ⊓ Subgroup.centralizer ({t} : Set K) := by
  have hR := normalized_sylow_centralizer_intersection 2 p Nat.prime_two hp
    (Subgroup.zpowers t) Y (involution_cyclic_actor_is_two_group t ht) hnorm
    (Nat.coprime_two_left.mpr hYodd) P (Subgroup.zpowers_le.mpr hPnorm)
  have hcent : Subgroup.centralizer (Subgroup.zpowers t : Set K) =
      Subgroup.centralizer ({t} : Set K) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rwa [hcent] at hR

theorem odd_central_quotient_normalized_two_subgroup_centralized [Finite K]
    (J U : Subgroup K) [J.Normal] (t : K)
    (hJodd : Odd (Nat.card J)) (hU : IsPGroup 2 U)
    (hnorm : t ∈ Subgroup.normalizer (U : Set K))
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J)) :
    U ≤ Subgroup.centralizer ({t} : Set K) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  have hcop : Nat.Coprime (Nat.card U) (Nat.card J) := by
    rw [hn]
    exact (Nat.coprime_two_left.mpr hJodd).pow_left n
  have hdisjoint : U ⊓ J = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  intro u hu
  have hconj : t * u * t⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hnorm u).mp hu
  have hdiffU : (t * u * t⁻¹) * u⁻¹ ∈ U := U.mul_mem hconj (U.inv_mem hu)
  let q := QuotientGroup.mk' J
  have hcomm : Commute (q t) (q u) :=
    (Subgroup.mem_center_iff.mp hcentral (q u)).symm
  have hdiffJ : (t * u * t⁻¹) * u⁻¹ ∈ J := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((t * u * t⁻¹) * u⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [hcomm.eq]
    group
  have hone : (t * u * t⁻¹) * u⁻¹ = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hdisjoint]
    exact ⟨hdiffU, hdiffJ⟩
  have hfix : t * u * t⁻¹ = u := mul_inv_eq_one.mp hone
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp hfix).symm

theorem normal_subgroup_involution_invariant_two_sylow [Finite K]
    (B : Subgroup K) [B.Normal] (t : K) (ht : orderOf t = 2) :
    ∃ P : Sylow 2 B, t ∈ Subgroup.normalizer
      (((P : Subgroup B).map B.subtype : Subgroup K) : Set K) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hTR⟩ := (involution_cyclic_actor_is_two_group t ht).exists_le_sylow
  let P := hallSylowSubgroupOfNormal R B
  have himage : (P : Subgroup B).map B.subtype = (R : Subgroup K) ⊓ B := by
    rw [hallSylowSubgroupOfNormal_coe, Subgroup.comap_subtype,
      Subgroup.subgroupOf_map_subtype]
  refine ⟨P, ?_⟩
  rw [himage]
  apply Subgroup.mem_normalizer_iff.mpr
  intro u
  constructor
  · rintro ⟨huR, huB⟩
    exact ⟨(R : Subgroup K).mul_mem
      ((R : Subgroup K).mul_mem (hTR (Subgroup.mem_zpowers t)) huR)
      ((R : Subgroup K).inv_mem (hTR (Subgroup.mem_zpowers t))),
      (inferInstance : B.Normal).conj_mem u huB t⟩
  · rintro ⟨huR, huB⟩
    have htR := hTR (Subgroup.mem_zpowers t)
    have hR := (R : Subgroup K).mul_mem
      ((R : Subgroup K).mul_mem ((R : Subgroup K).inv_mem htR) huR) htR
    have hB := (inferInstance : B.Normal).conj_mem (t * u * t⁻¹) huB t⁻¹
    constructor
    · change u ∈ (R : Subgroup K)
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
        inv_mul_cancel, mul_one] using hR
    · change u ∈ B
      simpa only [inv_inv, mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel_right, inv_mul_cancel, mul_one] using hB

end CFSG.ProperTwoGeneratedCore
