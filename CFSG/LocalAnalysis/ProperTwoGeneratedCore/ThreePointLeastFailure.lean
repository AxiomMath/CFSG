module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ThreePointLeastFailureHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointCentralization

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction
  (four_group_has_distinct_nonidentity)

universe u

variable {G : Type u} [Group G] [Finite G]

theorem rank_one_pair_escaping_involution {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) :
    ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2 ∧ Commute u z ∧
      ¬ Subgroup.centralizer ({u} : Set G) ≤ H := by
  classical
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  set B := pairPointStabilizer H beta
  obtain ⟨-, -, -, -, hfac, -, -⟩ :=
    involution_point_sylow_flips_and_three_point_odd_core h.local_datum S hzS hzcenter beta
      hbeta t ht
  let O := CFSG.oddCore B
  let C := (Subgroup.centralizer ({z} : Set G)).subgroupOf B
  have hB2 : 2 ∣ Nat.card B := by
    obtain ⟨E, -, hEcard⟩ := CFSG.ComponentClassification.Helpers.twoRank_witness B
    rw [hpairRank, pow_one] at hEcard
    rw [← hEcard]
    exact Subgroup.card_subgroup_dvd_card E
  let f : C →* B ⧸ O := (QuotientGroup.mk' O).comp C.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective O q
    have hb : (b : G) ∈ (B : Set G) := b.2
    rw [hfac] at hb
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hb
    obtain ⟨hxB, hxC⟩ : x ∈ (B : Set G) ∧ x ∈ (Subgroup.centralizer ({z} : Set G) : Set G) := hx
    obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨⟨x, hxB⟩, hxC⟩, ?_⟩
    change QuotientGroup.mk' O ⟨x, hxB⟩ = QuotientGroup.mk' O b
    have hb' : b = ⟨x, hxB⟩ * o := Subtype.ext hxy.symm
    have ho1 : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    rw [hb', map_mul, ho1, mul_one]
  have hC2 : 2 ∣ Nat.card C := by
    have hdvd := Subgroup.card_dvd_of_surjective hf
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup O
    have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card B
    rw [hcard] at hB2
    exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_two_left.mpr hOodd) hB2).trans hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hC2
  have hxB : ((x : B) : G) ∈ B := (x : B).2
  have hxo : orderOf ((x : B) : G) = 2 :=
    (Subgroup.orderOf_coe (x : B)).trans ((Subgroup.orderOf_coe x).trans hx)
  have hxz : Commute ((x : B) : G) z :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp x.2)
  have hSH : (S : Subgroup G) ≤ H := fun s hs => point_centralizer_le h.local_datum
    (Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzcenter) ⟨s, hs⟩)))
  obtain ⟨-, htrans, -⟩ := unique_central_sylow_involution_centralizers_transitive_fixed_set S H
    hSH z hzS hzcenter h.local_datum.distinguished_order h.local_datum.unique_containment _
    (pairPointStabilizer_le_point H beta hxB) hxo
  obtain ⟨c, hc, hcβ⟩ := htrans _ _ ((mem_rightCosetStabilizer_iff H _ _).mp hxB.1)
    ((mem_rightCosetStabilizer_iff H _ _).mp hxB.2)
  refine ⟨_, hxB, hxo, hxz, fun hle => hbeta ?_⟩
  rw [← hcβ]
  exact (mem_rightCosetStabilizer_iff H _ c).mp (by rw [rightCosetStabilizer_base]; exact hle hc)

theorem rank_one_pair_fourGroup_meets_class_and_involutions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    (∀ V : Subgroup G, Nonempty (V ≃* Multiplicative (ZMod 2 × ZMod 2)) →
        ∃ s ∈ V, s ∈ involutionPointClass z) ∧
      ∀ v : G, orderOf v = 2 → v ∉ involutionPointClass z → v ∈ involutionPointClass u := by
  classical
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z u ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({u} : Set G))) := inferInstance
  have hmodel := rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm
    hsmallerR1 beta hbeta hpairRank huB hu huz hescape R T₁
  dsimp only at hmodel
  obtain ⟨-, -, -, -, -, U, -, -, -, -, -, -, -, ⟨S', hS'⟩, -, -, -, -, -, -, -, -, -, hUD, -, -,
    hinterA, -, -, hallinv, -⟩ := hmodel
  have hinvol : ∀ v : G, orderOf v = 2 → v ∉ involutionPointClass z →
      v ∈ involutionPointClass u := by
    intro v hv hvD
    have hv' : v ∈ {x : G | orderOf x = 2} := hv
    rw [hallinv] at hv'
    exact hv'.resolve_right hvD
  refine ⟨fun V ⟨e⟩ => ?_, hinvol⟩
  have : IsKleinFour V := ⟨(Nat.card_congr e.toEquiv).trans IsKleinFour.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two⟩
  obtain ⟨a, b, ha1, hb1, hab⟩ := four_group_has_distinct_nonidentity V
  have horder : ∀ x : V, x ≠ 1 → orderOf (x : G) = 2 := fun x hx =>
    (Subgroup.orderOf_coe x).trans (orderOf_eq_prime (by rw [sq, IsKleinFour.mul_self]) hx)
  by_cases haD : (a : G) ∈ involutionPointClass z
  · exact ⟨a, a.2, haD⟩
  by_cases hbD : (b : G) ∈ involutionPointClass z
  · exact ⟨b, b.2, hbD⟩
  refine ⟨(a : G) * b, V.mul_mem a.2 b.2, ?_⟩
  have hcommab : (a : G) * b = b * a := by
    have h2 := IsKleinFour.inv_eq_self (a * b)
    rw [mul_inv_rev, IsKleinFour.inv_eq_self, IsKleinFour.inv_eq_self] at h2
    exact congrArg Subtype.val h2.symm
  obtain ⟨g, hg⟩ := hinvol a (horder a ha1) haD
  have hbu := hinvol b (horder b hb1) hbD
  change g⁻¹ * u * g = a at hg
  have huu : u * u = 1 := by rw [← sq, ← hu, pow_orderOf_eq_one]
  have hb'M : g * b * g⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * b * g⁻¹ * u = g * (b * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * b) * g⁻¹ := by rw [hg, ← hcommab]
      _ = u * (g * b * g⁻¹) := by group
  let bM : Subgroup.centralizer ({u} : Set G) := ⟨g * b * g⁻¹, hb'M⟩
  have hbMo : orderOf bM = 2 := by
    rw [← Subgroup.orderOf_coe, show (bM : G) = MulAut.conj g b by simp [bM],
      MulEquiv.orderOf_eq, horder b hb1]
  obtain ⟨c, hc⟩ : ∃ c : Subgroup.centralizer ({u} : Set G),
      c⁻¹ * bM * c ∈ (S' : Subgroup (Subgroup.centralizer ({u} : Set G))) := by
    have hp : IsPGroup 2 (Subgroup.zpowers bM) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbMo, pow_one])
    obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (Subgroup.centralizer ({u} : Set G)) Q S'
    refine ⟨k⁻¹, ?_⟩
    rw [inv_inv, ← hk, Sylow.smul_def, Sylow.pointwise_smul_def]
    exact ⟨bM, hQ (Subgroup.mem_zpowers bM), by simp⟩
  have hcA : (c : G)⁻¹ * (g * b * g⁻¹) * c ∈
      (T₁ : Subgroup ↥(H ⊓ Subgroup.centralizer ({u} : Set G))).map
        (H ⊓ Subgroup.centralizer ({u} : Set G)).subtype := by
    rw [← hS']
    exact Subgroup.mem_map_of_mem _ hc
  have hcclass : (c : G)⁻¹ * (g * b * g⁻¹) * c ∈ involutionPointClass u := by
    have := pointClass_rightConjugate_mem hbu (g⁻¹ * c)
    simpa [rightConjugateElem, mul_assoc] using this
  have hmem : (c : G)⁻¹ * (g * b * g⁻¹) * c ∈ (fun x : G => u * x) '' (U : Set G) :=
    hinterA ▸ ⟨hcclass, hcA⟩
  obtain ⟨w, hwU, hw⟩ := hmem
  simp only at hw
  have hcu : (c : G) * u * (c : G)⁻¹ = u := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp c.2, mul_inv_cancel_right]
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hab
    apply Subtype.ext
    have h1 : g * b * g⁻¹ = u := by
      calc g * b * g⁻¹ = (c : G) * ((c : G)⁻¹ * (g * b * g⁻¹) * c) * (c : G)⁻¹ := by group
        _ = (c : G) * u * (c : G)⁻¹ := by rw [← hw, mul_one]
        _ = u := hcu
    rw [← hg]
    calc g⁻¹ * u * g = g⁻¹ * (g * b * g⁻¹) * g := by rw [h1]
      _ = b := by group
  have hwD : w ∈ involutionPointClass z := hUD ⟨hwU, hw1⟩
  have hwexpr : w = u * ((c : G)⁻¹ * (g * b * g⁻¹) * c) := by
    rw [← hw, ← mul_assoc, huu, one_mul]
  have hprod : (a : G) * b = rightConjugateElem w ((c : G)⁻¹ * g) := by
    rw [hwexpr, ← hg]
    simp only [rightConjugateElem]
    calc g⁻¹ * u * g * b = g⁻¹ * ((c : G) * u * (c : G)⁻¹) * g * b := by rw [hcu]
      _ = ((c : G)⁻¹ * g)⁻¹ * (u * ((c : G)⁻¹ * (g * b * g⁻¹) * c)) * ((c : G)⁻¹ * g) := by
        group
  rw [hprod]
  exact pointClass_rightConjugate_mem hwD _

theorem minimalLocalFailure_rank_one_pair_three_point_normalized_subgroup_centralization
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) :
    ∀ X : Subgroup G, X ≤ pairPointStabilizer H beta →
      t ∈ Subgroup.normalizer (X : Set G) → 3 ≤ Nat.card (pointFixedSet H X) →
        ⁅X, Subgroup.zpowers t⁆ = ⊥ := by
  intro X hXD hXnorm hthree
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨u, huB, hu, huz, hescape⟩ :=
    rank_one_pair_escaping_involution h beta hbeta hpairRank t ht
  obtain ⟨hcover, hinvol⟩ := rank_one_pair_fourGroup_meets_class_and_involutions h hcomm
    hsmallerR1 beta hbeta hpairRank huB hu huz hescape
  have hL := rank_one_pair_hull_conditions h hcomm hsmallerR1 beta hbeta hpairRank huB hu huz
    hescape
  refine local_involution_point_three_point_normalized_subgroup_centralization H z h.local_datum
    S hzS hzcenter (minimalLocalFailureSylowFixedPointsFromProperCommutingImages h hcomm).2.2.1
    hcover (fun v hv hvD => ?_)
    (properHull_minimal_failure_distinguished_triple_centralization h hcomm hsmallerR1)
    beta hbeta t ht.1
    ⟨ht.2, (involution_point_uniform_pair_flips h.local_datum beta hbeta).2.1 t ht⟩
    X hXD hXnorm hthree
  obtain ⟨g, rfl⟩ := hinvol v hv hvD
  exact ⟨_, involutionHullConditions_conj hL g⟩

end CFSG.ProperTwoGeneratedCore.RankOnePair
