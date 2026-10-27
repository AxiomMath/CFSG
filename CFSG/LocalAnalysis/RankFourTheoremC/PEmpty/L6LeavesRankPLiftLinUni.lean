module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLift
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Mult
public import CFSG.Permutation.FiveTransitive.PrimeFreeOrderLift

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open CFSG Subgroup

@[expose] def GL83I66TwoLinUni : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (f : ℕ), f.Prime → 5 ≤ f → CFSG.IsQuasisimple K →
    center K ≠ ⊥ → IsPGroup f (center K) →
    CFSG.LocalAnalysis.RankFourTheoremC.IsLinearOrUnitaryAt f (K ⧸ center K) →
    ∀ (K' : Type) [Group K'] (φ : K →* K'), Function.Surjective φ →
      φ.ker = center K → ∀ z : K', orderOf z = f →
        (∃ S : Sylow f K', z ∈ (S : Subgroup K') ∧ ∀ s ∈ (S : Subgroup K'), z * s = s * z) →
          ∃ w : K, orderOf w = f ∧ φ w = z

section CertificateInstances


theorem gl83I66Two_of_linUni (h : GL83I66TwoLinUni) : GL83I66Two := by
  intro K _ _ f hf hf5 hK hq K' _ φ hsurj hker z hz hcen
  haveI := Fact.mk hf
  by_cases hfZ : f ∣ Nat.card (center K)
  ·
    obtain ⟨N, hNle, hNd, hNexp⟩ :=
      CFSG.RankThree.PartOne.Mult.exists_central_p_complement (K := K) f
    haveI : N.Normal := Subgroup.normal_of_le_center hNle
    obtain ⟨hqN, hcomap, -⟩ := CFSG.LocalCores.quasisimple_central_quotient hq N hNle
    haveI : Finite (K ⧸ N) := Finite.of_surjective _ (QuotientGroup.mk'_surjective N)
    have key : ∀ y : K, QuotientGroup.mk' N y ∈ center (K ⧸ N) ↔ y ∈ center K := fun y => by
      rw [← hcomap, Subgroup.mem_comap]
    have hpgrp : IsPGroup f (center (K ⧸ N)) := by
      intro g
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (g : K ⧸ N)
      have hgc : QuotientGroup.mk' N y ∈ center (K ⧸ N) := by
        rw [hy]
        exact g.2
      obtain ⟨n, hn⟩ := hNexp y ((key y).mp hgc)
      refine ⟨n, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy, ← map_pow]
      exact (QuotientGroup.eq_one_iff (y ^ f ^ n)).mpr hn
    have hne : center (K ⧸ N) ≠ ⊥ := by
      intro hbot
      have hZN : center K = N := by
        ext x
        rw [← key x, hbot, Subgroup.mem_bot]
        exact QuotientGroup.eq_one_iff x
      rw [hZN] at hfZ
      exact hNd hfZ
    have hφN : N ≤ φ.ker := by
      rw [hker]
      exact hNle
    obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : K ⧸ N →* K', ∀ y : K, φ₁ (QuotientGroup.mk' N y) = φ y :=
      ⟨QuotientGroup.lift N φ hφN, fun _ => rfl⟩
    have hφ₁surj : Function.Surjective φ₁ := fun k => by
      obtain ⟨y, rfl⟩ := hsurj k
      exact ⟨QuotientGroup.mk' N y, hφ₁ y⟩
    have hkerφ₁ : φ₁.ker = center (K ⧸ N) := by
      ext t
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N t
      rw [MonoidHom.mem_ker, hφ₁, key y, ← hker, MonoidHom.mem_ker]
    have hK1 := CFSG.KCore.KGroupNonab.quotient isoInvariant_isCatalogGroup' hK N
    haveI : IsSimpleGroup ((K ⧸ N) ⧸ center (K ⧸ N)) := hqN.2.1
    obtain ⟨φt, hφt⟩ : ∃ φt : (⊤ : Subgroup (K ⧸ N)) →* (K ⧸ N) ⧸ center (K ⧸ N),
        Function.Surjective φt :=
      ⟨(QuotientGroup.mk' (center (K ⧸ N))).comp
          (Subgroup.topEquiv : (⊤ : Subgroup (K ⧸ N)) ≃* (K ⧸ N)).toMonoidHom,
        fun q => by
          obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center (K ⧸ N)) q
          exact ⟨⟨x, Subgroup.mem_top x⟩, hx⟩⟩
    have hcat₁ : CFSG.Open.IsCatalogGroup ((K ⧸ N) ⧸ center (K ⧸ N)) :=
      CFSG.KCore.KGroupNonab.catalogue_of_surjective isoInvariant_isCatalogGroup' hK1 ⊤ hqN.2.2
        φt hφt
    have hopen₁ : CFSG.Open.IsQuasisimple (K ⧸ N) := ⟨hqN.1.commutator_eq_top, hqN.2.1⟩
    have hLU : CFSG.LocalAnalysis.RankFourTheoremC.IsLinearOrUnitaryAt f
        ((K ⧸ N) ⧸ center (K ⧸ N)) :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.kdMultP5_of_tables
        CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
        CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
        f hf hf5 _ hopen₁ hcat₁ hne hpgrp
    obtain ⟨w₁, hw₁o, hw₁φ⟩ :=
      h (K ⧸ N) f hf hf5 hqN hne hpgrp hLU K' φ₁ hφ₁surj hkerφ₁ z hz hcen
    have hNd' : ¬ f ∣ Nat.card (QuotientGroup.mk' N).ker := by
      rw [QuotientGroup.ker_mk']
      exact hNd
    obtain ⟨w, hwmk, hw⟩ := CFSG.FiveTransitive.PrimeFreeOrderLift.exists_lift
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hNd' w₁ hw₁o
    refine ⟨w, hw, ?_⟩
    rw [← hφ₁ w, hwmk, hw₁φ]
  ·
    have hfK : ¬ f ∣ Nat.card φ.ker := by
      rw [hker]
      exact hfZ
    obtain ⟨x, hxz, hxo⟩ := CFSG.FiveTransitive.PrimeFreeOrderLift.exists_lift φ hsurj hfK z hz
    exact ⟨x, hxo, hxz⟩

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
