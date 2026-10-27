module

public import CFSG.ClassicalInvolution.Q3.Q3T8AF03
public import CFSG.ClassicalInvolution.Q3.Q3T8AF02

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3T8.AF
open scoped commutatorElement

section CommMod


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def CommMod (Ω : Set (Subgroup G)) (z : G) (M N : Subgroup G) : Prop :=
  ∀ a ∈ Q3NL.exactCore3 z M, ∀ b ∈ Q3NL.exactCore3 z N,
    ⁅a, b⁆ ∈ oddCoreOf (Q3NL.exactLayer3 Ω z)

theorem CommMod.symm {z : G} {M N : Subgroup G} (h : CommMod Ω z M N) : CommMod Ω z N M := by
  intro a ha b hb
  have := (oddCoreOf (Q3NL.exactLayer3 Ω z)).inv_mem (h b hb a ha)
  rwa [commutatorElement_inv] at this

theorem alphaConst_of_commMod [IsSimpleGroup G] {K₀ : Subgroup G}
    (hs : Q3.Disc3.AscStand3 Ω K₀) (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    {K A N : Subgroup G} {z tA tN : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hA : A ∈ omegaNbr Ω K) (hN : N ∈ omegaNbr Ω K) (htA : IsUniqueInvolution A tA)
    (htN : IsUniqueInvolution N tN)
    (hOA : oddCoreOf (Q3NL.exactLayer3 Ω z) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({tA, z} : Set G)) : Set G))
    (hAN : CommMod Ω z A N) (hJ : ∀ J ∈ omegaNbr Ω K, CommMod Ω z J A ∨ CommMod Ω z J N) :
    ∀ J ∈ omegaNbr Ω K, ∀ tJ : G, IsUniqueInvolution J tJ →
      alphaOf (Subgroup.closure ({tJ, z} : Set G)) =
        alphaOf (Subgroup.closure ({tA, z} : Set G)) := by
  have hΩ : HypOmegaMod Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hs.hyp
  have htAc : tA ∈ Q3NL.exactCore3 z A :=
    ⟨htA.mem, Subgroup.mem_centralizer_singleton_iff.mpr
      (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hA htA).symm⟩
  have htNc : tN ∈ Q3NL.exactCore3 z N :=
    ⟨htN.mem, Subgroup.mem_centralizer_singleton_iff.mpr
      (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hN htN).symm⟩
  have hNA : alphaOf (Subgroup.closure ({tN, z} : Set G)) =
      alphaOf (Subgroup.closure ({tA, z} : Set G)) :=
    alphaOf_eq_of_comm hs hnt hK hz hN hA htN htA hOA fun r hr => hAN.symm r hr tA htAc
  have hON : oddCoreOf (Q3NL.exactLayer3 Ω z) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({tN, z} : Set G)) : Set G) := by
    rw [hNA]
    exact hOA
  intro J hJ' tJ htJ
  rcases hJ J hJ' with h | h
  · exact alphaOf_eq_of_comm hs hnt hK hz hJ' hA htJ htA hOA fun r hr => h r hr tA htAc
  · rw [alphaOf_eq_of_comm hs hnt hK hz hJ' hN htJ htN hON fun r hr => h r hr tN htNc, hNA]

end CommMod

section Pure

@[expose] def PureLinkConst3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    Q3.Disc3.AscStand3 Ω K → (∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) → ∀ z : G,
      IsUniqueInvolution K z → ∀ (A B : Subgroup G) (tA tB : G), A ∈ omegaNbr Ω K →
        B ∈ omegaNbr Ω K → B ∈ omegaNbr Ω A → IsUniqueInvolution A tA →
          IsUniqueInvolution B tB → tB ∉ Subgroup.closure ({z, tA} : Set G) →
            ∀ (ι : Type) (D : Q3.LieSystemData3 ι (Q3T7.layerQuot3 Ω z) (Q3T7.layerFam3 Ω z)),
              (∀ N ∈ omegaNbr Ω K, ∀ (i j : ι) (R : Subgroup (D.kind i).G)
                (R' : Subgroup (D.kind j).G), Layer.layerImg3 Ω z N = R.map (D.hom i) →
                  Layer.layerImg3 Ω z A = R'.map (D.hom j) → i = j) →
                ∀ J ∈ omegaNbr Ω K, ∀ tJ : G, IsUniqueInvolution J tJ →
                  alphaOf (Subgroup.closure ({tJ, z} : Set G)) =
                    alphaOf (Subgroup.closure ({tA, z} : Set G))

end Pure

section Main



theorem alphaFrame3_of_pure (hP : PureLinkConst3) : AlphaFrame3 := by
  intro G _ _ _ Ω K hs hnt0 hframe z hz J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2
  have hΩ : HypOmegaMod Ω := hs.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.trans hnt0 hM
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.toStand3
  have hK : K ∈ Ω := hs.mem
  have hΩu : HypOmegaModU (.sl2 3 1) Ω := hs.modU
  obtain ⟨A, B, tA, tB, hA, hB, hAB, htA, htB, hind⟩ := exists_triangle hs3 hz hframe
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨a, -, hac⟩ := IsConcreteLE.not_le_iff_exists.mp
      (isClassicalMember3_of_uniqueInvolution hΩu hK hz).not_le_center
    rw [Subgroup.mem_center_iff] at hac
    push Not at hac
    obtain ⟨b, hb⟩ := hac
    exact ⟨b, a, hb⟩
  have hnc := Q3W.not_subset_center_of_ne_one hnab hz.ne_one
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) :=
    ExactLayer.isPGroup_zpowers_of_sq_eq_one hz.sq
  obtain ⟨ι, -, ⟨D⟩⟩ := Q3T7.lieSystemMod3_exactPair3_of_stand3 hs3 hc2 hnc
  have hOA := oddCore_le_normalizer_alpha hs3 hnt hK hz hA hB htA htB hAB hind
  have hdata : ∀ M ∈ omegaNbr Ω K, ∀ t : G, IsUniqueInvolution M t →
      ∃ i, ∃ R : Subgroup (D.kind i).G, Layer.layerImg3 Ω z M = R.map (D.hom i) := by
    intro M hM t ht
    obtain ⟨i, R, -, hMR⟩ := D.fundamental _
      (Layer.layerImg3_mem (mem_tqMembers3_of_omegaNbr hΩ hnt hz hM ht))
    exact ⟨i, R, hMR⟩
  have key : ∀ J ∈ omegaNbr Ω K, ∀ tJ : G, IsUniqueInvolution J tJ →
      alphaOf (Subgroup.closure ({tJ, z} : Set G)) =
        alphaOf (Subgroup.closure ({tA, z} : Set G)) := by
    by_cases hmulti : ∃ N ∈ omegaNbr Ω K, ∃ tN : G, IsUniqueInvolution N tN ∧
        ∃ (i j : ι) (R : Subgroup (D.kind i).G) (R' : Subgroup (D.kind j).G), i ≠ j ∧
          Layer.layerImg3 Ω z N = R.map (D.hom i) ∧ Layer.layerImg3 Ω z A = R'.map (D.hom j)
    · obtain ⟨N, hN, tN, htN, i, j, R, R', hij, hNR, hAR⟩ := hmulti
      have hNt := mem_tqMembers3_of_omegaNbr hΩ hnt hz hN htN
      have hAt := mem_tqMembers3_of_omegaNbr hΩ hnt hz hA htA
      have hNA : CommMod Ω z N A := comm_mem_oddCoreOf_of_components D hij hNt hAt hNR hAR
      have hAN : CommMod Ω z A N := hNA.symm
      refine alphaConst_of_commMod hs3 hnt hK hz hA hN htA htN hOA hAN ?_
      intro J hJ
      obtain ⟨tJ, htJ⟩ := hΩ.exists_uniqueInvolution hJ.1
      obtain ⟨k, RJ, hJR⟩ := hdata J hJ tJ htJ
      have hJt := mem_tqMembers3_of_omegaNbr hΩ hnt hz hJ htJ
      by_cases hkj : k = j
      · subst hkj
        have hki : k ≠ i := fun e => hij e.symm
        exact Or.inr (comm_mem_oddCoreOf_of_components D hki hJt hNt hJR hNR)
      · exact Or.inl (comm_mem_oddCoreOf_of_components D hkj hJt hAt hJR hAR)
    · push Not at hmulti
      refine hP G Ω K hs3 hnt z hz A B tA tB hA hB hAB htA htB hind ι D ?_
      intro N hN i j R R' hNR hAR
      obtain ⟨tN, htN⟩ := hΩ.exists_uniqueInvolution hN.1
      by_contra hne
      exact (hmulti N hN tN htN i j R R' hne hNR) hAR
  have e2 := key J₂ hJ₂ t₂ h2
  have e1 := key J₁ hJ₁ t₁ h1
  rw [e2, e1]

end Main

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
