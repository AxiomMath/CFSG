module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Shape


@[expose] def A7TCThin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    Std2A7 Ω K → (∀ L ∈ Ω, ∀ J ∈ twinSet Ω L, J = L) → ¬ DEdgeless Ω → DConnected Ω →
      (∀ L ∈ Ω, ∀ z : G, IsUniqueInvolution L z → ∀ J₁ ∈ omegaNbr Ω L, ∀ J₂ ∈ omegaNbr Ω L,
        ∃ q ∈ oddCoreOf (T8.layerJoin Ω z), J₂ = conjSub q J₁) →
      (∀ L ∈ Ω, ∀ A ∈ omegaNbr Ω L, ∀ B ∈ omegaNbr Ω L, B ∉ omegaNbr Ω A) → False

@[expose] def A7TCMatch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    Std2A7 Ω K → (∀ L ∈ Ω, ∀ J ∈ twinSet Ω L, J = L) →
      (∀ L ∈ Ω, ∀ z : G, IsUniqueInvolution L z → ¬ Hat2A7S8.IndepTri Ω L z) →
      ∀ L ∈ Ω, ∀ z : G, IsUniqueInvolution L z → ∀ J₁ ∈ omegaNbr Ω L, ∀ J₂ ∈ omegaNbr Ω L,
        T8.layerImg Ω z J₁ ≠ T8.layerImg Ω z J₂ → False

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G}

theorem not_mem_omegaNbr_of_layerImg_eq (hs : Pre2A7 Ω K₀)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {L : Subgroup G} (hL : L ∈ Ω) {z : G}
    (hz : IsUniqueInvolution L z) {A B : Subgroup G} (hA : A ∈ omegaNbr Ω L)
    (hB : B ∈ omegaNbr Ω L) (hAB : T8.layerImg Ω z A = T8.layerImg Ω z B) :
    B ∉ omegaNbr Ω A := by
  intro hBA
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hw : ∀ M ∈ Ω, A7Witness M := Hat2A7S8.witness_of_pre hs
  have hLH : Hat2A7S8.Asc77.T8.LayerHyp Ω z := Hat2A7S8.layerHyp_of_pre hs hz.sq hz.ne_one
  have hAx : T8.XMem Ω z A := Hat2A7S8.xMem_of_mem_omegaNbr hΩ hw hL hz hA
  have hBx : T8.XMem Ω z B := Hat2A7S8.xMem_of_mem_omegaNbr hΩ hw hL hz hB
  obtain ⟨n, hn, hnA⟩ := Hat2A7S8.Asc77.T8.exists_oddCore_conj_of_layerImg_eq hLH hAx hBx hAB
  obtain ⟨tA, htA⟩ := Sec6Gen.exists_uniqueInvolution hΩ hA.1
  have htB : IsUniqueInvolution B (n * tA * n⁻¹) := by
    rw [← hnA]
    exact htA.conj n
  have hcomm : tA * (n * tA * n⁻¹) = (n * tA * n⁻¹) * tA :=
    Q3.Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ htA hBA htB
  have htAz : tA ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : z * tA * z⁻¹ = tA := htA.conj_eq (mem_normalizer_iff_conjSub_eq.mp hAx.2.1)
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have htAN : tA ∈ Subgroup.normalizer (oddCoreOf (T8.layerJoin Ω z) : Set G) :=
    Hat2A7S8.Asc77.T8.mem_normalizer_oddCoreOf_layerJoin hΩ
      (by rw [T8.cenZ_eq_centralizer]; exact htAz)
  have hm : tA * (n * tA * n⁻¹) ∈ oddCoreOf (T8.layerJoin Ω z) := by
    have h1 : tA * n * tA⁻¹ ∈ oddCoreOf (T8.layerJoin Ω z) :=
      (Subgroup.mem_normalizer_iff.mp htAN n).mp hn
    have e : tA * (n * tA * n⁻¹) = (tA * n * tA⁻¹) * n⁻¹ := by
      have : tA⁻¹ = tA := inv_eq_of_mul_eq_one_right htA.sq
      rw [this]
      group
    rw [e]
    exact (oddCoreOf (T8.layerJoin Ω z)).mul_mem h1 ((oddCoreOf (T8.layerJoin Ω z)).inv_mem hn)
  have hm2 : (tA * (n * tA * n⁻¹)) * (tA * (n * tA * n⁻¹)) = 1 := by
    have hsq : (n * tA * n⁻¹) * (n * tA * n⁻¹) = 1 := htB.sq
    calc (tA * (n * tA * n⁻¹)) * (tA * (n * tA * n⁻¹))
        = tA * ((n * tA * n⁻¹) * tA) * (n * tA * n⁻¹) := by group
      _ = tA * (tA * (n * tA * n⁻¹)) * (n * tA * n⁻¹) := by rw [hcomm]
      _ = (tA * tA) * ((n * tA * n⁻¹) * (n * tA * n⁻¹)) := by group
      _ = 1 := by rw [htA.sq, hsq]; simp
  have hodd : Odd (orderOf (tA * (n * tA * n⁻¹))) :=
    (odd_natCard_oddCoreOf (T8.layerJoin Ω z)).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hm)
  have hord2 : orderOf (tA * (n * tA * n⁻¹)) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hm2)
  have hm1 : tA * (n * tA * n⁻¹) = 1 := by
    have h2 : orderOf (tA * (n * tA * n⁻¹)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h2
  have htBA : n * tA * n⁻¹ = tA := by
    have h3 : n * tA * n⁻¹ = tA⁻¹ := eq_inv_of_mul_eq_one_right hm1
    rw [h3]
    exact inv_eq_of_mul_eq_one_right htA.sq
  have hBt : IsUniqueInvolution B tA := by
    rw [← htBA]
    exact htB
  exact hBA.2.1 (hnt A hA.1 B ⟨hB.1, tA, htA, hBt⟩)

theorem a7TCRes_of_thin_match (hThin : A7TCThin) (hMatch : A7TCMatch) : A7TCRes := by
  intro G _ _ _ Ω K hs hnt hedge hconn hnoI
  have hΩ : HypOmegaGen Ω := hs.hyp
  by_cases hM : ∃ L ∈ Ω, ∃ z : G, IsUniqueInvolution L z ∧ ∃ J₁ ∈ omegaNbr Ω L,
      ∃ J₂ ∈ omegaNbr Ω L, T8.layerImg Ω z J₁ ≠ T8.layerImg Ω z J₂
  · obtain ⟨L, hL, z, hz, J₁, hJ₁, J₂, hJ₂, hne⟩ := hM
    exact hMatch G Ω K hs hnt hnoI L hL z hz J₁ hJ₁ J₂ hJ₂ hne
  · push Not at hM
    refine hThin G Ω K hs hnt hedge hconn (fun L hL z hz J₁ hJ₁ J₂ hJ₂ => ?_)
      (fun L hL A hA B hB => ?_)
    · have hw : ∀ M ∈ Ω, A7Witness M := Hat2A7S8.witness_of_pre hs.toPre2A7
      have hLH : Hat2A7S8.Asc77.T8.LayerHyp Ω z :=
        Hat2A7S8.layerHyp_of_pre hs.toPre2A7 hz.sq hz.ne_one
      have hx1 : T8.XMem Ω z J₁ := Hat2A7S8.xMem_of_mem_omegaNbr hΩ hw hL hz hJ₁
      have hx2 : T8.XMem Ω z J₂ := Hat2A7S8.xMem_of_mem_omegaNbr hΩ hw hL hz hJ₂
      obtain ⟨n, hn, hnJ⟩ := Hat2A7S8.Asc77.T8.exists_oddCore_conj_of_layerImg_eq hLH hx1 hx2
        (hM L hL z hz J₁ hJ₁ J₂ hJ₂)
      exact ⟨n, hn, hnJ.symm⟩
    · obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hL
      exact not_mem_omegaNbr_of_layerImg_eq hs.toPre2A7 hnt hL hz hA hB
        (hM L hL z hz A hA B hB)

end Shape

end CFSG.ClassicalInvolution.Hat2A7S
