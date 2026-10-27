module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoPGroup
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingInheritance

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem sylow_ambient_of_involution_centralizers
    (K : Subgroup G) (D : Sylow 2 K)
    (hD : (D : Subgroup K) ≠ ⊥)
    (hcentral : ∀ v ∈ K, orderOf v = 2 → Subgroup.centralizer ({v} : Set G) ≤ K) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = (D : Subgroup K).map K.subtype := by
  let A : Subgroup G := (D : Subgroup K).map K.subtype
  have hAp : IsPGroup 2 A := D.isPGroup'.map K.subtype
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  have hAK : A ≤ K := Subgroup.map_subtype_le _
  have hAne : A ≠ ⊥ := by
    intro hA
    apply hD
    exact Subgroup.map_injective K.subtype_injective (by simpa only [A, Subgroup.map_bot] using hA)
  let DP : Subgroup P := A.subgroupOf (P : Subgroup G)
  have hDPne : DP ≠ ⊥ := by
    intro hDP
    apply hAne
    rw [← Subgroup.map_subgroupOf_eq_of_le hAP]
    change DP.map (P : Subgroup G).subtype = ⊥
    rw [hDP, Subgroup.map_bot]
  have hDPtop : DP = ⊤ := by
    by_contra hDPproper
    let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
    have hlt : DP < Subgroup.normalizer (DP : Set P) :=
      Group.normalizerCondition_of_isNilpotent DP (lt_top_iff_ne_top.mpr hDPproper)
    let R : Subgroup P := Subgroup.normalizer (DP : Set P)
    have hDPR : DP ≤ R := DP.le_normalizer
    let N : Subgroup R := DP.subgroupOf R
    have hNnormal : N.Normal := by
      dsimp [N, R]
      infer_instance
    have hNne : N ≠ ⊥ := by
      intro hN
      apply hDPne
      rw [← Subgroup.map_subgroupOf_eq_of_le hDPR]
      change N.map R.subtype = ⊥
      rw [hN, Subgroup.map_bot]
    obtain ⟨v, hvN, hvcenter, hvorder⟩ :=
      normal_two_subgroup_contains_central_involution
        (P.isPGroup'.to_subgroup R) N hNne
    have hvA : ((v : P) : G) ∈ A := hvN
    have hvK : ((v : P) : G) ∈ K := hAK hvA
    have hvGorder : orderOf ((v : P) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hvorder]
    have hRK : ∀ r : R, ((r : P) : G) ∈ K := by
      intro r
      apply hcentral _ hvK hvGorder
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact congrArg (fun x : R => ((x : P) : G))
        ((Subgroup.mem_center_iff.mp hvcenter) r)
    let Rg : Subgroup G := R.map (P : Subgroup G).subtype
    have hRgK : Rg ≤ K := by
      rintro x ⟨r, hr, rfl⟩
      exact hRK ⟨r, hr⟩
    have hRgP : IsPGroup 2 Rg := (P.isPGroup'.to_subgroup R).map _
    have hARg : A ≤ Rg := by
      intro a ha
      exact ⟨⟨a, hAP ha⟩, hDPR ha, rfl⟩
    have hDRg : (D : Subgroup K) ≤ Rg.subgroupOf K := by
      intro d hd
      exact hARg (Subgroup.mem_map_of_mem K.subtype hd)
    have hRgD : Rg.subgroupOf K = (D : Subgroup K) :=
      D.is_maximal' (hRgP.of_equiv (Subgroup.subgroupOfEquivOfLe hRgK).symm) hDRg
    have hRgA : Rg = A := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hRgK, hRgD]
    have hRDP : R ≤ DP := by
      intro r hr
      have hrA : (r : G) ∈ A := hRgA ▸ (Subgroup.mem_map_of_mem _ hr)
      exact hrA
    exact (not_le_of_gt hlt) hRDP
  refine ⟨P, le_antisymm ?_ hAP⟩
  intro p hp
  have hpDP : (⟨p, hp⟩ : P) ∈ DP := hDPtop ▸ Subgroup.mem_top _
  exact hpDP

theorem ambient_sylows_conjugate_in_subgroup (H : Subgroup G)
    (P Q : Sylow 2 G) (hPH : (P : Subgroup G) ≤ H) (hQH : (Q : Subgroup G) ≤ H) :
    ∃ a : H, (a : G) • P = Q := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq H (P.subtype hPH) (Q.subtype hQH)
  refine ⟨a, Sylow.subtype_injective (N := H)
    (hP := Sylow.smul_le hPH a) (hQ := hQH) ?_⟩
  have hrestrict : ((a : G) • P : Sylow 2 G).subtype (Sylow.smul_le hPH a) =
      a • P.subtype hPH := by
    apply Sylow.ext
    exact (Subgroup.conj_smul_subgroupOf hPH a).symm
  exact hrestrict.trans ha

theorem ambient_sylow_normalizer_le_subgroup (H : Subgroup G)
    (S P : Sylow 2 G) (hSH : (S : Subgroup G) ≤ H) (hPH : (P : Subgroup G) ≤ H)
    (hNS : Subgroup.normalizer (S : Set G) ≤ H) :
    Subgroup.normalizer (P : Set G) ≤ H := by
  obtain ⟨a, ha⟩ := ambient_sylows_conjugate_in_subgroup H S P hSH hPH
  intro x hx
  have hfix : x • P = P := Sylow.smul_eq_iff_mem_normalizer.mpr hx
  have hfixS : ((a : G)⁻¹ * x * a) • S = S := by
    rw [mul_smul, mul_smul, ha, hfix, ← ha, inv_smul_smul]
  have hconjH := hNS (Sylow.smul_eq_iff_mem_normalizer.mp hfixS)
  have hmem := H.mul_mem (H.mul_mem a.property hconjH) (H.inv_mem a.property)
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
    mul_inv_cancel, mul_one] using hmem

theorem native_strong_embedding_of_sylow_normalizer_involution_centralizers
    (H : Subgroup G) (hproper : H ≠ ⊤) (heven : Even (Nat.card H))
    (S : Sylow 2 G) (hSH : (S : Subgroup G) ≤ H)
    (hNS : Subgroup.normalizer (S : Set G) ≤ H)
    (hcentral : ∀ v ∈ H, orderOf v = 2 → Subgroup.centralizer ({v} : Set G) ≤ H) :
    IsStronglyEmbedded H := by
  refine ⟨hproper, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := H) 2
      (even_iff_two_dvd.mp heven)
    have hvG : orderOf (v : G) = 2 := (Subgroup.orderOf_coe v).trans hv
    have hvI := orderOf_eq_prime_iff.mp hvG
    exact ⟨v, v.property, hvI.2, hvI.1⟩
  · intro g hg x hxH hxconj hxI
    let K : Subgroup G := H ⊓ rightConjugate H g
    let xK : K := ⟨x, hxH, hxconj⟩
    have hxKI : IsInvolution xK := IsInvolution.subtype hxI xK.property
    obtain ⟨D, hcyclicD⟩ := (isPGroup_zpowers_of_involution hxKI).exists_le_sylow
    have hDne : (D : Subgroup K) ≠ ⊥ := by
      intro hD
      have hxD := hcyclicD (Subgroup.mem_zpowers xK)
      rw [hD] at hxD
      exact hxKI.ne_one (Subgroup.mem_bot.mp hxD)
    have hcentralK : ∀ v ∈ K, orderOf v = 2 → Subgroup.centralizer ({v} : Set G) ≤ K := by
      intro v hv hvorder c hc
      refine ⟨hcentral v hv.1 hvorder hc, ?_⟩
      have hvback : g * v * g⁻¹ ∈ H := by
        have hvconj : v ∈ rightConjugate H g := hv.2
        have hback := rightConjugateElem_mem_of_mem_rightConjugate (g := g⁻¹)
          (by simpa only [inv_inv] using hvconj)
        simpa only [rightConjugateElem, inv_inv] using hback
      have hvbackorder : orderOf (g * v * g⁻¹) = 2 :=
        ((MulAut.conj g).orderOf_eq v).trans hvorder
      have hcback : g * c * g⁻¹ ∈ H := by
        apply hcentral _ hvback hvbackorder
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hc
        simpa only [map_mul, MulAut.conj_apply] using congrArg (MulAut.conj g) hcomm
      change c ∈ rightConjugate H g
      rw [rightConjugate, Subgroup.conjBy]
      exact Subgroup.mem_map.mpr ⟨g * c * g⁻¹, hcback, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
          mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]⟩
    obtain ⟨P, hP⟩ := sylow_ambient_of_involution_centralizers K D hDne hcentralK
    have hPK : (P : Subgroup G) ≤ K := by
      rw [hP]
      exact Subgroup.map_subtype_le _
    have hPH : (P : Subgroup G) ≤ H := hPK.trans inf_le_left
    have hPgH : ((g • P : Sylow 2 G) : Subgroup G) ≤ H := by
      intro y hy
      rw [Sylow.coe_subgroup_smul] at hy
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_smul_pointwise_iff_exists y (MulAut.conj g)
        (P : Subgroup G) |>.mp hy
      have hpconj : p ∈ rightConjugate H g := (hPK hp).2
      have hback := rightConjugateElem_mem_of_mem_rightConjugate (g := g⁻¹)
        (by simpa only [inv_inv] using hpconj)
      simpa only [MulAut.smul_def, MulAut.conj_apply, rightConjugateElem, inv_inv] using hback
    obtain ⟨a, ha⟩ := ambient_sylows_conjugate_in_subgroup H (g • P) P hPgH hPH
    have hfix : ((a : G) * g) • P = P := by rw [mul_smul, ha]
    have hagH : (a : G) * g ∈ H := ambient_sylow_normalizer_le_subgroup H S P hSH hPH hNS
      (Sylow.smul_eq_iff_mem_normalizer.mp hfix)
    have hgH := H.mul_mem (H.inv_mem a.property) hagH
    exact hg (by simpa only [inv_mul_cancel_left] using hgH)

theorem sylow_normalizer_involution_centralizer_strong_embedding
    (H : Subgroup G) (hproper : H ≠ ⊤) (heven : Even (Nat.card H))
    (S : Sylow 2 G) (hSH : (S : Subgroup G) ≤ H)
    (hNS : Subgroup.normalizer (S : Set G) ≤ H)
    (hcentral : ∀ v ∈ H, orderOf v = 2 → Subgroup.centralizer ({v} : Set G) ≤ H) :
    fusionStronglyEmbedded H :=
  order_strong_embedding_of_native
    (native_strong_embedding_of_sylow_normalizer_involution_centralizers
      H hproper heven S hSH hNS hcentral)

end CFSG.ProperTwoGeneratedCore
