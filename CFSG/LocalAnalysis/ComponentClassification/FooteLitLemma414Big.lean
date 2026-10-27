module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Bender
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Sylow
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Tools

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_inf_centralizer_lt_eight
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {M : Subgroup G} (hM : IsFooteM L M)
    (hPE : FooteEvenOrNormalizes M) {A S : Subgroup G} (hAC : A ≤ coreActionKernel M)
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hS : IsSylowOf 2 S (normalizer (M : Set G))) {t g : G}
    (ht : orderOf t = 2) (htA : t ∈ A) (htS : ∀ s ∈ S, s * t = t * s)
    (hyC : g⁻¹ * t * g ∉ coreActionKernel M) :
    Nat.card ↥(A ⊓ centralizer ({g⁻¹ * t * g} : Set G)) < 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := coreActionKernel M with hC
  set N := normalizer (M : Set G) with hN
  set y := g⁻¹ * t * g with hy
  set U := A ⊓ centralizer ({y} : Set G) with hU
  by_contra hU8
  push Not at hU8
  have htC : t ∈ C := hAC htA
  have hSN : S ≤ N := hS.le
  have hSt : S ≤ centralizer ({t} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (htS s hs)
  have hSCt := isSylowOf_centralizer_of_le h h47 hST hM ht htC hS hSt
  have hU2 : ∀ x ∈ U, x ^ 2 = 1 := fun x hx => hA2 x (mem_inf.mp hx).1
  set U' := conjugate U g⁻¹ with hU'
  have hU't : U' ≤ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
    rw [mem_centralizer_singleton_iff]
    calc x * t = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by rw [hy]; group
      _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = t * x := by rw [hy]; group
  have hU'p : IsPGroup 2 U' := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact sq_eq_one_of_mem_conjugate hU2 g⁻¹ x x.2)⟩
  obtain ⟨c, hc, hcS⟩ := exists_conj_le_of_isSylowOf hSCt hU't hU'p
  set k := g⁻¹ * c with hk
  have hkU : ∀ u ∈ U, k⁻¹ * u * k ∈ S := by
    intro u hu
    have h1 : g * u * g⁻¹ ∈ U' := by
      rw [hU', mem_conjugate_iff, inv_inv]
      rwa [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    have h2 := hcS _ h1
    rwa [hk, show (g⁻¹ * c)⁻¹ * u * (g⁻¹ * c) = c⁻¹ * (g * u * g⁻¹) * c by group]
  set V := conjugate U k with hV
  have hVS : V ≤ S := conjugate_le_of_forall hkU
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := sq_eq_one_of_mem_conjugate hU2 k
  have hV8 : 8 ≤ Nat.card V := by rw [hV, card_conjugate_eq_card]; exact hU8
  set M' := conjugate M k with hM'
  have hM'F := isFooteM_conjugate h hM k
  have hVC' : V ≤ coreActionKernel M' := fun x hx =>
    mem_coreActionKernel_conjugate (hAC (mem_inf.mp (mem_conjugate_iff.mp hx)).1)
  have hkN : k ∉ N := by
    intro hkN
    apply hyC
    have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hc
    have h1 : k * t * k⁻¹ = y := by
      rw [hk, hy]
      calc g⁻¹ * c * t * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * t) * c⁻¹ * g := by group
        _ = g⁻¹ * (t * c) * c⁻¹ * g := by rw [hct]
        _ = g⁻¹ * t * g := by group
    rw [← h1]
    exact (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel M hkN) t).mp htC
  obtain ⟨W, hW, hWV⟩ := exists_isKleinFour_le hV2 (by omega)
  have hVC : ¬ V ≤ C := fun hle =>
    hkN (foote_cor_4_8_ii h h47 hST hM hW (hWV.trans hle) (hWV.trans hVC'))
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hV2 x x.2)⟩
  obtain ⟨E, hEV, hE2, hE8'⟩ := exists_card_eight_le_of_sq_eq_one hV2 hV8
  rcases hPE k E (le_inf (hEV.trans hVC') (hEV.trans (hVS.trans hSN))) hE2 hE8' with
    ⟨x, hx, hx2⟩ | hle
  ·
    have hev : Even (Nat.card ↥(C ⊓ coreActionKernel M')) := by
      rw [even_iff_two_dvd, ← hx2]
      exact Subgroup.orderOf_dvd_natCard _ hx
    have hVn : V ≤ normalizer ((C ⊓ coreActionKernel M' : Subgroup G) : Set G) := fun v hv =>
      mem_normalizer_inf_of_mem (normalizer_le_normalizer_coreActionKernel M (hSN (hVS hv)))
        (normalizer_le_normalizer_coreActionKernel M' (mem_coreActionKernel.mp (hVC' hv)).1)
    obtain ⟨u, hu, hu2, huc⟩ := exists_involution_centralizing hVp hVn hev
    exact hVC (le_coreActionKernel_of_mem_inf h h47 hM hu2 (mem_inf.mp hu).1 (mem_inf.mp hu).2
      hVC' (hVS.trans hSN) fun v hv => mem_centralizer_singleton_iff.mpr (huc v hv))
  ·
    have htV : t ∈ normalizer (V : Set G) :=
      mem_normalizer_of_forall_commute fun v hv => htS v (hVS hv)
    have htN' : t ∈ normalizer (M' : Set G) := foote_cor_4_8_iv h h47 hST hM'F hVC' hW hWV htV
    have hMM' := eq_conjugate_of_le_normalizer h h47 hST hA5 hE8 hK hcalc hM hle ht htC htN'
    exact hkN (mem_normalizer_of_conjugate_eq hMM'.symm)

end CFSG.ComponentClassification.FooteLit
