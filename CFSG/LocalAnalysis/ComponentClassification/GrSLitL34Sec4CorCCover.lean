module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCTransfer

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem commutator_le_oddIn_of_ne {C K K' : Subgroup X} (hKC : K ≤ C) (hK'C : K' ≤ C)
    (hK : IsPComponent 2 (K.subgroupOf C)) (hK' : IsPComponent 2 (K'.subgroupOf C))
    (hne : K ≠ K') : ⁅K, K'⁆ ≤ (pPrimeCore 2 C).map C.subtype := by
  have hne' : K.subgroupOf C ≠ K'.subgroupOf C := by
    intro h
    apply hne
    have h1 := congrArg (Subgroup.map C.subtype) h
    rwa [map_subgroupOf_eq_of_le hKC, map_subgroupOf_eq_of_le hK'C] at h1
  obtain ⟨-, h2⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two
    _ _ hK hK'
  obtain ⟨-, -, hc, -⟩ := h2 hne'
  have hc' : ⁅K.subgroupOf C, K'.subgroupOf C⁆ ≤ pPrimeCore 2 ↥C := by
    refine hc.trans (inf_le_left.trans ?_)
    exact (UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal
      (hK.choose_spec.2.1)).le.trans inf_le_right
  have h3 := map_mono (f := C.subtype) hc'
  rwa [map_commutator, map_subgroupOf_eq_of_le hKC, map_subgroupOf_eq_of_le hK'C] at h3

theorem eq_or_eq_of_le_sup {C M N N' T : Subgroup X} (hMC : M ≤ C) (hNC : N ≤ C)
    (hN'C : N' ≤ C) (hM : IsPComponent 2 (M.subgroupOf C)) (hN : IsPComponent 2 (N.subgroupOf C))
    (hN' : IsPComponent 2 (N'.subgroupOf C)) (hTM : T ≤ M) (hTN : T ≤ N ⊔ N')
    (hTperf : ⁅T, T⁆ = T) (hTO : ¬ T ≤ (pPrimeCore 2 C).map C.subtype) : M = N ∨ M = N' := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hc₁ := commutator_le_oddIn_of_ne hNC hMC hN hM (Ne.symm h1)
  have hc₂ := commutator_le_oddIn_of_ne hN'C hMC hN' hM (Ne.symm h2)
  have hCN : C ≤ normalizer (((pPrimeCore 2 C).map C.subtype : Subgroup X) : Set X) :=
    fun g hg => UnbalancedGS.normalizer_le_normalizer_map_of_characteristic C (pPrimeCore 2 C)
      (le_normalizer hg)
  have hsup : ∀ m ∈ M, ∀ x ∈ N ⊔ N', x⁻¹ * m⁻¹ * x * m ∈ (pPrimeCore 2 C).map C.subtype := by
    intro m hm
    refine forall_sup_of_forall hCN hNC hN'C (fun x hx => ?_) fun x hx => ?_
    · have h3 : ⁅x⁻¹, m⁻¹⁆ ∈ ⁅N, M⁆ := commutator_mem_commutator (inv_mem hx) (inv_mem hm)
      have h4 := hc₁ h3
      rwa [commutatorElement_def, inv_inv, inv_inv] at h4
    · have h3 : ⁅x⁻¹, m⁻¹⁆ ∈ ⁅N', M⁆ := commutator_mem_commutator (inv_mem hx) (inv_mem hm)
      have h4 := hc₂ h3
      rwa [commutatorElement_def, inv_inv, inv_inv] at h4
  apply hTO
  rw [← hTperf, commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have h3 := hsup g₂⁻¹ (hTM (inv_mem hg₂)) g₁⁻¹ (hTN (inv_mem hg₁))
  rwa [inv_inv, inv_inv, ← commutatorElement_def] at h3

theorem mem_normalizer_of_le {C M T : Subgroup X} (hMC : M ≤ C)
    (hM : IsPComponent 2 (M.subgroupOf C)) (hTM : T ≤ M) (hTperf : ⁅T, T⁆ = T)
    (hTO : ¬ T ≤ (pPrimeCore 2 C).map C.subtype) {w : X} (hwC : w ∈ C)
    (hwT : w ∈ normalizer (T : Set X)) : w ∈ normalizer (M : Set X) := by
  have hMw : conjugate M w ≤ C := fun y hy => by
    rw [mem_conjugate_iff] at hy
    have h2 := mul_mem (mul_mem (inv_mem hwC) (hMC hy)) hwC
    rwa [show w⁻¹ * (w * y * w⁻¹) * w = y by group] at h2
  have hMwc : IsPComponent 2 ((conjugate M w).subgroupOf C) := by
    have h1 := isPComponent_conjugate hM (⟨w, hwC⟩ : C)
    rwa [conjugate_subgroupOf_eq] at h1
  have hTw : T ≤ conjugate M w := by
    intro t ht
    rw [mem_conjugate_iff]
    exact hTM ((mem_normalizer_iff.mp hwT t).mp ht)
  rcases eq_or_eq_of_le_sup hMC hMw hMw hM hMwc hMwc hTM (by rw [sup_idem]; exact hTw) hTperf
    hTO with h | h <;> exact mem_normalizer_of_conjugate_eq h.symm

theorem not_le_oddIn_of_nontrivial {C T : Subgroup X} (hT : Nontrivial (T ⧸ pPrimeCore 2 T)) :
    ¬ T ≤ (pPrimeCore 2 C).map C.subtype := by
  intro hle
  have hodd : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 C).map C.subtype)) := by
    rw [card_map_of_injective C.subtype_injective]
    exact pPrimeCore_coprime_card
  have hcop : Nat.Coprime 2 (Nat.card (⊤ : Subgroup T)) := by
    rw [card_top]
    exact Nat.Coprime.coprime_dvd_right (card_dvd_of_le hle) hodd
  have htop : pPrimeCore 2 T = ⊤ := eq_top_iff.mpr (le_sSup ⟨inferInstance, hcop⟩)
  have : Subsingleton (T ⧸ pPrimeCore 2 T) := QuotientGroup.subsingleton_iff.mpr htop
  exact false_of_nontrivial_of_subsingleton (T ⧸ pPrimeCore 2 T)

theorem fixedLayer_le_of_isoCorr (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog X) {e s t z : X} {Le Lz M : Subgroup X}
    (hez : GSIsoCorr e Le z Lz) (hC : GrSLit.GSWeakCorr s Le t M) (htz : z * t = t * z)
    (htZ : t ∉ center X) (htLe : t ∈ coreActionKernel Le) (htLz : t ∈ coreActionKernel Lz) :
    gsFixedLayer Lz t ≤ M ⊔ conjugate M s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hezC, hezK, -⟩ := gsIsoCorr_iff_sup.mp hez
  have hzLz : Lz ≤ centralizer ({z} : Set X) := hezC.2.2.2.2.2.1
  have hLzp := hezC.2.2.2.2.2.2.1
  have hz2 : orderOf z = 2 := hezC.2.1
  have ht2 : orderOf t = 2 := hC.2.1
  have heK : t ∈ normalizer ((Lz ⊔ conjugate Lz e : Subgroup X) : Set X) := by
    rw [hezK]
    exact (mem_coreActionKernel.mp htLz).1
  have hKe : ∀ k ∈ Lz ⊔ conjugate Lz e, k⁻¹ * t⁻¹ * k * t ∈
      (pPrimeCore 2 (centralizer ({z} : Set X))).map (centralizer ({z} : Set X)).subtype := by
    rw [hezK]
    intro k hk
    exact GSLit.map_pPrimeCore_le_of_isPComponent hzLz hLzp
      ((mem_coreActionKernel.mp htLz).2 k hk)
  obtain ⟨hWTU, -, -, -, -, hWV, hncl⟩ := correspondence_nested_fixed_layer_normal_closure hezC
    ht2 htz (mem_coreActionKernel.mp htLe).1 heK (mem_coreActionKernel.mp htLe).2 hKe rfl rfl rfl
    rfl
  have hVeq : gsFixedLayer (Lz ⊔ conjugate Lz e) t = gsFixedLayer Lz t := by rw [hezK]
  have hLzz : conjugate Lz z = Lz := UnbalancedCorr.conjugate_eq_self_of_le_centralizer hzLz
  have hKe' : ∀ k ∈ Lz ⊔ conjugate Lz z, k⁻¹ * t⁻¹ * k * t ∈
      (pPrimeCore 2 (centralizer ({z} : Set X))).map (centralizer ({z} : Set X)).subtype := by
    rw [hLzz, sup_idem]
    intro k hk
    exact GSLit.map_pPrimeCore_le_of_isPComponent hzLz hLzp
      ((mem_coreActionKernel.mp htLz).2 k hk)
  obtain ⟨-, -, -, -, -, -, -, hVE', -, -, -⟩ :=
    UGSChain.kProper_core_trivial_orbit_fixed_layer_containment_of_schreier hS hK (a := z)
      (b := z) (e := t) hz2 ht2 rfl htz htZ hzLz hLzp hKe'
  rw [hLzz, sup_idem] at hVE'
  obtain ⟨-, -, hst, -, -, htM, hMp, -, -, hUK₁⟩ := id hC
  obtain ⟨-, hEK₁⟩ := GrSLit.sup_conjugate_le_pLayer hst htM hMp
  rw [← hVeq] at hVE' ⊢
  exact GSLit.le_of_normalClosure_eq_top hncl (hVE'.trans hEK₁)
    (hWTU.trans (inf_le_right.trans hUK₁))

end CFSG.ComponentClassification.GSThmB.CorC
