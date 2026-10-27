module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndX
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndLift

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_centralizer_le_centralizer_mul {z t : G} {K : Subgroup G} (htK : t ∈ K) :
    centralizer ({z} : Set G) ⊓ centralizer (K : Set G) ≤ centralizer ({z * t} : Set G) := by
  intro x hx
  obtain ⟨hxz, hxK⟩ := mem_inf.mp hx
  have h1 := mem_centralizer_singleton_iff.mp hxz
  have h2 : x * t = t * x := (mem_centralizer_iff.mp hxK t htK).symm
  rw [mem_centralizer_singleton_iff]
  calc x * (z * t) = (x * z) * t := by group
    _ = z * (x * t) := by rw [h1]; group
    _ = z * (t * x) := by rw [h2]
    _ = z * t * x := by group

theorem not_isSolvable_centralizer_mul_of_ne {z t : G} {K K₂ : Subgroup G}
    (hK : IsTwoComponentAt z K) (hK₂ : IsTwoComponentAt z K₂) (hne : K ≠ K₂) (htK : t ∈ K)
    (ht : t * t = 1) : ¬ Group.IsSolvable ↥(centralizer ({z * t} : Set G)) := by
  intro hsolv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htC := le_coreActionKernel_of_ne hK.2.1 hK₂.2.1 hK.2.2 hK₂.2.2 hne htK
  set F := K₂ ⊓ centralizer ({t} : Set G) with hF
  set φ : ↥F →* ↥K₂ ⧸ pPrimeCore 2 ↥K₂ :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K₂)).comp (Subgroup.inclusion inf_le_left) with hφ
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K₂) q
    have hm : (g : G) * t * (g : G)⁻¹ * t⁻¹ ∈ oddCoreIn K₂ := by
      have h1 := (mem_coreActionKernel.mp htC).2 _ (inv_mem g.2)
      rw [inv_inv, htinv] at h1
      rwa [htinv]
    obtain ⟨k, hk, hkg⟩ := exists_mem_mul_centralizer_of_mem ht (odd_card_oddCoreIn K₂) hm
    obtain ⟨k', hk', hkk'⟩ := mem_map.mp hk
    have hk'g : ((k'⁻¹ * g : ↥K₂) : G) = k⁻¹ * (g : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, show ((k' : ↥K₂) : G) = k from hkk']
    refine ⟨⟨(k'⁻¹ * g : ↥K₂), mem_inf.mpr ⟨(k'⁻¹ * g).2, by rw [hk'g]; exact hkg⟩⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    change ((k'⁻¹ * g : ↥K₂) : ↥K₂ ⧸ pPrimeCore 2 ↥K₂) = (g : ↥K₂ ⧸ pPrimeCore 2 ↥K₂)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff k').mpr hk',
      inv_one, one_mul]
  have hFC : F ≤ centralizer ({z * t} : Set G) := by
    intro x hx
    obtain ⟨hxK, hxt⟩ := mem_inf.mp hx
    have h1 := mem_centralizer_singleton_iff.mp (hK₂.2.1 hxK)
    have h2 := mem_centralizer_singleton_iff.mp hxt
    rw [mem_centralizer_singleton_iff]
    calc x * (z * t) = (x * z) * t := by group
      _ = z * (x * t) := by rw [h1]; group
      _ = z * (t * x) := by rw [h2]
      _ = z * t * x := by group
  have hFs : Group.IsSolvable ↥F :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hFC)
  have hQs : Group.IsSolvable (↥K₂ ⧸ pPrimeCore 2 ↥K₂) := Group.isSolvable_of_surjective hsurj
  exact LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple
    (isQuasisimple_quotient_of_isPComponent hK₂.2.1 hK₂.2.2) hQs

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem footeF_le_of_component (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {N B : Subgroup G}
    (hWN : ∀ B₁ B₂ : Subgroup G, B₁ ≤ S ⊓ L → B₂ ≤ conjugate (S ⊓ L) s → B₁ ≠ ⊥ → B₂ ≠ ⊥ →
      normalizer ((B₁ ⊔ B₂ : Subgroup G) : Set G) ≤ N)
    (hBN : B ≤ N) (hB : IsPComponent 2 (B.subgroupOf N)) (hLB : L ≤ B)
    (hRsB : conjugate (S ⊓ L) s ≤ B) {b : G}
    (hb : b ∈ conjugate (S ⊓ L) s) (hb2 : orderOf b = 2) : footeF L₀ b ≤ B := by
  have hbQ := H.l511 hb
  obtain ⟨hfix, hM, -, -, -, -⟩ := H.sec5.footeF_data hbQ hb2
  have hMN := H.footeF_le_of_mem_Rs hK hcalc hWN hb hb2
  have hbB : b ∈ B := hRsB hb
  have hbN : b ∈ N := hBN hbB
  have hKC : footeF L₀ b ≤ N ⊓ centralizer ({b} : Set G) := le_inf hMN hM.2.1
  obtain ⟨B', hB'N, hB', hMB', -⟩ := foote_lemma_2_1_iv_subgroup hbN hb2 hKC
    (isPComponent_subgroupOf_of_le hKC inf_le_right hM.2.2)
  have hBb : conjugate B b = B := CFSG.conjugate_eq_self_of_mem_normalizer (le_normalizer hbB)
  by_cases hB'B : B' = B
  · rw [hB'B, hBb, sup_idem] at hMB'
    exact hMB'
  exfalso
  have hne2 : conjugate B' b ≠ B := fun h => hB'B (by
    ext x
    constructor
    · intro hx
      have h1 : b⁻¹ * x * b ∈ conjugate B' b := by
        rw [UnbalancedLayer.mem_conjugate_iff, show b * (b⁻¹ * x * b) * b⁻¹ = x by group]
        exact hx
      rw [h] at h1
      rw [show x = b * (b⁻¹ * x * b) * b⁻¹ by group]
      exact mul_mem (mul_mem hbB h1) (inv_mem hbB)
    · intro hx
      have h1 : b⁻¹ * x * b ∈ B := mul_mem (mul_mem (inv_mem hbB) hx) hbB
      rw [← h, UnbalancedLayer.mem_conjugate_iff,
        show b * (b⁻¹ * x * b) * b⁻¹ = x by group] at h1
      exact h1)
  have hle1 := le_coreActionKernel_of_ne hB'N hBN hB' hB hB'B
  have hle2 := le_coreActionKernel_of_ne (conjugate_le_of_mem hB'N hbN) hBN
    (isPComponent_conjugate_subgroupOf hbN hB') hB hne2
  have htM : t ∈ footeF L₀ b := hfix ▸ H.sec5.R_le_footeFixed hbQ H.sec5.tR
  have htL : t ∈ coreActionKernel L := mem_coreActionKernel_of_le hLB
    (le_normalizer H.sec5.tL) ((hMB'.trans (sup_le hle1 hle2)) htM)
  have : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := H.sec5.quotient_simple.1
  exact center_ne_bot_of_mem_coreActionKernel H.sec5.tL H.sec5.t2 htL
    (center_eq_bot_of_isSimpleGroup H.sec5.quotient_nonabelian)

theorem noPumpUp (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {N B : Subgroup G}
    (hWN : ∀ B₁ B₂ : Subgroup G, B₁ ≤ S ⊓ L → B₂ ≤ conjugate (S ⊓ L) s → B₁ ≠ ⊥ → B₂ ≠ ⊥ →
      normalizer ((B₁ ⊔ B₂ : Subgroup G) : Set G) ≤ N)
    (hBN : B ≤ N) (hB : IsPComponent 2 (B.subgroupOf N)) (hLB : L ≤ B)
    (hRsB : conjugate (S ⊓ L) s ≤ B) :
    ∀ b ∈ oddQuotImage B (conjugate (S ⊓ L) s), orderOf b = 2 →
      ∃ Y : Subgroup (↥B ⧸ pPrimeCore 2 ↥B), IsTwoComponentAt b Y ∧
        oddQuotImage B (S ⊓ L) ≤ Y ∧
        Nonempty (Y ⧸ pPrimeCore 2 Y ≃* oddQuotImage B L ⧸ pPrimeCore 2 (oddQuotImage B L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro b' hb' hb'2
  obtain ⟨bB, hbB, rfl⟩ := mem_map.mp hb'
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥B) with hπ
  have hRs2 : IsPGroup 2 ↥((conjugate (S ⊓ L) s).subgroupOf B) :=
    (H.sec5.R_sylow.isPGroup.map _).comap_subtype
  have hbb : bB * bB = 1 := by
    refine GSThmB.OddQuot.injOn_of_isPGroup hRs2 (mul_mem hbB hbB) (one_mem _) ?_
    have h := pow_orderOf_eq_one (π bB)
    rw [hb'2, sq] at h
    rw [map_mul, map_one]
    exact h
  have hb1 : bB ≠ 1 := fun h => by
    rw [h, map_one, orderOf_one] at hb'2
    omega
  have hb2 : orderOf (bB : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hbb) hb1
  have hbRs : (bB : G) ∈ conjugate (S ⊓ L) s := mem_subgroupOf.mp hbB
  have hbQ := H.l511 hbRs
  obtain ⟨hfix, hM, -, -, -, -⟩ := H.sec5.footeF_data hbQ hb2
  have hMB := H.footeF_le_of_component hK hcalc hWN hBN hB hLB hRsB hbRs hb2
  have hRM : S ⊓ L ≤ footeF L₀ (bB : G) := hfix ▸ H.sec5.R_le_footeFixed hbQ
  obtain ⟨e₁⟩ := nonempty_quotient_equiv_oddQuotImage (B := B) hMB
  obtain ⟨e₂⟩ := H.nonempty_footeF_equiv hbQ hb2
  obtain ⟨e₃⟩ := nonempty_quotient_equiv_oddQuotImage (B := B) hLB
  exact ⟨oddQuotImage B (footeF L₀ (bB : G)), isTwoComponentAt_oddQuotImage bB.2 hMB hM,
    map_mono fun x hx => mem_subgroupOf.mpr (hRM (mem_subgroupOf.mp hx)),
    ⟨e₁.symm.trans (e₂.symm.trans e₃)⟩⟩

end Hyp

end CFSG.ComponentClassification.Sol78.F514
