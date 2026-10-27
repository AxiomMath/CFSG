module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCor48
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Cent

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def FooteNoEscape (M : Subgroup G) : Prop :=
  ∀ t ∈ coreActionKernel M, orderOf t = 2 → centralizer ({t} : Set G) ≤ normalizer (M : Set G)

omit [Finite G] in
theorem FooteNoEscape.conjugate {M : Subgroup G} (hM : FooteNoEscape M) (g : G) :
    FooteNoEscape (conjugate M g) := by
  intro t ht ht2 x hx
  rw [← GSThmB.conjugate_coreActionKernel, mem_conjugate_iff] at ht
  have hgt : orderOf (g * t * g⁻¹) = 2 := by
    rw [← ht2]
    exact MulEquiv.orderOf_eq (MulAut.conj g) t
  rw [← GSThmB.conjugate_normalizer, mem_conjugate_iff]
  apply hM _ ht hgt
  rw [mem_centralizer_singleton_iff] at hx ⊢
  calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
    _ = g * (t * x) * g⁻¹ := by rw [hx]
    _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group

theorem normalizer_coreActionKernel_eq (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) {M : Subgroup G} (hM : IsFooteM L M) :
    normalizer (coreActionKernel M : Set G) = normalizer (M : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (normalizer_le_normalizer_coreActionKernel M)
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (coreActionKernel M)
  obtain ⟨E, hE2, hE8, hEC⟩ := hM.exists_card_eight h
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hE8]; norm_num)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hT hEC hEp
  obtain ⟨W, hW, hWE⟩ := exists_isKleinFour_le (B := conjugate E k)
    (sq_eq_one_of_mem_conjugate hE2 k) (by rw [card_conjugate_eq_card, hE8]; norm_num)
  have hWT : W ≤ T := hWE.trans (conjugate_le_of_forall hk)
  exact normalizer_le_of_isSylowOf hT (fun c hc => (mem_coreActionKernel.mp hc).1)
    (foote_cor_4_8_iv h h47 hST hM hT.le hW hWT)

theorem tightlyEmbedded_coreActionKernel (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) {M : Subgroup G} (hM : IsFooteM L M)
    (hne : FooteNoEscape M) : TightlyEmbedded (coreActionKernel M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE2, hE8, hEC⟩ := hM.exists_card_eight h
  refine ⟨?_, fun g hg => ?_⟩
  · have h1 : 8 ∣ Nat.card (coreActionKernel M) := hE8 ▸ Subgroup.card_dvd_of_le hEC
    exact even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 8).trans h1)
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(coreActionKernel M ⊓
    rightConjugate (coreActionKernel M) g)) 2 (even_iff_two_dvd.mp hodd)
  obtain ⟨ht₁, ht₂⟩ := mem_inf.mp t.2
  have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have ht₂' : (t : G) ∈ coreActionKernel (conjugate M g) := by
    rw [← GSThmB.conjugate_coreActionKernel]
    exact ht₂
  obtain ⟨n, hn, c, hc, rfl⟩ := foote_cor_4_8_iii h h47 hST hM ht2 ht₁ ht₂'
  apply hg
  rw [normalizer_coreActionKernel_eq h h47 hST hM]
  exact mul_mem hn (hne _ ht₁ ht2 hc)

end CFSG.ComponentClassification.FooteLit
