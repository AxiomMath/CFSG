module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNFour
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNResidue
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNTwo

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem heldSingleNormalResidue_holds
    (hMax : MaximalTwoComponentInputHe) (hS : SchreierFor Blueprint.Catalog)
    (hHN : HeldNotProperFixedInput) (h64 : HeldSylowElementarySixtyFour)
    (hOut : HeldOuterInvolutionRank) (hMult : TBLit.HeldTrivialMultiplier) :
    HeldSingleNormalResidue := by
  intro X _ _ a L W K T h hE h3 ⟨P₀, hP₀⟩ hb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup X := h.simple
  obtain ⟨e₁⟩ := h.heldK
  have hTsyl := hE.isSylow
  have hT2 := hTsyl.isPGroup
  have hTM := hTsyl.1
  have h1024 := h.card_inf_eq_of_isSylow e₁ hE.isSylow_normalizer
  obtain ⟨t, htT, htK, httK, hr2⟩ :=
    h.eq_or_eq_of_mem hMax hS hHN h64 hMult hTsyl hE.mem hE.not_le
  have hidx := relIndex_eq_two (hTM htT) htK httK hr2
  have hinv : ∀ y ∈ normalizer (W : Set X), orderOf y = 2 → y ∈ normalizer (K : Set X) :=
    fun y hy hy2 => (mem_inf.mp (hb _ inf_le_left hidx y hy hy2)).2
  have hQ : ∀ x ∈ T, x ∈ coreActionKernel K → x ∈ coreActionKernel (conjugate K t) →
      x = 1 := by
    intro x hxT hxK hxKt
    have h1 : x ∈ T ⊓ coreKernel (normalizer (W : Set X)) K :=
      mem_inf.mpr ⟨hxT, mem_coreKernel.mpr fun m hm => by
        rcases hr2 m hm with e | e <;> rw [e] <;> assumption⟩
    rw [hE.inf_coreKernel, mem_bot] at h1
    exact h1
  obtain ⟨u, huT, huK, hu4, hu2, huu⟩ :=
    h.exists_order_four e₁ hT2 hTM h1024 htT htK httK hQ hinv
  have hu4' : u * u * (u * u) = 1 := by
    have h1 := hu4
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two] at h1
    exact h1
  have hrank := h.three_le_pRank_of_sq e₁ h64 hOut hT2 hTM h1024 huT huK huu hu4'
  have huu2 : orderOf (u * u) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu4') hu2
  obtain ⟨A, -, hAe, hA64, hWA⟩ := h.wGroup_eq
  have hTsylA : IsSylowTwoIn T (normalizer (wGroup A : Set X)) := by rw [hWA]; exact hTsyl
  obtain ⟨-, hfus⟩ := sylow_and_fusion_of_threeConnected h.gwTwoBalanced hAe (by omega) hTsylA h3
  have hidx' : ((normalizer (W : Set X) ⊓ normalizer (K : Set X)).subgroupOf
      (normalizer (W : Set X))).index = 2 := hidx
  have hiff : ∀ x ∈ normalizer (W : Set X), ∀ y ∈ normalizer (W : Set X),
      (x * y ∈ normalizer (K : Set X) ↔
        (x ∈ normalizer (K : Set X) ↔ y ∈ normalizer (K : Set X))) := by
    intro x hx y hy
    have h1 := Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    simp only [mem_subgroupOf, Subgroup.coe_mul, mem_inf] at h1
    simpa [hx, hy, mul_mem hx hy] using h1
  have hconj : ∀ m ∈ normalizer (W : Set X), ∀ x ∈ normalizer (W : Set X),
      x ∈ normalizer (K : Set X) → m * x * m⁻¹ ∈ normalizer (K : Set X) := by
    intro m hm x hxM hx
    rw [hiff _ (mul_mem hm hxM) _ (inv_mem hm), hiff _ hm _ hxM]
    have h1 := hiff m hm m⁻¹ (inv_mem hm)
    rw [mul_inv_cancel] at h1
    have h2 := h1.mp (one_mem _)
    exact ⟨fun h3 => h2.mp (h3.mpr hx), fun h3 => ⟨fun _ => hx, fun _ => h2.mpr h3⟩⟩
  have hout : ∀ g ∈ T, g ∉ normalizer (K : Set X) → u⁻¹ * g ∈ normalizer (K : Set X) :=
    fun g hg hgK => (hiff _ (inv_mem (hTM huT)) _ (hTM hg)).mpr
      ⟨fun h1 => absurd (by simpa using inv_mem h1) huK, fun h1 => absurd h1 hgK⟩
  have hTidx : ¬ 2 ∣ T.index := by
    rw [← hP₀]
    exact P₀.not_dvd_index
  have hQn : ∀ g ∈ T, ∀ q ∈ T ⊓ normalizer (K : Set X),
      g * q * g⁻¹ ∈ T ⊓ normalizer (K : Set X) := fun g hg q hq =>
    mem_inf.mpr ⟨mul_mem (mul_mem hg (mem_inf.mp hq).1) (inv_mem hg),
      hconj g (hTM hg) q (hTM (mem_inf.mp hq).1) (mem_inf.mp hq).2⟩
  have hcyc : ∃ b ∈ T, ∀ g ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * g ∈ T ⊓ normalizer (K : Set X) := by
    refine ⟨u, huT, fun g hg => ?_⟩
    by_cases hgK : g ∈ normalizer (K : Set X)
    · exact ⟨0, by simpa using mem_inf.mpr ⟨hg, hgK⟩⟩
    · exact ⟨1, by simpa using mem_inf.mpr ⟨mul_mem (inv_mem huT) hg, hout g hg hgK⟩⟩
  have hb' : ∀ (g : X) (k : ℕ), g⁻¹ * u ^ (2 * k) * g ∈ T →
      g⁻¹ * u ^ (2 * k) * g ∈ T ⊓ normalizer (K : Set X) := by
    intro g k hg
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have h1 : u ^ (2 * (j + j)) = 1 := by
        rw [show 2 * (j + j) = 4 * j by ring, pow_mul, hu4, one_pow]
      rw [h1, mul_one, inv_mul_cancel]
      exact one_mem _
    · have h1 : u ^ (2 * (2 * j + 1)) = u * u := by
        rw [show 2 * (2 * j + 1) = 4 * j + 2 by ring, pow_add, pow_mul, hu4, one_pow, one_mul,
          pow_two]
      rw [h1] at hg ⊢
      refine mem_inf.mpr ⟨hg, hinv _ (hTM hg) ?_⟩
      rw [← huu2]
      exact SemiconjBy.orderOf_eq g (show g * (g⁻¹ * (u * u) * g) = u * u * g by group)
  have hc' : ∀ g : X, g⁻¹ * u * g ∈ T →
      GH74.GLS.Bg.Thompson.IsExtremalIn 2 T (g⁻¹ * u * g) →
        g⁻¹ * u * g ∈ T ⊓ normalizer (K : Set X) ∨
          u⁻¹ * (g⁻¹ * u * g) ∈ T ⊓ normalizer (K : Set X) := by
    intro g hg _
    by_cases h' : g⁻¹ * u * g ∈ normalizer (K : Set X)
    · exact Or.inl (mem_inf.mpr ⟨hg, h'⟩)
    · exact Or.inr (mem_inf.mpr ⟨mul_mem (inv_mem huT) hg, hout _ hg h'⟩)
  rcases GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hT2 hTidx hQn hcyc huT
      (fun h' => huK (mem_inf.mp h').2) hb' hc' with ⟨N, hNn, -, hNp, huN⟩ | ⟨g, hgQ, hgext, -⟩
  ·
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
    · subst hN
      have hX2 : IsPGroup 2 X := hNp.of_equiv QuotientGroup.quotientBot
      have : Group.IsNilpotent X := hX2.isNilpotent
      obtain ⟨x, y, hxy⟩ := h.nonabelian
      exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance x y)
    · exact huN (hN ▸ mem_top u)
  ·
    have hext := isExtremalIn_of_thompson (mem_inf.mp hgQ).1 hgext
    obtain ⟨m, hmA, hm⟩ := hfus (g⁻¹ * u * g) u huT hext ⟨g, rfl⟩ hrank
    rw [hWA] at hmA
    apply huK
    have h1 := hconj m⁻¹ (inv_mem hmA) _ (hTM (mem_inf.mp hgQ).1) (mem_inf.mp hgQ).2
    rwa [inv_inv, ← hm] at h1

end CFSG.ComponentClassification.GrSLit.HeSN
