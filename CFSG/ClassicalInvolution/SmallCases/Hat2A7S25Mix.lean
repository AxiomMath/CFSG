module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25F1
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25MixQ
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25MixL

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected

section Mix


theorem natCard_sylow_eq_sixteen {G : Type} [Group G] [Finite G] {J R : Subgroup G}
    (hw : A7Witness J) (hR : IsSylow2In R J) : Nat.card R = 16 := by
  obtain ⟨π, zE, hcov, -⟩ := Hat2A7.exists_cover_of_witness hw
  rw [Uniform.natCard_isSylow2In_eq hR]
  have h5040 : Nat.card (↥J ⧸ classicalInvolutionOddCore ↥J) = 5040 := hcov.card_E
  rw [h5040]
  have h4 : (Nat.factorization 5040) 2 = 4 := by decide +kernel
  rw [h4]
  norm_num

theorem a7Mix25_proved : A7Mix25 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ h a haS ha2 hF'
  have hΩ : AschTight.HypOmegaGen Ω := h.hΩ
  have hK : K ∈ Ω := h.hK
  have haR' : conjSub a R' = R' := mem_normalizer_iff_conjSub_eq.mp hF'.1
  have haR : conjSub a R = R := by
    rcases h.conj_R haS with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd (h2.symm.trans haR') h.ne
  have hRa : ∀ r ∈ R, a * r * a⁻¹ ∈ R := fun r hr => by
    have := conj_mem_conjSub (n := a) hr
    rwa [haR] at this
  have hw : A7Witness K := by
    obtain ⟨u, hu⟩ := h.std.1.stand.classical K hK
    exact hu.witness
  have h16 : Nat.card R = 16 := natCard_sylow_eq_sixteen hw h.hRsyl
  have hRle : R ≤ conjSub a K := by
    intro r hr
    have hr' : r ∈ conjSub a R := by rw [haR]; exact hr
    exact mem_conjSub_iff.mpr (h.hRsyl.1 (mem_conjSub_iff.mp hr'))
  have hnormK : conjSub a K = K :=
    (AschTight.Sec6Gen.eq_of_le_of_le hΩ hK (hΩ.conjInvariant a K hK) h.hRsyl.2.1 (by omega)
      h.hRsyl.1 hRle).symm
  have haN : a ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hnormK
  have hfix := Hat2A7.four_le_card_inf_centralizer hw h.hRsyl haN ha2 hRa
  have hRq : IsQuatSub R := AschTight.Sec6Gen.isQuatSub_of_mem_RSet hΩ h.hR.1
  have hzR : IsUniqueInvolution R z :=
    ⟨h.hzR, h.std.1.hz.ne_one, h.std.1.hz.sq, fun y hy hy2 =>
      h.std.1.hz.unique y (h.hRsyl.1 hy) hy2⟩
  set V : Subgroup G := (S : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) with hV
  have hV2 : IsPGroup 2 ↥V := S.isPGroup'.to_le inf_le_left
  have hRV : R ≤ V := le_inf h.hR.2.2 Subgroup.le_normalizer
  have hVR : ∀ y ∈ V, conjSub y R = R := fun y hy => mem_normalizer_iff_conjSub_eq.mp hy.2
  have haV : a ∈ V := ⟨haS, mem_normalizer_iff_conjSub_eq.mpr haR⟩
  exact mix_of_card_ge_four hRq hzR h16 hRV hV2 hVR haV ha2 hfix

end Mix

end CFSG.ClassicalInvolution.Hat2A7S
