module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY3Uniq
public import CFSG.ClassicalInvolution.Q3.Q3AM710Cls

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups commutatorElement

section Ten


variable {G : Type} [Group G] [Finite G]

theorem partnerUniq_of_thinY [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (h : Q3T8.Asc77.BadStd8 Ω K J S R T W z t) (hint : IsIntrinsicU (.sl2 3 1) K z)
    (hthin : ThinY Ω K z) {W₁ : Subgroup G} (hW : W₁ ∈ WSet Ω) :
    Q3AM710.PartnerUniq Ω W₁ := by
  intro ρ σ σ' hσ hσ'
  have hstd := h.std
  have hΩG : HypOmegaGen Ω := hstd.stand.hyp
  have hc : ConjInvariant Ω := hΩG.conjInvariant
  have hK : K ∈ Ω := hstd.stand.mem
  have hz : IsUniqueInvolution K z := hstd.hz
  obtain ⟨g, hg⟩ := hstd.stand.trans ρ.K ρ.hK
  have hW₀ : conjSub g⁻¹ W₁ ∈ WSet Ω := WSet.conj hc hW g⁻¹
  have hU : ∀ τ : Rep Ω W₁, conjSub g⁻¹ τ.K ⊓ conjSub g⁻¹ W₁ ∈ USet Ω := by
    intro τ
    have h' := USet.conj hc (Q3CL.Thompson.inf_W_of_mem_D hΩG hW τ.hR τ.hK τ.hRK).2.1 g⁻¹
    have e : conjSub g⁻¹ (τ.K ⊓ W₁) = conjSub g⁻¹ τ.K ⊓ conjSub g⁻¹ W₁ :=
      Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective
    rwa [e] at h'
  have hX : ∀ τ : Rep Ω W₁, τ.K ∈ omegaNbr Ω ρ.K → conjSub g⁻¹ τ.K ∈ omegaNbr Ω K := by
    intro τ hτ
    have h1 := omegaNbr_conj hc hτ g⁻¹
    rwa [← hg, conjSub_inv_conjSub] at h1
  have hzW : z ∈ conjSub g⁻¹ W₁ := by
    have hUρ := hU ρ
    rw [show conjSub g⁻¹ ρ.K = K by rw [← hg, conjSub_inv_conjSub]] at hUρ
    obtain ⟨u, hu, huW⟩ := exists_involution_mem_of_inf_mem_USet hΩG hK hUρ
    have huz : u = z := (hz.unique u hu.mem hu.sq).resolve_left hu.ne_one
    exact huz ▸ huW
  have key := uniq_of_thinY h hint hthin hW₀ hzW (hX σ hσ) (hX σ' hσ') (hU σ) (hU σ')
  exact (conjSub_inj g⁻¹).mp key

theorem c28_7_10Y_proved : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (Ω : Set (Subgroup G)) (K J : Subgroup G) (S : Sylow 2 G) (R T W : Subgroup G) (z t : G),
    Q3T8.Asc77.BadStd8 Ω K J S R T W z t → IsIntrinsicU (.sl2 3 1) K z →
      NoTriangleAtEdge Ω K J → ThinY Ω K z → MuIsoE4 Ω W ∨ MuIsoS4 Ω W := by
  intro G _ _ _ Ω K J S R T W z t h hint hN hthin
  have hs := h.std
  have hΩG : HypOmegaGen Ω := hs.stand.hyp
  have hW : W ∈ WSet Ω := hs.hW.1
  have hP : Q3CL.PartIHypG Ω := ⟨hs.stand.hyp, hs.stand.cls, hs.stand.aEmpty⟩
  have hU : Q3AM710.PartnerUniq Ω W := partnerUniq_of_thinY h hint hthin hW
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ x ∈ (S : Subgroup G), x ∈ Subgroup.normalizer (W : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 x hx)
  have hRD : R ∈ DSet Ω W := ⟨hs.hR.1, fun x hx => hSN x (hs.hR.2.2 hx)⟩
  have hTD : T ∈ DSet Ω W := ⟨hs.hT.1, fun x hx => hSN x (hs.hT.2.2 hx)⟩
  have hRsyl : IsSylow2In R K :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩG hK hs.hR.1 hs.hR.2.1
  have hTsyl : IsSylow2In T J :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩG hJΩ hs.hT.1 hs.hT.2.1
  obtain ⟨r₀, hr₀R, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩG hW hRD
  obtain ⟨t₀, ht₀T, ht₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩG hW hTD
  let ρ : Rep Ω W := ⟨K, R, r₀, hK, hRD, hRsyl, hr₀R, hr₀W⟩
  let σ : Rep Ω W := ⟨J, T, t₀, hJΩ, hTD, hTsyl, ht₀T, ht₀W⟩
  exact Q3AM710.muIso_E4_or_S4 hP hW hU ρ σ hs.hJ

end Ten

end CFSG.ClassicalInvolution.Q3.Q3AM
