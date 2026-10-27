module

public import CFSG.ClassicalInvolution.Asc77.AscT7FI
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer

section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.rLayer_tz_le_sigmaGen_of_eq (h : Hyp21 p f Ω K K' z u J t W) (hC3 : C21_3 p f)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) (heq : dComp Ω K = dstarComp Ω K) :
    rLayer Ω (t * z) ≤ sigmaGen Ω K := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hMF : DStarConnectedTwinGen p f :=
    dstarConnectedTwinGen_of smallNoThree G2D4Models.ih8G2D4_unconditional ih8D4Star hp hq
  have h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n :=
    G2D4Models.h3s_of_nonToral_free G2D4Models.g2NonToralGenerate_all
  have hcA : IsPGroup 2 (Subgroup.zpowers (t * z)) := isPGroup_zpowers_of_sq_eq_one h.tz_sq
  refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
  obtain ⟨J₁, hJ₁Ω, hRJ₁⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJ₁t : J₁ ∈ tqMembers Ω (t * z) :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hJ₁Ω, R, hRJ₁, hRc⟩
  have hJ₁d : J₁ ∈ dComp Ω K := by
    rw [heq]
    exact tqMembers_subset_dstarComp_gen h hMF h3s hC3 hα J₁ hJ₁t
  exact hRJ₁.1.trans (le_iSup₂_of_le J₁ hJ₁d le_rfl)

end Frame

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_NormCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({t * z} : Set G)

variable {p f}

theorem c21_15_of_normCent (hC3 : C21_3 p f) (hN : C21_NormCent p f) : C21_15 p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD M hM
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hne : dComp Ω K ≠ dstarComp Ω K := fun heq =>
    hD (h.rLayer_tz_le_sigmaGen_of_eq hC3 hα heq)
  have hNK := hN G Ω K K' z u J t W h hα hD
  have hMW : MGrp Ω W ≤ Subgroup.centralizer ({t * z} : Set G) :=
    (h.mGrp_le_rLayer_tz hne).trans (rLayer_le_centralizer Ω (t * z))
  have hMd : M ∈ dstarComp Ω K := T7A.mem_dstarComp_of_mem_dComp hp hΩ hM
  obtain ⟨x, hx, rfl⟩ := h.exists_mem_conj_of_dstarComp hne hMW hNK M hMd
  have hKc : K ≤ Subgroup.centralizer ({t * z} : Set G) := le_trans Subgroup.le_normalizer hNK
  intro y hy
  rw [mem_conjSub_iff] at hy
  have hy' := hKc hy
  have hyx : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
  rw [hyx]
  exact (Subgroup.centralizer ({t * z} : Set G)).mul_mem
    ((Subgroup.centralizer ({t * z} : Set G)).mul_mem hx hy')
    ((Subgroup.centralizer ({t * z} : Set G)).inv_mem hx)

theorem c21_normCent_of_c21_15 (hC3 : C21_3 p f) (h15 : C21_15 p f) : C21_NormCent p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD
  have hne : dComp Ω K ≠ dstarComp Ω K := fun heq =>
    hD (h.rLayer_tz_le_sigmaGen_of_eq hC3 hα heq)
  exact h.normalizer_le_centralizer_tz hne (h15 G Ω K K' z u J t W h hα hD)

end CFSG.ClassicalInvolution.Asc77
