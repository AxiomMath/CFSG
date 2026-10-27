module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Ex

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

theorem closure_sup_eq {A B : Subgroup G} {x : G} (hAB : A ≤ B)
    (hc : Nat.card B = 2 * Nat.card A) (hxB : x ∈ B) (hxA : x ∉ A) :
    Subgroup.closure {x} ⊔ A = B := by
  rcases eq_or_eq_of_natCard_eq_two_mul (le_sup_right : A ≤ Subgroup.closure {x} ⊔ A)
    (sup_le ((Subgroup.closure_le B).mpr (by simpa using hxB)) hAB) hc with h | h
  · exact absurd (h ▸ Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_singleton x))) hxA
  · exact h

theorem l6_4ThreeGen :
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaGen Ω →
      ∀ K ∈ Ω, ∀ J ∈ Ω, InA Ω K J → ∀ z j : G, IsUniqueInvolution K z → IsUniqueInvolution J j →
        ∀ X Y : Subgroup G,
          X = (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) →
          Y = pairNormalizers K J z j →
            ∃ u v r t : G, ∃ Kstar : Subgroup G, ∃ ustar rstar : G,
              Subgroup.zpowers u ∈ USet Ω ∧ Subgroup.zpowers u ≤ K ∧
              Subgroup.zpowers v ∈ USet Ω ∧ Subgroup.zpowers v ≤ J ∧
              Commutes (Subgroup.zpowers u) (Subgroup.zpowers v) ∧
              X = oddCoreOf X ⊔ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) ∧
              (Subgroup.closure {r} ⊔ Subgroup.zpowers u) ∈ RSet Ω ∧
              (Subgroup.closure {r} ⊔ Subgroup.zpowers u) ≤
                K ⊓ Subgroup.normalizer ((Subgroup.closure {z, j} : Subgroup G) : Set G) ∧
              (Subgroup.closure {t} ⊔ Subgroup.zpowers v) ∈ RSet Ω ∧
              (Subgroup.closure {t} ⊔ Subgroup.zpowers v) ≤
                J ⊓ Subgroup.normalizer ((Subgroup.closure {z, j} : Subgroup G) : Set G) ∧
              (∃ φ : ↥Y →* DihedralGroup 6, Function.Surjective φ ∧ φ.ker = X.subgroupOf Y) ∧
              Kstar ≠ K ∧ twinSet Ω K = {K, Kstar} ∧ (∃ y ∈ Y, conjSub y J = Kstar) ∧
              Subgroup.zpowers ustar ∈ USet Ω ∧
              (Subgroup.closure {rstar} ⊔ Subgroup.zpowers ustar) ∈ RSet Ω ∧
              (Subgroup.closure {rstar} ⊔ Subgroup.zpowers ustar) ≤ Kstar ⊓ Y ∧
              v * v ∈ K ⊔ Kstar ∧
              Subgroup.zpowers u ⊔ Subgroup.zpowers v =
                Subgroup.zpowers ustar ⊔ Subgroup.zpowers v ∧
              ∀ x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v,
                (r * rstar) * x * (r * rstar)⁻¹ = x⁻¹ := by
  intro G _ _ Ω hΩ K hK J hJ hInA z j hz hj X Y hX hY
  obtain ⟨u, v, R, T, c⟩ := exists_cfg64 hΩ hK hJ hz hj hInA.1 hInA.2.1
  obtain ⟨⟨hXe, -⟩, ⟨-, -, -, hφ⟩, ⟨Kstar, hKs, htw, hy, hvv, ⟨Rstar, hRs, hRsN⟩, hall⟩, -, -⟩ :=
    l6_4ThreeGenAll G Ω hΩ K hK J hJ hInA z j hz hj X Y hX hY u v c.hU c.hUK c.hV c.hVJ c.hUV
      R T c.hR c.hT c.huR c.hvT c.hRN c.hTN
  obtain ⟨r, hr, hru⟩ := c.exists_r
  obtain ⟨t, ht, htv⟩ := c.symm.exists_r
  obtain ⟨hRsY, ⟨ustar, hus, husU, hUVeq⟩, hinv⟩ := hall Rstar hRs hRsN
  have hKsΩ : Kstar ∈ Ω := by
    have : Kstar ∈ twinSet Ω K := by
      rw [htw]
      exact Or.inr rfl
    exact this.1
  have hUsR : Subgroup.zpowers ustar ≤ Rstar := by
    rw [hus]
    exact inf_le_left
  have hRscard : Nat.card Rstar = 2 * Nat.card (Subgroup.zpowers ustar) := by
    obtain ⟨R₁, -, J₁, hJ₁, hR₁J₁, hUR₁, -, hR₁card, -⟩ := exists_data_of_mem_USet hΩ husU
    have e : J₁ = Kstar :=
      eq_of_mem_USet hΩ husU hJ₁ hKsΩ (hUR₁.trans hR₁J₁.1) (hUsR.trans hRs.1)
    subst e
    rw [← hR₁card]
    exact hRs.natCard_eq hR₁J₁
  obtain ⟨rstar, hrstar, hrstarj⟩ :
      ∃ rs ∈ Rstar, rs ∉ Subgroup.centralizer ({j} : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : Rstar ≤ Subgroup.zpowers ustar := by
      rw [hus]
      exact le_inf le_rfl hcon
    have := Subgroup.card_le_of_le hle
    have h0 : 0 < Nat.card (Subgroup.zpowers ustar) := Nat.card_pos
    omega
  obtain ⟨hinv', -⟩ := hinv r hr hru rstar hrstar hrstarj
  have hR' := closure_sup_eq c.huR c.natCard_R hr hru
  have hT' := closure_sup_eq c.hvT c.symm.natCard_R ht htv
  have hRs' := closure_sup_eq hUsR hRscard hrstar (fun h => hrstarj (by rw [hus] at h; exact h.2))
  refine ⟨u, v, r, t, Kstar, ustar, rstar, c.hU, c.hUK, c.hV, c.hVJ, c.hUV, hXe, ?_, ?_, ?_, ?_,
    hφ, hKs, htw, hy, husU, ?_, ?_, hvv, hUVeq, hinv'⟩
  · rw [hR']
    exact mem_RSet_of_isSylow2In hK c.hR
  · rw [hR']
    exact le_inf c.hR.1 c.R_le_normalizer_Z
  · rw [hT']
    exact mem_RSet_of_isSylow2In hJ c.hT
  · rw [hT']
    have := c.symm.R_le_normalizer_Z
    rw [Set.pair_comm] at this
    exact le_inf c.hT.1 this
  · rw [hRs']
    exact mem_RSet_of_isSylow2In hKsΩ hRs
  · rw [hRs']
    exact le_inf hRs.1 hRsY

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
