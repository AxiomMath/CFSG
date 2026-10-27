module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA
open CFSG.Blueprint.Chevalley CFSG.LinearGroups CFSG.SeitzReduction
  CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.LieType.Chevalley

variable {f p : ℕ} {K : Type} [Field K] [Finite K]

@[expose] noncomputable def QLevi {σ : K →+* K} (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  (Qbar h p hp hp2 ζ hζ hζbar).map
    ((su6Levi σ).subtype.comp (su6LeviEquiv h hσ).toMonoidHom)

theorem QLevi_le_su6Levi {σ : K →+* K} (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    QLevi h p hp hp2 ζ hζ hζbar hσ ≤ su6Levi σ := by
  rw [QLevi]
  rintro _ ⟨x, -, rfl⟩
  exact Subtype.coe_prop _

private theorem QLevi_subgroupOf_eq {σ : K →+* K} (h : UnitaryFieldData 2 f K) (p : ℕ)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    (QLevi h p hp hp2 ζ hζ hζbar hσ).subgroupOf (su6Levi σ) =
      (Qbar h p hp hp2 ζ hζ hζbar).map (su6LeviEquiv h hσ).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_subgroupOf, QLevi, Subgroup.mem_map, MonoidHom.comp_apply,
    Subgroup.coe_subtype]
  exact ⟨fun ⟨q, hq, hqx⟩ => ⟨q, hq, Subtype.ext hqx⟩,
    fun ⟨q, hq, hqx⟩ => ⟨q, hq, by rw [hqx]⟩⟩

theorem isQuasisimple_QLevi {σ : K →+* K} (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    IsQuasisimple ↥((QLevi h p hp hp2 ζ hζ hζbar hσ).subgroupOf (su6Levi σ)) := by
  rw [QLevi_subgroupOf_eq h p hp hp2 ζ hζ hζbar hσ]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Qbar h p hp hp2 ζ hζ hζbar).equivMapOfInjective
      (su6LeviEquiv h hσ).toMonoidHom (su6LeviEquiv h hσ).injective)
    (isQuasisimple_Qbar h p hp hp2 ζ hζ hζbar)

theorem dvd_card_QLevi {σ : K →+* K} (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    p ∣ Nat.card ↥((QLevi h p hp hp2 ζ hζ hζbar hσ).subgroupOf (su6Levi σ)) := by
  rw [QLevi_subgroupOf_eq h p hp hp2 ζ hζ hζbar hσ,
    ← Nat.card_congr ((Qbar h p hp hp2 ζ hζ hζbar).equivMapOfInjective
      (su6LeviEquiv h hσ).toMonoidHom (su6LeviEquiv h hσ).injective).toEquiv]
  exact dvd_card_Qbar h p hp hp2 ζ hζ hζbar

theorem QLevi_le_centralizer_zLevi {σ : K →+* K} (h : UnitaryFieldData 2 f K) (p : ℕ)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    QLevi h p hp hp2 ζ hζ hζbar hσ ≤
      Subgroup.centralizer ({zLevi h p hp hp2 ζ hζ hζbar hσ} : Set (ModGL TwistTag.E6.tag K)) := by
  rintro _ ⟨q, hq, rfl⟩
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp
    (Qbar_le_centralizer_zbar h p hp hp2 ζ hζ hζbar hq)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h' : (su6LeviEquiv h hσ) q * (su6LeviEquiv h hσ) (zbar h p ζ hζ hζbar) =
      (su6LeviEquiv h hσ) (zbar h p ζ hζ hζbar) * (su6LeviEquiv h hσ) q := by
    rw [← map_mul, ← map_mul, hcomm]
  have h'' := congrArg (fun x : ↥(su6Levi σ) => (x : ModGL TwistTag.E6.tag K)) h'
  simpa [zLevi] using h''

theorem QLevi_conj_mem {σ : K →+* K} (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {g q : ModGL TwistTag.E6.tag K} (hgD : g ∈ su6Levi σ)
    (hgz : g ∈ Subgroup.centralizer ({zLevi h p hp hp2 ζ hζ hζbar hσ} :
      Set (ModGL TwistTag.E6.tag K)))
    (hq : q ∈ QLevi h p hp hp2 ζ hζ hζbar hσ) :
    g * q * g⁻¹ ∈ QLevi h p hp hp2 ζ hζ hζbar hσ := by
  obtain ⟨g', rfl⟩ : ∃ g' : ↥(su6Levi σ), (g' : ModGL TwistTag.E6.tag K) = g := ⟨⟨g, hgD⟩, rfl⟩
  obtain ⟨q', hq', rfl⟩ := hq
  set g₁ : primeFormP h (C6 K) := (su6LeviEquiv h hσ).symm g' with hg₁
  have hg₁g : ((su6LeviEquiv h hσ).toMonoidHom g₁ : ModGL TwistTag.E6.tag K) =
      (g' : ModGL TwistTag.E6.tag K) := by simp [hg₁]
  have hgz' : g₁ ∈ Subgroup.centralizer
      ({zbar h p ζ hζ hζbar} : Set (primeFormP h (C6 K))) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hgz ⊢
    apply (su6LeviEquiv h hσ).injective
    show (su6LeviEquiv h hσ) (g₁ * zbar h p ζ hζ hζbar) =
      (su6LeviEquiv h hσ) (zbar h p ζ hζ hζbar * g₁)
    rw [map_mul, map_mul]
    have h'' : ((su6LeviEquiv h hσ).toMonoidHom g₁ : ModGL TwistTag.E6.tag K) *
        zLevi h p hp hp2 ζ hζ hζbar hσ =
        zLevi h p hp hp2 ζ hζ hζbar hσ *
          ((su6LeviEquiv h hσ).toMonoidHom g₁ : ModGL TwistTag.E6.tag K) := by
      rw [hg₁g]
      exact hgz
    exact Subtype.ext h''
  refine ⟨g₁ * q' * g₁⁻¹, Qbar_conj_mem h p hp hp2 ζ hζ hζbar hgz' hq', ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_inv, map_mul, map_inv,
    hg₁g]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
