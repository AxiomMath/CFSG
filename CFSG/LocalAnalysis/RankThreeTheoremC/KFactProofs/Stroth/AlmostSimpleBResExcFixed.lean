module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResIndepPair
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResPairDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

section


theorem exists_fixed_embedding {τ : Tag} {K : Type} [Field K] (σ : K ≃+* K) :
    ∃ ι : adjointGroup τ (fixSubfield σ) →* adjointGroup τ K, Function.Injective ι ∧
      ∀ y, entrywiseAdjointAut τ σ (ι y) = ι y := by
  let jk : adjointGroup τ (fixSubfield σ) →* ModGL τ K :=
    (fixedFieldImage τ σ).subtype.comp (fixedFieldImageEquiv σ).toMonoidHom
  have hmem : ∀ y, jk y ∈ entrywiseFixedGroup τ σ := fun y =>
    fixedFieldImage_le (fixedFieldImageEquiv σ y).2
  let ι : adjointGroup τ (fixSubfield σ) →* adjointGroup τ K :=
    jk.codRestrict (adjointGroup τ K) (fun y => (hmem y).1)
  refine ⟨ι, ?_, ?_⟩
  · intro a b h
    have h' : ((ι a : adjointGroup τ K) : ModGL τ K) = ((ι b : adjointGroup τ K) : ModGL τ K) :=
      congrArg Subtype.val h
    exact (fixedFieldImageEquiv σ).injective (Subtype.ext h')
  · intro y
    apply Subtype.ext
    rw [coe_entrywiseAdjointAut]
    exact (hmem y).2

theorem fixesPair_of_entrywise_conj {τ : Tag} {K : Type} [Field K] {p : ℕ} (σ : K ≃+* K)
    {α ψ : MulAut (adjointGroup τ K)} {r j : ℕ} (hαr : (α ^ r) ^ j = α)
    (hψ : ψ * α ^ r * ψ⁻¹ = entrywiseAdjointAut τ σ)
    (hpair : HasIndepPair p (adjointGroup τ (fixSubfield σ))) : FixesIndepPair p α := by
  obtain ⟨ι, hι, hfix⟩ := exists_fixed_embedding (τ := τ) σ
  obtain ⟨y₁, y₂, hc, h1, h2, hi⟩ := hpair
  let φ : adjointGroup τ (fixSubfield σ) →* adjointGroup τ K :=
    (ψ⁻¹ : MulAut (adjointGroup τ K)).toMonoidHom.comp ι
  have hφ : Function.Injective φ := (ψ⁻¹ : MulAut (adjointGroup τ K)).injective.comp hι
  have hz : ∀ y, α (φ y) = φ y := by
    intro y
    have e1 : (ψ * α ^ r * ψ⁻¹) (ι y) = ι y := by rw [hψ]; exact hfix y
    have e2 : (α ^ r) (ψ⁻¹ (ι y)) = ψ⁻¹ (ι y) := by
      have := congrArg (ψ⁻¹ : MulAut (adjointGroup τ K)) e1
      simpa [MulAut.mul_apply] using this
    have e3 : ∀ n : ℕ, ((α ^ r) ^ n) (ψ⁻¹ (ι y)) = ψ⁻¹ (ι y) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, MulAut.mul_apply, e2, ih]
    change α (ψ⁻¹ (ι y)) = ψ⁻¹ (ι y)
    rw [← hαr]
    exact e3 j
  refine ⟨φ y₁, φ y₂, hc.map φ, ?_, ?_, fun i j hij => ?_, hz y₁, hz y₂⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · rw [← map_zpow, ← map_zpow, ← map_mul] at hij
    exact hi i j (hφ (hij.trans (map_one φ).symm))

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
