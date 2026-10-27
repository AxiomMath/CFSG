module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularInputs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTorus
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Sporadic.Suz.Simple

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg

section Pure

theorem twE6_rootChar_eq_one_iff_triPairing
    {τ : Tag} {L : Type}
    [Field L] {ω : Lˣ}
    (hω : IsPrimitiveRoot ω 3) {a : Fin τ.rank → Lˣ} {k : Fin τ.rank → ℕ}
    (hak : ∀ i, a i = ω ^ k i) (v : Fin τ.rank → ℤ) :
    rootChar a v = 1 ↔ triPairing (fun i => ((k i : ℕ) : ZMod 3)) v = 0 := by
  have h1 : rootChar a v = ω ^ (∑ i, v i * (k i : ℤ)) := by
    rw [rootChar, ← prod_zpow_eq_zpow_sum_of_group]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hak i, ← zpow_natCast, ← zpow_mul, mul_comm]
  have h2 : rootChar a v = 1 ↔ (3 : ℤ) ∣ ∑ i, v i * (k i : ℤ) := by
    rw [h1]
    have := hω.zpow_eq_one_iff_dvd (∑ i, v i * (k i : ℤ))
    simpa using this
  rw [h2]
  have : triPairing (fun i => ((k i : ℕ) : ZMod 3)) v = ((∑ i, v i * (k i : ℤ) : ℤ) : ZMod 3) := by
    simp only [triPairing]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).symm

end Pure

section Twisted

theorem TwLangData.kills_of_generators {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (D : TwLangData K σ q A) {x₁ x₂ : ModGL TwistTag.E6.tag K}
    (hgen : Subgroup.closure ({x₁, x₂} : Set (ModGL TwistTag.E6.tag K)) = A)
    {a₁ a₂ : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (ha₁ : rootDiagUnit TwistTag.E6.tag a₁ = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x₁ * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0)
    (ha₂ : rootDiagUnit TwistTag.E6.tag a₂ = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x₂ * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hr₁ : rootChar a₁ α = 1) (hr₂ : rootChar a₂ α = 1) :
    D.Kills α := by
  set Sg : Subgroup (ModGL TwistTag.E6.tag K) :=
    ((rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α).ker.map
      (rootDiagUnitHom Tag.E6 (AlgebraicClosure K))).comap (diagG D.g0 D.c) with hSg
  have hker : ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ, rootChar a α = 1 →
      a ∈ (rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α).ker :=
    fun a h => MonoidHom.mem_ker.2
      (show rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α a = 1 from h)
  have hmem : ∀ (x : ModGL TwistTag.E6.tag K) (a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ),
      rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 → rootChar a α = 1 → x ∈ Sg := by
    intro x a hax hr
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨a, hker a hr, ?_⟩)
    exact hax.trans (diagG_apply D.g0 D.c x).symm
  have hx₁S : x₁ ∈ Sg := hmem x₁ a₁ ha₁ hr₁
  have hx₂S : x₂ ∈ Sg := hmem x₂ a₂ ha₂ hr₂
  have hAS : A ≤ Sg := by
    rw [← hgen]
    refine (Subgroup.closure_le Sg).2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact hx₁S
    · exact hx₂S
  intro y hy
  obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hAS hy))
  refine ⟨a, ?_, ?_⟩
  · exact hay.trans (diagG_apply D.g0 D.c y)
  · exact (show rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α a = 1 from
      MonoidHom.mem_ker.1 ha)

end Twisted

end CFSG.LieType.SeitzGeneration.ExcWideThree
