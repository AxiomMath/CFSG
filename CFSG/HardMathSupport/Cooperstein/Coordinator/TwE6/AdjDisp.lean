module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.AdjDispIso
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.AdjDispRank
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.AdjDisp
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SylowGlue

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc TensorProduct


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem twAdj_rank_ge (g : ↥(graphFixedRootGroup TwistTag.E6 K σ)) (hg1 : g ≠ 1) (hg2 : g ^ 2 = 1) :
    22 ≤ Module.finrank K (LinearMap.range (twAdj σ g - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : graphFixedRootGroup TwistTag.E6 K σ ≤ adjointGroup TwistTag.E6.tag K :=
    (graphFixedRootGroup_le TwistTag.E6 K σ).trans inf_le_left
  let g' : ↥(adjointGroup TwistTag.E6.tag K) := ⟨g.1, hle g.2⟩
  have hg'2 : g' ^ 2 = 1 := Subtype.ext (by
    have := congrArg Subtype.val hg2
    simpa using this)
  have hA : IsPGroup 2 (Subgroup.zpowers g') := by
    intro x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : g' ^ ((2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact hg'2
    rw [this, one_zpow]
  obtain ⟨h, hh⟩ := FFExc.adjoint_conj_into_U K TwistTag.E6.tag (Subgroup.zpowers g') hA
  have hmem : h * g' * h⁻¹ ∈ FFExc.Uad K TwistTag.E6.tag :=
    hh ⟨g', Subgroup.mem_zpowers g', by simp [MulAut.conj_apply]⟩
  have hne : h * g' * h⁻¹ ≠ 1 := by
    intro h1
    apply hg1
    have h2 : g' = 1 := by
      have e : g' = h⁻¹ * (h * g' * h⁻¹) * h := by group
      rw [e, h1]
      group
    refine Subtype.ext ?_
    have h3 := congrArg Subtype.val h2
    exact h3
  have hdisp := FFExc.displacement_E6 K (u := ((h * g' * h⁻¹ : ↥(adjointGroup TwistTag.E6.tag K)) :
    ModGL TwistTag.E6.tag K)) (Subgroup.mem_subgroupOf.1 hmem) (fun h1 => hne (Subtype.ext h1))
  set W : Module.End K (RootModule TwistTag.E6.tag K) := (((h : ↥(adjointGroup TwistTag.E6.tag K)) :
    ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) with hWdef
  set Wi : Module.End K (RootModule TwistTag.E6.tag K) := (((h⁻¹ : ↥(adjointGroup TwistTag.E6.tag K)) :
    ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) with hWidef
  have hW1 : W * Wi = 1 :=
    Units.mul_inv ((h : ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K)
  have hW2 : Wi * W = 1 :=
    Units.inv_mul ((h : ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K)
  have hX : ((((h * g' * h⁻¹ : ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) :
      Module.End K (RootModule TwistTag.E6.tag K))) - 1 =
      (1 : K) • (W * (twAdj σ g - 1) * Wi) := by
    rw [one_smul, mul_sub, sub_mul, mul_one, hW1]
    congr 1
  have := FFExc.finrank_range_conj W Wi (twAdj σ g - 1) hW1 hW2 1 one_ne_zero
  rw [← hX] at this
  rw [← this]
  exact hdisp

include hf hK hσ in
theorem twE6AdjDisplacement_holds : TwE6AdjDisplacement hf K hK σ hσ := by
  intro k _ _ _ _ m ρ y χ J hρ ht h78 u hu1 hu2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, β, hβ⟩ := twE6_iso_78 hf hK σ hσ hρ ht h78
  have hpu1 : coverHom hf hK σ hσ u ≠ 1 := by
    intro h1
    apply hu1
    exact (isCentralCover_coverHom hf hK σ hσ).eq_one_of_isPElt (MonoidHom.mem_ker.2 h1)
      ⟨1, by rw [pow_one]; exact hu2⟩
  have hpu2 : (coverHom hf hK σ hσ u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hr := twAdj_rank_ge hf hK σ hσ _ hpu1 hpu2
  have hbc := finrank_range_le_bc (k := k) (twAdj σ (coverHom hf hK σ hσ u) - 1)
  have hMhat : (((bcRep k (twAdj σ)).comp (coverHom hf hK σ hσ)) u - 1 :
      Module.End k (k ⊗[K] RootModule TwistTag.E6.tag K)) =
      (twAdj σ (coverHom hf hK σ hσ u) - 1).baseChange k := by
    show (twAdj σ (coverHom hf hK σ hσ u)).baseChange k - 1 = _
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_one]
  have hrange : LinearMap.range (twistRep (frobAut k b) ρ u - 1) =
      (LinearMap.range (((bcRep k (twAdj σ)).comp (coverHom hf hK σ hσ)) u - 1)).map
        β.toLinearMap := by
    ext w
    constructor
    · rintro ⟨v', rfl⟩
      obtain ⟨v₀, rfl⟩ := β.surjective v'
      refine ⟨_, ⟨v₀, rfl⟩, ?_⟩
      show β (((bcRep k (twAdj σ)).comp (coverHom hf hK σ hσ)) u v₀ - v₀) = _
      rw [map_sub, hβ u v₀]
      rfl
    · rintro ⟨_, ⟨v₀, rfl⟩, rfl⟩
      refine ⟨β v₀, ?_⟩
      show twistRep (frobAut k b) ρ u (β v₀) - β v₀ = _
      rw [← hβ u v₀, ← map_sub]
      rfl
  have h1 := LinearEquiv.finrank_map_eq β
    (LinearMap.range (((bcRep k (twAdj σ)).comp (coverHom hf hK σ hσ)) u - 1))
  have h2 := finrank_range_twist (frobAut k b) ρ u
  rw [hrange] at h2
  have h4 : Module.finrank k (LinearMap.range (((bcRep k (twAdj σ)).comp (coverHom hf hK σ hσ)) u - 1)) =
      Module.finrank k (LinearMap.range ((twAdj σ (coverHom hf hK σ hσ u) - 1).baseChange k)) := by
    rw [hMhat]
  omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
