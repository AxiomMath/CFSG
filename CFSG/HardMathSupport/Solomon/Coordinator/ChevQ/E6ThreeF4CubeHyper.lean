module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeHyperDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeGlue

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

open CFSG.Open TauCeti CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Fold

private def foldWt : Fin Tag.F4.rank → Fin TwistTag.E6.tag.rank → ℤ :=
  (![![1, 2, 2, 3, 2, 1], ![2, 3, 4, 6, 4, 2], ![3, 4, 6, 8, 6, 3], ![2, 2, 3, 4, 3, 2]] :
    Fin 4 → Fin 6 → ℤ)

private theorem foldWt_mul_cartan :
    ∀ (j : Fin Tag.F4.rank) (l : Fin TwistTag.E6.tag.rank),
      ∑ i, foldWt j i * TwistTag.E6.tag.cartan i l = if e6IndexToF4 l = j then 1 else 0 := by
  decide +kernel

private theorem cartanChar_foldWt {k : Type} [Field k] (b : Fin Tag.F4.rank → kˣ) :
    cartanChar (τ := TwistTag.E6.tag) (fun i => ∏ j, b j ^ foldWt j i) =
      fun l : Fin TwistTag.E6.tag.rank => b (e6IndexToF4 l) := by
  funext l
  calc ∏ i, (∏ j, b j ^ foldWt j i) ^ TwistTag.E6.tag.cartan i l
      = ∏ i, ∏ j, b j ^ (foldWt j i * TwistTag.E6.tag.cartan i l) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm
    _ = ∏ j, ∏ i, b j ^ (foldWt j i * TwistTag.E6.tag.cartan i l) := Finset.prod_comm
    _ = ∏ j, b j ^ (if e6IndexToF4 l = j then (1 : ℤ) else 0) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Finset.prod_zpow_eq_zpow_sum, foldWt_mul_cartan]
    _ = b (e6IndexToF4 l) := by
        refine (Finset.prod_eq_single (e6IndexToF4 l) (fun j _ hj => ?_) (fun h => ?_)).trans ?_
        · rw [if_neg (Ne.symm hj), zpow_zero]
        · exact absurd (Finset.mem_univ _) h
        · rw [if_pos rfl, zpow_one]

end Fold

section FoldMem

theorem rootDiagUnit_e6IndexToF4_mem {k : Type} [Field k] (b : Fin Tag.F4.rank → kˣ) :
    rootDiagUnit TwistTag.E6.tag (fun i => b (e6IndexToF4 i)) ∈
      twistedFixedGroup TwistTag.E6 k (RingHom.id k) := by
  rw [mem_twistedFixedGroup_iff_twistHom]
  refine ⟨?_, twistHom_rootDiagUnit fun i => ?_⟩
  · have he : rootDiagUnit TwistTag.E6.tag (fun i => b (e6IndexToF4 i)) =
        ((List.finRange TwistTag.E6.tag.rank).map fun i =>
          torusElt TwistTag.E6.tag k i (∏ j, b j ^ foldWt j i)).prod := by
      rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_foldWt]
    rw [he]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact torusElt_mem_adjointGroup i _
  · exact (congrArg b (e6IndexToF4_rhoE6 i)).trans (Units.ext rfl)

end FoldMem

section Diag

private theorem exists_conj_rootDiagUnit_of_split_datum {K : Type} [Field K] [Finite K]
    {E : Subgroup (adjointGroup Tag.F4 K)} (D : LangPlaneData Tag.F4 K E) (hw : D.w = 1) :
    ∃ k : adjointGroup Tag.F4 K, ∀ x ∈ E, ∃ b : Fin Tag.F4.rank → Kˣ,
      ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) = rootDiagUnit Tag.F4 b := by
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ := D
  subst hw
  rw [CFSG.LieType.Chevalley.canonicalRep_one, mul_one] at hg0
  rw [CFSG.LieType.Chevalley.canonicalRep_one] at hc
  have hbij : Function.Bijective Fr := by
    refine ⟨Fr.injective, fun c => ?_⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.card_pos (α := K))
    exact ⟨z, by rw [hFr z, hz]⟩
  obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.1
    (CFSG.RankThree.Chevalley.mem_map_adjointGroup_of_frobenius_fixed (τ := Tag.F4) (Or.inr rfl)
      Fr hFr hbij hg0C hg0)
  obtain ⟨g', hg'⟩ : ∃ g' : adjointGroup Tag.F4 K, (g' : ModGL Tag.F4 K) = γ := ⟨⟨γ, hγ⟩, rfl⟩
  have hg'B : baseChangeGL (algebraMap K (AlgebraicClosure K)) (g' : ModGL Tag.F4 K) = g0 := by
    rw [hg']
    exact hγg
  obtain ⟨k, hk⟩ : ∃ k : adjointGroup Tag.F4 K, k = g'⁻¹ * c := ⟨_, rfl⟩
  refine ⟨k, fun x hx => ?_⟩
  obtain ⟨t, ht, htb⟩ := Subgroup.mem_map.1 (hc x hx)
  have htb' : g0 * t * g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((c * x * c⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) :=
    htb
  have e : ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
      (g' : ModGL Tag.F4 K)⁻¹ * ((c * x * c⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) *
        (g' : ModGL Tag.F4 K) := by
    rw [hk]
    simp only [mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hyb : baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) = t := by
    rw [e, map_mul, map_mul, map_inv, hg'B, ← htb']
    group
  have ht' := mem_twistedTorusOf.1 ht
  have hT : baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ∈
        torusGroup Tag.F4 (AlgebraicClosure K) := by
    rw [hyb]
    exact ht'.1
  have hF : Units.map (entrywiseHom Fr)
      (baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) := by
    rw [hyb]
    simpa using ht'.2
  exact e8Split_rational_of_torus Tag.F4 Fr hFr hT hF

theorem e6FixedF4EquivAll_symm_rootDiagUnit {k : Type} [Field k] (b : Fin Tag.F4.rank → kˣ)
    (hb : rootDiagUnit Tag.F4 b ∈ adjointGroup Tag.F4 k) :
    (e6FixedF4EquivAll k).symm ⟨_, hb⟩ = ⟨_, rootDiagUnit_e6IndexToF4_mem b⟩ := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [coe_e6FixedF4EquivAll]
  refine Eq.trans ?_ (CFSG.SeitzReduction.F4Pilot.e6FixedToF4_rootDiagUnit
    (a := fun i => b (e6IndexToF4 i)) (fun i => congrArg b (e6IndexToF4_rhoE6 i))
    (rootDiagUnit_e6IndexToF4_mem b)).symm
  exact congrArg (rootDiagUnit Tag.F4)
    (funext fun j => (congrArg b (e6IndexToF4_f4IndexRep j)).symm)

theorem commute_iota_rootDiagUnit_torusWord {k K : Type} [Field k] [Finite k] [Field K]
    [Finite K] [Algebra k K] (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c) (hK : Nat.card K = Nat.card k ^ 2)
    {y : adjointGroup Tag.F4 k} {b : Fin Tag.F4.rank → kˣ}
    (hb : (y : ModGL Tag.F4 k) = rootDiagUnit Tag.F4 b) (t : Kˣ) :
    Commute ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom y)
      (torusWord σ hσ hK t) := by
  have hmem : rootDiagUnit Tag.F4 b ∈ adjointGroup Tag.F4 k := by
    rw [← hb]
    exact y.2
  have hy : y = ⟨_, hmem⟩ := Subtype.ext hb
  have hcoe : (((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom y :
      twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag
        (fun i => Units.map (algebraMap k K).toMonoidHom (b (e6IndexToF4 i))) := by
    rw [hy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_phiG,
      e6FixedF4EquivAll_symm_rootDiagUnit b hmem]
    exact baseChangeGL_rootDiagUnit (algebraMap k K) _
  show _ * _ = _ * _
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe, ExcHighThree.coe_torusWord,
    ← CFSG.LieType.Chevalley.rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
    mul_comm]

end Diag

section Two

theorem e6F4CubeD4Two_of_negHyperplane (h : F4NonToralNegHyperplane) : E6F4CubeD4Two := by
  intro K _ _ hK hs E₀ hE₀F hE₀ hc hN hemp
  have hle : E₀ ≤ (embE6F4 K).range := by
    rw [range_embE6F4_eq K]
    exact hE₀F
  obtain ⟨hmap, hE₃, hc₃, hN₃⟩ := cube_comap_of_le_range (embE6F4_inj K) hle hE₀ hc hN
  obtain ⟨F, hFE, hFi, D, hw⟩ := h K hK (threeScope_F4_of_E6 hs) _ hE₃ hc₃ hN₃ hemp
  obtain ⟨k, hk⟩ := SeitzExcOpenRest5.f4_exists_conj_le_frame_of_neg
    (fun x hx => hE₃.2 x (hFE hx)) D hw
  refine ⟨F.map (embE6F4 K), ?_, ?_, embE6F4 K k, (isoE6F4 K k).2, ?_⟩
  · rw [← hmap]
    exact Subgroup.map_mono hFE
  · rw [← hmap, Subgroup.relIndex_map_map_of_injective _ _ (embE6F4_inj K)]
    exact hFi
  · rintro _ ⟨x, hx, rfl⟩ u
    have hxF : k * x * k⁻¹ ∈ f4FrameGroup K := by
      have h1 := hk ⟨x, hx, rfl⟩
      rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have h2 := commute_anti_of_mem_f4FrameGroup K hxF u
    rwa [map_mul, map_mul, map_inv] at h2

end Two

section One

theorem twE6F4CubeD4One_of_splitHyperplane (h : F4NonToralSplitHyperplane) :
    TwE6F4CubeD4One := by
  intro k K _ _ _ _ _ σ hσ hfix hK hq hs E₀ hle hE₀ hc hN hemp
  set ι : adjointGroup .F4 k →* twistedE6RootGroup K σ :=
    (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom with hιdef
  have hι : Function.Injective ι :=
    (phiG_injective σ hfix).comp (e6FixedF4EquivAll k).symm.injective
  have hle' : E₀ ≤ ι.range := by
    intro x hx
    obtain ⟨y, rfl⟩ := hle hx
    exact ⟨e6FixedF4EquivAll k y, by simp [hιdef]⟩
  obtain ⟨hmap, hE₃, hc₃, hN₃⟩ := cube_comap_of_le_range hι hle' hE₀ hc hN
  rw [← Algebra.ringChar_eq k K] at hN₃
  obtain ⟨F, hFE, hFi, D, hw⟩ :=
    h k hq (threeScope_F4_of_twThreeScope hK hs) _ hE₃ hc₃ hN₃ hemp
  obtain ⟨g, hg⟩ := exists_conj_rootDiagUnit_of_split_datum D hw
  refine ⟨F.map ι, ?_, ?_, ι g, ⟨(e6FixedF4EquivAll k).symm g, rfl⟩, ?_⟩
  · rw [← hmap]
    exact Subgroup.map_mono hFE
  · rw [← hmap, Subgroup.relIndex_map_map_of_injective _ _ hι]
    exact hFi
  · rintro _ ⟨x, hx, rfl⟩ t -
    obtain ⟨b, hb⟩ := hg x hx
    rw [← map_inv ι, ← map_mul ι, ← map_mul ι]
    exact commute_iota_rootDiagUnit_torusWord σ hσ hfix hK hb t

end One

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

end
