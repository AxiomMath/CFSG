module

public import CFSG.HardMathSupport.Lang.E27Lie.TrialityThreeLayers
public import CFSG.HardMathSupport.Lang.Triality.TraceKernel
public import CFSG.HardMathSupport.Lang.Triality.Char3Sylow
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
public import CFSG.RankThree.PartOne.KGD.D4T36Core
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerRoots
public import CFSG.HardMathSupport.Lang.Triality.G2ClassOrder
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


section Aux

variable {K : Type} [Field K] [Finite K]

private theorem eq_one_of_coord_eq_zero {t : TwistTag} {α : Fin t.tag.rank → ℤ}
    (hα : IsRoot t.tag α ∧ 0 < height α) {g : ModGL t.tag K}
    (hg : g ∈ rootSpan t.tag K (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)))
    (h0 : ∀ β (_ : β ∈ t.diagramOrbit α) (hβ' : IsRoot t.tag β ∧ 0 < height β),
      rootCoord hβ' g = 0) : g = 1 := by
  classical
  have hroot : ∀ β ∈ t.diagramOrbit α, IsRoot t.tag β ∧ 0 < height β := fun β hβ =>
    ⟨t.isRoot_of_mem_diagramOrbit hα.1 hβ, by rw [t.height_of_mem_diagramOrbit hβ]; exact hα.2⟩
  have hclosed : ∀ β ∈ (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)),
      ∀ γ ∈ (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)), ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot t.tag (a • β + b • γ) →
          a • β + b • γ ∈ (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)) :=
    fun β hβ γ hγ a b ha hb hr =>
      absurd hr (t.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit hα.1 hβ hγ ha hb)
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq K
    (S := (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ))) (fun β hβ => hroot β hβ) hclosed
    (l := (t.diagramOrbit α).toList) (Finset.nodup_toList _) (fun β => by simp) hg
  have hcz : ∀ β ∈ t.diagramOrbit α, c β = 0 := by
    intro β hβ
    have hβ' := hroot β hβ
    have h1 := h0 β hβ hβ'
    have hL : ∀ x ∈ (t.diagramOrbit α).toList.map (fun γ => pinnedX t.tag K γ (c γ)),
        x ∈ heightSeries t.tag K (height β) := by
      intro x hx
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
      have hγ' := Finset.mem_toList.1 hγ
      have := pinnedX_mem_heightSeries_height (hroot γ hγ') (c γ)
      rwa [t.height_of_mem_diagramOrbit hγ', ← t.height_of_mem_diagramOrbit hβ] at this
    rw [← hc, rootCoord_list_prod hβ' _ hL, List.map_map, Finset.sum_map_toList,
      Finset.sum_eq_single β (fun γ hγ hne => ?_) (fun h => absurd hβ h)] at h1
    · simpa [Function.comp_def, rootCoord_self hβ'] using h1
    · simp only [Function.comp_apply]
      exact rootCoord_pinnedX_of_ne hβ' (hroot γ hγ)
        (le_of_eq (by rw [t.height_of_mem_diagramOrbit hγ, t.height_of_mem_diagramOrbit hβ])) hne
        (c γ)
  rw [← hc]
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
  rw [hcz γ (Finset.mem_toList.1 hγ), pinnedX_zero]

private theorem isRoot_pos_of_mem_diagramOrbit {t : TwistTag} {α β : Fin t.tag.rank → ℤ}
    (hα : IsRoot t.tag α ∧ 0 < height α) (hβ : β ∈ t.diagramOrbit α) :
    IsRoot t.tag β ∧ 0 < height β :=
  ⟨t.isRoot_of_mem_diagramOrbit hα.1 hβ, by rw [t.height_of_mem_diagramOrbit hβ]; exact hα.2⟩

private theorem permLattice_eq_of_card_eq_one {α : Fin TwistTag.D4.tag.rank → ℤ}
    (h : (TwistTag.D4.diagramOrbit α).card = 1) : permLattice TwistTag.D4.perm α = α := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h
  have h1 : α ∈ TwistTag.D4.diagramOrbit α := TwistTag.D4.self_mem_diagramOrbit α
  have h2 := TwistTag.D4.permLattice_mem_diagramOrbit h1
  rw [ha, Finset.mem_singleton] at h1 h2
  rw [h2, h1]

variable (σ : K ≃+* K)

private theorem sigma_rootCoord_of_fixed {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ ∧ 0 < height γ)
    (hρ : permLattice TwistTag.D4.perm γ = γ)
    (htw : ∀ c : K, twistHom TwistTag.D4 K σ.toRingHom (pinnedX TwistTag.D4.tag K γ c) =
      pinnedX TwistTag.D4.tag K γ (σ c))
    {x : ModGL TwistTag.D4.tag K} (hxΓ : x ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom)
    (hx : x ∈ heightSeries TwistTag.D4.tag K (height γ)) :
    σ (rootCoord hγ x) = rootCoord hγ x := by
  have hγ' : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm γ) ∧
      0 < height (permLattice TwistTag.D4.perm γ) := by
    rw [hρ]
    exact hγ
  obtain ⟨ε, hε⟩ := rootCoord_twistHom TwistTag.D4 σ.toRingHom hγ hγ'
  have hF : twistHom TwistTag.D4 K σ.toRingHom x = x :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hxΓ).2
  have hcongr : ∀ y : ModGL TwistTag.D4.tag K, rootCoord hγ' y = rootCoord hγ y := fun y =>
    rootCoord_congr TwistTag.D4 hρ hγ' hγ
  have hε1 : ε = 1 := by
    have h1 := hε (pinnedX TwistTag.D4.tag K γ 1) (pinnedX_mem_heightSeries_height hγ 1)
    rw [htw, map_one, hcongr, rootCoord_self hγ, map_one, mul_one] at h1
    exact h1.symm
  have h2 := hε x hx
  rw [hF, hcongr, hε1, one_mul] at h2
  exact h2.symm

end Aux

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

private theorem card_allowed {n : ℕ} (hn : n = 1 ∨ n = 3) :
    Nat.card {c : K // n = 1 → σ c = c} = (3 ^ f) ^ n := by
  rcases hn with rfl | rfl
  · have h := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ
    rw [pow_one, ← h]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c => ⟨fun h1 => h1 rfl, fun h1 _ => h1⟩)
  · rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun c h => absurd h (by norm_num))), hK]

private theorem exists_unique_mem_orbit_inf {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α ∧ 0 < height α) (c : K)
    (hc : (TwistTag.D4.diagramOrbit α).card = 1 → σ c = c) :
    ∃ g ∈ rootSpan TwistTag.D4.tag K
        (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
          twistedFixedGroup TwistTag.D4 K σ.toRingHom,
      rootCoord hα g = c ∧
        ∀ g' ∈ rootSpan TwistTag.D4.tag K
          (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
            twistedFixedGroup TwistTag.D4 K σ.toRingHom, rootCoord hα g' = c → g' = g := by
  classical
  set O := TwistTag.D4.diagramOrbit α
  set G : Subgroup (ModGL TwistTag.D4.tag K) :=
    rootSpan TwistTag.D4.tag K (O : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
      twistedFixedGroup TwistTag.D4 K σ.toRingHom
  have hroot : ∀ β ∈ O, IsRoot TwistTag.D4.tag β ∧ 0 < height β := fun β hβ =>
    isRoot_pos_of_mem_diagramOrbit hα hβ
  have hsub : rootSpan TwistTag.D4.tag K (O : Set (Fin TwistTag.D4.tag.rank → ℤ)) ≤
      heightSeries TwistTag.D4.tag K (height α) :=
    rootSpan_mono fun β hβ => ⟨(hroot β hβ).1, (hroot β hβ).2,
      le_of_eq (TwistTag.D4.height_of_mem_diagramOrbit hβ).symm⟩
  have hGH : ∀ g ∈ G, g ∈ heightSeries TwistTag.D4.tag K (height α) := fun g hg =>
    hsub (Subgroup.mem_inf.1 hg).1
  let Qh : ↥G →* Multiplicative K :=
    { toFun := fun g => Multiplicative.ofAdd (rootCoord hα (g : ModGL TwistTag.D4.tag K))
      map_one' := congrArg Multiplicative.ofAdd (rootCoord_one hα)
      map_mul' := fun g g' =>
        congrArg Multiplicative.ofAdd (rootCoord_mul hα (hGH _ g.2) (hGH _ g'.2)) }
  have hker : ∀ g : ↥G, Qh g = 1 → g = 1 := by
    intro g hg
    have h0 : rootCoord hα (g : ModGL TwistTag.D4.tag K) = 0 := congrArg Multiplicative.toAdd hg
    refine Subtype.ext (eq_one_of_coord_eq_zero hα (Subgroup.mem_inf.1 g.2).1 ?_)
    intro β hβ hβ'
    exact rootCoord_orbit_eq_zero TwistTag.D4 σ.toRingHom (Subgroup.mem_inf.1 g.2).2 hα
      (hGH _ g.2) h0 hβ hβ'
  have hQinj : Function.Injective Qh := (injective_iff_map_eq_one Qh).2 hker
  have hfix : ∀ g ∈ G, O.card = 1 → σ (rootCoord hα g) = rootCoord hα g := fun g hg h1 =>
    sigma_rootCoord_of_fixed σ hα (permLattice_eq_of_card_eq_one h1)
      (fun c => twistHom_pinnedX_of_fixedRoot hf hK σ hσ hα.1
        (permLattice_eq_of_card_eq_one h1) c)
      (Subgroup.mem_inf.1 hg).2 (hGH g hg)
  let F : ↥G → {c : K // O.card = 1 → σ c = c} := fun g =>
    ⟨rootCoord hα (g : ModGL TwistTag.D4.tag K), hfix g g.2⟩
  have hFinj : Function.Injective F := fun g g' h =>
    hQinj (congrArg Multiplicative.ofAdd (congrArg Subtype.val h))
  have hOcard : O.card = 1 ∨ O.card = 3 := by
    obtain ⟨w, hw, a, -, hcard, hord⟩ := (diagram_root_orbit_reduction TwistTag.D4).1 α hα.1
    rw [hcard]
    exact hord
  have hq : ∀ a, Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) =
      (3 ^ f) ^ (TwistTag.D4.orbit a).card := fun a =>
    CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.D4) Nat.prime_three hf hK
      (fun c => hσ c) a
  have hGcard : Nat.card ↥G = (3 ^ f) ^ O.card :=
    CFSG.Timmesfeld.ExceptionalOrders.card_diagramOrbit_inf hq hα.1
  have hFbij : Function.Bijective F :=
    hFinj.bijective_of_nat_card_le (by rw [hGcard, card_allowed hf hK σ hσ hOcard])
  obtain ⟨g, hg⟩ := hFbij.2 ⟨c, hc⟩
  refine ⟨g, g.2, congrArg Subtype.val hg, fun g' hg' hc' => ?_⟩
  exact congrArg Subtype.val (hFinj (a₁ := ⟨g', hg'⟩) (a₂ := g)
    (Subtype.ext (hc'.trans (congrArg Subtype.val hg).symm)))

theorem exists_orbitElt {k : ℕ} (hk : k < (maxHeight TwistTag.D4.tag).toNat)
    (O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ))) (c : K) (hc : O.1.card = 1 → σ c = c) :
    ∃ x : layerN σ k,
      layerPhi σ k x = Multiplicative.ofAdd (Pi.single O c) ∧
        (σ c = c → fieldActor (t := TwistTag.D4) σ σ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = x) := by
  classical
  have hrep := repOf_spec TwistTag.D4 ((k + 1 : ℕ) : ℤ) O
  have hα : IsRoot TwistTag.D4.tag (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O) ∧
      0 < height (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O) :=
    ⟨hrep.1, by rw [hrep.2.1]; positivity⟩
  set α := repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O
  have hroot : ∀ β ∈ TwistTag.D4.diagramOrbit α, IsRoot TwistTag.D4.tag β ∧ 0 < height β :=
    fun β hβ => isRoot_pos_of_mem_diagramOrbit hα hβ
  obtain ⟨g, hgG, hgc, hguniq⟩ := exists_unique_mem_orbit_inf hf hK σ hσ hα c
    (by rw [hrep.2.2]; exact hc)
  obtain ⟨hgO, hgΓ⟩ := Subgroup.mem_inf.1 hgG
  have hgH : g ∈ heightSeries TwistTag.D4.tag K (height α) :=
    (rootSpan_mono (S := (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)))
      (T := {γ | IsRoot TwistTag.D4.tag γ ∧ 0 < height γ ∧ height α ≤ height γ})
      fun β hβ => ⟨(hroot β hβ).1, (hroot β hβ).2,
        le_of_eq (TwistTag.D4.height_of_mem_diagramOrbit hβ).symm⟩) hgO
  have hgU : g ∈ posUnipotent TwistTag.D4.tag K := heightSeries_le_posUnipotent _ hgH
  have hgC : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
      (Subgroup.mem_inf.2 ⟨hgU, hgΓ⟩)
  have hgN : (⟨g, hgC⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈ layerN σ k := by
    rw [mem_layerN, ← hrep.2.1]
    exact hgH
  refine ⟨⟨⟨g, hgC⟩, hgN⟩, ?_, ?_⟩
  · refine congrArg Multiplicative.ofAdd (funext fun O' => ?_)
    show rootCoord (α := repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O') _ g =
      (Pi.single O c : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)) → K) O'
    by_cases h : O' = O
    · subst h
      rw [Pi.single_eq_same]
      exact hgc
    · rw [Pi.single_eq_of_ne h]
      have hrep' := repOf_spec TwistTag.D4 ((k + 1 : ℕ) : ℤ) O'
      have hα' : IsRoot TwistTag.D4.tag (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O') ∧
          0 < height (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O') :=
        ⟨hrep'.1, by rw [hrep'.2.1]; positivity⟩
      refine rootCoord_of_mem_coordKer hα' ((rootSpan_mono ?_) hgO)
      intro β hβ
      refine ⟨(hroot β hβ).1, (hroot β hβ).2, ?_, fun hβeq => h ?_⟩
      · rw [hrep'.2.1, TwistTag.D4.height_of_mem_diagramOrbit hβ, hrep.2.1]
      · apply Subtype.ext
        calc O'.1 = TwistTag.D4.diagramOrbit (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O') :=
              hrep'.2.2.symm
          _ = TwistTag.D4.diagramOrbit β := by rw [hβeq]
          _ = TwistTag.D4.diagramOrbit α := TwistTag.D4.diagramOrbit_eq_of_mem hβ
          _ = O.1 := hrep.2.2
  · intro hσc
    have hyeq : ((fieldActor (t := TwistTag.D4) σ σ ⟨g, hgC⟩ :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
        Units.map (entrywiseHom σ.toRingHom) g := rfl
    have hyC := (fieldActor (t := TwistTag.D4) σ σ ⟨g, hgC⟩).2
    have hyΓ := graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom hyC
    have hyO : Units.map (entrywiseHom σ.toRingHom) g ∈ rootSpan TwistTag.D4.tag K
        (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) :=
      map_rootSpan_le (Units.map (entrywiseHom σ.toRingHom)) id
        (fun γ _ c => ⟨σ c, Units.ext (entrywise_pinnedX σ.toRingHom γ c)⟩)
        (fun γ hγ => ⟨(hroot γ hγ).1, hγ⟩) hgO
    have hycoord : rootCoord hα (Units.map (entrywiseHom σ.toRingHom) g) = c := by
      rw [rootCoord_entrywise σ.toRingHom hα hgH, hgc]
      exact hσc
    have hy := hguniq _ (Subgroup.mem_inf.2 ⟨hyO, hyeq ▸ hyΓ⟩) hycoord
    exact Subtype.ext hy

theorem layerPhi_apply_fixed {k : ℕ} (hk : k < (maxHeight TwistTag.D4.tag).toNat)
    (x : layerN σ k) (O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ))) (hO : O.1.card = 1) :
    σ (Multiplicative.toAdd (layerPhi σ k x) O) = Multiplicative.toAdd (layerPhi σ k x) O := by
  have hrep := repOf_spec TwistTag.D4 ((k + 1 : ℕ) : ℤ) O
  have hγ : IsRoot TwistTag.D4.tag (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O) ∧
      0 < height (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O) :=
    ⟨hrep.1, by rw [hrep.2.1]; positivity⟩
  have hcard : (TwistTag.D4.diagramOrbit (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O)).card = 1 := by
    rw [hrep.2.2]
    exact hO
  have hρ := permLattice_eq_of_card_eq_one hcard
  exact sigma_rootCoord_of_fixed σ hγ hρ
    (fun c => twistHom_pinnedX_of_fixedRoot hf hK σ hσ hγ.1 hρ c)
    (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom x.1.2)
    (mem_heightSeries_of_height_eq TwistTag.D4 hrep.2.1 x.2)

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
