module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerKill
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerCob
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerLong

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


private theorem la_fixed_height_one : ∀ v ∈ CFSG.Blueprint.Chevalley.rootFinset TwistTag.D4.tag,
    height v = 1 → permLattice TwistTag.D4.perm v = v → v = rootB := by
  decide +kernel

private theorem la_fixed_height_two_three :
    ∀ v ∈ CFSG.Blueprint.Chevalley.rootFinset TwistTag.D4.tag,
      (height v = 2 ∨ height v = 3) → permLattice TwistTag.D4.perm v ≠ v := by
  decide +kernel

private theorem la_rootB_fixed : permLattice TwistTag.D4.perm rootB = rootB := by
  decide +kernel

private theorem la_rootB_height : height rootB = 1 := by
  decide +kernel

private theorem la_rootB_mem : rootB ∈ CFSG.Blueprint.Chevalley.rootFinset TwistTag.D4.tag := by
  decide +kernel

private theorem la_rootC_mem : rootC ∈ CFSG.Blueprint.Chevalley.rootFinset TwistTag.D4.tag := by
  decide +kernel

private theorem la_rootC_height : height rootC = 4 := by
  decide +kernel

private theorem la_diagramOrbit_of_fixed {α : Fin TwistTag.D4.tag.rank → ℤ}
    (h : permLattice TwistTag.D4.perm α = α) :
    TwistTag.diagramOrbit TwistTag.D4 α = {α} := by
  have hk : ∀ k : ℕ, permLattice (TwistTag.D4.perm ^ k) α = α := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [permLattice_pow_succ TwistTag.D4 TwistTag.D4.perm k α, ih, h]
  ext β
  unfold TwistTag.diagramOrbit
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact hk k
  · rintro rfl
    exact ⟨0, by decide, hk 0⟩

private theorem la_fixed_of_card_eq_one {α : Fin TwistTag.D4.tag.rank → ℤ}
    (h : (TwistTag.diagramOrbit TwistTag.D4 α).card = 1) :
    permLattice TwistTag.D4.perm α = α := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h
  have h1 : permLattice TwistTag.D4.perm α ∈ TwistTag.diagramOrbit TwistTag.D4 α := by
    unfold TwistTag.diagramOrbit
    exact Finset.mem_image.2 ⟨1, Finset.mem_range.2 (by decide), by simp⟩
  have h2 : α ∈ TwistTag.diagramOrbit TwistTag.D4 α :=
    TwistTag.self_mem_diagramOrbit TwistTag.D4 α
  rw [ha, Finset.mem_singleton] at h1 h2
  exact h1.trans h2.symm

private theorem la_orbit_one_eq {O : Finset (Fin TwistTag.D4.tag.rank → ℤ)}
    (hO : O ∈ orbitsAt TwistTag.D4 ((0 + 1 : ℕ) : ℤ)) (hc : O.card = 1) :
    O = TwistTag.diagramOrbit TwistTag.D4 rootB := by
  obtain ⟨α, hα, hαh, rfl⟩ := (mem_orbitsAt TwistTag.D4).1 hO
  have h1 : height α = 1 := by rw [hαh]; norm_num
  rw [la_fixed_height_one α (mem_rootFinset.2 hα) h1 (la_fixed_of_card_eq_one hc)]

private theorem la_card_ne_one {h : ℤ} (hh : h = 2 ∨ h = 3)
    {O : Finset (Fin TwistTag.D4.tag.rank → ℤ)} (hO : O ∈ orbitsAt TwistTag.D4 h) :
    O.card ≠ 1 := by
  obtain ⟨α, hα, hαh, rfl⟩ := (mem_orbitsAt TwistTag.D4).1 hO
  intro hc
  have hαh' : height α = 2 ∨ height α = 3 := by rw [hαh]; exact hh
  exact la_fixed_height_two_three α (mem_rootFinset.2 hα) hαh' (la_fixed_of_card_eq_one hc)

private theorem la_three_le_toNat_maxHeight : 3 ≤ (maxHeight TwistTag.D4.tag).toNat := by
  have h1 : height rootC ≤ maxHeight TwistTag.D4.tag :=
    height_le_maxHeight (mem_rootFinset.1 la_rootC_mem) (by rw [la_rootC_height]; norm_num)
  rw [la_rootC_height] at h1
  have h2 := Int.self_le_toNat (maxHeight TwistTag.D4.tag)
  omega

private theorem la_mem_layerN_zero_iff {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    x ∈ layerN σ 0 ↔ (x : ModGL TwistTag.D4.tag K) ∈ posUnipotent TwistTag.D4.tag K := by
  rw [mem_layerN]
  show (x : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 1 ↔ _
  rw [heightSeries_one]

private theorem la_toAdd_layerPhi {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {k : ℕ}
    (x : layerN σ k) (O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)))
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α ∧ 0 < height α)
    (hαO : α = repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O) :
    Multiplicative.toAdd (layerPhi σ k x) O =
      rootCoord hα ((x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) := by
  subst hαO
  rfl

private theorem la_fieldActor_pow_three {f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) :
    fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    exact ringEquiv_cube_apply_eq hK hσ c
  have h1 : fieldActor (t := TwistTag.D4) σ (σ ^ 3) = fieldActor σ σ ^ 3 :=
    map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
  rw [← h1, hσ3, fieldActor_one]

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

private theorem la_coe_longElt {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : γ = rootB ∨ γ = rootC ∨ γ = rootD) (c : K) (hc : σ c = c) :
    ((longElt hf hK σ hσ hγ c hc : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K γ c :=
  coe_longElt hf hK σ hσ hγ c hc

private theorem la_toAdd_layerPhi_zero_longElt (s : K) (hs : σ s = s)
    (m : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hmcoe : ((m : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K rootB s) (hm0 : m ∈ layerN σ 0)
    (O : ↥(orbitsAt TwistTag.D4 ((0 + 1 : ℕ) : ℤ))) :
    Multiplicative.toAdd (layerPhi σ 0 ⟨m, hm0⟩) O =
      if O.1 = TwistTag.diagramOrbit TwistTag.D4 rootB then s else 0 := by
  have hrep := repOf_spec TwistTag.D4 ((0 + 1 : ℕ) : ℤ) O
  have hh1 : height (repOf TwistTag.D4 ((0 + 1 : ℕ) : ℤ) O) = 1 := hrep.2.1
  have hα : IsRoot TwistTag.D4.tag (repOf TwistTag.D4 ((0 + 1 : ℕ) : ℤ) O) ∧
      0 < height (repOf TwistTag.D4 ((0 + 1 : ℕ) : ℤ) O) :=
    ⟨hrep.1, by rw [hh1]; norm_num⟩
  have hβ : IsRoot TwistTag.D4.tag rootB ∧ 0 < height rootB :=
    ⟨mem_rootFinset.1 la_rootB_mem, by rw [la_rootB_height]; norm_num⟩
  rw [la_toAdd_layerPhi σ _ O hα rfl]
  change rootCoord hα ((m : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ModGL TwistTag.D4.tag K) = _
  rw [hmcoe]
  by_cases h : O.1 = TwistTag.diagramOrbit TwistTag.D4 rootB
  · rw [if_pos h]
    have hrepB : repOf TwistTag.D4 ((0 + 1 : ℕ) : ℤ) O = rootB := by
      have hmem : repOf TwistTag.D4 ((0 + 1 : ℕ) : ℤ) O ∈
          TwistTag.diagramOrbit TwistTag.D4 rootB := by
        rw [← h, ← hrep.2.2]
        exact TwistTag.self_mem_diagramOrbit TwistTag.D4 _
      rw [la_diagramOrbit_of_fixed la_rootB_fixed, Finset.mem_singleton] at hmem
      exact hmem
    exact (rootCoord_congr TwistTag.D4 hrepB hα hβ).trans (rootCoord_self hβ s)
  · rw [if_neg h]
    have hne : rootB ≠ repOf TwistTag.D4 ((0 + 1 : ℕ) : ℤ) O := by
      intro heq
      apply h
      rw [← hrep.2.2, ← heq]
    exact rootCoord_pinnedX_of_ne hα hβ (le_of_eq (by rw [hh1, la_rootB_height])) hne s

private theorem la_kill_step {k : ℕ} (hk : k < (maxHeight TwistTag.D4.tag).toNat)
    {m y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hm : m ∈ layerN σ 0)
    (hmc : cocycleProd (fieldActor (t := TwistTag.D4) σ σ) m = 1)
    (hyc : cocycleProd (fieldActor (t := TwistTag.D4) σ σ) y = 1)
    (hmy : m⁻¹ * y ∈ layerN σ k)
    (hz : ∀ O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)), O.1.card = 1 →
      Multiplicative.toAdd (layerPhi σ k ⟨m⁻¹ * y, hmy⟩) O = 0) :
    ∃ w ∈ layerN σ k,
      cocycleProd (fieldActor (t := TwistTag.D4) σ σ)
          (w⁻¹ * y * fieldActor (t := TwistTag.D4) σ σ w) = 1 ∧
        m⁻¹ * (w⁻¹ * y * fieldActor (t := TwistTag.D4) σ σ w) ∈ layerN σ (k + 1) := by
  have hN := CocycleData.norm_eq_one (cocycleData_delta0 σ) hk hm hmc hyc hmy
  obtain ⟨c, hc, hcob⟩ := exists_layer_cob hf hK σ hσ hk _ hN hz
  obtain ⟨w, hw, hmem⟩ :=
    CocycleData.exists_kill_step (cocycleData_delta0 σ) hk hm hmy hc hcob
  refine ⟨w, hw, ?_, hmem⟩
  rw [cocycleProd_twistedConj (la_fieldActor_pow_three hK σ hσ) y w, hyc, mul_one, inv_mul_cancel]

theorem exists_kill_layers_one_two {m y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hm : (m : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    (hmc : cocycleProd (fieldActor (t := TwistTag.D4) σ σ) m = 1)
    (hyc : cocycleProd (fieldActor (t := TwistTag.D4) σ σ) y = 1) (hy : m⁻¹ * y ∈ layerN σ 1) :
    ∃ w ∈ layerN σ 1, m⁻¹ * (w⁻¹ * y * fieldActor (t := TwistTag.D4) σ σ w) ∈ layerN σ 3 := by
  have hm0 : m ∈ layerN σ 0 := (la_mem_layerN_zero_iff σ m).2 (Subgroup.mem_inf.1 hm).1
  have h3 := la_three_le_toNat_maxHeight
  have hk1 : 1 < (maxHeight TwistTag.D4.tag).toNat := by omega
  have hk2 : 2 < (maxHeight TwistTag.D4.tag).toNat := by omega
  obtain ⟨w₂, hw₂, hyc₂, hm₂⟩ := la_kill_step hf hK σ hσ hk1 hm0 hmc hyc hy
    (fun O hO => absurd hO
      (la_card_ne_one (h := ((1 + 1 : ℕ) : ℤ)) (Or.inl (by norm_num)) O.2))
  obtain ⟨w₃, hw₃, -, hm₃⟩ := la_kill_step hf hK σ hσ hk2 hm0 hmc hyc₂ hm₂
    (fun O hO => absurd hO
      (la_card_ne_one (h := ((2 + 1 : ℕ) : ℤ)) (Or.inr (by norm_num)) O.2))
  refine ⟨w₂ * w₃, (layerN σ 1).mul_mem hw₂ (layerN_chain σ 1 hw₃), ?_⟩
  have e : (w₂ * w₃)⁻¹ * y * fieldActor (t := TwistTag.D4) σ σ (w₂ * w₃) =
      w₃⁻¹ * (w₂⁻¹ * y * fieldActor (t := TwistTag.D4) σ σ w₂) *
        fieldActor (t := TwistTag.D4) σ σ w₃ := by
    rw [map_mul]
    group
  rw [e]
  exact hm₃

theorem exists_twistedConj_longForm {u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hu : (u : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    (hu3 : (MulAut.conj u * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1) :
    ∃ (w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (s r r' : K)
      (hs : σ s = s) (hr : σ r = r) (hr' : σ r' = r'),
      w⁻¹ * u * fieldActor (t := TwistTag.D4) σ σ w =
        longElt hf hK σ hσ (Or.inl rfl) s hs *
          longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
          longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr' := by
  have hyc : cocycleProd (fieldActor (t := TwistTag.D4) σ σ) u = 1 :=
    cocycleProd_eq_one_of_pow_three hf hK σ hσ u hu3
  have hu0 : u ∈ layerN σ 0 := (la_mem_layerN_zero_iff σ u).2 (Subgroup.mem_inf.1 hu).1
  have h3 := la_three_le_toNat_maxHeight
  have hk0 : 0 < (maxHeight TwistTag.D4.tag).toNat := by omega
  have hO2 : TwistTag.diagramOrbit TwistTag.D4 rootB ∈
      orbitsAt TwistTag.D4 ((0 + 1 : ℕ) : ℤ) :=
    (mem_orbitsAt TwistTag.D4).2 ⟨rootB, mem_rootFinset.1 la_rootB_mem, la_rootB_height, rfl⟩
  have hcard2 : (TwistTag.diagramOrbit TwistTag.D4 rootB).card = 1 := by
    rw [la_diagramOrbit_of_fixed la_rootB_fixed, Finset.card_singleton]
  obtain ⟨s, hsdef⟩ : ∃ s : K, s = Multiplicative.toAdd (layerPhi σ 0 ⟨u, hu0⟩)
      ⟨TwistTag.diagramOrbit TwistTag.D4 rootB, hO2⟩ := ⟨_, rfl⟩
  have hs : σ s = s := by
    rw [hsdef]
    exact layerPhi_apply_fixed hf hK σ hσ hk0 ⟨u, hu0⟩
      ⟨TwistTag.diagramOrbit TwistTag.D4 rootB, hO2⟩ hcard2
  obtain ⟨m, hmdef⟩ : ∃ m, m = longElt hf hK σ hσ (Or.inl rfl) s hs := ⟨_, rfl⟩
  have hmcoe : ((m : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K rootB s := by
    rw [hmdef]
    exact la_coe_longElt hf hK σ hσ (Or.inl rfl) s hs
  have hmU : ((m : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    rw [hmcoe]
    exact pinnedX_mem_graphFixedPosUnipotent hf hK σ hσ (Or.inl rfl) hs
  have hm0 : m ∈ layerN σ 0 := (la_mem_layerN_zero_iff σ m).2 (Subgroup.mem_inf.1 hmU).1
  have hδm : fieldActor (t := TwistTag.D4) σ σ m = m := by
    apply Subtype.ext
    rw [coe_fieldActor, hmcoe]
    have e : Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.D4.tag K rootB s) =
        pinnedX TwistTag.D4.tag K rootB (σ s) :=
      Units.ext (entrywise_pinnedX σ.toRingHom rootB s)
    rw [e, hs]
  have hmc : cocycleProd (fieldActor (t := TwistTag.D4) σ σ) m = 1 := by
    have h3s : s + s + s = 0 := by
      have h3' : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
      linear_combination s * h3'
    have hmmm : m * m * m = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_one, hmcoe]
      rw [← pinnedX_add TwistTag.D4.tag K rootB s s,
        ← pinnedX_add TwistTag.D4.tag K rootB (s + s) s, h3s,
        pinnedX_zero TwistTag.D4.tag K rootB]
    simp only [cocycleProd, hδm]
    exact hmmm
  have hmy0 : m⁻¹ * u ∈ layerN σ 0 := (layerN σ 0).mul_mem (inv_mem hm0) hu0
  have hz0 : ∀ O : ↥(orbitsAt TwistTag.D4 ((0 + 1 : ℕ) : ℤ)), O.1.card = 1 →
      Multiplicative.toAdd (layerPhi σ 0 ⟨m⁻¹ * u, hmy0⟩) O = 0 := by
    intro O hO
    have hOe : O = ⟨TwistTag.diagramOrbit TwistTag.D4 rootB, hO2⟩ :=
      Subtype.ext (la_orbit_one_eq O.2 hO)
    have key : Multiplicative.toAdd (layerPhi σ 0 ⟨m⁻¹ * u, hmy0⟩) O =
        -Multiplicative.toAdd (layerPhi σ 0 ⟨m, hm0⟩) O +
          Multiplicative.toAdd (layerPhi σ 0 ⟨u, hu0⟩) O := by
      rw [show (⟨m⁻¹ * u, hmy0⟩ : layerN σ 0) = (⟨m, hm0⟩ : layerN σ 0)⁻¹ * ⟨u, hu0⟩ from rfl,
        map_mul, map_inv]
      rfl
    have hOd : O.1 = TwistTag.diagramOrbit TwistTag.D4 rootB := by rw [hOe]
    rw [key, la_toAdd_layerPhi_zero_longElt hf hK σ hσ s hs m hmcoe hm0 O, if_pos hOd,
      hOe, ← hsdef]
    exact neg_add_cancel s
  obtain ⟨w₁, -, hyc₁, hm₁⟩ := la_kill_step hf hK σ hσ hk0 hm0 hmc hyc hmy0 hz0
  obtain ⟨w₂, -, hm₂⟩ := exists_kill_layers_one_two hf hK σ hσ hmU hmc hyc₁ hm₁
  obtain ⟨r, r', hr, hr', hxeq⟩ :=
    exists_long_form_of_mem_layerN_three hf hK σ hσ ⟨_, hm₂⟩
  refine ⟨w₁ * w₂, s, r, r', hs, hr, hr', ?_⟩
  have hW : (w₁ * w₂)⁻¹ * u * fieldActor (t := TwistTag.D4) σ σ (w₁ * w₂) =
      w₂⁻¹ * (w₁⁻¹ * u * fieldActor (t := TwistTag.D4) σ σ w₁) *
        fieldActor (t := TwistTag.D4) σ σ w₂ := by
    rw [map_mul]
    group
  have hsub : longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
      longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr' =
        m⁻¹ * (w₂⁻¹ * (w₁⁻¹ * u * fieldActor (t := TwistTag.D4) σ σ w₁) *
          fieldActor (t := TwistTag.D4) σ σ w₂) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, la_coe_longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr,
      la_coe_longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr']
    exact hxeq.symm
  rw [hW, mul_assoc (longElt hf hK σ hσ (Or.inl rfl) s hs)
      (longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr)
      (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr'), hsub, ← hmdef, mul_inv_cancel_left]

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
