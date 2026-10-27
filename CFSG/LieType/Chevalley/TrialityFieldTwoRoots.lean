module

public import CFSG.LieType.Chevalley.TrialityCover
public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer

public noncomputable section

namespace CFSG.LieType.Chevalley.TrialityFieldTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Chevalley.TrialityCover
open scoped commutatorElement

section Proj

variable {τ : Tag} {K : Type} [Field K]

open scoped _root_.Classical in
def heightQuotProj
    (h : ℤ) (g : ModGL τ K) : Additive (HeightQuot τ K h) :=
  if hg : g ∈ heightSeries τ K h then Additive.ofMul (QuotientGroup.mk ⟨g, hg⟩) else 0

theorem heightQuotProj_of_mem
    {h : ℤ} {g : ModGL τ K} (hg : g ∈ heightSeries τ K h) :
    heightQuotProj h g = Additive.ofMul (QuotientGroup.mk ⟨g, hg⟩ : HeightQuot τ K h) := by
  unfold heightQuotProj
  exact dite_eq_left hg

theorem heightQuotProj_mul
    {h : ℤ} {g g' : ModGL τ K} (hg : g ∈ heightSeries τ K h)
    (hg' : g' ∈ heightSeries τ K h) :
    heightQuotProj h (g * g') = heightQuotProj h g + heightQuotProj h g' := by
  rw [heightQuotProj_of_mem hg, heightQuotProj_of_mem hg', heightQuotProj_of_mem (mul_mem hg hg'),
    ← ofMul_mul, ← QuotientGroup.mk_mul]
  rfl

theorem heightQuotProj_one
    (h : ℤ) : heightQuotProj h (1 : ModGL τ K) = 0 := by
  have e := heightQuotProj_mul (τ := τ) (K := K) (h := h) (one_mem _) (one_mem _)
  rw [mul_one] at e
  exact left_eq_add.1 e

theorem heightQuotProj_conj
    {h : ℤ} {u g : ModGL τ K} (hu : u ∈ posUnipotent τ K)
    (hg : g ∈ heightSeries τ K h) : heightQuotProj h (u * g * u⁻¹) = heightQuotProj h g := by
  have hug : u * g * u⁻¹ ∈ heightSeries τ K h :=
    (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K h hu) g).1 hg
  rw [heightQuotProj_of_mem hug, heightQuotProj_of_mem hg]
  congr 1
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hc : ⁅u, g⁻¹⁆ ∈ heightSeries τ K (h + 1) :=
    commutator_posUnipotent_heightSeries_le h
      (Subgroup.commutator_mem_commutator hu (inv_mem hg))
  convert hc using 1

theorem mem_heightSeries_succ_of_heightQuotProj_eq
    {h : ℤ} {g g' : ModGL τ K}
    (hg : g ∈ heightSeries τ K h) (hg' : g' ∈ heightSeries τ K h)
    (he : heightQuotProj h g = heightQuotProj h g') : g⁻¹ * g' ∈ heightSeries τ K (h + 1) := by
  rw [heightQuotProj_of_mem hg, heightQuotProj_of_mem hg'] at he
  have he' := QuotientGroup.eq.1 (Additive.ofMul.injective he)
  rw [Subgroup.mem_subgroupOf] at he'
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using he'

theorem heightQuotProj_pinnedX_add
    {h : ℤ} {α : Fin τ.rank → ℤ} (hα : α ∈ heightSet τ h)
    (a b : K) :
    heightQuotProj h (pinnedX τ K α (a + b)) =
      heightQuotProj h (pinnedX τ K α a) + heightQuotProj h (pinnedX τ K α b) := by
  rw [pinnedX_add]
  exact heightQuotProj_mul (pinnedX_mem_heightSeries hα a) (pinnedX_mem_heightSeries hα b)

theorem commutator_prod_heightQuotProj
    (h : ℤ) (zs ws : List (ModGL τ K))
    (hz : ∀ z ∈ zs, z ∈ posUnipotent τ K) (hw : ∀ w ∈ ws, w ∈ posUnipotent τ K)
    (hzw : ∀ z ∈ zs, ∀ w ∈ ws, ⁅z, w⁆ ∈ heightSeries τ K h) :
    ⁅zs.prod, ws.prod⁆ ∈ heightSeries τ K h ∧
      heightQuotProj h ⁅zs.prod, ws.prod⁆ =
        (zs.map fun z => (ws.map fun w => heightQuotProj h ⁅z, w⁆).sum).sum :=
  commutator_prod_mem_and_coord (heightSeries_le_normalizer K h) (heightQuotProj h)
    (fun _ hx _ hy => heightQuotProj_mul hx hy) (fun _ hg _ hx => heightQuotProj_conj hg hx)
    zs ws hz hw hzw

end Proj

abbrev ρL (α : Fin TwistTag.D4.tag.rank → ℤ) : Fin TwistTag.D4.tag.rank → ℤ :=
  permLattice TwistTag.D4.perm α

abbrev ρL2 (α : Fin TwistTag.D4.tag.rank → ℤ) : Fin TwistTag.D4.tag.rank → ℤ :=
  permLattice (TwistTag.D4.perm ^ 2) α

theorem mem_heightSet_of
    {α : Fin TwistTag.D4.tag.rank → ℤ} {h : ℤ} (hα : d4IsRootB α = true)
    (hh : 0 < height α ∧ h ≤ height α) : α ∈ heightSet TwistTag.D4.tag h :=
  ⟨d4IsRootB_iff.1 hα, hh.1, hh.2⟩

theorem orbit_zero_mem :
    (trialityRoot 0 ∈ heightSet TwistTag.D4.tag 1) ∧ ρL (trialityRoot 0) ∈ heightSet _ 1 ∧
      ρL2 (trialityRoot 0) ∈ heightSet _ 1 := by
  refine ⟨mem_heightSet_of ?_ ?_, mem_heightSet_of ?_ ?_, mem_heightSet_of ?_ ?_⟩ <;>
    decide +kernel

theorem orbit_two_mem :
    (trialityRoot 2 ∈ heightSet TwistTag.D4.tag 2) ∧ ρL (trialityRoot 2) ∈ heightSet _ 2 ∧
      ρL2 (trialityRoot 2) ∈ heightSet _ 2 := by
  refine ⟨mem_heightSet_of ?_ ?_, mem_heightSet_of ?_ ?_, mem_heightSet_of ?_ ?_⟩ <;>
    decide +kernel

theorem orbit_three_mem :
    (trialityRoot 3 ∈ heightSet TwistTag.D4.tag 3) ∧ ρL (trialityRoot 3) ∈ heightSet _ 3 ∧
      ρL2 (trialityRoot 3) ∈ heightSet _ 3 := by
  refine ⟨mem_heightSet_of ?_ ?_, mem_heightSet_of ?_ ?_, mem_heightSet_of ?_ ?_⟩ <;>
    decide +kernel

theorem root_one_mem : trialityRoot 1 ∈ heightSet TwistTag.D4.tag 1 :=
  mem_heightSet_of (by decide +kernel) (by decide +kernel)

theorem sums_zero_two :
    d4CommB (trialityRoot 0) (trialityRoot 2) = true ∧
    d4SumB (trialityRoot 0) (ρL (trialityRoot 2)) (ρL2 (trialityRoot 3)) = true ∧
    d4SumB (trialityRoot 0) (ρL2 (trialityRoot 2)) (ρL (trialityRoot 3)) = true ∧
    d4SumB (ρL (trialityRoot 0)) (trialityRoot 2) (ρL2 (trialityRoot 3)) = true ∧
    d4CommB (ρL (trialityRoot 0)) (ρL (trialityRoot 2)) = true ∧
    d4SumB (ρL (trialityRoot 0)) (ρL2 (trialityRoot 2)) (trialityRoot 3) = true ∧
    d4SumB (ρL2 (trialityRoot 0)) (trialityRoot 2) (ρL (trialityRoot 3)) = true ∧
    d4SumB (ρL2 (trialityRoot 0)) (ρL (trialityRoot 2)) (trialityRoot 3) = true ∧
    d4CommB (ρL2 (trialityRoot 0)) (ρL2 (trialityRoot 2)) = true := by
  decide +kernel

theorem sums_one_zero :
    d4SumB (trialityRoot 1) (trialityRoot 0) (trialityRoot 2) = true ∧
    d4SumB (trialityRoot 1) (ρL (trialityRoot 0)) (ρL (trialityRoot 2)) = true ∧
    d4SumB (trialityRoot 1) (ρL2 (trialityRoot 0)) (ρL2 (trialityRoot 2)) = true := by
  decide +kernel

section Truncated

variable {K : Type} [Field K] [CharP K 2] {σ : K →+* K}

theorem commutator_pinnedX_eq_one
    {α β : Fin TwistTag.D4.tag.rank → ℤ}
    (h : d4CommB α β = true) (s t : K) :
    ⁅pinnedX TwistTag.D4.tag K α s, pinnedX TwistTag.D4.tag K β t⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.2 (commute_of_d4CommB h s t)

theorem orbitProd_commutator_mem_four
    (hσ : σ ^ 3 = 1) (s t : K) :
    (trialityOrbitProd K σ (trialityRoot 3) (σ s * σ (σ t) + σ (σ s) * σ t) :
        ModGL TwistTag.D4.tag K)⁻¹ *
      ⁅(trialityOrbitProd K σ (trialityRoot 0) s : ModGL TwistTag.D4.tag K),
        (trialityOrbitProd K σ (trialityRoot 2) t : ModGL TwistTag.D4.tag K)⁆ ∈
      heightSeries TwistTag.D4.tag K 4 := by
  obtain ⟨m0, m1, m2⟩ := orbit_zero_mem
  obtain ⟨n0, n1, n2⟩ := orbit_two_mem
  obtain ⟨p0, p1, p2⟩ := orbit_three_mem
  obtain ⟨c00, c01, c02, c10, c11, c12, c20, c21, c22⟩ := sums_zero_two
  have ez : (trialityOrbitProd K σ (trialityRoot 0) s : ModGL TwistTag.D4.tag K) =
      [pinnedX TwistTag.D4.tag K (trialityRoot 0) s,
        pinnedX TwistTag.D4.tag K (ρL (trialityRoot 0)) (σ s),
        pinnedX TwistTag.D4.tag K (ρL2 (trialityRoot 0)) (σ (σ s))].prod := by
    simp only [coe_trialityOrbitProd, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have ew : (trialityOrbitProd K σ (trialityRoot 2) t : ModGL TwistTag.D4.tag K) =
      [pinnedX TwistTag.D4.tag K (trialityRoot 2) t,
        pinnedX TwistTag.D4.tag K (ρL (trialityRoot 2)) (σ t),
        pinnedX TwistTag.D4.tag K (ρL2 (trialityRoot 2)) (σ (σ t))].prod := by
    simp only [coe_trialityOrbitProd, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hz : ∀ z ∈ [pinnedX TwistTag.D4.tag K (trialityRoot 0) s,
      pinnedX TwistTag.D4.tag K (ρL (trialityRoot 0)) (σ s),
      pinnedX TwistTag.D4.tag K (ρL2 (trialityRoot 0)) (σ (σ s))],
      z ∈ heightSeries TwistTag.D4.tag K 1 := by
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact pinnedX_mem_heightSeries m0 _
    rcases List.mem_cons.1 hz with rfl | hz
    · exact pinnedX_mem_heightSeries m1 _
    rcases List.mem_cons.1 hz with rfl | hz
    · exact pinnedX_mem_heightSeries m2 _
    exact absurd hz List.not_mem_nil
  have hw : ∀ w ∈ [pinnedX TwistTag.D4.tag K (trialityRoot 2) t,
      pinnedX TwistTag.D4.tag K (ρL (trialityRoot 2)) (σ t),
      pinnedX TwistTag.D4.tag K (ρL2 (trialityRoot 2)) (σ (σ t))],
      w ∈ heightSeries TwistTag.D4.tag K 2 := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact pinnedX_mem_heightSeries n0 _
    rcases List.mem_cons.1 hw with rfl | hw
    · exact pinnedX_mem_heightSeries n1 _
    rcases List.mem_cons.1 hw with rfl | hw
    · exact pinnedX_mem_heightSeries n2 _
    exact absurd hw List.not_mem_nil
  have key := commutator_prod_heightQuotProj 3 _ _
    (fun z h => heightSeries_le_posUnipotent 1 (hz z h))
    (fun w h => heightSeries_le_posUnipotent 2 (hw w h))
    (fun z h w h' => commutator_heightSeries_le K 1 2
      (Subgroup.commutator_mem_commutator (hz z h) (hw w h')))
  rw [← ez, ← ew] at key
  obtain ⟨hmem, hπ⟩ := key
  have hx4 : (trialityOrbitProd K σ (trialityRoot 3) (σ s * σ (σ t) + σ (σ s) * σ t) :
      ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 3 := by
    rw [coe_trialityOrbitProd]
    exact mul_mem (mul_mem (pinnedX_mem_heightSeries p0 _) (pinnedX_mem_heightSeries p1 _))
      (pinnedX_mem_heightSeries p2 _)
  suffices hsuf : heightQuotProj 3 (trialityOrbitProd K σ (trialityRoot 3)
      (σ s * σ (σ t) + σ (σ s) * σ t) : ModGL TwistTag.D4.tag K) =
      heightQuotProj 3 ⁅(trialityOrbitProd K σ (trialityRoot 0) s : ModGL TwistTag.D4.tag K),
        (trialityOrbitProd K σ (trialityRoot 2) t : ModGL TwistTag.D4.tag K)⁆ by
    have h4 := mem_heightSeries_succ_of_heightQuotProj_eq hx4 hmem hsuf
    rwa [show (3 : ℤ) + 1 = 4 by norm_num] at h4
  rw [hπ, coe_trialityOrbitProd, heightQuotProj_mul (mul_mem (pinnedX_mem_heightSeries p0 _)
    (pinnedX_mem_heightSeries p1 _)) (pinnedX_mem_heightSeries p2 _),
    heightQuotProj_mul (pinnedX_mem_heightSeries p0 _) (pinnedX_mem_heightSeries p1 _)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [commutator_of_d4SumB c01, commutator_of_d4SumB c02, commutator_of_d4SumB c10,
    commutator_of_d4SumB c12, commutator_of_d4SumB c20, commutator_of_d4SumB c21,
    commutator_pinnedX_eq_one c00, commutator_pinnedX_eq_one c11, commutator_pinnedX_eq_one c22]
  simp only [heightQuotProj_one, map_add, map_mul, ringHom_apply_apply_apply_of_pow_three hσ,
    heightQuotProj_pinnedX_add p0, heightQuotProj_pinnedX_add p1, heightQuotProj_pinnedX_add p2]
  abel

theorem commutator_orbitProd_mem_three
    (s : K) :
    (trialityOrbitProd K σ (trialityRoot 2) s : ModGL TwistTag.D4.tag K)⁻¹ *
      ⁅pinnedX TwistTag.D4.tag K (trialityRoot 1) 1,
        (trialityOrbitProd K σ (trialityRoot 0) s : ModGL TwistTag.D4.tag K)⁆ ∈
      heightSeries TwistTag.D4.tag K 3 := by
  obtain ⟨m0, m1, m2⟩ := orbit_zero_mem
  obtain ⟨n0, n1, n2⟩ := orbit_two_mem
  obtain ⟨d0, d1, d2⟩ := sums_one_zero
  have ez : (trialityOrbitProd K σ (trialityRoot 0) s : ModGL TwistTag.D4.tag K) =
      [pinnedX TwistTag.D4.tag K (trialityRoot 0) s,
        pinnedX TwistTag.D4.tag K (ρL (trialityRoot 0)) (σ s),
        pinnedX TwistTag.D4.tag K (ρL2 (trialityRoot 0)) (σ (σ s))].prod := by
    simp only [coe_trialityOrbitProd, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have ey : pinnedX TwistTag.D4.tag K (trialityRoot 1) 1 =
      [pinnedX TwistTag.D4.tag K (trialityRoot 1) (1 : K)].prod := by
    rw [List.prod_cons, List.prod_nil, mul_one]
  have hz : ∀ z ∈ [pinnedX TwistTag.D4.tag K (trialityRoot 0) s,
      pinnedX TwistTag.D4.tag K (ρL (trialityRoot 0)) (σ s),
      pinnedX TwistTag.D4.tag K (ρL2 (trialityRoot 0)) (σ (σ s))],
      z ∈ heightSeries TwistTag.D4.tag K 1 := by
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact pinnedX_mem_heightSeries m0 _
    rcases List.mem_cons.1 hz with rfl | hz
    · exact pinnedX_mem_heightSeries m1 _
    rcases List.mem_cons.1 hz with rfl | hz
    · exact pinnedX_mem_heightSeries m2 _
    exact absurd hz List.not_mem_nil
  have hy : ∀ y ∈ [pinnedX TwistTag.D4.tag K (trialityRoot 1) (1 : K)],
      y ∈ heightSeries TwistTag.D4.tag K 1 := by
    intro y hy
    rw [List.mem_singleton] at hy
    rw [hy]
    exact pinnedX_mem_heightSeries root_one_mem 1
  have key := commutator_prod_heightQuotProj 2 _ _
    (fun y h => heightSeries_le_posUnipotent 1 (hy y h))
    (fun z h => heightSeries_le_posUnipotent 1 (hz z h))
    (fun y h z h' => commutator_heightSeries_le K 1 1
      (Subgroup.commutator_mem_commutator (hy y h) (hz z h')))
  rw [← ey, ← ez] at key
  obtain ⟨hmem, hπ⟩ := key
  have hx3 : (trialityOrbitProd K σ (trialityRoot 2) s : ModGL TwistTag.D4.tag K) ∈
      heightSeries TwistTag.D4.tag K 2 := by
    rw [coe_trialityOrbitProd]
    exact mul_mem (mul_mem (pinnedX_mem_heightSeries n0 _) (pinnedX_mem_heightSeries n1 _))
      (pinnedX_mem_heightSeries n2 _)
  suffices hsuf : heightQuotProj 2 (trialityOrbitProd K σ (trialityRoot 2) s :
      ModGL TwistTag.D4.tag K) = heightQuotProj 2 ⁅pinnedX TwistTag.D4.tag K (trialityRoot 1) 1,
        (trialityOrbitProd K σ (trialityRoot 0) s : ModGL TwistTag.D4.tag K)⁆ by
    have h3 := mem_heightSeries_succ_of_heightQuotProj_eq hx3 hmem hsuf
    rwa [show (2 : ℤ) + 1 = 3 by norm_num] at h3
  rw [hπ, coe_trialityOrbitProd, heightQuotProj_mul (mul_mem (pinnedX_mem_heightSeries n0 _)
    (pinnedX_mem_heightSeries n1 _)) (pinnedX_mem_heightSeries n2 _),
    heightQuotProj_mul (pinnedX_mem_heightSeries n0 _) (pinnedX_mem_heightSeries n1 _)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [commutator_of_d4SumB d0, commutator_of_d4SumB d1, commutator_of_d4SumB d2, one_mul,
    one_mul, one_mul]
  abel

end Truncated

theorem height_mem_trialityOrbit : ∀ j : Fin 6, ∀ β ∈ trialityOrbit j,
    height β = height (trialityRoot j) := by
  decide +kernel

section Generation

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem heightSeries_inf_le_closure
    (h : ℤ) :
    heightSeries TwistTag.D4.tag K h ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom ≤
      Subgroup.closure {g | ∃ j : Fin 6, h ≤ height (trialityRoot j) ∧
        g ∈ trialityGroup σ j} := by
  have e : heightSeries TwistTag.D4.tag K h = rootSpan TwistTag.D4.tag K
      (heightSet TwistTag.D4.tag h) := rfl
  rw [e]
  refine (rootSpan_inf_le_closure σ heightSet_pos heightSet_permLattice heightSet_closed).trans
    (Subgroup.closure_mono ?_)
  rintro g ⟨α, hα, hg⟩
  obtain ⟨j, hj, hO⟩ := exists_orbitGroup_eq σ hα.1 hα.2.1
  have hαj : α ∈ trialityOrbit j := hj ▸ TwistTag.D4.self_mem_diagramOrbit α
  refine ⟨j, ?_, hO ▸ hg⟩
  rw [← height_mem_trialityOrbit j α hαj]
  exact hα.2.2

end Generation

theorem orbitReflection_one_smul_root_zero :
    TwistTag.D4.orbitReflection ⟨1, by decide⟩ • trialityRoot 0 = trialityRoot 2 := by
  rw [TwistTag.orbitReflection_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem orbitReflection_zero_smul_root_two :
    TwistTag.D4.orbitReflection ⟨0, by decide⟩ • trialityRoot 2 = trialityRoot 3 := by
  rw [TwistTag.orbitReflection_smul]
  exact List.ofFn_injective (by decide +kernel)

section FieldTwo

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem fixedField_eq_zero_or_one (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2)
    (c : trialityFixedField K σ.toRingHom) : c = 0 ∨ c = 1 := by
  classical
  have : Finite (trialityFixedField K σ.toRingHom) := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite (trialityFixedField K σ.toRingHom)
  by_contra hc
  push Not at hc
  have h3 : ({0, 1, c} : Finset (trialityFixedField K σ.toRingHom)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hc.2.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, hc.1.symm⟩
  have hle := Finset.card_le_univ ({0, 1, c} : Finset (trialityFixedField K σ.toRingHom))
  rw [h3, Fintype.card_eq_nat_card, hk] at hle
  omega

theorem fixedUnits_subsingleton (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2) :
    Subsingleton (trialityFixedField K σ.toRingHom)ˣ := by
  refine ⟨fun u v => Units.ext ?_⟩
  rcases fixedField_eq_zero_or_one σ hk (u : trialityFixedField K σ.toRingHom) with hu | hu
  · exact absurd hu u.ne_zero
  rcases fixedField_eq_zero_or_one σ hk (v : trialityFixedField K σ.toRingHom) with hv | hv
  · exact absurd hv v.ne_zero
  rw [hu, hv]

theorem norm_eq_one (hσ : σ ^ 3 = 1) (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2)
    (a : Kˣ) : a * unitsSigma σ a * unitsSigma σ (unitsSigma σ a) = 1 := by
  have := fixedUnits_subsingleton σ hk
  have h1 : trialityNorm σ hσ a = 1 := Subsingleton.elim _ _
  refine Units.ext ?_
  have h2 := coe_trialityNorm hσ a
  rw [h1, map_one, Units.val_one] at h2
  rw [Units.val_mul, Units.val_mul, Units.val_one, h2]
  rfl

theorem eq_of_trace_eq_zero [CharP K 2] {z : K} (hz : z + σ z + σ (σ z) = 0) :
    z = σ z + σ (σ z) := by
  linear_combination hz - (σ z + σ (σ z)) * (CharTwo.two_eq_zero : (2 : K) = 0)

end FieldTwo

end CFSG.LieType.Chevalley.TrialityFieldTwo
