module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcSRBridge
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcSRE7Gamma
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1Comp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Row
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Cent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Inner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Layer

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRE7

open CFSG Subgroup CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.Burgoyne.E2
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.HighestRoot (rankOneGroup rankOneGroup_adjDatum)
open CFSG.RankThree.Chevalley (baseChangeGL_simpleRootSL2)
open scoped MatrixGroups

theorem commute_uSL_of_field
    {K L : Type} [Field K] [Fintype K] [Field L] (ι : K →+* L)
    (hK : 3 ≤ Fintype.card K) (β : Fin (Tag.rank .E7) → ℤ)
    {z : Module.End L (RootModule .E7 L)}
    (hz : ∀ c : K, z * (rootSL2 .E7 L β (uSL (ι c)) : Module.End L (RootModule .E7 L)) =
      (rootSL2 .E7 L β (uSL (ι c)) : Module.End L (RootModule .E7 L)) * z) (t : L) :
    z * (rootSL2 .E7 L β (uSL t) : Module.End L (RootModule .E7 L)) =
      (rootSL2 .E7 L β (uSL t) : Module.End L (RootModule .E7 L)) * z := by
  have hτ : Tag.E7 ≠ .G2 := by decide
  rw [TwE7.rootSL2_uSL_eq_sum hτ, ← sub_eq_zero, TwE7.commutator_sum_smul]
  refine Finset.sum_eq_zero fun a ha => ?_
  have h0 := TwE7.eq_zero_of_forall_sum_smul_eq_zero (f := fun c : K => ι c) ι.injective
    (Finset.range 3) id (Set.injOn_id _) (D := 2)
    (fun x hx => by have := Finset.mem_range.1 hx; simp only [id]; omega) (by omega)
    (fun a => z * TwE7.rootUCoeff (k := L) β a - TwE7.rootUCoeff (k := L) β a * z)
    (fun c => by
      rw [← TwE7.commutator_sum_smul]
      simp only [id]
      rw [← TwE7.rootSL2_uSL_eq_sum hτ, hz c, sub_self]) ha
  rw [h0, smul_zero]

theorem commute_vSL_of_field
    {K L : Type} [Field K] [Fintype K] [Field L] (ι : K →+* L)
    (hK : 3 ≤ Fintype.card K) (β : Fin (Tag.rank .E7) → ℤ)
    {z : Module.End L (RootModule .E7 L)}
    (hz : ∀ c : K, z * (rootSL2 .E7 L β (vSL (ι c)) : Module.End L (RootModule .E7 L)) =
      (rootSL2 .E7 L β (vSL (ι c)) : Module.End L (RootModule .E7 L)) * z) (t : L) :
    z * (rootSL2 .E7 L β (vSL t) : Module.End L (RootModule .E7 L)) =
      (rootSL2 .E7 L β (vSL t) : Module.End L (RootModule .E7 L)) * z := by
  have hτ : Tag.E7 ≠ .G2 := by decide
  rw [TwE7.rootSL2_vSL_eq_sum hτ, ← sub_eq_zero, TwE7.commutator_sum_smul]
  refine Finset.sum_eq_zero fun a ha => ?_
  have h0 := TwE7.eq_zero_of_forall_sum_smul_eq_zero (f := fun c : K => ι c) ι.injective
    (Finset.range 3) id (Set.injOn_id _) (D := 2)
    (fun x hx => by have := Finset.mem_range.1 hx; simp only [id]; omega) (by omega)
    (fun a => z * TwE7.rootVCoeff (k := L) β a - TwE7.rootVCoeff (k := L) β a * z)
    (fun c => by
      rw [← TwE7.commutator_sum_smul]
      simp only [id]
      rw [← TwE7.rootSL2_vSL_eq_sum hτ, hz c, sub_self]) ha
  rw [h0, smul_zero]

theorem commute_rootSL2_of_field
    {K L : Type} [Field K] [Fintype K] [Field L] (ι : K →+* L)
    (hK : 3 ≤ Fintype.card K) (β : Fin (Tag.rank .E7) → ℤ) {z : ModGL .E7 L}
    (hz : ∀ B : SL2 K, z * rootSL2 .E7 L β (Matrix.SpecialLinearGroup.map ι B) =
      rootSL2 .E7 L β (Matrix.SpecialLinearGroup.map ι B) * z) (A : SL2 L) :
    z * rootSL2 .E7 L β A = rootSL2 .E7 L β A * z := by
  have hu := commute_uSL_of_field ι hK β (z := (z : Module.End L (RootModule .E7 L))) fun c => by
    have h := congrArg Units.val (hz (uSL c))
    rwa [map_uSL, Units.val_mul, Units.val_mul] at h
  have hv := commute_vSL_of_field ι hK β (z := (z : Module.End L (RootModule .E7 L))) fun c => by
    have h := congrArg Units.val (hz (vSL c))
    rwa [map_vSL, Units.val_mul, Units.val_mul] at h
  have hle : (⊤ : Subgroup (SL2 L)) ≤
      (Subgroup.centralizer ({z} : Set (ModGL .E7 L))).comap (rootSL2 .E7 L β) := by
    rw [← sl2_closure_upper_lower, Subgroup.closure_le]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) <;>
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    · exact Units.ext (hu t).symm
    · exact Units.ext (hv t).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top A))).symm

theorem simpleRootSL2_mem_e7LeviE6
    (K : Type) [Field K] (k : Fin 6) (B : SL2 K) :
    (⟨simpleRootSL2 .E7 K (e7LeviE6Node k) B, simpleRootSL2_mem_adjointGroup _ B⟩ :
      adjointGroup .E7 K) ∈ e7LeviE6 K := by
  refine le_iSup (fun k => rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup
    (e7LeviE6Node k)) k ?_
  change _ ∈ rankOneGroup (adjDatum (rootOperatorFamily .E7) K) (Pi.single (e7LeviE6Node k) 1)
  rw [rankOneGroup_adjDatum _ (isRoot_single _ _), mem_subgroupOf,
    ← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2]
  exact ⟨B, rfl⟩


theorem mem_torusGroup_of_centralizes_e7LeviE6 {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Finite K] (hK3 : 3 ≤ Nat.card K) {L : Type} [Field L] [Algebra K L] [IsAlgClosed L]
    [CharP L p] {g : adjointGroup .E7 K} (hg : ∀ y ∈ e7LeviE6 K, g * y = y * g) :
    baseChangeGL (algebraMap K L) (g : ModGL .E7 K) ∈ torusGroup .E7 L := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hK3' : 3 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hzG : baseChangeGL (algebraMap K L) (g : ModGL .E7 K) ∈ adjointGroup .E7 L :=
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (algebraMap K L) g.2
  have hcomm : ∀ (k : Fin 6) (A : SL2 L),
      baseChangeGL (algebraMap K L) (g : ModGL .E7 K) *
          rootSL2 .E7 L (Pi.single (e7LeviE6Node k) 1) A =
        rootSL2 .E7 L (Pi.single (e7LeviE6Node k) 1) A *
          baseChangeGL (algebraMap K L) (g : ModGL .E7 K) := by
    intro k
    refine commute_rootSL2_of_field (algebraMap K L) hK3' _ fun B => ?_
    have h := congrArg Subtype.val (hg _ (simpleRootSL2_mem_e7LeviE6 K k B))
    have h' := congrArg (baseChangeGL (algebraMap K L)) h
    simp only [Subgroup.coe_mul, map_mul] at h'
    rw [TwE7.rootSL2_single, ← baseChangeGL_simpleRootSL2]
    exact h'
  have hroot : ∀ y ∈ leviGamma, IsRoot .E7 y.1 := fun y hy => by
    obtain ⟨k, hk⟩ := leviGamma_mem y hy
    rw [hk]
    exact isRoot_single _ _
  exact TwE7.mem_torusGroup_of_commute_rootTorus p (Or.inr (Or.inl rfl)) hzG leviGamma hroot
    (fun y hy s => by
      obtain ⟨k, hk⟩ := leviGamma_mem y hy
      rw [hk]
      exact hcomm k (HSL s)) 19 (fun α hα => leviGamma_reg α (mem_rootFinset.2 hα))

theorem outerCoreAt_t7 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) : OuterCoreAt (rootDiagAut .E7 K (bitsTuple e7BitsSix)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := finite_field_prime_power_characteristic hp
    (one_le_and_three_le_of_card hp hp2 hK).1 hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hK3 := (one_le_and_three_le_of_card hp hp2 hK).2
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hle := e7LeviE6_le_fixedSubgroup (K := K) hK2
  have hX : GorensteinWalter.IsComponentOf (e7LeviE6 K)
      (oddFixed (rootDiagAut .E7 K (bitsTuple e7BitsSix))) := by
    have h := HarrisLit.L33.SR.E1.isComponentOf_oddFixed_of_map
      (rootDiagAut .E7 K (bitsTuple e7BitsSix)) (MonoidHom.id _) Function.injective_id
      (Subgroup.map_id _) hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2
        (fixedSubgroup_le_normalizer_e7LeviE6 hK2)).isSubnormal
      (HarrisLit.L33.SR.E1.gw_isQuasisimple_of_isQuasisimple (isQuasisimple_e7LeviE6 hp hp2 hK))
    rw [Subgroup.comap_id] at h
    exact h.1
  refine outerCoreAt_of_component (center_adjointGroup_eq_bot_field .E7 K) hX
    (fun r hr _ hfix => mem_inner_of_odd_fix_e7LeviE6 hr hfix) ?_
  intro g h _ _ _ _ hgX hhX
  have hc : ∀ x : adjointGroup .E7 K, (∀ y ∈ e7LeviE6 K, x * y * x⁻¹ = y) →
      ∀ y ∈ e7LeviE6 K, x * y = y * x := fun x hx y hy => by
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [hx y hy]
  have hgT := mem_torusGroup_of_centralizes_e7LeviE6 (p := p) hK3
    (L := AlgebraicClosure K) (hc g hgX)
  have hhT := mem_torusGroup_of_centralizes_e7LeviE6 (p := p) hK3
    (L := AlgebraicClosure K) (hc h hhX)
  have h12 := TwE7.torus_mul_comm hgT hhT
  rw [← map_mul, ← map_mul] at h12
  exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h12)

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRE7
