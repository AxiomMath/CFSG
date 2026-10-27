module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInner
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneHeightRigidity

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise


variable {τ : Tag} {K : Type} [Field K]

theorem mem_rootSubgroup_highRoot_of_commute_posUnipotent (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    [Finite K] {g : adjointGroup τ K}
    (hg : ∀ u ∈ posUnipotent τ K, (g : ModGL τ K) * u = u * g) :
    (g : ModGL τ K) ∈ rootSubgroup τ K (highRoot τ) := by
  have hA : MulAut.conj g ∈ diagonalFieldActors τ K :=
    (Chevalley_diagonal_field_actor_data.1 τ K).2.2 ⟨g, rfl⟩
  obtain ⟨u, hu, huC, hgu⟩ := exists_eq_conj_of_mem_actors_of_fix_heightSeries' le_rfl
    (simpleDiffTail_one τ) hA fun x hx => by
      rw [MulAut.conj_apply]
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hg x (heightSeries_le_posUnipotent 1 hx), mul_inv_cancel_right]
  have hg' : g = ⟨u, huC⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.conj_injective center_adjointGroup_eq_bot hgu
  have hgU : (g : ModGL τ K) ∈ posUnipotent τ K := by
    rw [hg']
    exact hu
  exact mem_rootSubgroup_highRoot_of_commute_simple hτ hgU fun j =>
    hg _ (pinnedX_single_mem_posUnipotent j 1)

theorem posUnipotent_le_centralizer_pinnedX_highRoot (c : K) :
    posUnipotent τ K ≤ Subgroup.centralizer {pinnedX τ K (highRoot τ) c} := by
  refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact (commute_pinnedX_highRoot K hβ.1 hβ.2 a c).eq

theorem torusElt_conj_pinnedX_highRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {d : K} (hd : d ≠ 0) :
    torusElt τ K (highNode τ) (Units.mk0 d hd)⁻¹ * pinnedX τ K (highRoot τ) d *
        (torusElt τ K (highNode τ) (Units.mk0 d hd)⁻¹)⁻¹ = pinnedX τ K (highRoot τ) 1 := by
  rw [torusElt_conj_pinnedX_coPair _ _ (isRoot_highRoot τ), EPilot.coPair_highRoot hτ,
    ite_eq_left rfl, zpow_one]
  congr 1
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hd]

variable (τ K) in
noncomputable def posUnipotentSylowE [Finite K] [CharP K 2] : Sylow 2 (adjointGroup τ K) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (isPGroup_and_not_dvd_index 2 (posUnipotent_le_adjointGroup (K := K))
      (card_posUnipotent (τ := τ) (K := K))).1.toSylow
    (isPGroup_and_not_dvd_index 2 (posUnipotent_le_adjointGroup (K := K))
      (card_posUnipotent (τ := τ) (K := K))).2

theorem mem_posUnipotentSylowE [Finite K] [CharP K 2] {x : adjointGroup τ K} :
    x ∈ (posUnipotentSylowE τ K : Subgroup (adjointGroup τ K)) ↔
      (x : ModGL τ K) ∈ posUnipotent τ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [posUnipotentSylowE, IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf]

theorem exists_conj_commute_posUnipotent_of_mem_centralizer [Finite K] [CharP K 2]
    (U : Sylow 2 (adjointGroup τ K)) {z : adjointGroup τ K}
    (hz : z ∈ centralizer ((U : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K))) :
    ∃ g : adjointGroup τ K, (U : Subgroup (adjointGroup τ K)) =
        (posUnipotentSylowE τ K : Subgroup (adjointGroup τ K)).map (MulAut.conj g).toMonoidHom ∧
      ∀ u ∈ posUnipotent τ K,
        ((g⁻¹ * z * g : adjointGroup τ K) : ModGL τ K) * u =
          u * ((g⁻¹ * z * g : adjointGroup τ K) : ModGL τ K) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup τ K) (posUnipotentSylowE τ K) U
  have hU : (U : Subgroup (adjointGroup τ K)) =
      (posUnipotentSylowE τ K : Subgroup (adjointGroup τ K)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, coe_smul_sylow_eq_map]
  refine ⟨g, hU, fun u hu => ?_⟩
  have huC : u ∈ adjointGroup τ K := posUnipotent_le_adjointGroup hu
  have hmem : g * ⟨u, huC⟩ * g⁻¹ ∈ (U : Subgroup (adjointGroup τ K)) := by
    rw [hU]
    exact ⟨⟨u, huC⟩, mem_posUnipotentSylowE.2 hu, rfl⟩
  have hc := mem_centralizer_iff.1 hz _ hmem
  have hc' := congrArg Subtype.val hc
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc' ⊢
  calc (g : ModGL τ K)⁻¹ * z * g * u =
        (g : ModGL τ K)⁻¹ * (z * (g * u * (g : ModGL τ K)⁻¹)) * g := by group
    _ = (g : ModGL τ K)⁻¹ * ((g * u * (g : ModGL τ K)⁻¹) * z) * g := by rw [hc']
    _ = u * ((g : ModGL τ K)⁻¹ * z * g) := by group

theorem exists_conj_eq_pinnedX_highRoot_of_mem_centralizer (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    [Finite K] [CharP K 2] (U : Sylow 2 (adjointGroup τ K)) {z : adjointGroup τ K}
    (hz : z ∈ centralizer ((U : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K))) :
    ∃ g : adjointGroup τ K, (U : Subgroup (adjointGroup τ K)) =
        (posUnipotentSylowE τ K : Subgroup (adjointGroup τ K)).map (MulAut.conj g).toMonoidHom ∧
      ∃ d : K, ((g⁻¹ * z * g : adjointGroup τ K) : ModGL τ K) = pinnedX τ K (highRoot τ) d := by
  obtain ⟨g, hU, hcomm⟩ := exists_conj_commute_posUnipotent_of_mem_centralizer U hz
  obtain ⟨d, hd⟩ := mem_rootSubgroup.1 (mem_rootSubgroup_highRoot_of_commute_posUnipotent hτ hcomm)
  exact ⟨g, hU, d, hd.symm⟩

theorem centralizer_sylow_le (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K] [CharP K 2]
    (U : Sylow 2 (adjointGroup τ K)) :
    centralizer ((U : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) ≤ U := by
  intro z hz
  obtain ⟨g, hU, d, hd⟩ := exists_conj_eq_pinnedX_highRoot_of_mem_centralizer hτ U hz
  rw [hU]
  refine ⟨g⁻¹ * z * g, mem_posUnipotentSylowE.2 ?_, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group⟩
  rw [hd]
  exact rootSubgroup_le_posUnipotent_of_height_pos (isRoot_highRoot τ)
    (height_highRoot_pos τ) (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem exists_conj_eq_pinnedElt_highRoot_of_mem_centralizer_sylow
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K] [CharP K 2] (U : Sylow 2 (adjointGroup τ K))
    {z : adjointGroup τ K}
    (hz : z ∈ centralizer ((U : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)))
    (hz1 : z ≠ 1) :
    ∃ c : adjointGroup τ K, c * z * c⁻¹ = EPilot.pinnedElt τ (highRoot τ) (1 : K) := by
  obtain ⟨g, -, d, hd⟩ := exists_conj_eq_pinnedX_highRoot_of_mem_centralizer hτ U hz
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hz1
    have h1 : g⁻¹ * z * g = 1 := Subtype.ext (by rw [hd, pinnedX_zero]; rfl)
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  set h : adjointGroup τ K :=
    ⟨torusElt τ K (highNode τ) (Units.mk0 d hd0)⁻¹, torusElt_mem_adjointGroup _ _⟩ with hhdef
  refine ⟨h * g⁻¹, Subtype.ext ?_⟩
  have e : ((h * g⁻¹ * z * (h * g⁻¹)⁻¹ : adjointGroup τ K) : ModGL τ K) =
      (h : ModGL τ K) * ((g⁻¹ * z * g : adjointGroup τ K) : ModGL τ K) * (h : ModGL τ K)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
    group
  rw [e, hd, hhdef]
  exact torusElt_conj_pinnedX_highRoot hτ hd0

theorem exists_conj_pinnedElt_highRoot_eq (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [CharP K 2]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ n : adjointGroup τ K,
      n * EPilot.pinnedElt τ (highRoot τ) (1 : K) * n⁻¹ = EPilot.pinnedElt τ γ (1 : K) := by
  obtain ⟨w, rfl⟩ := EPilot.exists_smul_highRoot_eq hτ hγ
  obtain ⟨ε, hε, hεc⟩ := EPilot.exists_conj_canonicalRep_pinnedX_highRoot_eq (K := K) w
  have hε1 : ε = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  refine ⟨⟨canonicalRep (coxeterSystem τ) K w, canonicalRep_mem_adjointGroup _ K w⟩,
    Subtype.ext ?_⟩
  have h := hεc 1
  rw [hε1, one_mul] at h
  simpa using h

theorem exists_conj_eq_pinnedElt_of_mem_centralizer_sylow (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    [Finite K] [CharP K 2] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (U : Sylow 2 (adjointGroup τ K)) {z : adjointGroup τ K}
    (hz : z ∈ centralizer ((U : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)))
    (hz1 : z ≠ 1) :
    ∃ c : adjointGroup τ K, c * z * c⁻¹ = EPilot.pinnedElt τ γ (1 : K) := by
  obtain ⟨c, hc⟩ := exists_conj_eq_pinnedElt_highRoot_of_mem_centralizer_sylow hτ U hz hz1
  obtain ⟨n, hn⟩ := exists_conj_pinnedElt_highRoot_eq (K := K) hτ hγ
  refine ⟨n * c, ?_⟩
  rw [← hn, ← hc]
  group

theorem exists_sylow_le_centralizer_pinnedElt (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K]
    [CharP K 2] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ U : Sylow 2 (adjointGroup τ K), EPilot.pinnedElt τ γ (1 : K) ∈
      centralizer ((U : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
  obtain ⟨n, hn⟩ := exists_conj_pinnedElt_highRoot_eq (K := K) hτ hγ
  have hθ : EPilot.pinnedElt τ (highRoot τ) (1 : K) ∈ centralizer
      ((posUnipotentSylowE τ K : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
    rw [mem_centralizer_iff]
    intro u hu
    refine Subtype.ext ?_
    have h := posUnipotent_le_centralizer_pinnedX_highRoot (τ := τ) (1 : K)
      (mem_posUnipotentSylowE.1 hu)
    exact Subgroup.mem_centralizer_singleton_iff.1 h
  refine ⟨n • posUnipotentSylowE τ K, ?_⟩
  rw [mem_centralizer_iff]
  intro u hu
  rw [SetLike.mem_coe, Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have hc := mem_centralizer_iff.1 hθ v hv
  rw [← hn, MulAut.smul_def, MulAut.conj_apply]
  calc n * v * n⁻¹ * (n * EPilot.pinnedElt τ (highRoot τ) 1 * n⁻¹) =
        n * (v * EPilot.pinnedElt τ (highRoot τ) 1) * n⁻¹ := by group
    _ = n * (EPilot.pinnedElt τ (highRoot τ) 1 * v) * n⁻¹ := by rw [hc]
    _ = n * EPilot.pinnedElt τ (highRoot τ) 1 * n⁻¹ * (n * v * n⁻¹) := by group

end CFSG.SeitzReduction.E8Pilot
