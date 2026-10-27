module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGEichler
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCplxGrp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCplxCls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGFixMem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCyc4
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_polar_symm (x y : V) : Q.polarBilin x y = Q.polarBilin y x := by
  simp only [QuadraticMap.polarBilin_apply_apply]
  exact QuadraticMap.polar_comm Q x y

theorem fg_mem_omegaGroup_of_pow_three (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {g : OGroup Q} (hg : g ^ 3 = 1) :
    g ∈ omegaGroup hQ := by
  have h4 := index_omegaGroup hQ h2
  have hq : (QuotientGroup.mk g : OGroup Q ⧸ omegaGroup hQ) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one]
  have hd3 : orderOf (QuotientGroup.mk g : OGroup Q ⧸ omegaGroup hQ) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one hq
  have hd4 : orderOf (QuotientGroup.mk g : OGroup Q ⧸ omegaGroup hQ) ∣ 4 := by
    rw [← h4]
    exact orderOf_dvd_natCard _
  have h1 : orderOf (QuotientGroup.mk g : OGroup Q ⧸ omegaGroup hQ) = 1 := by
    have h := Nat.dvd_gcd hd3 hd4
    exact Nat.dvd_one.mp (by simpa using h)
  rw [orderOf_eq_one_iff] at h1
  exact (QuotientGroup.eq_one_iff g).mp h1

theorem fg_eichler_elem {ρ : ↥(simGroup Q)}
    (hρ2 : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = v)
    (hρB : ∀ x y, Q.polarBilin ((ρ : V ≃ₗ[ZMod 3] V) x) ((ρ : V ≃ₗ[ZMod 3] V) y) =
      -Q.polarBilin x y) {u w : V} (huw : Q.polarBilin u w = 0)
    (hcase : ((ρ : V ≃ₗ[ZMod 3] V) u = u ∧ (ρ : V ≃ₗ[ZMod 3] V) w = -w) ∨
      ((ρ : V ≃ₗ[ZMod 3] V) u = -u ∧ (ρ : V ≃ₗ[ZMod 3] V) w = w)) :
    ∃ t : OGroup Q, (∀ x, (t : V ≃ₗ[ZMod 3] V) x = fgEichler Q.polarBilin u w x) ∧ t ^ 3 = 1 ∧
      simAct Q ρ t = t := by
  have hsymm : ∀ x y, Q.polarBilin x y = Q.polarBilin y x := fun x y => fg_polar_symm x y
  have hu0 : Q.polarBilin u u = 0 ∧ Q.polarBilin w w = 0 ∧
      ∃ ε : ZMod 3, (ρ : V ≃ₗ[ZMod 3] V) u = ε • u ∧ (ρ : V ≃ₗ[ZMod 3] V) w = (-ε) • w := by
    rcases hcase with ⟨hu, hw⟩ | ⟨hu, hw⟩
    · exact ⟨fg_plus_isotropic (ρ := (ρ : V ≃ₗ[ZMod 3] V).toLinearMap) hρB (mem_fgPlus.mpr hu)
          (mem_fgPlus.mpr hu),
        fg_minus_isotropic (ρ := (ρ : V ≃ₗ[ZMod 3] V).toLinearMap) hρB (mem_fgMinus.mpr hw)
          (mem_fgMinus.mpr hw),
        1, by simpa using hu, by simpa using hw⟩
    · exact ⟨fg_minus_isotropic (ρ := (ρ : V ≃ₗ[ZMod 3] V).toLinearMap) hρB (mem_fgMinus.mpr hu)
          (mem_fgMinus.mpr hu),
        fg_plus_isotropic (ρ := (ρ : V ≃ₗ[ZMod 3] V).toLinearMap) hρB (mem_fgPlus.mpr hw)
          (mem_fgPlus.mpr hw),
        -1, by simpa using hu, by simpa using hw⟩
  obtain ⟨hu, hw, ε, hεu, hεw⟩ := hu0
  obtain ⟨σ, hσ⟩ := fg_exists_eichler_equiv hsymm hu hw huw
  have hσO : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fg_mem_orthogonalGroup_of_polar (fun x y => by
      rw [hσ x, hσ y]
      exact fg_eichler_isom hsymm hu hw huw x y)
  have hcomm : ∀ x, (ρ : V ≃ₗ[ZMod 3] V) (σ x) = σ ((ρ : V ≃ₗ[ZMod 3] V) x) := by
    intro x
    rw [hσ x, hσ]
    exact fg_eichler_comm (ρ := (ρ : V ≃ₗ[ZMod 3] V).toLinearMap) hρ2 hρB hsymm hεu hεw x
  refine ⟨⟨σ, hσO⟩, fun x => hσ x, ?_, ?_⟩
  · apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change σ (σ (σ x)) = x
    rw [hσ x, hσ, hσ]
    exact fg_eichler_cube hsymm hu hw huw x
  · apply Subtype.ext
    rw [coe_simAct]
    apply mul_inv_eq_iff_eq_mul.mpr
    apply LinearEquiv.ext
    intro x
    exact hcomm x

theorem fg_cent_typeIII (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = v)
    (hLM : LayerModel ↥(ffFix hQ h2 (QuotientGroup.mk ρ : ProjSim Q)) .PSL 3 1)
    {J : Subgroup ↥(omegaProj hQ)}
    (hJ : IsComponentIn J (ffFix hQ h2 (QuotientGroup.mk ρ : ProjSim Q)))
    {A : Subgroup (ProjSim Q)}
    (hAJ : ∀ a ∈ A, ∀ j ∈ J, projSimAct Q a (j : ProjOrth Q) = (j : ProjOrth Q)) :
    Nat.card A ≤ 2 := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 3) (by rw [hdim]; norm_num)
  have hpos : 0 < Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  have hB : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hρB : ∀ x y, Q.polarBilin ((ρ : V ≃ₗ[ZMod 3] V) x) ((ρ : V ≃ₗ[ZMod 3] V) y) =
      -Q.polarBilin x y := by
    intro x y
    have h := fg_polar_of_similitude hρ x y
    simpa using h
  have hsh : ∀ (E : Type) [Group E], LieModel E .PSL 3 3 1 →
      IsSimpleGroup E ∧ ∃ a b : E, a * b ≠ b * a := fun E _ hE => ff_simple_of_lieModel_psl3 hE
  have hρ1 : (QuotientGroup.mk ρ : ProjSim Q) ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    refine mem_piSim_iff.mpr (Or.inl ?_)
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact hρρ v
  refine fg_card_le_two_of_le_zpowers hρ1 (fun a haA => ?_)
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective a
  have hc : FGEichlerComm Q.polarBilin (ρ : V ≃ₗ[ZMod 3] V).toLinearMap
      (γ : V ≃ₗ[ZMod 3] V).toLinearMap := by
    intro u w huw hcase x
    obtain ⟨t, ht, ht3, htfix⟩ := fg_eichler_elem hρρ hρB huw hcase
    have hΩ := fg_mem_omegaGroup_of_pow_three hQ h2 ht3
    have hmem := fg_mem_ffFix_of_fixed hQ h2 ρ hΩ htfix
    let g : ↥(ffFix hQ h2 (QuotientGroup.mk ρ : ProjSim Q)) := ⟨_, hmem⟩
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one, g]
      rw [← map_pow, ht3, map_one]
    have hJmem := fg_mem_component_of_pow_three hsh hLM hJ g hg3
    have hfix := hAJ _ haA _ hJmem
    have hx : toProj Q (projSimActO Q (QuotientGroup.mk γ) t) = toProj Q t := by
      rw [toProj_projSimActO]
      exact hfix
    have hcomm := fg_projSimActO_eq_of_pow_three hpos (QuotientGroup.mk γ) ht3 hx
    rw [projSimActO_mk] at hcomm
    have h := fg_apply_comm_of_simAct γ hcomm x
    change (γ : V ≃ₗ[ZMod 3] V) (fgEichler Q.polarBilin u w x) =
      fgEichler Q.polarBilin u w ((γ : V ≃ₗ[ZMod 3] V) x)
    rw [← ht x, ← ht ((γ : V ≃ₗ[ZMod 3] V) x)]
    exact h
  obtain ⟨α, β, hαβ⟩ := fg_commutant_eichler (B := Q.polarBilin)
    (ρ := (ρ : V ≃ₗ[ZMod 3] V).toLinearMap) hB (fun x y => fg_polar_symm x y) hρρ hρB hdim hc
  have hγ : ∀ v, (γ : V ≃ₗ[ZMod 3] V) v = α • v + β • (ρ : V ≃ₗ[ZMod 3] V) v := hαβ
  obtain ⟨μ, hμ⟩ := γ.2
  have hab : α * β = 0 := by
    refine fg_cplx_ab_zero_pos (B := Q.polarBilin) (ρ := (ρ : V ≃ₗ[ZMod 3] V).toLinearMap) hρρ hρB
      hB (μ := (μ : ZMod 3)) (Units.ne_zero μ) (fun x y => ?_)
    have h := fg_polar_of_similitude hμ x y
    rw [hγ x, hγ y] at h
    exact h
  rcases fg_class_of_ab_zero hγ hab with h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact mem_zpowers _

end CFSG.OddStandard.SmallF3.Omega
