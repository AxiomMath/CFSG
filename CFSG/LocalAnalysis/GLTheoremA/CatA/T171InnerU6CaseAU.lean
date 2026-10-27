module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Trans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open scoped commutatorElement

private theorem theta_commutator_mem_range {Ω : Type} [Group Ω] {L : Subgroup Ω} [L.Normal]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) {t b : Ω} (hb3 : b ^ 3 = 1) :
    theta L e ⁅t, b⁆ ∈ Psi.range := by
  rw [map_commutatorElement]
  have hθb3 : (theta L e b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hconj3 : (theta L e t * theta L e b * (theta L e t)⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hθb3, mul_one, mul_inv_cancel]
  have hinv3 : ((theta L e b)⁻¹) ^ 3 = 1 := by rw [inv_pow, hθb3, inv_one]
  obtain ⟨g₁, hg₁⟩ := exists_Psi_of_pow_three _ hconj3
  obtain ⟨g₂, hg₂⟩ := exists_Psi_of_pow_three _ hinv3
  refine MonoidHom.mem_range.mpr ⟨g₁ * g₂, ?_⟩
  rw [map_mul, hg₁, hg₂, commutatorElement_def]

private theorem map_commutator_theta_le_range {Ω : Type} [Group Ω] {L : Subgroup Ω} [L.Normal]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* S6) {B T : Subgroup Ω}
    (hB : ∀ b ∈ B, b ^ 3 = 1) :
    (⁅T, B⁆ : Subgroup Ω).map (theta L e) ≤ Psi.range := by
  rw [Subgroup.map_le_iff_le_comap]
  exact Subgroup.commutator_le.mpr fun _ _ b hb =>
    Subgroup.mem_comap.mpr (theta_commutator_mem_range e (hB b hb))

theorem stepCaseAU_holds :
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L : Subgroup Ω) [L.Normal]
      (e : ↥L ⧸ Subgroup.center ↥L ≃* S6), Setup B x L →
      ∀ T : Subgroup Ω, IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set Ω) →
        ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (L : Set Ω) →
      ∃ U : Subgroup PGU6, IsPGroup 2 U ∧ U ≠ ⊥ ∧ Bt B L e ≤ Subgroup.normalizer (U : Set PGU6) := by
  intro Ω _ _ B x L _ e hsetup T hT hBT hnot
  classical
  obtain ⟨hcfg, -, -⟩ := hsetup
  haveI : Group.IsPerfect ↥L := isPerfect_of_cfg hcfg
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := fun b hb => hcfg.elem.2 b hb
  let C : Subgroup Ω := ⁅T, B⁆
  have hC_le_T : C ≤ T := Subgroup.le_normalizer_iff_commutator_le_left.mp hBT
  have hC2 : IsPGroup 2 C := hT.to_le hC_le_T
  have hC_le_range : C.map (theta L e) ≤ Psi.range :=
    map_commutator_theta_le_range e hB3
  let U : Subgroup PGU6 := (C.map (theta L e)).comap Psi
  have hU2 : IsPGroup 2 U :=
    (hC2.map (theta L e)).comap_of_injective Psi Psi_injective
  have hC_conj : ∀ b ∈ B, ∀ c ∈ C, b * c * b⁻¹ ∈ C := by
    intro b hb c hc
    have hN : (C.subgroupOf (T ⊔ B)).Normal := CFSG.commutator_normal_in_sup T B
    have hle : T ⊔ B ≤ Subgroup.normalizer (C : Set Ω) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (H := C) (K := T ⊔ B)
        (hC_le_T.trans le_sup_left)).mp hN
    exact (Subgroup.mem_normalizer_iff.mp (hle (Subgroup.mem_sup_right hb)) c).mp hc
  have hnot' : ¬ C ≤ Subgroup.centralizer (L : Set Ω) := hnot
  have hex : ∃ c ∈ C, c ∉ Subgroup.centralizer (L : Set Ω) := by
    by_contra h
    apply hnot'
    intro c hc
    by_contra hcL
    exact h ⟨c, hc, hcL⟩
  obtain ⟨c, hcC, hcL⟩ := hex
  have hθc_ne : theta L e c ≠ 1 := fun h1 => hcL ((theta_eq_one_iff e c).mp h1)
  have hθc_mem : theta L e c ∈ C.map (theta L e) := Subgroup.mem_map.mpr ⟨c, hcC, rfl⟩
  have hθc_range : theta L e c ∈ Psi.range := hC_le_range hθc_mem
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hθc_range
  have hu_mem : u ∈ U := by
    change Psi u ∈ C.map (theta L e)
    rw [hu]
    exact hθc_mem
  have hu_ne : u ≠ 1 := by
    intro h1
    rw [h1, map_one] at hu
    exact hθc_ne hu.symm
  have hU_ne : U ≠ ⊥ := by
    intro hbot
    exact hu_ne (Subgroup.mem_bot.mp (hbot ▸ hu_mem))
  have hconj_mem : ∀ g ∈ Bt B L e, ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg u hu
    obtain ⟨b, hbB, hbPsi⟩ := (mem_Bt e).mp hg
    have hu' : Psi u ∈ C.map (theta L e) := hu
    obtain ⟨c, hcC, hcPsi⟩ := Subgroup.mem_map.mp hu'
    change g * u * g⁻¹ ∈ (C.map (theta L e)).comap Psi
    refine Subgroup.mem_comap.mpr ?_
    rw [map_mul, map_mul, map_inv, ← hbPsi, ← hcPsi]
    exact Subgroup.mem_map.mpr ⟨b * c * b⁻¹, hC_conj b hbB c hcC, by
      simp only [map_mul, map_inv]⟩
  refine ⟨U, hU2, hU_ne, ?_⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact hconj_mem g hg u
  · intro hu
    have hginv : g⁻¹ ∈ Bt B L e := (Bt B L e).inv_mem hg
    have h := hconj_mem g⁻¹ hginv (g * u * g⁻¹) hu
    simpa [mul_assoc] using h

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
