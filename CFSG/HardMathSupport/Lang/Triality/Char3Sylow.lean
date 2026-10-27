module

public import CFSG.HardMathSupport.Lang.Triality.Char3Reduction
public import CFSG.HardMathSupport.Lang.Triality.SylowInnerExt

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Triality

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)


theorem exists_unipotent_conj_fieldActor_of_order_three {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] [CharP K 3] (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (3 ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (u : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ∧
        (MulAut.conj u * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 ∧
        Nat.card (fixedSubgroup α) =
          Nat.card (fixedSubgroup (MulAut.conj u * fieldActor (t := TwistTag.D4) σ σ)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hfix, hg3⟩ := exists_conj_fieldActor_of_order_three Nat.prime_three (by norm_num) hf hK
    σ hσ α hα3 hαin
  have : Finite (WeylGroup TwistTag.D4.tag) := inferInstance
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨P, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 3 σ w₀ hw₀).1
  have hZ : Function.Injective (MulAut.conj : (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    conj_injective_of_center_eq_bot (center_graphFixedRootGroup_eq_bot σ.surjective)
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    exact ringEquiv_cube_apply_eq hK hσ c
  have hδ3 : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
    have h1 : fieldActor (t := TwistTag.D4) σ (σ ^ 3) = fieldActor σ σ ^ 3 :=
      map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
    rw [← h1, hσ3, fieldActor_one]
  have hF : fieldActor (t := TwistTag.D4) σ σ ∈
      graphFixedUnipotentStabilizer TwistTag.D4 K σ.toRingHom := by
    have := normalActor_mem (t := TwistTag.D4) σ 1 σ
    rwa [normalActor_one_left] at this
  have hδU : ∀ u ∈ (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), fieldActor (t := TwistTag.D4) σ σ u ∈ (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro u hu
    rw [hPU] at hu ⊢
    have := Subgroup.mem_map_of_mem (fieldActor (t := TwistTag.D4) σ σ).toMonoidHom hu
    rwa [hF.1] at this
  obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -, -, -, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form Nat.prime_three (by norm_num) hf K hK σ hσ
  have hσ1 : σ ≠ 1 := by
    intro h
    have hc := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ
    have htop : fixSubfield σ = ⊤ := by
      ext c
      simp [h]
    rw [htop] at hc
    have hc' : Nat.card K = 3 ^ f := by
      rw [← hc]
      exact (Nat.card_congr Subfield.topEquiv.toEquiv).symm
    have hp1 : 1 < 3 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
    rw [hK] at hc'
    nlinarith [hp1, pow_pos (lt_trans Nat.zero_lt_one hp1) 2]
  have hδI : fieldActor (t := TwistTag.D4) σ σ ∉ (MulAut.conj : (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    intro hmem
    have hmem' : fieldActor (t := TwistTag.D4) σ σ ∈ Θ.ker := by rw [hker]; exact hmem
    have hΘδ : Θ (fieldActor (t := TwistTag.D4) σ σ) = σ :=
      hΘ (fieldActor (t := TwistTag.D4) σ σ) 1 σ (by rw [map_one, one_mul])
    exact hσ1 (hΘδ.symm.trans hmem')
  obtain ⟨ε, u, hu, hcase⟩ := exists_conj_mem_innExt P hZ hδ3 hδU hδI g hg3
  have huU : (u : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    have : u ∈ (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := hu
    rw [hPU, Subgroup.mem_subgroupOf] at this
    exact this
  refine ⟨u, huU, ?_, ?_⟩
  · rcases hcase with h | h
    · rw [← h, conj_pow, hg3, mul_one, mul_inv_cancel]
    · rw [← h, conj_pow, inv_pow, hg3, inv_one, mul_one, mul_inv_cancel]
  · rw [hfix]
    rcases hcase with h | h
    · rw [← h]
      exact (card_fixed_conj ε _).symm
    · rw [← h, ← fixedSubgroup_inv_eq (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ)]
      exact (card_fixed_conj ε _).symm

end CFSG.HardMathSupport.Lang.Triality
