module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivAut
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivWeyl

public noncomputable section

namespace CFSG.ComponentClassification.AS81.Sec2Aut

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.LieType.Chevalley
open scoped commutatorElement

variable {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)

include hk in
theorem exists_mul_inv_leviOne_mem {g : projectiveSL 3 k}
    (hg : g ∈ normalizer (projRad k 0 : Set (projectiveSL 3 k))) :
    ∃ B : SL2 k, g * (proj 3 k (leviOne k B))⁻¹ ∈ projRad k 0 := by
  rw [normalizer_projRad_zero hk] at hg
  have hle : ((proj 3 k).comp (leviOne k)).range ≤ normalizer (projRad k 0 : Set _) := by
    rintro _ ⟨B, rfl⟩
    exact leviOne_mem_normalizer B
  have hg' : g ∈ ((projRad k 0 ⊔ ((proj 3 k).comp (leviOne k)).range : Subgroup _) : Set _) :=
    hg
  rw [coe_mul_of_right_le_normalizer_left _ _ hle] at hg'
  obtain ⟨r, hr, _, ⟨B, rfl⟩, hrg⟩ := hg'
  refine ⟨B, ?_⟩
  rw [← hrg]
  simpa using hr

omit [Finite k] in
theorem eq_of_mul_inv_leviOne_mem {g : projectiveSL 3 k} {B B' : SL2 k}
    (h : g * (proj 3 k (leviOne k B))⁻¹ ∈ projRad k 0)
    (h' : g * (proj 3 k (leviOne k B'))⁻¹ ∈ projRad k 0) : B = B' := by
  have heq : (proj 3 k).comp (leviOne k) (B' * B⁻¹) =
      (g * (proj 3 k (leviOne k B'))⁻¹)⁻¹ * (g * (proj 3 k (leviOne k B))⁻¹) := by
    rw [MonoidHom.comp_apply, map_mul, map_mul, map_inv, map_inv]
    group
  have h1 : (proj 3 k).comp (leviOne k) (B' * B⁻¹) ∈
      projRad k 0 ⊓ ((proj 3 k).comp (leviOne k)).range :=
    Subgroup.mem_inf.mpr ⟨by rw [heq]; exact mul_mem (inv_mem h') h, ⟨_, rfl⟩⟩
  rw [projRad_zero_inf_range, mem_bot] at h1
  have h2 := leviOne_proj_injective (k := k) (h1.trans (map_one _).symm)
  exact (mul_inv_eq_one.mp h2).symm

@[expose] noncomputable def leviHom :
    ↥(normalizer (projRad k 0 : Set (projectiveSL 3 k))) →* SL2 k :=
  MonoidHom.mk' (fun g => Classical.choose (exists_mul_inv_leviOne_mem hk g.2)) fun g₁ g₂ => by
    have h₁ := Classical.choose_spec (exists_mul_inv_leviOne_mem hk g₁.2)
    have h₂ := Classical.choose_spec (exists_mul_inv_leviOne_mem hk g₂.2)
    have h₁₂ := Classical.choose_spec (exists_mul_inv_leviOne_mem hk (g₁ * g₂).2)
    refine eq_of_mul_inv_leviOne_mem h₁₂ ?_
    set B₁ := Classical.choose (exists_mul_inv_leviOne_mem hk g₁.2)
    set B₂ := Classical.choose (exists_mul_inv_leviOne_mem hk g₂.2)
    have hL : proj 3 k (leviOne k B₁) ∈ normalizer (projRad k 0 : Set _) :=
      leviOne_mem_normalizer B₁
    have h₃ := (mem_normalizer_iff.mp hL _).mp h₂
    have : ((g₁ * g₂ : ↥(normalizer (projRad k 0 : Set (projectiveSL 3 k)))) :
        projectiveSL 3 k) * (proj 3 k (leviOne k (B₁ * B₂)))⁻¹ =
        ((g₁ : projectiveSL 3 k) * (proj 3 k (leviOne k B₁))⁻¹) *
          (proj 3 k (leviOne k B₁) * ((g₂ : projectiveSL 3 k) * (proj 3 k (leviOne k B₂))⁻¹) *
            (proj 3 k (leviOne k B₁))⁻¹) := by
      rw [coe_mul, map_mul, map_mul]
      group
    rw [this]
    exact mul_mem h₁ h₃

include hk in
theorem mul_inv_leviOne_leviHom_mem
    (g : ↥(normalizer (projRad k 0 : Set (projectiveSL 3 k)))) :
    (g : projectiveSL 3 k) * (proj 3 k (leviOne k (leviHom hk g)))⁻¹ ∈ projRad k 0 :=
  Classical.choose_spec (exists_mul_inv_leviOne_mem hk g.2)

include hk in
theorem leviHom_leviOne (B : SL2 k) :
    leviHom hk ⟨proj 3 k (leviOne k B), leviOne_mem_normalizer B⟩ = B :=
  eq_of_mul_inv_leviOne_mem (mul_inv_leviOne_leviHom_mem hk _) (by
    rw [mul_inv_cancel]
    exact one_mem _)

include hk in
theorem leviHom_eq_one_iff (g : ↥(normalizer (projRad k 0 : Set (projectiveSL 3 k)))) :
    leviHom hk g = 1 ↔ (g : projectiveSL 3 k) ∈ projRad k 0 := by
  constructor
  · intro h
    have := mul_inv_leviOne_leviHom_mem hk g
    rwa [h, map_one, map_one, inv_one, mul_one] at this
  · intro h
    refine (eq_of_mul_inv_leviOne_mem (mul_inv_leviOne_leviHom_mem hk g) ?_)
    rwa [map_one, map_one, inv_one, mul_one]

omit [Finite k] in
theorem commutatorElement_leviOne_torus_unipU {t : k} (ht : t ≠ 0) (x z : k) :
    ⁅proj 3 k (leviOne k (torusSL2 ht)), proj 3 k (unipU k x 0 z)⁆ =
      proj 3 k (unipU k (x * (t⁻¹ - 1)) 0 (z * (t - 1))) := by
  rw [commutatorElement_def, Sec2Weyl.proj_conj_eq (Sec2Weyl.leviOne_torus_mul_unipU ht x 0 z),
    ← map_inv, ← map_mul, unipU_inv, unipU_mul]
  congr 1
  congr 1 <;> ring

include hk in
theorem commutator_normalizer_projRad_zero :
    ⁅normalizer (projRad k 0 : Set (projectiveSL 3 k)),
      normalizer (projRad k 0 : Set (projectiveSL 3 k))⁆ =
      normalizer (projRad k 0 : Set (projectiveSL 3 k)) := by
  set N := normalizer (projRad k 0 : Set (projectiveSL 3 k)) with hN
  have hLN : ((proj 3 k).comp (leviOne k)).range ≤ N := by
    rintro _ ⟨B, rfl⟩
    exact leviOne_mem_normalizer B
  refine le_antisymm (commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hR : projRad k 0 ≤ ⁅N, N⁆ := by
    intro r hr
    obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hr
    obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_card hk
    have h1 : t⁻¹ - 1 ≠ 0 := fun h => ht1 (by
      have := sub_eq_zero.mp h
      rwa [inv_eq_one] at this)
    have h2 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
    have heq := commutatorElement_leviOne_torus_unipU ht0 (a / (t⁻¹ - 1)) (c / (t - 1))
    rw [div_mul_cancel₀ _ h1, div_mul_cancel₀ _ h2] at heq
    rw [← heq]
    exact commutator_mem_commutator (leviOne_mem_normalizer _)
      (le_normalizer (mem_projRad_zero.2 ⟨_, _, rfl⟩))
  have hL : ((proj 3 k).comp (leviOne k)).range ≤ ⁅N, N⁆ := by
    have hperf := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k (by omega)
    have hcomm : ((proj 3 k).comp (leviOne k)).range =
        ⁅((proj 3 k).comp (leviOne k)).range, ((proj 3 k).comp (leviOne k)).range⁆ := by
      rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def,
        hperf.commutator_eq_top]
    calc ((proj 3 k).comp (leviOne k)).range
        = ⁅((proj 3 k).comp (leviOne k)).range, ((proj 3 k).comp (leviOne k)).range⁆ := hcomm
      _ ≤ ⁅N, N⁆ := commutator_mono hLN hLN
  calc N = projRad k 0 ⊔ ((proj 3 k).comp (leviOne k)).range := normalizer_projRad_zero hk
    _ ≤ ⁅N, N⁆ := sup_le hR hL

variable [CharP k 2]

omit [Finite k] in
theorem radSwap_proj_unipU_zero (a c : k) :
    radSwap (proj 3 k (unipU k a 0 c)) = proj 3 k (unipU k 0 a c) := by
  rw [radSwap, MulAut.mul_apply, dualAut_proj, unipU_inv, MulAut.conj_apply, ← map_mul,
    ← map_inv, ← map_mul]
  congr 1
  have hJ : (antidiagSL : SpecialLinearGroup (Fin 3) k)⁻¹ = antidiagSL :=
    inv_eq_of_mul_eq_one_right antidiagSL_mul_self
  rw [hJ]
  have ht : ((unipU k (-a) (-0) (-c + a * 0)).transpose : Matrix (Fin 3) (Fin 3) k) =
      !![1, 0, 0; a, 1, 0; c, 0, 1] := by
    rw [SpecialLinearGroup.coe_transpose, coe_unipU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ht, coe_unipU]
  simp only [antidiagSL, Matrix.mul_fin_three]
  fin_cases i <;> fin_cases j <;> simp

omit [Finite k] in
theorem map_projRad_zero_radSwap :
    (projRad k 0).map (radSwap : MulAut (projectiveSL 3 k)).toMonoidHom = projRad k 1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hy
    rw [MulEquiv.coe_toMonoidHom, radSwap_proj_unipU_zero]
    exact mem_projRad_one.2 ⟨a, c, rfl⟩
  · intro hx
    obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hx
    exact ⟨_, mem_projRad_zero.2 ⟨b, c, rfl⟩, by
      rw [MulEquiv.coe_toMonoidHom, radSwap_proj_unipU_zero]⟩

end CFSG.ComponentClassification.AS81.Sec2Aut
