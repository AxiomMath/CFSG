module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumPower
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218d
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (projUnipotent proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjSp fieldSp conjAut fieldAut
  conjAut_proj fieldAut_proj proj_surjective)
open CFSG.Quasithin.H13.L32A.C.SkPf (sp4T fieldAut_sp4T map_std_sp4 sp4_comm_mem sp4T_range_le
  mem_normalizer_of_map_conj_eq map_mul_eq map_inv_eq mul_conj_mul_inv
  isSylowTwoOf_projUnipotent_two normalizer_map isSylowTwoOf_map_symm)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (uc22pwlie_ringEquiv_pow uc22p218c_normalizer_le_sup
  uc22p218d_mul_pow_mul_inv_mem)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (proj_bijective_of_charTwo)

private theorem map_congr_map_eq {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (U : Subgroup M) (f : MulAut M) :
    (U.map e.toMonoidHom).map (MulAut.congr e f).toMonoidHom =
      (U.map f.toMonoidHom).map e.toMonoidHom := by
  have h : (MulAut.congr e f).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp f.toMonoidHom := by
    ext x
    change (MulAut.congr e f) (e x) = e (f x)
    rw [MulAut.congr_apply]
    simp [MulEquiv.trans_apply]
  rw [Subgroup.map_map, Subgroup.map_map, h]

private theorem exists_pow_mul_inv_mem_of_conj_fieldAut_projUnipotent {K : Type} [Field K]
    [Finite K] [CharP K 2] (y : StatedProj (StatedSp 2 K)) (σ : K ≃+* K)
    (hα : (projUnipotent 2 K).map (MulAut.conj y * fieldAut 2 K σ).toMonoidHom =
      projUnipotent 2 K) :
    ∃ k : ℕ, ∀ b ∈ normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
        Set (StatedProj (StatedSp 2 K))),
      (MulAut.conj y * fieldAut 2 K σ) b * (b ^ k)⁻¹ ∈ projUnipotent 2 K := by
  obtain ⟨i, hi⟩ := uc22pwlie_ringEquiv_pow σ
  have hy : y ∈ normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K))) := by
    apply mem_normalizer_of_map_conj_eq
    have h1 := map_mul_eq hα (map_inv_eq (map_std_sp4 σ 0))
    rw [pow_zero, mul_one] at h1
    rwa [mul_inv_cancel_right] at h1
  have hfield : ∀ u : Fin 2 → Kˣ,
      (fun j => Units.map σ.toRingHom.toMonoidHom (u j)) = u ^ 2 ^ i := by
    intro u
    funext j
    apply Units.ext
    simp [hi]
  have hk : ∀ t : Fin 2 → Kˣ,
      (MulAut.conj y * fieldAut 2 K σ) (sp4T K t) *
        (sp4T K t ^ 2 ^ i)⁻¹ ∈ projUnipotent 2 K := by
    intro t
    have h1 : (MulAut.conj y * fieldAut 2 K σ) (sp4T K t) =
        MulAut.conj y (sp4T K (t ^ 2 ^ i)) := by
      rw [MulAut.mul_apply, fieldAut_sp4T, hfield, map_pow]
    rw [h1, MulAut.conj_apply, ← map_pow]
    exact sp4_comm_mem y hy _ (sp4T_range_le ⟨_, rfl⟩)
  refine ⟨2 ^ i, fun b hb => ?_⟩
  have hαu : ∀ u ∈ projUnipotent 2 K,
      (MulAut.conj y * fieldAut 2 K σ) u ∈ projUnipotent 2 K := fun u hu => by
    have h1 := mem_map_of_mem (MulAut.conj y * fieldAut 2 K σ).toMonoidHom hu
    rwa [hα] at h1
  have hb' := uc22p218c_normalizer_le_sup hb
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ sp4T_range_le] at hb'
  obtain ⟨_, ⟨t, rfl⟩, u, hu, rfl⟩ := hb'
  have hh : sp4T K t ∈ normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K))) := sp4T_range_le ⟨t, rfl⟩
  have h2 : sp4T K t ^ 2 ^ i * (MulAut.conj y * fieldAut 2 K σ) u *
      (sp4T K t ^ 2 ^ i)⁻¹ ∈ projUnipotent 2 K :=
    (mem_normalizer_iff.1 (pow_mem hh (2 ^ i)) _).1 (hαu u hu)
  have e : (MulAut.conj y * fieldAut 2 K σ) (sp4T K t * u) *
      ((sp4T K t * u) ^ 2 ^ i)⁻¹ =
      ((MulAut.conj y * fieldAut 2 K σ) (sp4T K t) * (sp4T K t ^ 2 ^ i)⁻¹) *
        (sp4T K t ^ 2 ^ i * (MulAut.conj y * fieldAut 2 K σ) u * (sp4T K t ^ 2 ^ i)⁻¹) *
        ((sp4T K t * u) ^ 2 ^ i * (sp4T K t ^ 2 ^ i)⁻¹)⁻¹ := by
    rw [map_mul]
    group
  rw [e]
  exact mul_mem (mul_mem (hk t) h2)
    (inv_mem (uc22p218d_mul_pow_mul_inv_mem hh hu (2 ^ i)))

private theorem exists_pow_mul_inv_mem_of_conj_fieldAut {K : Type} [Field K] [Finite K] [CharP K 2]
    {U : Subgroup (StatedProj (StatedSp 2 K))} (hU : IsSylowTwoOf U ⊤)
    (y : StatedProj (StatedSp 2 K)) (σ : K ≃+* K)
    (hα : U.map (MulAut.conj y * fieldAut 2 K σ).toMonoidHom = U) :
    ∃ k : ℕ, ∀ b ∈ normalizer (U : Set (StatedProj (StatedSp 2 K))),
      (MulAut.conj y * fieldAut 2 K σ) b * (b ^ k)⁻¹ ∈ U := by
  have : Finite (StatedProj (StatedSp 2 K)) := inferInstance
  refine exists_pow_action_of_isSylowTwoOf
    (fun α : MulAut (StatedProj (StatedSp 2 K)) =>
      ∃ (y : StatedProj (StatedSp 2 K)) (σ : K ≃+* K), α = MulAut.conj y * fieldAut 2 K σ)
    ?_ isSylowTwoOf_projUnipotent_two ?_ hU ⟨y, σ, rfl⟩ hα
  · rintro α ⟨y, σ, rfl⟩ g
    refine ⟨g⁻¹ * y * fieldAut 2 K σ g, σ, ?_⟩
    have h1 : fieldAut 2 K σ * MulAut.conj g =
        MulAut.conj (fieldAut 2 K σ g) * fieldAut 2 K σ := by
      calc fieldAut 2 K σ * MulAut.conj g
          = (fieldAut 2 K σ * MulAut.conj g * (fieldAut 2 K σ)⁻¹) * fieldAut 2 K σ := by
              group
        _ = MulAut.conj (fieldAut 2 K σ g) * fieldAut 2 K σ := by
              rw [mul_conj_mul_inv]
    calc MulAut.conj g⁻¹ * (MulAut.conj y * fieldAut 2 K σ) * MulAut.conj g
        = (MulAut.conj g⁻¹ * MulAut.conj y) * (fieldAut 2 K σ * MulAut.conj g) := by group
      _ = MulAut.conj (g⁻¹ * y) * (MulAut.conj (fieldAut 2 K σ g) * fieldAut 2 K σ) := by
            rw [← map_mul, h1]
      _ = MulAut.conj (g⁻¹ * y * fieldAut 2 K σ g) * fieldAut 2 K σ := by
            rw [← mul_assoc, ← map_mul]
  · rintro α ⟨y, σ, rfl⟩ hαU
    exact exists_pow_mul_inv_mem_of_conj_fieldAut_projUnipotent y σ hαU

theorem exists_pow_mul_inv_mem_of_conjSp_fieldSp {K : Type} [Field K] [Finite K] [CharP K 2]
    {U : Subgroup (StatedSp 2 K)} (hU : IsSylowTwoOf U ⊤) (A : gsp 2 K) (σ : K ≃+* K)
    (hα : U.map (conjSp 2 K A * fieldSp 2 K σ).toMonoidHom = U) :
    ∃ k : ℕ, ∀ b ∈ normalizer (U : Set (StatedSp 2 K)),
      (conjSp 2 K A * fieldSp 2 K σ) b * (b ^ k)⁻¹ ∈ U := by
  set β : MulAut (StatedSp 2 K) := conjSp 2 K A * fieldSp 2 K σ with hβdef
  let Pj : StatedSp 2 K ≃* StatedProj (StatedSp 2 K) :=
    MulEquiv.ofBijective (proj 2 K) proj_bijective_of_charTwo
  obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.KFacts.conjAut_mem_inner_of_charTwo A
  have hcongr_conj : MulAut.congr Pj (conjSp 2 K A) = MulAut.conj y := by
    rw [hy]
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective x
    change MulAut.congr Pj (conjSp 2 K A) (Pj g) = conjAut 2 K A (proj 2 K g)
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change proj 2 K (conjSp 2 K A g) = conjAut 2 K A (proj 2 K g)
    rw [conjAut_proj]
  have hcongr_field : MulAut.congr Pj (fieldSp 2 K σ) = fieldAut 2 K σ := by
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective x
    change MulAut.congr Pj (fieldSp 2 K σ) (Pj g) = fieldAut 2 K σ (proj 2 K g)
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change proj 2 K (fieldSp 2 K σ g) = fieldAut 2 K σ (proj 2 K g)
    rw [fieldAut_proj]
  have hβ : MulAut.congr Pj β = MulAut.conj y * fieldAut 2 K σ := by
    rw [hβdef, map_mul, hcongr_conj, hcongr_field]
  have hU' : IsSylowTwoOf (U.map Pj.toMonoidHom) ⊤ :=
    isSylowTwoOf_map_symm Pj.symm hU
  have hαU' : (U.map Pj.toMonoidHom).map (MulAut.conj y * fieldAut 2 K σ).toMonoidHom =
      U.map Pj.toMonoidHom := by
    rw [← hβ, map_congr_map_eq Pj U β, hα]
  obtain ⟨k, hk⟩ := exists_pow_mul_inv_mem_of_conj_fieldAut hU' y σ hαU'
  refine ⟨k, fun b hb => ?_⟩
  have hb' : Pj b ∈ normalizer ((U.map Pj.toMonoidHom : Subgroup
      (StatedProj (StatedSp 2 K))) : Set (StatedProj (StatedSp 2 K))) := by
    rw [normalizer_map]
    exact mem_map_of_mem Pj.toMonoidHom hb
  have h1 : (MulAut.congr Pj β) (Pj b) * (Pj b ^ k)⁻¹ ∈ U.map Pj.toMonoidHom := by
    rw [hβ]
    exact hk (Pj b) hb'
  have h2 : (MulAut.congr Pj β) (Pj b) * (Pj b ^ k)⁻¹ =
      Pj (β b * (b ^ k)⁻¹) := by
    rw [show (MulAut.congr Pj β) (Pj b) = Pj (β b) from by
          rw [MulAut.congr_apply]
          simp [MulEquiv.trans_apply]]
    rw [map_mul, map_inv, map_pow]
  have h3 : Pj (β b * (b ^ k)⁻¹) ∈ U.map Pj.toMonoidHom := by
    rwa [h2] at h1
  have h4 := Subgroup.mem_map_equiv.mp h3
  rwa [MulEquiv.symm_apply_apply] at h4

end CFSG.LocalAnalysis.RankThreeUC.S15

end
