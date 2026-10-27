module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddLinear
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryUniversalPairExclusion
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification CFSG.LinearGroups CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace EscapingNotOddUnitary

open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff_isometry)

variable {p f : ℕ} {k : Type} [Field k] (h : UnitaryFieldData p f k) (n : ℕ)

@[expose] def toSesqUnitary : unitarySU p f k n →* sesqUnitaryGroup (stdHermForm h n) :=
  ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) k ≃* _).toMonoidHom.comp
    (unitarySU p f k n).subtype).codRestrict _ fun A x y =>
      ((mem_unitarySU_iff_isometry h).1 A.2).2 x y

theorem toSesqUnitary_apply (A : unitarySU p f k n) (x : Fin n → k) :
    (((toSesqUnitary h n A : sesqUnitaryGroup (stdHermForm h n)) :
      LinearMap.GeneralLinearGroup k (Fin n → k)) : (Fin n → k) →ₗ[k] Fin n → k) x =
      ((A : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec x :=
  rfl

theorem range_toSesqUnitary_normal : (toSesqUnitary h n).range.Normal where
  conj_mem := by
    rintro _ ⟨A, rfl⟩ u
    set g : sesqUnitaryGroup (stdHermForm h n) := u * toSesqUnitary h n A * u⁻¹ with hg
    set M : GL (Fin n) k :=
      Matrix.GeneralLinearGroup.toLin.symm (g : LinearMap.GeneralLinearGroup k (Fin n → k))
      with hMdef
    have hM : Matrix.GeneralLinearGroup.toLin M =
        (g : LinearMap.GeneralLinearGroup k (Fin n → k)) :=
      MulEquiv.apply_symm_apply _ _
    have hMv : ∀ x, (M : Matrix (Fin n) (Fin n) k).mulVec x =
        ((g : LinearMap.GeneralLinearGroup k (Fin n → k)) : (Fin n → k) →ₗ[k] Fin n → k) x :=
      fun x => by
        rw [← hM]
        rfl
    have hdetA : (((A : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).det = 1 := by
      have := (mem_unitarySU_iff_isometry h).1 A.2
      exact this.1
    have hdet : (M : Matrix (Fin n) (Fin n) k).det = 1 := by
      rw [← LinearMap.det_toLin', Matrix.toLin'_apply']
      have hMl : (M : Matrix (Fin n) (Fin n) k).mulVecLin =
          ((g : LinearMap.GeneralLinearGroup k (Fin n → k)) : (Fin n → k) →ₗ[k] Fin n → k) :=
        LinearMap.ext hMv
      rw [hMl, hg, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
        Units.val_mul, map_mul, map_mul]
      have hA' : LinearMap.det (((toSesqUnitary h n A : sesqUnitaryGroup (stdHermForm h n)) :
          LinearMap.GeneralLinearGroup k (Fin n → k)) : (Fin n → k) →ₗ[k] Fin n → k) = 1 := by
        rw [← hdetA, ← LinearMap.det_toLin', Matrix.toLin'_apply']
        rfl
      rw [hA', mul_one, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    have hMmem : M ∈ unitarySU p f k n := by
      rw [mem_unitarySU_iff_isometry h]
      refine ⟨hdet, fun x y => ?_⟩
      rw [hMv, hMv]
      exact g.2 x y
    exact ⟨⟨M, hMmem⟩, Subtype.ext hM⟩

@[expose] def toProj : unitarySU p f k n →* sesqProjUnitary h (stdHermForm h n) :=
  (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h n))).comp (toSesqUnitary h n)

theorem toProj_range_normal : (toProj h n).range.Normal := by
  rw [toProj, MonoidHom.range_comp]
  exact (range_toSesqUnitary_normal h n).map _ (QuotientGroup.mk'_surjective _)

theorem eq_smul_one_of_mulVecLin {A : Matrix (Fin n) (Fin n) k} {c : k}
    (hA : A.mulVecLin = c • (1 : Module.End k (Fin n → k))) : A = c • 1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_apply', hA, map_smul, Matrix.toLin'_one]
  rfl

theorem ker_toProj (hn : 1 ≤ n) :
    (toProj h n).ker = (StatedScalars (Fin n) k).subgroupOf (unitarySU p f k n) := by
  ext A
  rw [MonoidHom.mem_ker, toProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_sesqNormOneScalars, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc, hA⟩
    refine ⟨Units.mk0 c (ne_zero_of_norm_eq_one h hc), Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
    exact (eq_smul_one_of_mulVecLin n hA).symm
  · rintro ⟨c, hcA⟩
    have hAc : ((A : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = (c : k) • 1 := by
      rw [← hcA, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
    refine ⟨c, ?_, ?_⟩
    ·
      obtain ⟨-, hiso⟩ := (mem_unitarySU_iff_isometry h).1 A.2
      have h1 := hiso (Pi.single ⟨0, hn⟩ 1) (Pi.single ⟨0, hn⟩ 1)
      rw [hAc, Matrix.smul_mulVec, Matrix.one_mulVec, stdHermForm_apply, stdHermForm_apply,
        Finset.sum_eq_single ⟨0, hn⟩ (fun j _ hj => by simp [hj]) (by simp),
        Finset.sum_eq_single ⟨0, hn⟩ (fun j _ hj => by simp [hj]) (by simp)] at h1
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, map_one] at h1
      rw [UnitaryFieldData.norm, mul_comm]
      exact h1
    · show ((A : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVecLin = (c : k) • 1
      rw [hAc, ← Matrix.toLin'_apply', map_smul, Matrix.toLin'_one]
      rfl

@[expose] def projEmbed (hn : 1 ≤ n) :
    StatedProj (StatedSU n (p ^ f) k) →* sesqProjUnitary h (stdHermForm h n) :=
  QuotientGroup.lift _ (toProj h n) (ker_toProj h n hn).ge

theorem projEmbed_mk (hn : 1 ≤ n) (A : unitarySU p f k n) :
    projEmbed h n hn (QuotientGroup.mk A) = toProj h n A :=
  rfl

theorem projEmbed_injective (hn : 1 ≤ n) : Function.Injective (projEmbed h n hn) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H A =>
    rw [projEmbed_mk] at hx
    rw [QuotientGroup.eq_one_iff, ← ker_toProj h n hn]
    exact hx

theorem range_projEmbed (hn : 1 ≤ n) : (projEmbed h n hn).range = (toProj h n).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    induction y using QuotientGroup.induction_on with
    | H A => exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨QuotientGroup.mk A, rfl⟩

end EscapingNotOddUnitary

open EscapingNotOddUnitary

theorem commuting_block_odd_unitary_overgroup_exclusion {G : Type} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {L : Subgroup G} (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) (n p f : ℕ) (hp : p ≠ 2) :
    ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSU n p f := by
  rintro ⟨⟨hpp, hf, hn, -⟩, k, _, _, hk, ⟨e⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : UnitaryFieldData p f k := ⟨hpp, hf, by rw [hk, ← pow_mul, mul_comm]⟩
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  let ψ : L ⧸ center L →* sesqProjUnitary hU (stdHermForm hU n) :=
    (projEmbed hU n hn1).comp e.toMonoidHom
  have hψ : Function.Injective ψ := (projEmbed_injective hU n hn1).comp e.injective
  have hψrange : ψ.range.Normal := by
    have h' : ψ.range = (toProj hU n).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map,
        range_projEmbed]
    rw [h']
    exact toProj_range_normal hU n
  have hfour : ∀ K ∈ block J, ∃ V : Subgroup (sesqProjUnitary hU (stdHermForm hU n)),
      V ≤ (centerQuotientImage L K).map ψ ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
    intro K hK
    obtain ⟨V, hVK, hVe, hVc⟩ :=
      exists_four_group_centerQuotientImage hV hK.1 ((le_blockGroup hK).trans hML) hodd
    exact ⟨V.map ψ, Subgroup.map_mono hVK, CFSG.IsElementaryAbelian.map ψ,
      by rw [Subgroup.card_map_of_injective hψ, hVc]⟩
  have hlocal : ∀ K ∈ block J, ∀ K' ∈ block J, K ≠ K' →
      ∀ t ∈ (centerQuotientImage L K').map ψ, orderOf t = 2 →
        CFSG.Assembly.IsComponentOf ((centerQuotientImage L K).map ψ)
          (centralizer ({t} : Set (sesqProjUnitary hU (stdHermForm hU n)))) := by
    intro K hK K' hK' hKK' t ht ht2
    obtain ⟨w, hw, rfl⟩ := ht
    rw [orderOf_injective ψ hψ] at ht2
    obtain ⟨t₀, ht₀K, ht₀2, rfl⟩ := exists_involution_lift_of_odd_center hodd hw ht2
    have h := (isComponentOf_map_iff hψ).2 (hloc K hK K' hK' hKK' t₀ ht₀K ht₀2).2
    rw [map_centralizer_singleton_of_injective hψ] at h
    exact isComponentOf_of_normal_inf hψrange h
  exact odd_projective_unitary_commuting_universal_pair_exclusion hU hp (V := Fin n → k)
    (by rw [Module.finrank_fin_fun]; omega) (stdHermForm_isSymm hU n)
    (stdHermForm_separatingLeft hU n)
    ⟨_, _, isQuasisimple_map_of_injective hψ (hπKq K₁ hK₁).1,
      isQuasisimple_map_of_injective hψ (hπKq K₂ hK₂).1,
      by rw [← Subgroup.map_commutator, (hcomm K₁ hK₁ K₂ hK₂ hne).2, Subgroup.map_bot],
      hfour K₁ hK₁, hfour K₂ hK₂, hlocal K₁ hK₁ K₂ hK₂ hne, hlocal K₂ hK₂ K₁ hK₁ (Ne.symm hne)⟩

end CFSG.LocalAnalysis.ComponentInitial
