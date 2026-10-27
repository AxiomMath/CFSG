module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGrModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalIso
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCKind
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelParamCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X]

theorem mem_normalizer_map_of_fieldAut {Ks : Subgroup X} {s : X}
    (hsN : s ∈ normalizer (Ks : Set X)) (hs2 : s * s = 1) {M : Type*} [Group M] (ψ : Ks ≃* M)
    (f : MulAut M) (hψθ : ∀ y, ψ (Ks.normalizerMonoidHom ⟨s, hsN⟩ y) = f (ψ y))
    {R₀ : Subgroup M} (hR₀ : ∀ r ∈ R₀, f r ∈ R₀) :
    s ∈ normalizer (((R₀.map ψ.symm.toMonoidHom).map Ks.subtype : Subgroup X) : Set X) := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hθapp : ∀ k : Ks, ((Ks.normalizerMonoidHom ⟨s, hsN⟩ k : Ks) : X) = s * k * s⁻¹ :=
    F4Pilot.coe_normalizerMonoidHom_mk_apply Ks hsN
  have hfwd : ∀ g : X, g ∈ (R₀.map ψ.symm.toMonoidHom).map Ks.subtype →
      s * g * s⁻¹ ∈ (R₀.map ψ.symm.toMonoidHom).map Ks.subtype := by
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    refine ⟨Ks.normalizerMonoidHom ⟨s, hsN⟩ (ψ.symm r), ⟨f r, hR₀ r hr, ?_⟩, ?_⟩
    · apply ψ.injective
      change ψ (ψ.symm (f r)) = ψ (Ks.normalizerMonoidHom ⟨s, hsN⟩ (ψ.symm r))
      rw [MulEquiv.apply_symm_apply, hψθ, MulEquiv.apply_symm_apply]
    · rw [Subgroup.subtype_apply, hθapp]
      rfl
  rw [mem_normalizer_iff]
  intro g
  refine ⟨hfwd g, fun h => ?_⟩
  have h1 := hfwd _ h
  have h2 : s * (s * g * s⁻¹) * s⁻¹ = g := by
    calc s * (s * g * s⁻¹) * s⁻¹ = (s * s) * g * (s⁻¹ * s⁻¹) := by group
      _ = g := by rw [hs2, hsi, hs2]; group
  rwa [h2] at h1

theorem facts_of_lieModel_four_four_of_fieldAut {K : Type} [Field K] (hK : Nat.card K = 2)
    {s : X} (hs : orderOf s = 2) {Lb : Subgroup X} (hLs : Lb ≤ centralizer ({s} : Set X))
    (hLq : CFSG.Open.IsQuasisimple Lb) (hLZ : center Lb = ⊥)
    (hCs : centralizer ({s} : Set X) ≤ Lb ⊔ zpowers s) {Ks : Subgroup X}
    (hsN : s ∈ normalizer (Ks : Set X)) (hsK : s ∉ Ks) (hLK : Lb ≤ Ks)
    (hKm : LieModel Ks .PSL 4 2 2) (φ : SpecialLinearGroup (Fin 4) K →* X) (hφ : φ.range = Lb) :
    (∃ R : Subgroup X, R ≤ Ks ∧ IsPGroup 2 R ∧ Nat.card R = 2 ^ 12 ∧
      s ∈ normalizer (R : Set X)) ∧
    (∀ z ∈ Ks, z * z = 1 → z ≠ 1 → ∃ k ∈ Ks, k * z * k⁻¹ ∈ Lb ∧
      ∃ R : Subgroup X, R ≤ Ks ∧ R ≤ centralizer ({k * z * k⁻¹} : Set X) ∧ IsPGroup 2 R ∧
        2 ^ 10 ≤ Nat.card R ∧ s ∈ normalizer (R : Set X)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hfixL : ∀ x ∈ Ks, x ∈ centralizer ({s} : Set X) → x ∈ Lb := by
    intro x hxK hxs
    rcases mem_or_mul_mem_of_centralizer_le_sup hs2 hLs hCs hxs with h | h
    · exact h
    · exfalso
      apply hsK
      have h1 : x⁻¹ * (x * s) = s := by group
      rw [← h1]
      exact mul_mem (inv_mem hxK) (hLK h)
  obtain ⟨F, _, _, hF, ⟨ψ₀⟩⟩ := exists_projectiveSL_equiv_of_lieModel_PSL hKm
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have : CharP F 2 := SeitzQ2.charTwo_of_natCard_eq_two_pow hF
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  obtain ⟨ι, σ, hσ1, hσσ, hfix⟩ := exists_subfield_involution (le_refl 1) hK1 hF
  have hσι : ∀ a, σ (ι a) = ι a := fun a => (hfix _).2 ⟨a, rfl⟩
  set θ := Ks.normalizerMonoidHom ⟨s, hsN⟩ with hθdef
  have hθ : θ * θ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one Ks hsN (by rw [sq]; exact hs2)
  have hne : φ.range ≠ ⊥ := hφ ▸ CFSG.SeitzReduction.ne_bot_of_isQuasisimple hLq
  obtain ⟨ε, hεinj, hεrange, -⟩ := SymplecticPilot.exists_projectiveSL_embedding_of_hom
    (by norm_num) φ hne (hφ ▸ hLZ) (hφ ▸ hLK)
  have hεθ : ε.range ≤ fixedSubgroup θ := by
    rw [hεrange, hφ, F4Pilot.fixedSubgroup_normalizerMonoidHom]
    intro x hx
    exact mem_subgroupOf.2 (hLs (mem_subgroupOf.1 hx))
  have hfixeq : (fixedSubgroup θ).map Ks.subtype = Lb := by
    rw [F4Pilot.map_fixedSubgroup_normalizerMonoidHom]
    refine le_antisymm (fun x hx => hfixL x (mem_inf.1 hx).1 (mem_inf.1 hx).2) ?_
    exact fun x hx => mem_inf.2 ⟨hLK hx, hLs hx⟩
  have hfixq : CFSG.Open.IsQuasisimple (fixedSubgroup θ) :=
    F4Pilot.isQuasisimple_open_of_mulEquiv
      ((MulEquiv.subgroupCongr hfixeq).symm.trans
        (equivMapOfInjective _ Ks.subtype Ks.subtype_injective).symm) hLq
  have htop : ε.range.subgroupOf (fixedSubgroup θ) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    rw [mem_subgroupOf, hεrange, hφ, mem_subgroupOf]
    exact hfixL _ (x : Ks).2 (mem_subgroupOf.1
      ((F4Pilot.fixedSubgroup_normalizerMonoidHom Ks hsN) ▸ x.2))
  have hcomp : IsComponent (ε.range.subgroupOf (fixedSubgroup θ)) := by
    rw [htop, CFSG.isComponent_iff_open]
    exact ⟨le_rfl, CFSG.Open.IsSubnormal.refl _,
      F4Pilot.isQuasisimple_open_of_mulEquiv Subgroup.topEquiv.symm hfixq⟩
  obtain ⟨ψ, hψε, hψθ⟩ := exists_mulEquiv_projMap_eq_of_isComponent (n := 4) (by norm_num)
    (f := 1) le_rfl hK1 ι hσ1 hσσ hfix ψ₀ hθ ε hεinj hεθ hcomp
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨hU2, hUc⟩ := isPGroup_projUnitriangular_four (F := F) hF4
    refine ⟨((projUnitriangular 4 F).map ψ.symm.toMonoidHom).map Ks.subtype, map_subtype_le _,
      (hU2.map _).map _, ?_, mem_normalizer_map_of_fieldAut hsN hs2 ψ (fieldAut 4 F σ) hψθ
        fun r hr => fieldAut_mem_projUnitriangular σ hr⟩
    rw [card_map_of_injective Ks.subtype_injective, card_map_of_injective ψ.symm.injective, hUc]
  ·
    intro z hzK hzz hz1
    set z' : Ks := ⟨z, hzK⟩ with hz'
    have hz'z : ψ z' * ψ z' = 1 := by
      rw [← map_mul]
      have h1 : z' * z' = 1 := Subtype.ext hzz
      rw [h1, map_one]
    have hz'1 : ψ z' ≠ 1 := by
      intro h1
      apply hz1
      have h2 : z' = 1 := ψ.injective (h1.trans (map_one ψ).symm)
      exact congrArg Subtype.val h2
    obtain ⟨c, z₀, R₀, hc, hR₀C, hR₀p, hR₀c, hR₀σ⟩ :=
      exists_conj_eq_projMap_of_mul_self_of_fieldAut hF4 ι hz'z hz'1
    set k' : Ks := ψ.symm c with hk'
    have hkz : k' * z' * k'⁻¹ = ε z₀ := by
      apply ψ.injective
      rw [map_mul, map_mul, map_inv, hk', MulEquiv.apply_symm_apply, hc, hψε]
    refine ⟨(k' : X), k'.2, ?_, ((R₀.map ψ.symm.toMonoidHom).map Ks.subtype), map_subtype_le _,
      ?_, (hR₀p.map _).map _, ?_,
      mem_normalizer_map_of_fieldAut hsN hs2 ψ (fieldAut 4 F σ) hψθ (hR₀σ σ hσι)⟩
    · have h1 : ((k' * z' * k'⁻¹ : Ks) : X) ∈ Lb := by
        rw [hkz]
        have h2 : ε z₀ ∈ ε.range := ⟨z₀, rfl⟩
        rw [hεrange, hφ] at h2
        exact mem_subgroupOf.1 h2
      exact h1
    · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hrc : r * projMap 4 ι z₀ = projMap 4 ι z₀ * r :=
        mem_centralizer_singleton_iff.1 (hR₀C hr)
      have h1 : ψ.symm r * (k' * z' * k'⁻¹) = (k' * z' * k'⁻¹) * ψ.symm r := by
        apply ψ.injective
        rw [hkz, map_mul, map_mul, hψε, MulEquiv.apply_symm_apply, hrc]
      exact congrArg Subtype.val h1
    · rw [card_map_of_injective Ks.subtype_injective, card_map_of_injective ψ.symm.injective]
      exact hR₀c

end CFSG.SeitzReduction.LinearPilot
