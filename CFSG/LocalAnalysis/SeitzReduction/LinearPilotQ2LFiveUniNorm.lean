module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveUniModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalIso
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCKind
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveNModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelParamCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X]

theorem exists_normalized_mulEquiv_of_lieModel_four_four {K : Type} [Field K]
    (hK : Nat.card K = 2) {s : X} (hs : orderOf s = 2) {Lb : Subgroup X}
    (hLs : Lb ≤ centralizer ({s} : Set X)) (hLq : CFSG.Open.IsQuasisimple Lb)
    (hLZ : center Lb = ⊥) (hCs : centralizer ({s} : Set X) ≤ Lb ⊔ zpowers s) {Ks : Subgroup X}
    (hsN : s ∈ normalizer (Ks : Set X)) (hsK : s ∉ Ks) (hLK : Lb ≤ Ks)
    (hKm : LieModel Ks .PSL 4 2 2) (φ : SpecialLinearGroup (Fin 4) K →* X) (hφ : φ.range = Lb) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (ι : K →+* F) (σ : F ≃+* F)
      (ψ : Ks ≃* projectiveSL 4 F), Nat.card F = 4 ∧ σ ≠ 1 ∧ (∀ x, σ (σ x) = x) ∧
      (∀ c, σ (ι c) = ι c) ∧ (∀ k : Ks, (k : X) ∈ Lb → ψ k ∈ (projMap 4 ι).range) ∧
      ∀ k : Ks, ψ (Ks.normalizerMonoidHom ⟨s, hsN⟩ k) = fieldAut 4 F σ (ψ k) := by
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
  refine ⟨F, inferInstance, inferInstance, inferInstance, ι, σ, ψ, hF4, hσ1, fun x => ?_, hσι,
    fun k hk => ?_, hψθ⟩
  · exact DFunLike.congr_fun hσσ x
  · have h1 : k ∈ ε.range := by
      rw [hεrange, hφ]
      exact mem_subgroupOf.2 hk
    obtain ⟨z, rfl⟩ := h1
    exact ⟨z, (hψε z).symm⟩

theorem exists_conj_projUnitriangular_le_of_card {K : Type} [Field K] (hK : Nat.card K = 2)
    {Q : Subgroup (projectiveSL 4 K)} (hQ : IsPGroup 2 Q) (hQc : 2 ^ 6 ≤ Nat.card Q) :
    ∃ h : projectiveSL 4 K, ∀ y ∈ projUnitriangular 4 K, h * y * h⁻¹ ∈ Q := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := SeitzQ2.charTwo_of_natCard_eq_two_pow (f := 1) (by rw [pow_one]; exact hK)
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (by norm_num : 1 ≤ 4)
  obtain ⟨P₁, hQP⟩ := hQ.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (projectiveSL 4 K) U₀ P₁
  have hUc : Nat.card (U₀ : Subgroup (projectiveSL 4 K)) = 2 ^ 6 := by
    rw [hU₀, card_projUnitriangular, hK]
  have hPc : Nat.card (P₁ : Subgroup (projectiveSL 4 K)) = 2 ^ 6 := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity U₀, hUc]
  have hQP' : Q = (P₁ : Subgroup (projectiveSL 4 K)) :=
    eq_of_le_of_card_ge hQP (by rw [hPc]; exact hQc)
  refine ⟨h, fun y hy => ?_⟩
  rw [hQP', ← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← map_inv, MulAut.smul_def, MulAut.conj_apply, hU₀]
  convert hy using 1
  group

theorem exists_inv_mul_mul_eq_one_of_fieldComponent [Finite X] {K : Type} [Field K]
    (hK : Nat.card K = 2) {s : X} (hs : orderOf s = 2) {Lb : Subgroup X}
    (hLs : Lb ≤ centralizer ({s} : Set X)) (hLq : CFSG.Open.IsQuasisimple Lb)
    (hLZ : center Lb = ⊥) (hCs : centralizer ({s} : Set X) ≤ Lb ⊔ zpowers s) {Ks : Subgroup X}
    (hsN : s ∈ normalizer (Ks : Set X)) (hsK : s ∉ Ks) (hLK : Lb ≤ Ks)
    (hKm : LieModel Ks .PSL 4 2 2) (φ : SpecialLinearGroup (Fin 4) K →* X) (hφ : φ.range = Lb)
    {S : Subgroup X} (hSK : S ≤ Ks) (hS2 : IsPGroup 2 S)
    (hmax : ∀ R : Subgroup X, IsPGroup 2 R → S ≤ R → R ≤ Ks → R = S) {Q : Subgroup X}
    (hQS : Q ≤ S) (hQs : Q ≤ centralizer ({s} : Set X)) (hQc : 2 ^ 6 ≤ Nat.card Q)
    {u : X} (huS : u ∈ S) (hu : u * s * (u * s) = 1) :
    ∃ v ∈ S, v⁻¹ * (u * s) * v * s⁻¹ = 1 := by
  classical
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  obtain ⟨F, _, _, _, ι, σ, ψ, hF4, hσ1, hσσ, hσι, hψL, hψθ⟩ :=
    exists_normalized_mulEquiv_of_lieModel_four_four hK hs hLs hLq hLZ hCs hsN hsK hLK hKm φ hφ
  set θ := Ks.normalizerMonoidHom ⟨s, hsN⟩ with hθdef
  have hθapp : ∀ k : Ks, ((θ k : Ks) : X) = s * k * s⁻¹ :=
    F4Pilot.coe_normalizerMonoidHom_mk_apply Ks hsN
  have hfixL : ∀ x ∈ Ks, x ∈ centralizer ({s} : Set X) → x ∈ Lb := by
    intro x hxK hxs
    rcases mem_or_mul_mem_of_centralizer_le_sup hs2 hLs hCs hxs with h | h
    · exact h
    · exfalso
      apply hsK
      have h1 : x⁻¹ * (x * s) = s := by group
      rw [← h1]
      exact mul_mem (inv_mem hxK) (hLK h)
  set Qψ : Subgroup (projectiveSL 4 F) := (Q.subgroupOf Ks).map ψ.toMonoidHom with hQψ
  set Q' : Subgroup (projectiveSL 4 K) := Qψ.comap (projMap 4 ι) with hQ'
  have hQψι : Qψ ≤ (projMap 4 ι).range := by
    rintro _ ⟨k, hk, rfl⟩
    exact hψL k (hfixL _ k.2 (hQs (mem_subgroupOf.1 hk)))
  have hQ'map : Q'.map (projMap 4 ι) = Qψ := map_comap_eq_self hQψι
  have hinjι : Function.Injective (projMap 4 ι) := projMap_injective (by norm_num) ι
  have hQ'c : 2 ^ 6 ≤ Nat.card Q' := by
    have h1 : Nat.card Q' = Nat.card Qψ := by rw [← hQ'map, card_map_of_injective hinjι]
    have h2 : Nat.card Qψ = Nat.card Q := by
      rw [hQψ, card_map_of_injective ψ.injective]
      exact Nat.card_congr (subgroupOfEquivOfLe (hQS.trans hSK)).toEquiv
    rw [h1, h2]
    exact hQc
  have hQ'2 : IsPGroup 2 Q' :=
    (((hS2.to_le hQS).comap_subtype (K := Ks)).map ψ.toMonoidHom).comap_of_injective _ hinjι
  obtain ⟨h, hh⟩ := exists_conj_projUnitriangular_le_of_card hK hQ'2 hQ'c
  set g := projMap 4 ι h with hgdef
  have hσg : fieldAut 4 F σ g = g := fieldAut_projMap ι hσι h
  set Sψ : Subgroup (projectiveSL 4 F) := (S.subgroupOf Ks).map ψ.toMonoidHom with hSψ
  have hSψ2 : IsPGroup 2 Sψ := (hS2.comap_subtype (K := Ks)).map _
  have hconjU : ∀ x ∈ Sψ, g⁻¹ * x * g ∈ projUnitriangular 4 F := by
    have hP' := le_projUnitriangular_of_isPGroup (F := F) (n := 4) (by rw [hF4]; norm_num)
      isPGroup_scalars_four (hSψ2.map (MulAut.conj g⁻¹).toMonoidHom) (fun i j hij hij1 => by
        have hlt : i < j := Fin.lt_def.2 (by omega)
        have h1 := hh _ (proj_transvection_mem_projUnitriangular hlt (1 : K))
        have h2 : projMap 4 ι (h * proj 4 K (SpecialLinearGroup.transvection hlt.ne 1) * h⁻¹) ∈
            Sψ := by
          have h3 : projMap 4 ι (h * proj 4 K (SpecialLinearGroup.transvection hlt.ne 1) * h⁻¹)
              ∈ Qψ := h1
          rw [hQψ] at h3
          obtain ⟨k, hk, hk'⟩ := h3
          exact ⟨k, mem_subgroupOf.2 (hQS (mem_subgroupOf.1 hk)), hk'⟩
        rw [map_mul, map_mul, map_inv, ← hgdef, projMap_proj, specialLinearGroup_map_transvection,
          map_one] at h2
        refine ⟨_, h2, ?_⟩
        change MulAut.conj g⁻¹ _ = _
        rw [MulAut.conj_apply]
        group)
    intro x hx
    have h1 : MulAut.conj g⁻¹ x ∈ projUnitriangular 4 F := hP' ⟨x, hx, rfl⟩
    rw [MulAut.conj_apply, inv_inv] at h1
    exact h1
  set R : Subgroup X := (((projUnitriangular 4 F).map (MulAut.conj g).toMonoidHom).map
    ψ.symm.toMonoidHom).map Ks.subtype with hR
  have hR2 : IsPGroup 2 R := ((((isPGroup_projUnitriangular_four hF4).1.map _).map _).map _)
  have hSR : S ≤ R := by
    intro x hx
    have hxK := hSK hx
    have h1 : g⁻¹ * ψ ⟨x, hxK⟩ * g ∈ projUnitriangular 4 F :=
      hconjU _ ⟨⟨x, hxK⟩, mem_subgroupOf.2 hx, rfl⟩
    refine ⟨⟨x, hxK⟩, ⟨ψ ⟨x, hxK⟩, ⟨g⁻¹ * ψ ⟨x, hxK⟩ * g, h1, ?_⟩, ?_⟩, rfl⟩
    · change MulAut.conj g _ = _
      rw [MulAut.conj_apply]
      group
    · change ψ.symm (ψ ⟨x, hxK⟩) = _
      rw [MulEquiv.symm_apply_apply]
  have hRS : R = S := hmax R hR2 hSR (map_subtype_le _)
  set uK : Ks := ⟨u, hSK huS⟩ with huK
  have huθ : uK * θ uK = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hθapp, Subgroup.coe_one, hsi]
    calc u * (s * u * s) = u * s * (u * s) := by group
      _ = 1 := hu
  have hx1 : ψ uK * fieldAut 4 F σ (ψ uK) = 1 := by
    rw [← hψθ, ← map_mul, huθ, map_one]
  set x' := g⁻¹ * ψ uK * g with hx'
  have hx'U : x' ∈ projUnitriangular 4 F := hconjU _ ⟨uK, mem_subgroupOf.2 huS, rfl⟩
  have hx'c : x' * fieldAut 4 F σ x' = 1 := by
    rw [hx', map_mul, map_mul, map_inv, hσg]
    calc g⁻¹ * ψ uK * g * (g⁻¹ * fieldAut 4 F σ (ψ uK) * g) =
          g⁻¹ * (ψ uK * fieldAut 4 F σ (ψ uK)) * g := by group
      _ = 1 := by rw [hx1]; group
  obtain ⟨β, hβ⟩ := exists_add_fieldAut_eq_one hσ1 hσσ
  obtain ⟨y', hy'U, hy'⟩ := exists_inv_mul_mul_fieldAut_eq_one hσσ hβ hx'U hx'c
  set y := g * y' * g⁻¹ with hy
  have hyR : ((ψ.symm y : Ks) : X) ∈ R := ⟨ψ.symm y, ⟨y, ⟨y', hy'U, rfl⟩, rfl⟩, rfl⟩
  rw [hRS] at hyR
  refine ⟨_, hyR, ?_⟩
  have hkey : (ψ.symm y)⁻¹ * uK * θ (ψ.symm y) = 1 := by
    apply ψ.injective
    rw [map_mul, map_mul, map_inv, hψθ, MulEquiv.apply_symm_apply, map_one, hy, map_mul,
      map_mul, map_inv, hσg]
    calc (g * y' * g⁻¹)⁻¹ * ψ uK * (g * fieldAut 4 F σ y' * g⁻¹) =
          g * (y'⁻¹ * x' * fieldAut 4 F σ y') * g⁻¹ := by rw [hx']; group
      _ = 1 := by rw [hy']; group
  have h1 := congrArg (fun k : Ks => (k : X)) hkey
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hθapp, Subgroup.coe_one] at h1
  calc ((ψ.symm y : Ks) : X)⁻¹ * (u * s) * ((ψ.symm y : Ks) : X) * s⁻¹ =
        ((ψ.symm y : Ks) : X)⁻¹ * u * (s * ((ψ.symm y : Ks) : X) * s⁻¹) := by group
    _ = 1 := h1

end CFSG.SeitzReduction.LinearPilot
