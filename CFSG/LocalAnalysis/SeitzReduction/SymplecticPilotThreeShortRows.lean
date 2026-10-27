module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeShortOrient

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt)
open CFSG.SeitzReduction.LinearPilot (upperUnit diagUnit weylUnit coe_upperUnit subfieldSL
  twistedSubfield mem_twistedSubfield upperUnit_add upperUnit_inv upperUnit_mul_comm map_upperUnit
  upperUnit_one_inv twistedDiagSL2 diagSL2)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_le_centralizer)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] [CharP K 2] in
theorem modelToG_simpleRootSL2_zero_le_centralizer_longRootSp2_two (e : L ≃* StatedSp 3 K) :
    modelToG e (simpleRootSL2 K (0 : Fin 3)) ≤
      centralizer (modelToG e (longRootSp2 K 3 (2 : Fin 3)) : Set G) :=
  UnitaryPilot.modelToG_le_centralizer e
    (simpleRootSL2_zero_le_complSp_two.trans fun _ hb => mem_centralizer_iff.2 fun _ ha =>
      (commute_of_mem_longRootSp2_of_mem_complSp ha hb).eq)

omit [Finite G] [Finite K] [CharP K 2] in
theorem pieceCore_zero_le_centralizer_inf (e : L ≃* StatedSp 3 K) :
    pieceCore e ({0} : Finset (Fin 3)) ≤
      centralizer ((modelToG e (leviTorusSp K ({0} : Finset (Fin 3))) ⊓
        modelToG e (leviTorusSp K ({2} : Finset (Fin 3))) : Subgroup G) : Set G) :=
  (centralizerPerfectCore_le_centralizer _).trans (centralizer_le inf_le_left)

omit [Finite K] [CharP K 2] in
theorem elt_difference_zero_one_eq :
    (elt (.difference 0 1 (by decide)) (1 : K) : StatedSp 3 K) =
      simpleRootHom K (0 : Fin 3) (upperUnit 1) :=
  simpleRootHom_zero_upperUnit_one.symm

theorem range_le_centralizer_longRootSp2_two_of_field {F : Type} [Field F] [Finite F]
    (hset : SeitzSetting G L) (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {ψ : SL(2, F) →* G} (hψ : ψ.range ≤ pieceCore e ({0} : Finset (Fin 3)))
    (hψι : ∀ A : SL(2, K),
      ψ (SpecialLinearGroup.map ι A) = ((e.symm (simpleRootHom K (0 : Fin 3) A) : L) : G))
    (hψσ : ∀ A : SL(2, F), t * ψ A * t⁻¹ = ψ (SpecialLinearGroup.map σ.toRingHom A)) :
    ψ.range ≤ centralizer (modelToG e (longRootSp2 K 3 (2 : Fin 3)) : Set G) := by
  classical
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by norm_num) e)
  have hσι : ∀ c : K, σ.toRingHom (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  obtain ⟨ω, hω⟩ := LinearPilot.exists_trace_one_of_involution hσ1 hσσ
  have hFK : Nat.card F = Nat.card K ^ 2 := LinearPilot.natCard_eq_sq_of_trace_one ι hσσ hfix hω
  set x : StatedSp 3 K := elt (.difference 0 1 (by decide)) 1 with hxdef
  set z : G := ((e.symm x : L) : G) with hzdef
  have hz : ψ (upperUnit 1) = z := by
    have h := hψι (upperUnit 1)
    rw [map_upperUnit, map_one] at h
    rw [h, hzdef, hxdef, elt_difference_zero_one_eq]
  set g : G := (ψ (upperUnit ω))⁻¹ with hgdef
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hσω : t * ψ (upperUnit ω) * t = ψ (upperUnit ω * upperUnit 1) := by
    have h := hψσ (upperUnit ω)
    rw [htinv, map_upperUnit] at h
    rw [h, ← upperUnit_add]
    congr 2
  have hg : g⁻¹ * t * g = t * z := by
    rw [hgdef, inv_inv, ← hz]
    calc ψ (upperUnit ω) * t * (ψ (upperUnit ω))⁻¹
        = t * (t * ψ (upperUnit ω) * t) * (ψ (upperUnit ω))⁻¹ := by
          rw [show t * (t * ψ (upperUnit ω) * t) * (ψ (upperUnit ω))⁻¹ =
            (t * t) * ψ (upperUnit ω) * t * (ψ (upperUnit ω))⁻¹ by group, htt, one_mul]
      _ = t * ψ (upperUnit 1) := by rw [hσω, upperUnit_mul_comm, map_mul]; group
  have hgz : g * z = z * g := by
    rw [hgdef, ← hz, ← map_inv, ← map_mul, ← map_mul, upperUnit_inv, upperUnit_mul_comm]
  set φ' : StatedSp 3 K →* G :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom) with hφ'def
  have hφ' : Function.Injective φ' :=
    (MulAut.conj g⁻¹).injective.comp (L.subtype_injective.comp e.symm.injective)
  have hφ'r : φ'.range = CFSG.conjugate L g := by
    rw [hφ'def, MonoidHom.range_comp, EPilot.range_subtype_comp_mulEquiv_symm]
    rfl
  have hφ'z : φ' x = ((e.symm x : L) : G) := by
    change g⁻¹ * ((e.symm x : L) : G) * g⁻¹⁻¹ = z
    rw [← hzdef, ((show Commute g z from hgz).inv_left).eq, mul_inv_cancel_right]
  set j : SL(2, K) →* G :=
    ψ.comp ((MulAut.conj (upperUnit ω)).toMonoidHom.comp (SpecialLinearGroup.map ι)) with hjdef
  have hj : ∀ s, j s = ψ (upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹) :=
    fun s => rfl
  have hS : (twistedSubfield ι ω).map ψ = j.range := by
    rw [hjdef, MonoidHom.range_comp, MonoidHom.range_comp]
    rfl
  have := LinearPilot.isSimpleGroup_specialLinearGroup_two (K := K) hK
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have hSt : j.range ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff, hg]
    set y := upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹ with hydef
    have hy : y ∈ twistedSubfield ι ω := (mem_twistedSubfield ι).2 ⟨s, rfl⟩
    have hfixed : (t * z) * ψ y * (t * z)⁻¹ = ψ y := by
      rw [← hz]
      calc t * ψ (upperUnit 1) * ψ y * (t * ψ (upperUnit 1))⁻¹ =
            t * ψ (upperUnit 1 * y * (upperUnit 1)⁻¹) * t⁻¹ := by
              simp only [map_mul, map_inv]
              group
        _ = ψ (SpecialLinearGroup.map σ.toRingHom (upperUnit 1 * y * (upperUnit 1)⁻¹)) := hψσ _
        _ = ψ (upperUnit 1 * SpecialLinearGroup.map σ.toRingHom y * upperUnit 1) := by
              congr 1
              rw [map_mul, map_mul, map_inv, map_upperUnit, map_one, upperUnit_one_inv]
        _ = ψ y := by rw [LinearPilot.twistedSubfield_fixed ι σ.toRingHom hσι hω hy]
    rw [hj, ← hydef]
    rw [mul_inv_eq_iff_eq_mul] at hfixed
    exact hfixed.symm
  have hSY : j.range ≤ centralizer ((modelToG e (leviTorusSp K ({0} : Finset (Fin 3))) ⊓
      modelToG e (leviTorusSp K ({2} : Finset (Fin 3))) : Subgroup G) : Set G) := by
    have h1 : j.range ≤ ψ.range := by
      rintro _ ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    exact h1.trans (hψ.trans (pieceCore_zero_le_centralizer_inf e))
  have hzS : z ∈ j.range := ⟨upperUnit 1, by
    rw [hj, map_upperUnit, map_one, upperUnit_mul_comm, mul_inv_cancel_right, hz]⟩
  have hcore := le_centralizer_of_conj_eq_mul_three_short_zero_two hset.standardSetting hOut hK e
    htC ht hg hφ' hφ'r hφ'z (LinearPilot.commutator_range_eq_self_of_isPerfect j)
    (LinearPilot.eq_bot_or_eq_top_of_normal_range j) hSt hSY hzS
  rw [MonoidHom.range_eq_map, ← LinearPilot.sup_twistedSubfield_eq_top_of_trace_one ι hK hFK hσι hω,
    Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    rw [hψι A]
    exact modelToG_simpleRootSL2_zero_le_centralizer_longRootSp2_two e
      (UnitaryPilot.symm_mem_modelToG e ⟨A, rfl⟩)
  · rw [hS]
    exact hcore

theorem range_le_centralizer_longRootSp2_two_of_swap (hset : SeitzSetting G L)
    (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {ψ : SL(2, K) × SL(2, K) →* G}
    (hψ : ψ.range ≤ pieceCore e ({0} : Finset (Fin 3)))
    (hψΔ : ∀ A : SL(2, K), ψ (A, A) = ((e.symm (simpleRootHom K (0 : Fin 3) A) : L) : G))
    (hψt : ∀ p : SL(2, K) × SL(2, K), t * ψ p * t⁻¹ = ψ p.swap) :
    ψ.range ≤ centralizer (modelToG e (longRootSp2 K 3 (2 : Fin 3)) : Set G) := by
  classical
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by norm_num) e)
  set u : SL(2, K) × SL(2, K) := (upperUnit 1, upperUnit 1) with hudef
  set x : StatedSp 3 K := elt (.difference 0 1 (by decide)) 1 with hxdef
  set z : G := ((e.symm x : L) : G) with hzdef
  have hz : ψ u = z := by rw [hudef, hψΔ, hzdef, hxdef, elt_difference_zero_one_eq]
  set g : G := ψ (upperUnit 1, 1) with hgdef
  have hgg : g * g = 1 := by
    rw [hgdef, ← map_mul, Prod.mk_mul_mk, mul_one, ← LinearPilot.upperUnit_add,
      CharTwo.add_self_eq_zero, LinearPilot.upperUnit_zero]
    exact map_one ψ
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hg : g⁻¹ * t * g = t * z := by
    have htg : t * g * t⁻¹ = ψ (1, upperUnit 1) := hψt _
    have hzt : z * t = t * z := mem_centralizer_iff.1 htC z (e.symm _).2
    calc g⁻¹ * t * g = g * (t * g * t⁻¹) * t := by rw [hginv]; group
      _ = z * t := by
          rw [htg, hgdef, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, ← hz]
      _ = t * z := hzt
  have hgz : g * z = z * g := by
    rw [hgdef, ← hz, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one]
  set φ' : StatedSp 3 K →* G :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom) with hφ'def
  have hφ' : Function.Injective φ' :=
    (MulAut.conj g⁻¹).injective.comp (L.subtype_injective.comp e.symm.injective)
  have hφ'r : φ'.range = CFSG.conjugate L g := by
    rw [hφ'def, MonoidHom.range_comp, EPilot.range_subtype_comp_mulEquiv_symm]
    rfl
  have hφ'z : φ' x = ((e.symm x : L) : G) := by
    change g⁻¹ * ((e.symm x : L) : G) * g⁻¹⁻¹ = z
    rw [← hzdef, ((show Commute g z from hgz).inv_left).eq, mul_inv_cancel_right]
  obtain ⟨θ⟩ := LinearPilot.nonempty_mulEquiv_twistedDiagSL2 (K := K)
  set j : SL(2, K) →* G := ψ.comp ((twistedDiagSL2 K).subtype.comp θ.toMonoidHom) with hjdef
  have hj : ∀ s, j s = ψ (θ s : twistedDiagSL2 K) := fun s => rfl
  have hjmem : ∀ p ∈ twistedDiagSL2 K, ψ p ∈ j.range := fun p hp =>
    ⟨θ.symm ⟨p, hp⟩, by rw [hj, MulEquiv.apply_symm_apply]⟩
  have hS : (twistedDiagSL2 K).map ψ = j.range := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hjmem p hp
    · rintro ⟨s, rfl⟩
      exact ⟨_, (θ s).2, rfl⟩
  have := LinearPilot.isSimpleGroup_specialLinearGroup_two (K := K) hK
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have hfixed : ∀ p ∈ twistedDiagSL2 K, (t * z) * ψ p * (t * z)⁻¹ = ψ p := by
    intro p hp
    rw [← hz]
    calc t * ψ u * ψ p * (t * ψ u)⁻¹ = t * ψ (u * p * u⁻¹) * t⁻¹ := by
          simp only [map_mul, map_inv]
          group
      _ = ψ (u * p * u⁻¹).swap := hψt _
      _ = ψ p := by rw [hudef, LinearPilot.twistedDiagSL2_fixed hp]
  have hSt : j.range ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff, hg]
    have h' := hfixed _ (θ s).2
    rw [mul_inv_eq_iff_eq_mul] at h'
    exact h'.symm
  have hSY : j.range ≤ centralizer ((modelToG e (leviTorusSp K ({0} : Finset (Fin 3))) ⊓
      modelToG e (leviTorusSp K ({2} : Finset (Fin 3))) : Subgroup G) : Set G) := by
    have h1 : j.range ≤ ψ.range := by
      rintro _ ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    exact h1.trans (hψ.trans (pieceCore_zero_le_centralizer_inf e))
  have hzS : z ∈ j.range := hz ▸ hjmem u LinearPilot.upperUnit_one_pair_mem_twistedDiagSL2
  have hcore := le_centralizer_of_conj_eq_mul_three_short_zero_two hset.standardSetting hOut hK e
    htC ht hg hφ' hφ'r hφ'z (LinearPilot.commutator_range_eq_self_of_isPerfect j)
    (LinearPilot.eq_bot_or_eq_top_of_normal_range j) hSt hSY hzS
  rw [MonoidHom.range_eq_map, ← LinearPilot.diag_sup_twistedDiag_eq_top hK, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    change ψ (A, A) ∈ _
    rw [hψΔ A]
    exact modelToG_simpleRootSL2_zero_le_centralizer_longRootSp2_two e
      (UnitaryPilot.symm_mem_modelToG e ⟨A, rfl⟩)
  · rw [hS]
    exact hcore

end CFSG.SeitzReduction.SymplecticPilot
