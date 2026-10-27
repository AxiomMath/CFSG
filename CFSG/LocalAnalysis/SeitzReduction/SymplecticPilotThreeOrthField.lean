module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOrthCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRoot
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrth

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg (sl2Upper)
open CFSG.SeitzReduction.LinearPilot (upperUnit diagUnit weylUnit coe_upperUnit subfieldSL
  twistedSubfield mem_twistedSubfield upperUnit_add upperUnit_inv upperUnit_mul_comm map_upperUnit
  map_weylUnit upperUnit_one_inv)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_le_centralizer
  normalizer_le_normalizer_centralizerPerfectCore)
open scoped MatrixGroups

section Swap

variable {K : Type} [Field K]

theorem upperUnit_eq_sl2Upper {R : Type} [Field R] (c : R) : upperUnit c = sl2Upper c :=
  Subtype.ext (by rw [coe_upperUnit]; rfl)

theorem siegDiag_eq_longBlock {n : ℕ} (p : Fin n) (c : K) :
    siegDiag K p c = longBlock K n p (upperUnit c) := by
  rw [upperUnit_eq_sl2Upper, longBlock_sl2Upper, elt_positiveLong_eq_upperUnipotentSp]
  rfl

@[expose] def swapOneTwo : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem conj_permSp_swapOneTwo_siegDiag (c : K) :
    permSp K swapOneTwo * siegDiag K (1 : Fin 3) c * (permSp K swapOneTwo)⁻¹ =
      siegDiag K (2 : Fin 3) c := by
  rw [siegDiag_eq_longBlock, siegDiag_eq_longBlock, conj_permSp_longBlock]
  rfl

theorem conj_permSp_swapOneTwo_diagSp (r : Kˣ) :
    permSp K swapOneTwo * diagSp K 3 ![r, 1, r] * (permSp K swapOneTwo)⁻¹ =
      diagSp K 3 ![r, r, 1] := by
  rw [conj_permSp_diagSp]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem diagSp_rr1_mem_leviTorusSp_zero (r : Kˣ) :
    diagSp K 3 ![r, r, 1] ∈ leviTorusSp K ({0} : Finset (Fin 3)) := by
  refine diagSp_mem_leviTorusSp fun j hj => ?_
  rw [Finset.mem_singleton] at hj
  subst hj
  exact ⟨fun _ => rfl, fun h => absurd h (by decide)⟩

theorem diagSp_rr1_mem_leviTorusSp_two (r : Kˣ) :
    diagSp K 3 ![r, r, 1] ∈ leviTorusSp K ({2} : Finset (Fin 3)) := by
  refine diagSp_mem_leviTorusSp fun j hj => ?_
  rw [Finset.mem_singleton] at hj
  subst hj
  exact ⟨fun h => absurd h (by decide), fun _ => rfl⟩

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def swapChart (e : L ≃* StatedSp 3 K) : L ≃* StatedSp 3 K :=
  e.trans (MulAut.conj (permSp K swapOneTwo)⁻¹)

theorem swapChart_symm_apply (e : L ≃* StatedSp 3 K) (y : StatedSp 3 K) :
    (swapChart e).symm y = e.symm (permSp K swapOneTwo * y * (permSp K swapOneTwo)⁻¹) := by
  rw [swapChart, MulEquiv.symm_trans_apply, MulAut.conj_symm_apply, inv_inv]

theorem swapChart_symm_siegDiag (e : L ≃* StatedSp 3 K) (c : K) :
    (swapChart e).symm (siegDiag K 1 c) = e.symm (siegDiag K 2 c) := by
  rw [swapChart_symm_apply, conj_permSp_swapOneTwo_siegDiag]

theorem modelToG_swapChart_threeTorus_le (e : L ≃* StatedSp 3 K) :
    modelToG (swapChart e) (threeTorus K) ≤
      modelToG e (leviTorusSp K ({0} : Finset (Fin 3))) ⊓
        modelToG e (leviTorusSp K ({2} : Finset (Fin 3))) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (UnitaryPilot.mem_modelToG _).1 hx
  obtain ⟨r, rfl⟩ := mem_threeTorus.1 hy
  rw [swapChart_symm_apply, conj_permSp_swapOneTwo_diagSp]
  exact ⟨UnitaryPilot.symm_mem_modelToG e (diagSp_rr1_mem_leviTorusSp_zero r),
    UnitaryPilot.symm_mem_modelToG e (diagSp_rr1_mem_leviTorusSp_two r)⟩

end Swap

section Orth

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F]

omit [Finite K] [CharP K 2] in
theorem simpleRootSL2_zero_le_complSp_two :
    simpleRootSL2 K (0 : Fin 3) ≤ complSp K (2 : Fin 3) := by
  rw [← spBlock_compl_singleton]
  exact simpleRootSL2_le_spBlock_compl (by decide) (fun _ => by decide)

theorem modelToG_simpleRootSL2_zero_le_centralizer_pieceCore_two_field
    (hset : SeitzSetting G L) (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {k : Fin 3} (hk : k ≠ 2) (P : FieldNeighbourParam e t ι σ k) :
    modelToG e (simpleRootSL2 K (0 : Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G) := by
  classical
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by norm_num) e)
  have hσι : ∀ c : K, σ.toRingHom (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  obtain ⟨ω, hω⟩ := LinearPilot.exists_trace_one_of_involution hσ1 hσσ
  have hFK : Nat.card F = Nat.card K ^ 2 := LinearPilot.natCard_eq_sq_of_trace_one ι hσσ hfix hω
  have hk1 : (2 : Fin 3).val + 1 < 3 → k.val ≠ (2 : Fin 3).val + 1 :=
    fun h => absurd h (by decide)
  have h2 : ¬ (2 : Fin 3).val + 1 < 3 := by decide
  set φ := P.rootHom hk hk1 with hφdef
  have hM : φ.range = pieceCore e ({2} : Finset (Fin 3)) := P.range_rootHom hk hk1 hK
  have hφι : ∀ A : SL(2, K),
      φ (SpecialLinearGroup.map ι A) = ((e.symm (longBlock K 3 2 A) : L) : G) := by
    intro A
    rw [hφdef, P.rootHom_map, simpleRootHom_of_not_lt h2]
  have hφσ : ∀ A : SL(2, F), t * φ A * t⁻¹ = φ (SpecialLinearGroup.map σ.toRingHom A) :=
    fun A => P.conj_rootHom hk hk1 A
  set z : G := ((e.symm (siegDiag K 2 1) : L) : G) with hzdef
  have hz : φ (upperUnit 1) = z := by
    have h := hφι (upperUnit 1)
    rw [map_upperUnit, map_one] at h
    rw [h, hzdef, siegDiag_eq_longBlock]
  set g : G := (φ (upperUnit ω))⁻¹ with hgdef
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hσω : t * φ (upperUnit ω) * t = φ (upperUnit ω * upperUnit 1) := by
    have h := hφσ (upperUnit ω)
    rw [htinv, map_upperUnit] at h
    rw [h, ← upperUnit_add]
    congr 2
  have hg : g⁻¹ * t * g = t * z := by
    rw [hgdef, inv_inv, ← hz]
    calc φ (upperUnit ω) * t * (φ (upperUnit ω))⁻¹
        = t * (t * φ (upperUnit ω) * t) * (φ (upperUnit ω))⁻¹ := by
          rw [show t * (t * φ (upperUnit ω) * t) * (φ (upperUnit ω))⁻¹ =
            (t * t) * φ (upperUnit ω) * t * (φ (upperUnit ω))⁻¹ by group, htt, one_mul]
      _ = t * φ (upperUnit 1) := by rw [hσω, upperUnit_mul_comm, map_mul]; group
  have hgz : g * z = z * g := by
    rw [hgdef, ← hz, ← map_inv, ← map_mul, ← map_mul, upperUnit_inv, upperUnit_mul_comm]
  set e₁ := swapChart e with he₁
  have hz₁ : ((e₁.symm (siegDiag K 1 1) : L) : G) = z := by
    rw [he₁, swapChart_symm_siegDiag]
  set φ' : StatedSp 3 K →* G :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (L.subtype.comp e₁.symm.toMonoidHom) with hφ'def
  have hφ' : Function.Injective φ' :=
    (MulAut.conj g⁻¹).injective.comp (L.subtype_injective.comp e₁.symm.injective)
  have hφ'r : φ'.range = CFSG.conjugate L g := by
    rw [hφ'def, MonoidHom.range_comp, EPilot.range_subtype_comp_mulEquiv_symm]
    rfl
  have hφ'z : φ' (siegDiag K 1 1) = ((e₁.symm (siegDiag K 1 1) : L) : G) := by
    rw [hz₁]
    change g⁻¹ * ((e₁.symm (siegDiag K 1 1) : L) : G) * g⁻¹⁻¹ = z
    rw [hz₁, ((show Commute g z from hgz).inv_left).eq, mul_inv_cancel_right]
  set j : SL(2, K) →* G :=
    φ.comp ((MulAut.conj (upperUnit ω)).toMonoidHom.comp (SpecialLinearGroup.map ι)) with hjdef
  have hj : ∀ s, j s = φ (upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹) :=
    fun s => rfl
  have hS : (twistedSubfield ι ω).map φ = j.range := by
    rw [hjdef, MonoidHom.range_comp, MonoidHom.range_comp]
    rfl
  have := LinearPilot.isSimpleGroup_specialLinearGroup_two (K := K) hK
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have hSt : j.range ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff, hg]
    set y := upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹ with hydef
    have hy : y ∈ twistedSubfield ι ω := (mem_twistedSubfield ι).2 ⟨s, rfl⟩
    have hfixed : (t * z) * φ y * (t * z)⁻¹ = φ y := by
      rw [← hz]
      calc t * φ (upperUnit 1) * φ y * (t * φ (upperUnit 1))⁻¹ =
            t * φ (upperUnit 1 * y * (upperUnit 1)⁻¹) * t⁻¹ := by
              simp only [map_mul, map_inv]
              group
        _ = φ (SpecialLinearGroup.map σ.toRingHom (upperUnit 1 * y * (upperUnit 1)⁻¹)) := hφσ _
        _ = φ (upperUnit 1 * SpecialLinearGroup.map σ.toRingHom y * upperUnit 1) := by
              congr 1
              rw [map_mul, map_mul, map_inv, map_upperUnit, map_one, upperUnit_one_inv]
        _ = φ y := by rw [LinearPilot.twistedSubfield_fixed ι σ.toRingHom hσι hω hy]
    rw [hj, ← hydef]
    rw [mul_inv_eq_iff_eq_mul] at hfixed
    exact hfixed.symm
  have hSY : j.range ≤ centralizer (modelToG e₁ (threeTorus K) : Set G) := by
    have h1 : j.range ≤ φ.range := by
      rintro _ ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    rw [hM] at h1
    exact h1.trans ((centralizerPerfectCore_le_centralizer _).trans
      (centralizer_le ((modelToG_swapChart_threeTorus_le e).trans inf_le_right)))
  have hzS : z ∈ j.range := ⟨upperUnit 1, by
    rw [hj, map_upperUnit, map_one, upperUnit_mul_comm, mul_inv_cancel_right, hz]⟩
  set B := modelToG e (simpleRootSL2 K (0 : Fin 3)) with hBdef
  have hBperf : ⁅B, B⁆ = B := by
    rw [hBdef, UnitaryPilot.modelToG_def, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      commutator_simpleRootSL2_eq_of_four_le hK 0]
  have hBL : B ≤ L := map_subtype_le _
  have hBA : B ≤ centralizer (modelToG e (longRootSp2 K 3 2) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e
      (simpleRootSL2_zero_le_complSp_two.trans (complSp_le_centralizer_longRootSp2 2))
  have hzA : z ∈ modelToG e (longRootSp2 K 3 2) :=
    UnitaryPilot.symm_mem_modelToG e (siegDiag_mem_longRootSp2 2 1)
  have hBz : B ≤ centralizer ({z} : Set G) :=
    hBA.trans (centralizer_le (Set.singleton_subset_iff.2 hzA))
  have hBY : B ≤ centralizer (modelToG e₁ (threeTorus K) : Set G) :=
    (UnitaryPilot.modelToG_le_centralizer e
      (simpleRootSL2_le_centralizer_leviTorusSp (Finset.mem_singleton_self 0))).trans
      (centralizer_le ((modelToG_swapChart_threeTorus_le e).trans inf_le_left))
  have hcore := le_centralizer_of_conj_eq_mul_three hset.standardSetting hOut hK e₁ htC ht
    (by rw [hz₁]; exact hg) hφ' hφ'r hφ'z (LinearPilot.commutator_range_eq_self_of_isPerfect j)
    (LinearPilot.eq_bot_or_eq_top_of_normal_range j) hSt hSY (by rw [hz₁]; exact hzS) hBperf
    hBL (by rw [hz₁]; exact hBz) hBY
  rw [le_centralizer_iff, ← hM, MonoidHom.range_eq_map,
    ← LinearPilot.sup_twistedSubfield_eq_top_of_trace_one ι hK hFK hσι hω, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    rw [hφι A]
    exact (le_centralizer_iff.1 hBA) (UnitaryPilot.symm_mem_modelToG e ⟨A, rfl⟩)
  · rw [hS]
    exact hcore

omit [Finite K] in
theorem pieceCore_zero_le_centralizer_pieceCore_two_of_le (hK : 4 ≤ Nat.card K)
    (e : L ≃* StatedSp 3 K) {t : G} (ι : K →+* F) {σ : F ≃+* F}
    (P₂ : FieldNeighbourParam e t ι σ 2)
    (hB : modelToG e (simpleRootSL2 K (0 : Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G)) :
    pieceCore e ({0} : Finset (Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G) := by
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hkj : (2 : Fin 3) ≠ 0 := by decide
  have hk1 : (0 : Fin 3).val + 1 < 3 → (2 : Fin 3).val ≠ (0 : Fin 3).val + 1 := fun _ => by decide
  set φ' := P₂.rootHom hkj hk1 with hφ'def
  set C := centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G) with hC
  have hφ'K : ∀ A : SL(2, K), φ' (SpecialLinearGroup.map ι A) ∈ C := fun A => by
    rw [hφ'def, P₂.rootHom_map]
    exact hB (UnitaryPilot.symm_mem_modelToG e ⟨A, rfl⟩)
  have htop : C.comap φ' = ⊤ := by
    refine LinearPilot.eq_top_of_upperUnit_one_mem_of_conj_mem ?_ ?_ ?_
    · have h := hφ'K (upperUnit 1)
      rwa [map_upperUnit, map_one] at h
    · have h := hφ'K weylUnit
      rwa [map_weylUnit] at h
    · intro α x hx
      change φ' (diagUnit α * x * (diagUnit α)⁻¹) ∈ C
      rw [map_mul, map_mul, map_inv]
      have hy : φ' (diagUnit α) ∈
          centralizer (modelToG e (leviTorusSp K ({2} : Finset (Fin 3))) : Set G) := by
        rw [mem_centralizer_iff]
        intro d hd
        obtain ⟨x', hx', rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hd
        obtain ⟨s, -, rfl⟩ := hx'
        exact (P₂.commute_rootHom_diagUnit hkj hk1 α s).eq.symm
      exact CFSG.EvenSmallLie.conj_mem_centralizer_of_mem_normalizer
        (normalizer_le_normalizer_centralizerPerfectCore _ (centralizer_le_normalizer _ hy)) hx
  rw [← P₂.range_rootHom hkj hk1 hK, MonoidHom.range_eq_map, ← htop]
  exact map_comap_le _ _

theorem commute_pieceCore_zero_two_field_three (hset : SeitzSetting G L) (hK : 4 ≤ Nat.card K)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {k : Fin 3} (hk : k ≠ 2)
    (P : FieldNeighbourParam e t ι σ k) (P₂ : FieldNeighbourParam e t ι σ 2) :
    ∀ a ∈ pieceCore e ({0} : Finset (Fin 3)), ∀ b ∈ pieceCore e ({2} : Finset (Fin 3)),
      Commute a b := by
  have h := pieceCore_zero_le_centralizer_pieceCore_two_of_le hK e ι P₂
    (modelToG_simpleRootSL2_zero_le_centralizer_pieceCore_two_field hset hK e htC ht ι hσ1 hσσ
      hfix hk P)
  intro a ha b hb
  exact (mem_centralizer_iff.1 (h ha) b hb).symm

theorem commute_pieceCore_zero_two_three (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (ι : K →+* F)
    {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hparam : ∀ k : Fin 3, Nonempty (FieldNeighbourParam e t ι σ k)) :
    ∀ a ∈ pieceCore e ({0} : Finset (Fin 3)), ∀ b ∈ pieceCore e ({2} : Finset (Fin 3)),
      Commute a b := by
  have hσ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  exact commute_pieceCore_zero_two_field_three hset ((LinearPilot.four_le_card_iff_two_le hKc).2 hf)
    e (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht ι hσ1 hσσ hfix (k := 0)
    (by decide) (hparam 0).some (hparam 2).some

end Orth

end CFSG.SeitzReduction.SymplecticPilot
