module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LULinear
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamField

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective spProjEquiv)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)

section Model

variable {m : ℕ} {F : Type} [Field F] [CharP F 2]

theorem fieldAut_spModelPSL (ρ : F ≃+* F) (x : StatedSp m F) :
    fieldAut (2 * m) F ρ (spModelPSL m F x) =
      spModelPSL m F (statedSpMap (ρ : F →+* F) m x) := by
  rw [spModelPSL_apply, fieldAut_proj, spModelPSL_apply]
  congr 1

theorem map_spBlockSwapGL (ρ : F ≃+* F) :
    Matrix.GeneralLinearGroup.map (ρ : F →+* F) (spBlockSwapGL m F) = spBlockSwapGL m F := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, coe_spBlockSwapGL,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ]
  simp only [Matrix.of_apply]
  split_ifs <;> simp

theorem fieldAut_mul_graph_eq (ρ : F ≃+* F) :
    fieldAut (2 * m) F ρ * (conjAut (2 * m) F (spBlockSwapGL m F) * dualAut (2 * m) F) =
      conjAut (2 * m) F (spBlockSwapGL m F) * dualAut (2 * m) F * fieldAut (2 * m) F ρ := by
  rw [← mul_assoc, LinearFlag.fieldAut_mul_conjAut, map_spBlockSwapGL, mul_assoc, mul_assoc,
    ← LinearFlag.dualAut_mul_fieldAut]

theorem conj_spModelPSL_mul_graph_eq [Finite F] (hm : 2 ≤ m) (y : StatedSp m F) :
    MulAut.conj (spModelPSL m F y) *
        (conjAut (2 * m) F (spBlockSwapGL m F) * dualAut (2 * m) F) =
      conjAut (2 * m) F (spBlockSwapGL m F) * dualAut (2 * m) F *
        MulAut.conj (spModelPSL m F y) := by
  rw [mulAut_mul_conj_eq_conj_apply_mul,
    conjAut_dualAut_spModelPSL hm coe_spBlockSwapGL y]

end Model

section Extension

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_mulAut_spModelPSL_comm_graph (hm : 3 ≤ m) (σ : K ≃+* F)
    (δ : MulAut (StatedSp m K)) :
    ∃ δ' : MulAut (projectiveSL (2 * m) F),
      (∀ g, δ' (spModelPSL m F (statedSpMap (σ : K →+* F) m g)) =
        spModelPSL m F (statedSpMap (σ : K →+* F) m (δ g))) ∧
      δ' * (conjAut (2 * m) F (spBlockSwapGL m F) * dualAut (2 * m) F) =
        conjAut (2 * m) F (spBlockSwapGL m F) * dualAut (2 * m) F * δ' := by
  obtain ⟨s, ρ₀, hδ⟩ := exists_eq_conj_mul_fieldSp hm δ
  set ρ' : F ≃+* F := (σ.symm.trans ρ₀).trans σ with hρ'
  have hρ'σ : (ρ' : F →+* F).comp (σ : K →+* F) = (σ : K →+* F).comp (ρ₀ : K →+* K) := by
    ext c
    simp [hρ']
  refine ⟨MulAut.conj (spModelPSL m F (statedSpMap (σ : K →+* F) m s)) * fieldAut (2 * m) F ρ',
    fun g => ?_, ?_⟩
  · rw [MulAut.mul_apply, fieldAut_spModelPSL, F4Pilot.statedSpMap_comp, hρ'σ,
      ← F4Pilot.statedSpMap_comp, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
      ← map_inv, ← map_mul, ← map_mul, hδ, MulAut.mul_apply, MulAut.conj_apply,
      F4Pilot.fieldSp_eq_statedSpMap]
  · rw [mul_assoc, fieldAut_mul_graph_eq, ← mul_assoc, conj_spModelPSL_mul_graph_eq (by omega),
      mul_assoc]

end Extension

section Normalize

variable {m f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_mulEquiv_spModelPSL_eq_comm (hm : 3 ≤ m)
    (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f) (σ : K ≃+* F) {M : Type} [Group M]
    (ψ : projectiveSL (2 * m) F ≃* M) {θ : MulAut M} (hθ : θ * θ = 1)
    (hθE : MulAut.congr ψ.symm θ ∉ semilinearAutGroup (2 * m) F)
    (hθfix : LieModel (fixedSubgroup θ) .PSp m 2 f) (ε : StatedSp m K →* M)
    (hε : Function.Injective ε) (hεr : ε.range = perfectCore (fixedSubgroup θ)) :
    ∃ ψ' : projectiveSL (2 * m) F ≃* M,
      (∀ g, ψ' (spModelPSL m F (statedSpMap (σ : K →+* F) m g)) = ε g) ∧
      ∀ x, θ (ψ' x) = ψ' ((conjAut (2 * m) F (spBlockSwapGL m F) * dualAut (2 * m) F) x) := by
  have hF4 : 4 ≤ Nat.card F := (LinearPilot.four_le_card_iff_two_le hF).2 hf
  set θ' := MulAut.congr ψ.symm θ with hθ'
  have hθ'app : ∀ y, θ' y = ψ.symm (θ (ψ y)) := fun _ => rfl
  have hθ'2 : θ' ^ 2 = 1 := by rw [sq, hθ', ← map_mul, hθ, map_one]
  have hθ'fix : LieModel (fixedSubgroup θ') .PSp m 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ψ.symm θ) hθfix
  obtain ⟨H, C, hC, hθ'HC⟩ := exists_conjAut_dualAut_normalForm (by omega : 3 ≤ 2 * m)
    (by omega : 1 ≤ f) hF hθ'2 hθE hθ'fix
  have hCJ : C = spBlockSwapGL m F := by
    rcases hC with h1 | ⟨r', hr', hJ⟩
    · exfalso
      have hfix' := hθ'fix
      rw [hθ'HC, ← LinearPilot.mulAut_congr_eq_mul] at hfix'
      exact not_lieModel_PSp_fixedSubgroup_dualAut_one (by omega) hF (by omega) (even_two_mul m)
        h1 (LieType.CurtisTits.lieModel_of_mulEquiv
          (fixedSubgroupCongrEquiv (conjAut (2 * m) F H) _).symm hfix')
    · obtain rfl : r' = m := by omega
      exact Units.ext (hJ.trans coe_spBlockSwapGL.symm)
  rw [hCJ] at hθ'HC
  set c := conjAut (2 * m) F H with hc
  set ψ₁ : projectiveSL (2 * m) F ≃* M := (c : projectiveSL (2 * m) F ≃* _).trans ψ with hψ₁
  have hψ₁app : ∀ x, ψ₁ x = ψ (c x) := fun _ => rfl
  have hθψ₁ : ∀ x, θ (ψ₁ x) =
      ψ₁ ((conjAut (2 * m) F (spBlockSwapGL m F) * dualAut (2 * m) F) x) := by
    intro x
    have h1 : θ' (c x) = c ((conjAut (2 * m) F (spBlockSwapGL m F) * dualAut (2 * m) F) x) := by
      rw [hθ'HC]
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rw [hθ'app] at h1
    rw [hψ₁app, hψ₁app, ← h1, MulEquiv.apply_symm_apply]
  have hfixθ : fixedSubgroup θ = (spModelPSL m F).range.map ψ₁.toMonoidHom := by
    rw [range_spModelPSL (by omega) hF (by omega) coe_spBlockSwapGL]
    ext y
    obtain ⟨x, rfl⟩ := ψ₁.surjective y
    rw [mem_map_equiv, ψ₁.symm_apply_apply]
    change θ (ψ₁ x) = ψ₁ x ↔
      (conjAut (2 * m) F (spBlockSwapGL m F) * dualAut (2 * m) F) x = x
    rw [hθψ₁]
    exact ψ₁.injective.eq_iff
  have htop : ⁅(⊤ : Subgroup (StatedSp m F)), (⊤ : Subgroup (StatedSp m F))⁆ = ⊤ := by
    have := isPerfect_statedSp_of_four_le hF4 m
    rw [← _root_.commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hperf : ⁅(spModelPSL m F).range.map ψ₁.toMonoidHom,
      (spModelPSL m F).range.map ψ₁.toMonoidHom⁆ =
        (spModelPSL m F).range.map ψ₁.toMonoidHom := by
    rw [← map_commutator, MonoidHom.range_eq_map, ← map_commutator, htop]
  have hrange : ε.range = (ψ₁.toMonoidHom.comp
      ((spModelPSL m F).comp (statedSpMap (σ : K →+* F) m))).range := by
    rw [hεr, hfixθ, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf, MonoidHom.range_comp,
      MonoidHom.range_comp, MonoidHom.range_eq_top.2 (statedSpMap_surjective σ),
      ← MonoidHom.range_eq_map]
  have hinj₁ : Function.Injective (ψ₁.toMonoidHom.comp
      ((spModelPSL m F).comp (statedSpMap (σ : K →+* F) m))) :=
    ψ₁.injective.comp ((spModelPSL_injective (by omega)).comp (statedSpMap_injective _ m))
  set δ₀ : MulAut (StatedSp m K) := ((MonoidHom.ofInjective hε).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hinj₁).symm with hδ₀def
  have hδ₀ : ∀ g, ψ₁ (spModelPSL m F (statedSpMap (σ : K →+* F) m (δ₀ g))) = ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hinj₁).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ', hδβ⟩ := exists_mulAut_spModelPSL_comm_graph hm σ δ₀
  refine ⟨δ'.trans ψ₁, fun g => ?_, fun x => ?_⟩
  · change ψ₁ (δ' (spModelPSL m F (statedSpMap (σ : K →+* F) m g))) = ε g
    rw [hδ', hδ₀]
  · change θ (ψ₁ (δ' x)) =
      ψ₁ (δ' ((conjAut (2 * m) F (spBlockSwapGL m F) * dualAut (2 * m) F) x))
    rw [hθψ₁]
    exact congrArg ψ₁ (DFunLike.congr_fun hδβ x).symm

end Normalize

section Fix

variable {X P : Type*} [Group X] [Group P] [Finite X] [Finite P]

theorem perfectCore_fixedSubgroup_eq_map_of_surjective (ρ : X →* P)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center X) {θ : MulAut X} {α : MulAut P}
    (hρθ : ∀ x, ρ (θ x) = α (ρ x)) :
    perfectCore (fixedSubgroup α) = (perfectCore (fixedSubgroup θ)).map ρ := by
  have hcomap : (fixedSubgroup α).comap ρ =
      LinearPilot.twistedFix (fun _ : Unit => θ) ρ.ker hker := by
    ext x
    rw [mem_comap, LinearPilot.mem_twistedFix]
    change α (ρ x) = ρ x ↔ ∀ _ : Unit, θ x * x⁻¹ ∈ ρ.ker
    rw [← hρθ]
    constructor
    · intro h _
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
    · intro h
      have h1 := h ()
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
  rw [← Subgroup.map_comap_eq_self_of_surjective hρ (fixedSubgroup α),
    ← CFSG.Quasithin.map_perfectCore, hcomap, LinearPilot.perfectCore_twistedFix,
    LinearPilot.fixAll_const_eq_fixedSubgroup]

end Fix

section Neighbour

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_normalized_neighbourCore_linearEven {m f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 3 ≤ m)
    (e : L ≃* StatedSp (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (m + 1)) {X : Subgroup G}
    (hX : X = modelToG e (rootTorusSp K k)) {D : Subgroup G} (hD : D = modelToG e (complSp K k))
    (h : HR8KindAtSp t m f X D .linearEven)
    (hN : t ∈ normalizer (F4Pilot.centralizerPerfectCore X : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (σ : K ≃+* F)
      (ρ : F4Pilot.centralizerPerfectCore X →* projectiveSL (2 * m) F),
      Nat.card F = 2 ^ f ∧ Function.Surjective ρ ∧
        ρ.ker ≤ center (F4Pilot.centralizerPerfectCore X) ∧ Odd (Nat.card ρ.ker) ∧
        (∀ (x : StatedSp m K) (y : F4Pilot.centralizerPerfectCore X),
          (y : G) = ((e.symm (complSpEquiv k x : complSp K k) : L) : G) →
            ρ y = spModelPSL m F (statedSpMap (σ : K →+* F) m x)) ∧
        ∀ y, ρ ((F4Pilot.centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y) =
          (conjAut (2 * m) F (spBlockSwapGL m F) * dualAut (2 * m) F) (ρ y) := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  set E := F4Pilot.centralizerPerfectCore X with hEdef
  set θ := E.normalizerMonoidHom ⟨t, hN⟩ with hθdef
  obtain ⟨S, _, ρ, τ, hρ, hker, hodd, hty, -, hρθ, hττ, hout, hfix⟩ :=
    exists_surjective_neighbourCore_linearUnitary hset hKc hf (by omega) e htC ht k hX hD
      (Or.inl rfl) h hN
  have hS : LieModel S .PSL (2 * m) 2 f := hty
  have hadm : StatedLieAdmissible .PSL (2 * m) 2 f := F4Pilot.statedLieAdmissible_of_lieModel hS
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hS
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  set εS : S ≃* projectiveSL (2 * m) F :=
    eJ.trans (CFSG.ComponentClassification.CatalogueBLinearHigherB.nativeEquiv (2 * m) F).symm
    with hεS
  set α : MulAut (projectiveSL (2 * m) F) := MulAut.congr εS τ with hα
  have hαα : α * α = 1 := by rw [hα, ← map_mul, hττ, map_one]
  have hα2 : α ^ 2 = 1 := by rw [_root_.sq]; exact hαα
  have hαo : α ∉ (MulAut.conj : projectiveSL (2 * m) F →* MulAut _).range :=
    fun h' => hout ((FixedFourGroup.congr_mem_inner_iff εS τ).1 h')
  have hαfix : LieModel (fixedSubgroup α) .PSp m 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv εS τ) hfix
  have hαE : α ∉ semilinearAutGroup (2 * m) F :=
    not_mem_semilinearAutGroup_of_lieModel_PSp (by omega) hadm.2.1 hF hα2 hαo hαfix
  set ρ' : E →* projectiveSL (2 * m) F := εS.toMonoidHom.comp ρ with hρ'def
  have hρ's : Function.Surjective ρ' := εS.surjective.comp hρ
  have hker' : ρ'.ker = ρ.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hρ'def, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  have hρ'α : ∀ y, ρ' (θ y) = α (ρ' y) := by
    intro y
    rw [hρ'def, MonoidHom.comp_apply, MonoidHom.comp_apply, hρθ]
    change εS (τ (ρ y)) = εS (τ (εS.symm (εS (ρ y))))
    rw [MulEquiv.symm_apply_apply]
  have hDE : ∀ x : StatedSp m K, ((e.symm (complSpEquiv k x : complSp K k) : L) : G) ∈ E := by
    intro x
    rw [hEdef, hX]
    exact modelToG_complSp_le_neighbourCore e hq (by omega) k
      (symm_mem_modelToG e (complSpEquiv k x).2)
  let ιD : StatedSp m K →* E :=
    ((L.subtype.comp e.symm.toMonoidHom).comp
      ((complSp K k).subtype.comp (complSpEquiv k).toMonoidHom)).codRestrict E hDE
  have hιD : ∀ x, ((ιD x : E) : G) = ((e.symm (complSpEquiv k x : complSp K k) : L) : G) :=
    fun _ => rfl
  have hιDinj : Function.Injective ιD := by
    intro x y hxy
    have h1 := congrArg (fun z : E => (z : G)) hxy
    simp only [hιD] at h1
    have h2 : e.symm ((complSpEquiv k x : complSp K k) : StatedSp (m + 1) K) =
        e.symm (complSpEquiv k y : complSp K k) := Subtype.ext h1
    exact (complSpEquiv k).injective (Subtype.ext (e.symm.injective h2))
  have hε₀inj : Function.Injective (ρ'.comp ιD) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxk : ιD x ∈ ρ'.ker := hx
    rw [hker'] at hxk
    have hz := hker hxk
    have hxc : x ∈ center (StatedSp m K) := by
      rw [mem_center_iff]
      intro g
      apply hιDinj
      rw [map_mul, map_mul]
      exact mem_center_iff.1 hz (ιD g)
    rw [center_statedSp_eq_bot m] at hxc
    exact Subgroup.mem_bot.1 hxc
  have hcoreG : perfectCore (E ⊓ centralizer ({t} : Set G)) = modelToG e (complSp K k) := by
    rw [hEdef, hX]
    exact perfectCore_neighbourCore_inf_centralizer_eq hset hKc hf (by omega) e htC ht k
  have hcore : perfectCore (fixedSubgroup θ) = ιD.range := by
    apply Subgroup.map_injective E.subtype_injective
    have hfixG : (fixedSubgroup θ).map E.subtype = E ⊓ centralizer ({t} : Set G) :=
      map_eqLocus_normalizerMonoidHom_eq hN
    rw [CFSG.Quasithin.map_perfectCore, hfixG, hcoreG]
    ext g
    constructor
    · intro hg
      obtain ⟨y, hy, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
      obtain ⟨x, hx⟩ := (complSpEquiv k).surjective ⟨y, hy⟩
      refine ⟨ιD x, ⟨x, rfl⟩, ?_⟩
      change ((ιD x : E) : G) = _
      rw [hιD, hx]
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact symm_mem_modelToG e (complSpEquiv k x).2
  have hρ'ker : ρ'.ker ≤ center E := by
    rw [hker']
    exact hker
  have hrange : (ρ'.comp ιD).range = perfectCore (fixedSubgroup α) := by
    rw [perfectCore_fixedSubgroup_eq_map_of_surjective ρ' hρ's hρ'ker hρ'α, hcore,
      MonoidHom.range_comp]
  have : Fintype K := Fintype.ofFinite K
  have : Fintype F := Fintype.ofFinite F
  set σ : K ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc, hF]) with hσ
  have hcongr : MulAut.congr (MulEquiv.refl (projectiveSL (2 * m) F)).symm α = α :=
    MulEquiv.ext fun _ => rfl
  obtain ⟨ψ', hψ'1, hψ'3⟩ := exists_mulEquiv_spModelPSL_eq_comm hm hf hF σ
    (MulEquiv.refl _) hαα (by rw [hcongr]; exact hαE) hαfix (ρ'.comp ιD) hε₀inj hrange
  have hkerψ : (ψ'.symm.toMonoidHom.comp ρ').ker = ρ.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hker']
  refine ⟨F, inferInstance, inferInstance, inferInstance, σ, ψ'.symm.toMonoidHom.comp ρ', hF,
    ψ'.symm.surjective.comp hρ's, hkerψ ▸ hker, hkerψ ▸ hodd, fun x y hy => ?_, fun y => ?_⟩
  · have hyx : y = ιD x := Subtype.ext (hy.trans (hιD x).symm)
    rw [hyx]
    change ψ'.symm ((ρ'.comp ιD) x) = _
    rw [← hψ'1 x, MulEquiv.symm_apply_apply]
  · change ψ'.symm (ρ' (θ y)) = _
    rw [hρ'α]
    have h1 := hψ'3 (ψ'.symm (ρ' y))
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1, MulEquiv.symm_apply_apply]
    rfl

end Neighbour

end CFSG.SeitzReduction.SymplecticPilot
