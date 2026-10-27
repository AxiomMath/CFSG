module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOdd

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open scoped MatrixGroups

section Graph

variable {m : ℕ} {F : Type} [Field F] [CharP F 2]

theorem ctGraph_map_ringEquiv (ρ : F ≃+* F) (x : SpecialLinearGroup (Fin (2 * m + 1)) F) :
    ctGraph 1 (SpecialLinearGroup.map ρ.toRingHom x) =
      SpecialLinearGroup.map ρ.toRingHom (ctGraph 1 x) := by
  apply Subtype.ext
  ext a b
  rw [coe_ctGraph, q2GramMat_mul_mul_apply, transpose_apply, ← map_inv]
  change _ = ρ.toRingHom (((ctGraph 1 x : SpecialLinearGroup (Fin (2 * m + 1)) F) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) F) a b)
  rw [coe_ctGraph, q2GramMat_mul_mul_apply, transpose_apply]
  rfl

theorem ctGraphPSL_fieldAut (ρ : F ≃+* F) (z : projectiveSL (2 * m + 1) F) :
    ctGraphPSL m F (fieldAut (2 * m + 1) F ρ z) = fieldAut (2 * m + 1) F ρ (ctGraphPSL m F z) := by
  obtain ⟨x, rfl⟩ := proj_surjective (2 * m + 1) F z
  rw [fieldAut_proj, ctGraphPSL_proj, ctGraphPSL_proj, fieldAut_proj, ctGraph_map_ringEquiv]

theorem ctGraphPSL_ctOddPSL (y : StatedSp m F) :
    ctGraphPSL m F (ctOddPSL m F y) = ctOddPSL m F y := by
  rw [ctOddPSL_apply, ctGraphPSL_proj, ctGraph_ctEmbed]

theorem exists_mulAut_ctOddPSL_of_eq_graph {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* F) {δ : MulAut (StatedSp m K)} (s : StatedSp m K) (ρ₀ : K ≃+* K)
    (hδ : δ = MulAut.conj s * fieldSp m K ρ₀) :
    ∃ δ' : MulAut (projectiveSL (2 * m + 1) F),
      (∀ g, δ' (ctOddPSL m F (statedSpMap (σ : K →+* F) m g)) =
        ctOddPSL m F (statedSpMap (σ : K →+* F) m (δ g))) ∧
      ∀ z, δ' (ctGraphPSL m F z) = ctGraphPSL m F (δ' z) := by
  set ρ' : F ≃+* F := (σ.symm.trans ρ₀).trans σ with hρ'
  have hρ'σ : (ρ' : F →+* F).comp (σ : K →+* F) = (σ : K →+* F).comp (ρ₀ : K →+* K) := by
    ext c
    simp [hρ']
  set c := ctOddPSL m F (statedSpMap (σ : K →+* F) m s) with hc
  refine ⟨MulAut.conj c * fieldAut (2 * m + 1) F ρ', fun g => ?_, fun z => ?_⟩
  · rw [MulAut.mul_apply, fieldAut_ctOddPSL, F4Pilot.statedSpMap_comp, hρ'σ,
      ← F4Pilot.statedSpMap_comp, MulAut.conj_apply, hc, ← map_inv, ← map_mul, ← map_mul,
      ← map_inv, ← map_mul, ← map_mul, hδ, MulAut.mul_apply, MulAut.conj_apply,
      F4Pilot.fieldSp_eq_statedSpMap]
  · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
      map_mul, map_inv, hc, ctGraphPSL_ctOddPSL, ctGraphPSL_fieldAut]

end Graph

section Normal

variable {m : ℕ} {F : Type} [Field F] [CharP F 2]

theorem exists_mulEquiv_ctOddPSL_comp_eq_graph [Finite F]
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hm : 1 ≤ m) (hf : 2 ≤ f)
    (hF : Nat.card F = 2 ^ f) (σ : K ≃+* F) {M : Type} [Group M]
    (ψ : projectiveSL (2 * m + 1) F ≃* M) {θ : MulAut M} (hθ : θ * θ = 1)
    (hθE : MulAut.congr ψ.symm θ ∉ semilinearAutGroup (2 * m + 1) F)
    (hθfix : LieModel (fixedSubgroup θ) .PSp m 2 f) (ε : StatedSp m K →* M)
    (hε : Function.Injective ε) (hεr : ε.range = perfectCore (fixedSubgroup θ)) :
    ∃ (ψ₁ : projectiveSL (2 * m + 1) F ≃* M) (δ₀ : MulAut (StatedSp m K)),
      (∀ g, ψ₁ (ctOddPSL m F (statedSpMap (σ : K →+* F) m (δ₀ g))) = ε g) ∧
        ∀ x, θ (ψ₁ x) = ψ₁ (ctGraphPSL m F x) := by
  have hF4 : 4 ≤ Nat.card F := (LinearPilot.four_le_card_iff_two_le hF).2 hf
  set θ' := MulAut.congr ψ.symm θ with hθ'
  have hθ'app : ∀ y, θ' y = ψ.symm (θ (ψ y)) := fun _ => rfl
  have hθ'2 : θ' ^ 2 = 1 := by rw [sq, hθ', ← map_mul, hθ, map_one]
  have hθ'fix : LieModel (fixedSubgroup θ') .PSp m 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ψ.symm θ) hθfix
  obtain ⟨H, hθ'H⟩ := exists_conjAut_eq_ctGraphPSL (by omega) (by omega : 1 ≤ f) hF hθ'2 hθE
    hθ'fix
  set c := conjAut (2 * m + 1) F H with hc
  set ψ₁ : projectiveSL (2 * m + 1) F ≃* M := (c : projectiveSL (2 * m + 1) F ≃* _).trans ψ
    with hψ₁
  have hψ₁app : ∀ x, ψ₁ x = ψ (c x) := fun _ => rfl
  have hθψ₁ : ∀ x, θ (ψ₁ x) = ψ₁ (ctGraphPSL m F x) := by
    intro x
    have h1 : θ' (c x) = c (ctGraphPSL m F x) := by
      rw [hθ'H]
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rw [hθ'app] at h1
    rw [hψ₁app, hψ₁app, ← h1, MulEquiv.apply_symm_apply]
  have hfixθ : fixedSubgroup θ = (ctOddPSL m F).range.map ψ₁.toMonoidHom := by
    rw [← fixedSubgroup_ctGraphPSL]
    ext y
    obtain ⟨x, rfl⟩ := ψ₁.surjective y
    rw [mem_map_equiv, ψ₁.symm_apply_apply]
    change θ (ψ₁ x) = ψ₁ x ↔ ctGraphPSL m F x = x
    rw [hθψ₁]
    exact ψ₁.injective.eq_iff
  have htop : ⁅(⊤ : Subgroup (StatedSp m F)), (⊤ : Subgroup (StatedSp m F))⁆ = ⊤ := by
    have := isPerfect_statedSp_of_four_le hF4 m
    rw [← _root_.commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hperf : ⁅(ctOddPSL m F).range.map ψ₁.toMonoidHom,
      (ctOddPSL m F).range.map ψ₁.toMonoidHom⁆ = (ctOddPSL m F).range.map ψ₁.toMonoidHom := by
    rw [← map_commutator, MonoidHom.range_eq_map, ← map_commutator, htop]
  have hrange : ε.range = (ψ₁.toMonoidHom.comp
      ((ctOddPSL m F).comp (statedSpMap (σ : K →+* F) m))).range := by
    rw [hεr, hfixθ, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf, MonoidHom.range_comp,
      MonoidHom.range_comp, MonoidHom.range_eq_top.2 (statedSpMap_surjective σ),
      ← MonoidHom.range_eq_map]
  have hinj₁ : Function.Injective (ψ₁.toMonoidHom.comp
      ((ctOddPSL m F).comp (statedSpMap (σ : K →+* F) m))) :=
    ψ₁.injective.comp (ctOddPSL_injective.comp (statedSpMap_injective _ m))
  set δ₀ : MulAut (StatedSp m K) := ((MonoidHom.ofInjective hε).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hinj₁).symm with hδ₀def
  have hδ₀ : ∀ g, ψ₁ (ctOddPSL m F (statedSpMap (σ : K →+* F) m (δ₀ g))) = ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hinj₁).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  exact ⟨ψ₁, δ₀, hδ₀, hθψ₁⟩

theorem exists_mulEquiv_ctOddPSL_eq_two_graph [Finite F] {K : Type}
    [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (σ : K ≃+* F) {M : Type} [Group M] (ψ : projectiveSL (2 * 2 + 1) F ≃* M) {θ : MulAut M}
    (hθ : θ * θ = 1) (hθE : MulAut.congr ψ.symm θ ∉ semilinearAutGroup (2 * 2 + 1) F)
    (hθfix : LieModel (fixedSubgroup θ) .PSp 2 2 f) (ε : StatedSp 2 K →* M)
    (hε : Function.Injective ε) (hεr : ε.range = perfectCore (fixedSubgroup θ)) :
    ∃ ψ' : projectiveSL (2 * 2 + 1) F ≃* M,
      ((∀ g, ψ' (ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 g)) = ε g) ∨
        (∀ g, ψ' (ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp g))) = ε g)) ∧
      ∀ x, θ (ψ' x) = ψ' (ctGraphPSL 2 F x) := by
  obtain ⟨ψ₁, δ₀, hδ₀, hθψ₁⟩ :=
    exists_mulEquiv_ctOddPSL_comp_eq_graph (by norm_num) hf hF σ ψ hθ hθE hθfix ε hε hεr
  have hN3 : ∀ δ' : MulAut (projectiveSL (2 * 2 + 1) F),
      (∀ z, δ' (ctGraphPSL 2 F z) = ctGraphPSL 2 F (δ' z)) →
        ∀ x, θ ((δ'.trans ψ₁) x) = (δ'.trans ψ₁) (ctGraphPSL 2 F x) := by
    intro δ' hδ' x
    change θ (ψ₁ (δ' x)) = ψ₁ (δ' (ctGraphPSL 2 F x))
    rw [hθψ₁, hδ']
  obtain ⟨s, ρ₀, hδ | hδ⟩ := F4Pilot.exists_eq_conj_mul_fieldSp_tauSp δ₀
  · obtain ⟨δ', hδ', hδ'g⟩ := exists_mulAut_ctOddPSL_of_eq_graph (F := F) σ s ρ₀
      (MulEquiv.ext hδ)
    refine ⟨δ'.trans ψ₁, Or.inl fun g => ?_, hN3 δ' hδ'g⟩
    change ψ₁ (δ' (ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 g))) = ε g
    rw [hδ', hδ₀]
  · set δ₁ : MulAut (StatedSp 2 K) := MulAut.conj s * fieldSp 2 K ρ₀ with hδ₁
    have hδ₁app : ∀ g, δ₁ g = s * fieldSp 2 K ρ₀ g * s⁻¹ := fun _ => rfl
    obtain ⟨δ', hδ', hδ'g⟩ := exists_mulAut_ctOddPSL_of_eq_graph (F := F) (δ := δ₁) σ s ρ₀ hδ₁
    refine ⟨δ'.trans ψ₁, Or.inr fun g => ?_, hN3 δ' hδ'g⟩
    change ψ₁ (δ' (ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp g)))) = ε g
    rw [hδ', ← hδ₀ g, hδ₁app, hδ g]

end Normal

section Neighbour

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_normalized_neighbourCore_linearOdd_three_graph
    {f : ℕ} (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin 3) {X : Subgroup G}
    (hX : X = modelToG e (rootTorusSp K k)) {D : Subgroup G} (hD : D = modelToG e (complSp K k))
    (h : HR8KindAtSp t 2 f X D .linearOdd)
    (hN : t ∈ normalizer (centralizerPerfectCore X : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (σ : K ≃+* F)
      (ρ : centralizerPerfectCore X →* projectiveSL (2 * 2 + 1) F),
      Nat.card F = 2 ^ f ∧ Function.Surjective ρ ∧
        ρ.ker ≤ center (centralizerPerfectCore X) ∧
        ((∀ (x : StatedSp 2 K) (y : centralizerPerfectCore X),
            (y : G) = ((e.symm (complSpEquiv k x : complSp K k) : L) : G) →
              ρ y = ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 x)) ∨
          (∀ (x : StatedSp 2 K) (y : centralizerPerfectCore X),
            (y : G) = ((e.symm (complSpEquiv k x : complSp K k) : L) : G) →
              ρ y = ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp x)))) ∧
        ∀ y, ρ ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y) =
          ctGraphPSL 2 F (ρ y) := by
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  set E := centralizerPerfectCore X with hEdef
  set θ := E.normalizerMonoidHom ⟨t, hN⟩ with hθdef
  obtain ⟨S, _, ρ, τ, hρ, hker, -, hty, -, hρθ, hττ, hout, hfix⟩ :=
    exists_surjective_neighbourCore_linearUnitary hset hKc hf (by omega) e htC ht k hX hD
      (Or.inr (Or.inr (Or.inl rfl))) h hN
  have hS : LieModel S .PSL (2 * 2 + 1) 2 f := hty
  have hadm : StatedLieAdmissible .PSL (2 * 2 + 1) 2 f := F4Pilot.statedLieAdmissible_of_lieModel hS
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hS
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  set εS : S ≃* projectiveSL (2 * 2 + 1) F :=
    eJ.trans (CFSG.ComponentClassification.CatalogueBLinearHigherB.nativeEquiv (2 * 2 + 1) F).symm
    with hεS
  set α : MulAut (projectiveSL (2 * 2 + 1) F) := MulAut.congr εS τ with hα
  have hαα : α * α = 1 := by rw [hα, ← map_mul, hττ, map_one]
  have hα2 : α ^ 2 = 1 := by rw [_root_.sq]; exact hαα
  have hαo : α ∉ (MulAut.conj : projectiveSL (2 * 2 + 1) F →* MulAut _).range :=
    fun h' => hout ((FixedFourGroup.congr_mem_inner_iff εS τ).1 h')
  have hαfix : LieModel (fixedSubgroup α) .PSp 2 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv εS τ) hfix
  have hαE : α ∉ semilinearAutGroup (2 * 2 + 1) F :=
    not_mem_semilinearAutGroup_of_lieModel_PSp (by omega) hadm.2.1 hF hα2 hαo hαfix
  set ρ' : E →* projectiveSL (2 * 2 + 1) F := εS.toMonoidHom.comp ρ with hρ'def
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
  have hDE : ∀ x : StatedSp 2 K, ((e.symm (complSpEquiv k x : complSp K k) : L) : G) ∈ E := by
    intro x
    rw [hEdef, hX]
    exact modelToG_complSp_le_neighbourCore e hq (by omega) k
      (symm_mem_modelToG e (complSpEquiv k x).2)
  let ιD : StatedSp 2 K →* E :=
    ((L.subtype.comp e.symm.toMonoidHom).comp
      ((complSp K k).subtype.comp (complSpEquiv k).toMonoidHom)).codRestrict E hDE
  have hιD : ∀ x, ((ιD x : E) : G) = ((e.symm (complSpEquiv k x : complSp K k) : L) : G) :=
    fun _ => rfl
  have hιDinj : Function.Injective ιD := by
    intro x y hxy
    have h1 := congrArg (fun z : E => (z : G)) hxy
    simp only [hιD] at h1
    have h2 : e.symm ((complSpEquiv k x : complSp K k) : StatedSp (2 + 1) K) =
        e.symm (complSpEquiv k y : complSp K k) := Subtype.ext h1
    exact (complSpEquiv k).injective (Subtype.ext (e.symm.injective h2))
  have hε₀inj : Function.Injective (ρ'.comp ιD) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxk : ιD x ∈ ρ'.ker := hx
    rw [hker'] at hxk
    have hz := hker hxk
    have hxc : x ∈ center (StatedSp 2 K) := by
      rw [mem_center_iff]
      intro g
      apply hιDinj
      rw [map_mul, map_mul]
      exact mem_center_iff.1 hz (ιD g)
    rw [center_statedSp_eq_bot 2] at hxc
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
  have hcongr : MulAut.congr (MulEquiv.refl (projectiveSL (2 * 2 + 1) F)).symm α = α :=
    MulEquiv.ext fun _ => rfl
  obtain ⟨ψ', hψ'1, hψ'3⟩ := exists_mulEquiv_ctOddPSL_eq_two_graph hf hF σ (MulEquiv.refl _) hαα
    (by rw [hcongr]; exact hαE) hαfix (ρ'.comp ιD) hε₀inj hrange
  have hkerψ : (ψ'.symm.toMonoidHom.comp ρ').ker = ρ.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hker']
  refine ⟨F, inferInstance, inferInstance, inferInstance, σ, ψ'.symm.toMonoidHom.comp ρ', hF,
    ψ'.symm.surjective.comp hρ's, hkerψ ▸ hker, ?_, ?_⟩
  · rcases hψ'1 with h1 | h1
    · refine Or.inl fun x y hy => ?_
      have hyx : y = ιD x := Subtype.ext (hy.trans (hιD x).symm)
      rw [hyx]
      change ψ'.symm ((ρ'.comp ιD) x) = _
      rw [← h1 x, MulEquiv.symm_apply_apply]
    · refine Or.inr fun x y hy => ?_
      have hyx : y = ιD x := Subtype.ext (hy.trans (hιD x).symm)
      rw [hyx]
      change ψ'.symm ((ρ'.comp ιD) x) = _
      rw [← h1 x, MulEquiv.symm_apply_apply]
  · intro y
    change ψ'.symm (ρ' (θ y)) = ctGraphPSL 2 F (ψ'.symm (ρ' y))
    have h3 := hψ'3 (ψ'.symm (ρ' y))
    change α (ψ' (ψ'.symm (ρ' y))) = ψ' (ctGraphPSL 2 F (ψ'.symm (ρ' y))) at h3
    rw [MulEquiv.apply_symm_apply] at h3
    rw [hρ'α, h3, MulEquiv.symm_apply_apply]

end Neighbour

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

@[expose] def SpThreeOddGraphNormalized (e : L ≃* StatedSp 3 K) (t : G) (f : ℕ) (k : Fin 3)
    (b : Bool) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (σ : K ≃+* F)
    (Φ : SpecialLinearGroup (Fin (2 * 2 + 1)) F →* G),
    Nat.card F = 2 ^ f ∧ Φ.range = neighbourCore e k ∧
      Φ.ker ≤ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F) ∧
      (∀ x : StatedSp 2 K, Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (cond b (tauSp x) x))) =
        ((e.symm (complSpEquiv k x : complSp K k) : L) : G)) ∧
      ∀ y, t * Φ y * t⁻¹ = Φ (ctGraph 1 y)

omit [Finite G] [Finite K] in
theorem SpThreeOddGraphNormalized.toNormalized {e : L ≃* StatedSp 3 K} {t : G} {f : ℕ}
    {k : Fin 3} {b : Bool} (h : SpThreeOddGraphNormalized e t f k b) :
    SpThreeOddNormalized e f k b := by
  obtain ⟨F, i1, i2, i3, σ, Φ, hF, hr, hk, hN1, -⟩ := h
  exact ⟨F, i1, i2, i3, σ, Φ, hF, hr, hk, hN1⟩

theorem spThreeOddGraphNormalized_false_or_true {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .linearOdd) :
    SpThreeOddGraphNormalized e t f k false ∨ SpThreeOddGraphNormalized e t f k true := by
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (rootTorusSp K k)) : Set G) :=
    le_normalizer_neighbourCore e htC k
  obtain ⟨F, _, _, _, σ, ρ, hF, hρ, hker, hN1, hN3⟩ :=
    exists_normalized_neighbourCore_linearOdd_three_graph hset hKc hf e htC ht k rfl rfl hk hN
  have : Group.IsPerfect (centralizerPerfectCore (modelToG e (rootTorusSp K k))) :=
    Subgroup.isPerfect_iff.2 (perfectCore_perfect _)
  have hF2 : Nat.card F ≠ 2 := by
    rw [hF]
    intro h2
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating (2 * 2) F :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card (by norm_num) hF2
      (fun h' => absurd h'.1 (by norm_num)) (fun h' => absurd h'.1 (by norm_num))
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := F4Pilot.exists_lift_of_central (proj (2 * 2 + 1) F)
    (proj_surjective _ _)
    (fun E' _ _ π' hπ' hker' =>
      CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating (m := 2 * 2)
        (by norm_num) hsep hπ' hker') ρ hρ hker
  have hrange : ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype.comp Φ₀).range =
      neighbourCore e k := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ₀s, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  have hkerΦ : ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype.comp Φ₀).ker ≤
      center (SpecialLinearGroup (Fin (2 * 2 + 1)) F) := by
    intro g hg
    have hg₀ : Φ₀ g = 1 := (centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype_injective
      (by rw [map_one]; exact hg)
    have h1 := hΦ₀ g
    rw [hg₀, map_one, eq_comm, proj_eq_one_iff] at h1
    exact LinearFlag.scalars_le_center (2 * 2 + 1) F h1
  have hDE : ∀ x : StatedSp 2 K, ((e.symm (complSpEquiv k x : complSp K k) : L) : G) ∈
      centralizerPerfectCore (modelToG e (rootTorusSp K k)) := by
    intro x
    exact modelToG_complSp_le_neighbourCore e hK4 (by norm_num) k
      (symm_mem_modelToG e (complSpEquiv k x).2)
  let ιD : StatedSp 2 K →* centralizerPerfectCore (modelToG e (rootTorusSp K k)) :=
    ((L.subtype.comp e.symm.toMonoidHom).comp
      ((complSp K k).subtype.comp (complSpEquiv k).toMonoidHom)).codRestrict _ hDE
  have : Group.IsPerfect (StatedSp 2 K) := isPerfect_statedSp_of_four_le hK4 2
  have key : ∀ (β : StatedSp 2 K →* StatedSp 2 K),
      (∀ (x : StatedSp 2 K) (y : centralizerPerfectCore (modelToG e (rootTorusSp K k))),
        (y : G) = ((e.symm (complSpEquiv k x : complSp K k) : L) : G) →
          ρ y = ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 (β x))) →
      ∀ x : StatedSp 2 K, ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype.comp
        Φ₀) (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (β x))) =
          ((e.symm (complSpEquiv k x : complSp K k) : L) : G) := by
    intro β hβ x
    have heq := LinearPilot.eq_of_comp_eq_of_ker_le_center (S := StatedSp 2 K) hker
      (φ := Φ₀.comp ((ctEmbed 1).comp ((statedSpMap (σ : K →+* F) 2).comp β))) (ψ := ιD)
      (fun x => by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hΦ₀,
          hβ x (ιD x) rfl]
        rfl)
    exact congrArg (fun Ψ : StatedSp 2 K →* centralizerPerfectCore
      (modelToG e (rootTorusSp K k)) => ((Ψ x : centralizerPerfectCore
        (modelToG e (rootTorusSp K k))) : G)) heq
  have : Group.IsPerfect (SpecialLinearGroup (Fin (2 * 2 + 1)) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  have hN3' : ∀ y, t * ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype.comp
      Φ₀) y * t⁻¹ = ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype.comp Φ₀)
        (ctGraph 1 y) := by
    have heq := LinearPilot.eq_of_comp_eq_of_ker_le_center
      (S := SpecialLinearGroup (Fin (2 * 2 + 1)) F) hker
      (φ := ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).normalizerMonoidHom
        ⟨t, hN⟩).toMonoidHom.comp Φ₀)
      (ψ := Φ₀.comp (ctGraph 1).toMonoidHom)
      (fun y => by
        change ρ ((centralizerPerfectCore (modelToG e (rootTorusSp K k))).normalizerMonoidHom
          ⟨t, hN⟩ (Φ₀ y)) = ρ (Φ₀ (ctGraph 1 y))
        rw [hN3, hΦ₀, hΦ₀, ctGraphPSL_proj])
    intro y
    exact congrArg (fun Ψ : SpecialLinearGroup (Fin (2 * 2 + 1)) F →*
      centralizerPerfectCore (modelToG e (rootTorusSp K k)) => ((Ψ y :
        centralizerPerfectCore (modelToG e (rootTorusSp K k))) : G)) heq
  rcases hN1 with h1 | h1
  · exact Or.inl ⟨F, inferInstance, inferInstance, inferInstance, σ,
      (centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype.comp Φ₀, hF,
      hrange, hkerΦ, key (MonoidHom.id _) h1, hN3'⟩
  · exact Or.inr ⟨F, inferInstance, inferInstance, inferInstance, σ,
      (centralizerPerfectCore (modelToG e (rootTorusSp K k))).subtype.comp Φ₀, hF,
      hrange, hkerΦ, key tauSp h1, hN3'⟩

theorem spThreeOddGraphNormalized_of_standard {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .linearOdd) (hstd : SpThreeOddStandard e) :
    SpThreeOddGraphNormalized e t f k false := by
  rcases spThreeOddGraphNormalized_false_or_true hset hKc hf e htC ht k hk with h | h
  · exact h
  · exact absurd (hstd k _ (ne_succAbove_zero_three k))
      (not_cube_dvd_natCard_edgeCoreSp_of_odd_twisted hKc hf h.toNormalized)

theorem spThreeOddGraphNormalized_of_twisted {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .linearOdd) (htw : SpThreeOddTwisted e) :
    SpThreeOddGraphNormalized e t f k true := by
  rcases spThreeOddGraphNormalized_false_or_true hset hKc hf e htC ht k hk with h | h
  · exact absurd (cube_dvd_natCard_edgeCoreSp_of_odd_std hKc hf h.toNormalized)
      (htw k _ (ne_succAbove_zero_three k))
  · exact h

end Lift

end CFSG.SeitzReduction.SymplecticPilot
