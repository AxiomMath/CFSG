module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTOddModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindLinearNormalize

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)

section Normal

variable {m : ℕ} {F : Type} [Field F] [CharP F 2]

theorem exists_mulAut_ctOddPSL_of_eq {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* F) {δ : MulAut (StatedSp m K)} (s : StatedSp m K) (ρ₀ : K ≃+* K)
    (hδ : δ = MulAut.conj s * fieldSp m K ρ₀) :
    ∃ δ' : MulAut (projectiveSL (2 * m + 1) F),
      ∀ g, δ' (ctOddPSL m F (statedSpMap (σ : K →+* F) m g)) =
        ctOddPSL m F (statedSpMap (σ : K →+* F) m (δ g)) := by
  set ρ' : F ≃+* F := (σ.symm.trans ρ₀).trans σ with hρ'
  have hρ'σ : (ρ' : F →+* F).comp (σ : K →+* F) = (σ : K →+* F).comp (ρ₀ : K →+* K) := by
    ext c
    simp [hρ']
  refine ⟨MulAut.conj (ctOddPSL m F (statedSpMap (σ : K →+* F) m s)) * fieldAut (2 * m + 1) F ρ',
    fun g => ?_⟩
  rw [MulAut.mul_apply, fieldAut_ctOddPSL, F4Pilot.statedSpMap_comp, hρ'σ,
    ← F4Pilot.statedSpMap_comp, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
    ← map_inv, ← map_mul, ← map_mul, hδ, MulAut.mul_apply, MulAut.conj_apply,
    F4Pilot.fieldSp_eq_statedSpMap]


theorem exists_mulEquiv_ctOddPSL_comp_eq [Finite F] {K : Type}
    [Field K] [Finite K] [CharP K 2] {f : ℕ} (hm : 1 ≤ m) (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (σ : K ≃+* F) {M : Type} [Group M] (ψ : projectiveSL (2 * m + 1) F ≃* M) {θ : MulAut M}
    (hθ : θ * θ = 1) (hθE : MulAut.congr ψ.symm θ ∉ semilinearAutGroup (2 * m + 1) F)
    (hθfix : LieModel (fixedSubgroup θ) .PSp m 2 f) (ε : StatedSp m K →* M)
    (hε : Function.Injective ε) (hεr : ε.range = perfectCore (fixedSubgroup θ)) :
    ∃ (ψ₁ : projectiveSL (2 * m + 1) F ≃* M) (δ₀ : MulAut (StatedSp m K)),
      ∀ g, ψ₁ (ctOddPSL m F (statedSpMap (σ : K →+* F) m (δ₀ g))) = ε g := by
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
  exact ⟨ψ₁, δ₀, hδ₀⟩

theorem exists_mulEquiv_ctOddPSL_eq_two [Finite F] {K : Type}
    [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (σ : K ≃+* F) {M : Type} [Group M] (ψ : projectiveSL (2 * 2 + 1) F ≃* M) {θ : MulAut M}
    (hθ : θ * θ = 1) (hθE : MulAut.congr ψ.symm θ ∉ semilinearAutGroup (2 * 2 + 1) F)
    (hθfix : LieModel (fixedSubgroup θ) .PSp 2 2 f) (ε : StatedSp 2 K →* M)
    (hε : Function.Injective ε) (hεr : ε.range = perfectCore (fixedSubgroup θ)) :
    ∃ ψ' : projectiveSL (2 * 2 + 1) F ≃* M,
      (∀ g, ψ' (ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 g)) = ε g) ∨
        (∀ g, ψ' (ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp g))) = ε g) := by
  obtain ⟨ψ₁, δ₀, hδ₀⟩ :=
    exists_mulEquiv_ctOddPSL_comp_eq (by norm_num) hf hF σ ψ hθ hθE hθfix ε hε hεr
  obtain ⟨s, ρ₀, hδ | hδ⟩ := F4Pilot.exists_eq_conj_mul_fieldSp_tauSp δ₀
  · obtain ⟨δ', hδ'⟩ := exists_mulAut_ctOddPSL_of_eq (F := F) σ s ρ₀ (MulEquiv.ext hδ)
    refine ⟨δ'.trans ψ₁, Or.inl fun g => ?_⟩
    change ψ₁ (δ' (ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 g))) = ε g
    rw [hδ', hδ₀]
  · set δ₁ : MulAut (StatedSp 2 K) := MulAut.conj s * fieldSp 2 K ρ₀ with hδ₁
    have hδ₁app : ∀ g, δ₁ g = s * fieldSp 2 K ρ₀ g * s⁻¹ := fun _ => rfl
    obtain ⟨δ', hδ'⟩ := exists_mulAut_ctOddPSL_of_eq (F := F) (δ := δ₁) σ s ρ₀ hδ₁
    refine ⟨δ'.trans ψ₁, Or.inr fun g => ?_⟩
    change ψ₁ (δ' (ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp g)))) = ε g
    rw [hδ', ← hδ₀ g, hδ₁app, hδ g]

end Normal

section Neighbour

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_normalized_neighbourCore_linearOdd_three {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
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
              ρ y = ctOddPSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp x)))) := by
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
  obtain ⟨ψ', hψ'1⟩ := exists_mulEquiv_ctOddPSL_eq_two hf hF σ (MulEquiv.refl _) hαα
    (by rw [hcongr]; exact hαE) hαfix (ρ'.comp ιD) hε₀inj hrange
  have hkerψ : (ψ'.symm.toMonoidHom.comp ρ').ker = ρ.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hker']
  refine ⟨F, inferInstance, inferInstance, inferInstance, σ, ψ'.symm.toMonoidHom.comp ρ', hF,
    ψ'.symm.surjective.comp hρ's, hkerψ ▸ hker, ?_⟩
  rcases hψ'1 with h1 | h1
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

end Neighbour

end CFSG.SeitzReduction.SymplecticPilot
