module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTOddModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTOddAlign
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTRows

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
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open scoped MatrixGroups

section Neighbour

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_normalized_neighbourCore_linearOdd {m f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 3 ≤ m)
    (e : L ≃* StatedSp (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (m + 1)) {X : Subgroup G}
    (hX : X = modelToG e (rootTorusSp K k)) {D : Subgroup G} (hD : D = modelToG e (complSp K k))
    (h : HR8KindAtSp t m f X D .linearOdd)
    (hN : t ∈ normalizer (centralizerPerfectCore X : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (σ : K ≃+* F)
      (ρ : centralizerPerfectCore X →* projectiveSL (2 * m + 1) F),
      Nat.card F = 2 ^ f ∧ Function.Surjective ρ ∧
        ρ.ker ≤ center (centralizerPerfectCore X) ∧
        ∀ (x : StatedSp m K) (y : centralizerPerfectCore X),
          (y : G) = ((e.symm (complSpEquiv k x : complSp K k) : L) : G) →
            ρ y = ctOddPSL m F (statedSpMap (σ : K →+* F) m x) := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  set E := centralizerPerfectCore X with hEdef
  set θ := E.normalizerMonoidHom ⟨t, hN⟩ with hθdef
  obtain ⟨S, _, ρ, τ, hρ, hker, -, hty, -, hρθ, hττ, hout, hfix⟩ :=
    exists_surjective_neighbourCore_linearUnitary hset hKc hf (by omega) e htC ht k hX hD
      (Or.inr (Or.inr (Or.inl rfl))) h hN
  have hS : LieModel S .PSL (2 * m + 1) 2 f := hty
  have hadm : StatedLieAdmissible .PSL (2 * m + 1) 2 f := F4Pilot.statedLieAdmissible_of_lieModel hS
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hS
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  set εS : S ≃* projectiveSL (2 * m + 1) F :=
    eJ.trans (CFSG.ComponentClassification.CatalogueBLinearHigherB.nativeEquiv (2 * m + 1) F).symm
    with hεS
  set α : MulAut (projectiveSL (2 * m + 1) F) := MulAut.congr εS τ with hα
  have hαα : α * α = 1 := by rw [hα, ← map_mul, hττ, map_one]
  have hα2 : α ^ 2 = 1 := by rw [_root_.sq]; exact hαα
  have hαo : α ∉ (MulAut.conj : projectiveSL (2 * m + 1) F →* MulAut _).range :=
    fun h' => hout ((FixedFourGroup.congr_mem_inner_iff εS τ).1 h')
  have hαfix : LieModel (fixedSubgroup α) .PSp m 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv εS τ) hfix
  have hαE : α ∉ semilinearAutGroup (2 * m + 1) F :=
    not_mem_semilinearAutGroup_of_lieModel_PSp (by omega) hadm.2.1 hF hα2 hαo hαfix
  set ρ' : E →* projectiveSL (2 * m + 1) F := εS.toMonoidHom.comp ρ with hρ'def
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
  have hcongr : MulAut.congr (MulEquiv.refl (projectiveSL (2 * m + 1) F)).symm α = α :=
    MulEquiv.ext fun _ => rfl
  obtain ⟨ψ', hψ'1⟩ := exists_mulEquiv_ctOddPSL_eq hm hf hF σ (MulEquiv.refl _) hαα
    (by rw [hcongr]; exact hαE) hαfix (ρ'.comp ιD) hε₀inj hrange
  have hkerψ : (ψ'.symm.toMonoidHom.comp ρ').ker = ρ.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hker']
  refine ⟨F, inferInstance, inferInstance, inferInstance, σ, ψ'.symm.toMonoidHom.comp ρ', hF,
    ψ'.symm.surjective.comp hρ's, hkerψ ▸ hker, fun x y hy => ?_⟩
  have hyx : y = ιD x := Subtype.ext (hy.trans (hιD x).symm)
  rw [hyx]
  change ψ'.symm ((ρ'.comp ιD) x) = _
  rw [← hψ'1 x, MulEquiv.symm_apply_apply]

end Neighbour

section Coord

variable {K : Type} [Field K] {m : ℕ} (k : Fin (m + 1))

noncomputable abbrev ctNbrCoordOdd (w : (Fin m ⊕ Fin m) ⊕ Fin 1) : Fin (2 * (m + 1) + 1) :=
  q2Coord (m + 1) 1 (Sum.map (Sum.map k.succAbove k.succAbove) id w)

theorem ctNbrCoordOdd_injective : Function.Injective (ctNbrCoordOdd k) := fun _ _ h =>
  (Sum.map_injective.2 ⟨Sum.map_injective.2 ⟨Fin.succAbove_right_injective,
    Fin.succAbove_right_injective⟩, Function.injective_id⟩) ((q2Coord (m + 1) 1).injective h)

theorem ctNbrCoordOdd_mem (w : (Fin m ⊕ Fin m) ⊕ Fin 1) :
    ctNbrCoordOdd k w ∈ (planeCoordsQ2 1 ({k} : Finset (Fin (m + 1))))ᶜ := by
  rw [Finset.mem_compl, q2Coord_mem_planeCoordsQ2]
  rcases w with (i | i) | i
  · simp [Fin.succAbove_ne]
  · simp [Fin.succAbove_ne]
  · exact not_inPlanes_inr _ i

theorem exists_ctNbrCoordOdd_eq {a : Fin (2 * (m + 1) + 1)}
    (ha : a ∈ (planeCoordsQ2 1 ({k} : Finset (Fin (m + 1))))ᶜ) : ∃ w, ctNbrCoordOdd k w = a := by
  obtain ⟨w, rfl⟩ := (q2Coord (m + 1) 1).surjective a
  rw [Finset.mem_compl, q2Coord_mem_planeCoordsQ2] at ha
  rcases w with (v | v) | i
  · simp only [inPlanes_inl, planeOf_inl, Finset.mem_singleton] at ha
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ha
    exact ⟨Sum.inl (Sum.inl j), rfl⟩
  · simp only [inPlanes_inl, planeOf_inr, Finset.mem_singleton] at ha
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ha
    exact ⟨Sum.inl (Sum.inr j), rfl⟩
  · exact ⟨Sum.inr i, rfl⟩

@[expose] noncomputable def ctNbrEquivOdd :
    Fin (2 * m + 1) ≃ ↥((planeCoordsQ2 1 ({k} : Finset (Fin (m + 1))))ᶜ) :=
  Equiv.ofBijective (fun j => ⟨ctNbrCoordOdd k ((q2Coord m 1).symm j), ctNbrCoordOdd_mem k _⟩)
    ⟨fun i j h => (q2Coord m 1).symm.injective (ctNbrCoordOdd_injective k
      (congrArg Subtype.val h)),
      fun a => by
        obtain ⟨w, hw⟩ := exists_ctNbrCoordOdd_eq k a.2
        exact ⟨q2Coord m 1 w, Subtype.ext (by simp [hw])⟩⟩

@[expose] noncomputable def ctNbrOdd : q2Block 1 K ({k} : Finset (Fin (m + 1))) ≃*
    SpecialLinearGroup (Fin (2 * m + 1)) K :=
  ((MonoidHom.ofInjective (LinearPilot.blockEmbed_injective (K := K)
      (planeCoordsQ2 1 ({k} : Finset (Fin (m + 1))))ᶜ)).trans
    (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed _))).symm.trans
    (LinearPilot.reindexSpecialLinear (ctNbrEquivOdd k).symm)

theorem ctNbrOdd_apply (x : q2Block 1 K ({k} : Finset (Fin (m + 1)))) (i j : Fin (2 * m + 1)) :
    ((ctNbrOdd k x : SpecialLinearGroup (Fin (2 * m + 1)) K) :
      Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K) i j =
      ((x : SpecialLinearGroup (Fin (2 * (m + 1) + 1)) K) :
        Matrix (Fin (2 * (m + 1) + 1)) (Fin (2 * (m + 1) + 1)) K)
        (ctNbrCoordOdd k ((q2Coord m 1).symm i)) (ctNbrCoordOdd k ((q2Coord m 1).symm j)) := by
  set g := ((MonoidHom.ofInjective (LinearPilot.blockEmbed_injective (K := K)
      (planeCoordsQ2 1 ({k} : Finset (Fin (m + 1))))ᶜ)).trans
    (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed _))).symm x with hg
  have hx : LinearPilot.blockEmbed _ g =
      (x : SpecialLinearGroup (Fin (2 * (m + 1) + 1)) K) := by
    have := congrArg Subtype.val ((((MonoidHom.ofInjective (LinearPilot.blockEmbed_injective
      (K := K) (planeCoordsQ2 1 ({k} : Finset (Fin (m + 1))))ᶜ)).trans
      (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed _)))).apply_symm_apply x)
    exact this
  change (reindex (ctNbrEquivOdd k).symm (ctNbrEquivOdd k).symm (g : Matrix _ _ K)) i j = _
  rw [reindex_apply, submatrix_apply, Equiv.symm_symm, ← hx, LinearPilot.coe_blockEmbed,
    LinearPilot.blockMatrix_apply,
    dite_eq_left_of_eq_true (eq_true ⟨ctNbrCoordOdd_mem k _, ctNbrCoordOdd_mem k _⟩)]
  rfl

theorem ctEmbed_spEmbed_mem_q2Block_odd [CharP K 2] (y : StatedSp m K) :
    ctEmbed 1 (spEmbed k.succAbove Fin.succAbove_right_injective y) ∈
      q2Block 1 K ({k} : Finset (Fin (m + 1))) := by
  rw [ctEmbed_mem_q2Block_iff, spBlock_compl_singleton, complSp_eq_range_spEmbed]
  exact ⟨y, rfl⟩

theorem ctNbrOdd_ctEmbed [CharP K 2] (y : StatedSp m K) :
    ctNbrOdd k ⟨ctEmbed 1 (spEmbed k.succAbove Fin.succAbove_right_injective y),
      ctEmbed_spEmbed_mem_q2Block_odd k y⟩ = ctEmbed 1 y := by
  apply Subtype.ext
  ext i j
  obtain ⟨w, rfl⟩ := (q2Coord m 1).surjective i
  obtain ⟨w', rfl⟩ := (q2Coord m 1).surjective j
  rw [ctNbrOdd_apply]
  simp only [Equiv.symm_apply_apply]
  rw [ctEmbed_apply_q2Coord, ctEmbed_apply_q2Coord]
  rcases w with u | i <;> rcases w' with v | j
  · rw [Sum.map_inl, Sum.map_inl, fromBlocks_apply₁₁, fromBlocks_apply₁₁, mat_spEmbed,
      spEmbedMat_apply_image Fin.succAbove_right_injective]
  · rw [Sum.map_inl, Sum.map_inr, fromBlocks_apply₁₂, fromBlocks_apply₁₂, Matrix.zero_apply,
      Matrix.zero_apply]
  · rw [Sum.map_inr, Sum.map_inl, fromBlocks_apply₂₁, fromBlocks_apply₂₁, Matrix.zero_apply,
      Matrix.zero_apply]
  · rw [Sum.map_inr, Sum.map_inr, fromBlocks_apply₂₂, fromBlocks_apply₂₂]
    rfl

end Coord

section Exists

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem nonempty_ctLinParam_linearOdd {m f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 3 ≤ m)
    (e : L ≃* StatedSp (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (m + 1)) (hk : RootKindSp e t f k .linearOdd) :
    Nonempty (CtLinParam 1 e k) := by
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  set X : Subgroup G := modelToG e (rootTorusSp K k) with hX
  have hN : t ∈ normalizer (centralizerPerfectCore X : Set G) := le_normalizer_neighbourCore e htC k
  obtain ⟨F, _, _, _, σ, ρ, hF, hρs, hρker, hρN1⟩ :=
    exists_normalized_neighbourCore_linearOdd hset hKc hf hm e htC ht k rfl rfl hk hN
  set ψ : q2Block 1 K ({k} : Finset (Fin (m + 1))) →* SpecialLinearGroup (Fin (2 * m + 1)) F :=
    (SpecialLinearGroup.map (σ : K →+* F)).comp (ctNbrOdd k).toMonoidHom with hψ
  have hmapinj : Function.Injective (SpecialLinearGroup.map (n := Fin (2 * m + 1))
      (σ : K →+* F)) := by
    intro a b hab
    apply Subtype.ext
    ext i j
    have := congrArg (fun z : SpecialLinearGroup (Fin (2 * m + 1)) F =>
      (z : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) F) i j) hab
    exact σ.injective this
  have hmapsurj : Function.Surjective (SpecialLinearGroup.map (n := Fin (2 * m + 1))
      (σ : K →+* F)) := by
    intro g
    refine ⟨SpecialLinearGroup.map (σ.symm : F →+* K) g, ?_⟩
    apply Subtype.ext
    ext i j
    change σ (σ.symm _) = _
    rw [RingEquiv.apply_symm_apply]
  have hψinj : Function.Injective ψ := hmapinj.comp (ctNbrOdd k).injective
  have hψs : Function.Surjective ψ := hmapsurj.comp (ctNbrOdd k).surjective
  set χ : q2Block 1 K ({k} : Finset (Fin (m + 1))) →* LinearFlag.projectiveSL (2 * m + 1) F :=
    (LinearFlag.proj (2 * m + 1) F).comp ψ with hχ
  have hχs : Function.Surjective χ := (LinearFlag.proj_surjective _ _).comp hψs
  have hkerχ : χ.ker ≤ center (q2Block 1 K ({k} : Finset (Fin (m + 1)))) := by
    intro x hx
    have h1 : ψ x ∈ center (SpecialLinearGroup (Fin (2 * m + 1)) F) := by
      rw [← LinearFlag.scalars_eq_center, ← LinearFlag.ker_proj]
      exact hx
    rw [mem_center_iff]
    intro g
    apply hψinj
    rw [map_mul, map_mul]
    exact mem_center_iff.1 h1 (ψ g)
  have hsplit : ∀ (E' : Type) [Group E'] [Finite E']
      (π' : E' →* q2Block 1 K ({k} : Finset (Fin (m + 1)))), Function.Surjective π' →
        π'.ker ≤ center E' → ∃ s : q2Block 1 K ({k} : Finset (Fin (m + 1))) →* E',
          ∀ g, π' (s g) = g := by
    refine F4Pilot.forall_exists_section_of_mulEquiv (ctNbrOdd k) ?_
    intro E' _ _ π' hπ' hcen
    exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_four_le (by omega) hπ'
      hcen
  have : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore _)
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := F4Pilot.exists_lift_of_central χ hχs hsplit ρ hρs hρker
  have hDE : ∀ x : StatedSp m K,
      ((e.symm (complSpEquiv k x : complSp K k) : L) : G) ∈ centralizerPerfectCore X := by
    intro x
    rw [hX]
    exact modelToG_complSp_le_neighbourCore e hq (by omega) k
      (UnitaryPilot.symm_mem_modelToG e (complSpEquiv k x).2)
  set ιD : StatedSp m K →* centralizerPerfectCore X :=
    ((L.subtype.comp e.symm.toMonoidHom).comp
      ((complSp K k).subtype.comp (complSpEquiv k).toMonoidHom)).codRestrict _ hDE with hιD
  set ιB : StatedSp m K →* q2Block 1 K ({k} : Finset (Fin (m + 1))) :=
    ((ctEmbed 1).comp (spEmbed k.succAbove Fin.succAbove_right_injective)).codRestrict _
      (ctEmbed_spEmbed_mem_q2Block_odd k) with hιB
  have : Group.IsPerfect (StatedSp m K) := isPerfect_statedSp_of_four_le hq m
  have heq : Φ₀.comp ιB = ιD := by
    refine LinearPilot.eq_of_comp_eq_of_ker_le_center (S := StatedSp m K) hρker fun x => ?_
    rw [MonoidHom.comp_apply, hΦ₀, hρN1 x (ιD x) rfl]
    change LinearFlag.proj (2 * m + 1) F
      (SpecialLinearGroup.map (σ : K →+* F) (ctNbrOdd k (ιB x))) = _
    have h1 : ctNbrOdd k (ιB x) = ctEmbed 1 x := ctNbrOdd_ctEmbed k x
    rw [h1, ← ctEmbed_statedSpMap]
    rfl
  refine ⟨⟨(centralizerPerfectCore X).subtype.comp Φ₀, ?_, ?_, ?_⟩⟩
  · intro x hx
    have hx₀ : Φ₀ x = 1 :=
      (centralizerPerfectCore X).subtype_injective (by rw [map_one]; exact hx)
    apply hkerχ
    rw [MonoidHom.mem_ker, ← hΦ₀, hx₀, map_one]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ₀s, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  · intro y hy
    rw [spBlock_compl_singleton, complSp_eq_range_spEmbed] at hy
    obtain ⟨x, rfl⟩ := hy
    have h1 := congrArg (fun F : StatedSp m K →* centralizerPerfectCore X => ((F x : _) : G)) heq
    exact h1

end Exists

theorem spLinearOddAlignedParamInput_holds :
    SpLinearOddAlignedParamInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hP : ∀ k : Fin (m + 1), Nonempty (CtLinParam 1 e k) := fun k =>
    nonempty_ctLinParam_linearOdd hset hKc hf (by omega) e htC ht k (hroot k)
  exact exists_ctLinParamAgree_odd hq (by omega) fun k => (hP k).some

theorem spKindCoverInput_linearOdd_of_four
    (h4 : SpLinearOddCoverFourInput) : SpKindCoverInput .linearOdd :=
  spKindCoverInput_linearOdd_of_alignedParam spLinearOddAlignedParamInput_holds h4

end CFSG.SeitzReduction.SymplecticPilot
