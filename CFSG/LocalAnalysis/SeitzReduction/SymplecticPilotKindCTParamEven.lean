module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindLinearNormalize
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryCover

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Coord

variable {K : Type} [Field K] {m : ℕ} (k : Fin (m + 1))

noncomputable abbrev ctNbrCoord (u : Fin m ⊕ Fin m) : Fin (2 * (m + 1) + 0) :=
  q2Coord (m + 1) 0 (Sum.inl (Sum.map k.succAbove k.succAbove u))

theorem ctNbrCoord_injective : Function.Injective (ctNbrCoord k) := fun _ _ h =>
  (Sum.map_injective.2 ⟨Fin.succAbove_right_injective, Fin.succAbove_right_injective⟩)
    (Sum.inl.inj ((q2Coord (m + 1) 0).injective h))

theorem ctNbrCoord_mem (u : Fin m ⊕ Fin m) :
    ctNbrCoord k u ∈ (planeCoordsQ2 0 ({k} : Finset (Fin (m + 1))))ᶜ := by
  rw [Finset.mem_compl, q2Coord_mem_planeCoordsQ2, inPlanes_inl, Finset.mem_singleton]
  rcases u with i | i <;> simp [Fin.succAbove_ne]

theorem exists_ctNbrCoord_eq {a : Fin (2 * (m + 1) + 0)}
    (ha : a ∈ (planeCoordsQ2 0 ({k} : Finset (Fin (m + 1))))ᶜ) : ∃ u, ctNbrCoord k u = a := by
  obtain ⟨w, rfl⟩ := (q2Coord (m + 1) 0).surjective a
  rw [Finset.mem_compl, q2Coord_mem_planeCoordsQ2] at ha
  rcases w with (v | v) | i
  · simp only [inPlanes_inl, planeOf_inl, Finset.mem_singleton] at ha
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ha
    exact ⟨Sum.inl j, rfl⟩
  · simp only [inPlanes_inl, planeOf_inr, Finset.mem_singleton] at ha
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ha
    exact ⟨Sum.inr j, rfl⟩
  · exact i.elim0

@[expose] noncomputable def ctNbrEquiv : Fin (2 * m) ≃ ↥((planeCoordsQ2 0 ({k} : Finset (Fin (m + 1))))ᶜ) :=
  Equiv.ofBijective (fun j => ⟨ctNbrCoord k ((spModelIdx m).symm j), ctNbrCoord_mem k _⟩)
    ⟨fun i j h => (spModelIdx m).symm.injective (ctNbrCoord_injective k (congrArg Subtype.val h)),
      fun a => by
        obtain ⟨u, hu⟩ := exists_ctNbrCoord_eq k a.2
        exact ⟨spModelIdx m u, Subtype.ext (by simp [hu])⟩⟩

@[expose] noncomputable def ctNbrSL : q2Block 0 K ({k} : Finset (Fin (m + 1))) ≃*
    SpecialLinearGroup (Fin (2 * m)) K :=
  ((MonoidHom.ofInjective (LinearPilot.blockEmbed_injective (K := K)
      (planeCoordsQ2 0 ({k} : Finset (Fin (m + 1))))ᶜ)).trans
    (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed _))).symm.trans
    (LinearPilot.reindexSpecialLinear (ctNbrEquiv k).symm)

theorem ctNbrSL_apply (x : q2Block 0 K ({k} : Finset (Fin (m + 1)))) (i j : Fin (2 * m)) :
    ((ctNbrSL k x : SpecialLinearGroup (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) i j =
      ((x : SpecialLinearGroup (Fin (2 * (m + 1) + 0)) K) :
        Matrix (Fin (2 * (m + 1) + 0)) (Fin (2 * (m + 1) + 0)) K)
        (ctNbrCoord k ((spModelIdx m).symm i)) (ctNbrCoord k ((spModelIdx m).symm j)) := by
  set g := ((MonoidHom.ofInjective (LinearPilot.blockEmbed_injective (K := K)
      (planeCoordsQ2 0 ({k} : Finset (Fin (m + 1))))ᶜ)).trans
    (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed _))).symm x with hg
  have hx : LinearPilot.blockEmbed _ g = (x : SpecialLinearGroup (Fin (2 * (m + 1) + 0)) K) := by
    have := congrArg Subtype.val ((((MonoidHom.ofInjective (LinearPilot.blockEmbed_injective
      (K := K) (planeCoordsQ2 0 ({k} : Finset (Fin (m + 1))))ᶜ)).trans
      (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed _)))).apply_symm_apply x)
    exact this
  change (reindex (ctNbrEquiv k).symm (ctNbrEquiv k).symm (g : Matrix _ _ K)) i j = _
  rw [reindex_apply, submatrix_apply, Equiv.symm_symm, ← hx, LinearPilot.coe_blockEmbed,
    LinearPilot.blockMatrix_apply,
    dite_eq_left_of_eq_true (eq_true ⟨ctNbrCoord_mem k _, ctNbrCoord_mem k _⟩)]
  rfl

theorem ctEmbed_spEmbed_mem_q2Block [CharP K 2] (y : StatedSp m K) :
    ctEmbed 0 (spEmbed k.succAbove Fin.succAbove_right_injective y) ∈
      q2Block 0 K ({k} : Finset (Fin (m + 1))) := by
  rw [ctEmbed_mem_q2Block_iff, spBlock_compl_singleton, complSp_eq_range_spEmbed]
  exact ⟨y, rfl⟩

theorem ctNbrSL_ctEmbed [CharP K 2] (y : StatedSp m K) :
    ctNbrSL k ⟨ctEmbed 0 (spEmbed k.succAbove Fin.succAbove_right_injective y),
      ctEmbed_spEmbed_mem_q2Block k y⟩ = spModelSL m K y := by
  apply Subtype.ext
  ext i j
  rw [ctNbrSL_apply, ctEmbed_apply_q2Coord, fromBlocks_apply₁₁, mat_spEmbed,
    spEmbedMat_apply_image Fin.succAbove_right_injective, coe_spModelSL, submatrix_apply]
  rfl

theorem map_spModelSL [CharP K 2] {F : Type} [Field F] [CharP F 2] (σ : K →+* F)
    (y : StatedSp m K) :
    SpecialLinearGroup.map σ (spModelSL m K y) = spModelSL m F (statedSpMap σ m y) := by
  apply Subtype.ext
  ext i j
  change σ (((spModelSL m K y : SpecialLinearGroup (Fin (2 * m)) K) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) K) i j) = _
  rw [coe_spModelSL, coe_spModelSL, submatrix_apply, submatrix_apply, F4Pilot.coe_statedSpMap]
  rfl

end Coord

section Exists

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem nonempty_ctLinParam_linearEven {m f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 3 ≤ m)
    (e : L ≃* StatedSp (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (m + 1)) (hk : RootKindSp e t f k .linearEven) :
    Nonempty (CtLinParam 0 e k) := by
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  set X : Subgroup G := modelToG e (rootTorusSp K k) with hX
  have hN : t ∈ normalizer (centralizerPerfectCore X : Set G) := le_normalizer_neighbourCore e htC k
  obtain ⟨F, _, _, _, σ, ρ, hF, hρs, hρker, -, hρN1, -⟩ :=
    exists_normalized_neighbourCore_linearEven hset hKc hf hm e htC ht k rfl rfl hk hN
  set ψ : q2Block 0 K ({k} : Finset (Fin (m + 1))) →* SpecialLinearGroup (Fin (2 * m)) F :=
    (SpecialLinearGroup.map (σ : K →+* F)).comp (ctNbrSL k).toMonoidHom with hψ
  have hmapinj : Function.Injective (SpecialLinearGroup.map (n := Fin (2 * m)) (σ : K →+* F)) := by
    intro a b hab
    apply Subtype.ext
    ext i j
    have := congrArg (fun z : SpecialLinearGroup (Fin (2 * m)) F =>
      (z : Matrix (Fin (2 * m)) (Fin (2 * m)) F) i j) hab
    exact σ.injective this
  have hmapsurj : Function.Surjective (SpecialLinearGroup.map (n := Fin (2 * m))
      (σ : K →+* F)) := by
    intro g
    refine ⟨SpecialLinearGroup.map (σ.symm : F →+* K) g, ?_⟩
    apply Subtype.ext
    ext i j
    change σ (σ.symm _) = _
    rw [RingEquiv.apply_symm_apply]
  have hψinj : Function.Injective ψ := hmapinj.comp (ctNbrSL k).injective
  have hψs : Function.Surjective ψ := hmapsurj.comp (ctNbrSL k).surjective
  set χ : q2Block 0 K ({k} : Finset (Fin (m + 1))) →* LinearFlag.projectiveSL (2 * m) F :=
    (LinearFlag.proj (2 * m) F).comp ψ with hχ
  have hχs : Function.Surjective χ := (LinearFlag.proj_surjective _ _).comp hψs
  have hkerχ : χ.ker ≤ center (q2Block 0 K ({k} : Finset (Fin (m + 1)))) := by
    intro x hx
    have h1 : ψ x ∈ center (SpecialLinearGroup (Fin (2 * m)) F) := by
      rw [← LinearFlag.scalars_eq_center, ← LinearFlag.ker_proj]
      exact hx
    rw [mem_center_iff]
    intro g
    apply hψinj
    rw [map_mul, map_mul]
    exact mem_center_iff.1 h1 (ψ g)
  have hsplit : ∀ (E' : Type) [Group E'] [Finite E']
      (π' : E' →* q2Block 0 K ({k} : Finset (Fin (m + 1)))), Function.Surjective π' →
        π'.ker ≤ center E' → ∃ s : q2Block 0 K ({k} : Finset (Fin (m + 1))) →* E',
          ∀ g, π' (s g) = g := by
    obtain ⟨m', hm'⟩ : ∃ m', 2 * m = m' + 1 := ⟨2 * m - 1, by omega⟩
    refine F4Pilot.forall_exists_section_of_mulEquiv
      ((ctNbrSL k).trans (LinearPilot.reindexSpecialLinear (finCongr hm'))) ?_
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
  set ιB : StatedSp m K →* q2Block 0 K ({k} : Finset (Fin (m + 1))) :=
    ((ctEmbed 0).comp (spEmbed k.succAbove Fin.succAbove_right_injective)).codRestrict _
      (ctEmbed_spEmbed_mem_q2Block k) with hιB
  have : Group.IsPerfect (StatedSp m K) := isPerfect_statedSp_of_four_le hq m
  have heq : Φ₀.comp ιB = ιD := by
    refine LinearPilot.eq_of_comp_eq_of_ker_le_center (S := StatedSp m K) hρker fun x => ?_
    rw [MonoidHom.comp_apply, hΦ₀, hρN1 x (ιD x) rfl]
    change LinearFlag.proj (2 * m) F (SpecialLinearGroup.map (σ : K →+* F) (ctNbrSL k (ιB x))) = _
    have h1 : ctNbrSL k (ιB x) = spModelSL m K x := ctNbrSL_ctEmbed k x
    rw [h1, map_spModelSL]
    rfl
  refine ⟨⟨(centralizerPerfectCore X).subtype.comp Φ₀, ?_, ?_, ?_⟩⟩
  · intro x hx
    have hx₀ : Φ₀ x = 1 := (centralizerPerfectCore X).subtype_injective (by rw [map_one]; exact hx)
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

end CFSG.SeitzReduction.SymplecticPilot
