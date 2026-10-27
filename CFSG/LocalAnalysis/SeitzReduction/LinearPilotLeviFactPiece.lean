module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCores
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotLeviFact

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  {F : Type*} [Field F]

theorem apply_mem_blockTorus_of_mem_modelToG (e : L ≃* LinearFlag.projectiveSL n K)
    {I : Finset (Fin n)} {d : G} (hd : d ∈ modelToG e (blockTorus (K := K) I)) :
    e ⟨d, modelToG_le e _ hd⟩ ∈ blockTorus (K := K) I := by
  obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hd
  simpa using hy

theorem pieceCore_eq_map_of_conjDiag [Finite G] [Finite F] (e : L ≃* LinearFlag.projectiveSL n K)
    (ι : K →+* F) {N I : Finset (Fin n)} (hIN : I ⊆ N)
    (hsep : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → (i ∉ I ∨ j ∉ I) →
      ∃ c ∈ blockTorusParam (K := K) I, c i ≠ c j)
    (hperf : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear I)
    {X : Subgroup G} (hXI : X ≤ modelToG e (blockTorus (K := K) I))
    (Φ : blockSpecialLinear (K := F) N →* G) (hker : Φ.ker ≤ center (blockSpecialLinear (K := F) N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)), c.1 ∈ blockTorusParam I →
      ∀ x : blockSpecialLinear (K := F) N,
        Φ (conjDiag ι N c x) = ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) * Φ x *
          ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G)⁻¹) :
    pieceCore e I = ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N)).map Φ := by
  set T := modelToG e (blockTorus (K := K) I)
  let f : T → blockTorus (K := K) I := fun d =>
    ⟨e ⟨(d : G), modelToG_le e _ d.2⟩, apply_mem_blockTorus_of_mem_modelToG e d.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    refine ⟨⟨((e.symm y : L) : G), symm_mem_modelToG e hy⟩, Subtype.ext ?_⟩
    simp [f]
  have hα : ∀ (d : T) (x : blockSpecialLinear (K := F) N),
      Φ (conjDiag ι N (blockTorusLift (f d)) x) = (d : G) * Φ x * (d : G)⁻¹ := by
    intro d x
    rw [hΦ _ (blockTorusLift_mem (f d)) x, proj_torusDiagSL_blockTorusLift]
    have hd : ((e.symm ((f d : blockTorus (K := K) I) : LinearFlag.projectiveSL n K) : L) : G) =
        (d : G) := by
      simp [f]
    rw [hd]
  rw [pieceCore_def, centralizerPerfectCore_eq_map_of_le Φ hker hXI hrange
    (fun d => conjDiag ι N (blockTorusLift (f d))) hα]
  congr 1
  rw [show (fixAll fun d : T => conjDiag ι N (blockTorusLift (f d))) =
      fixAll (fun d : blockTorus (K := K) I => conjDiag ι N (blockTorusLift d)) from
    fixAll_comp_of_surjective (fun d : blockTorus (K := K) I => conjDiag ι N (blockTorusLift d)) hf]
  refine perfectCore_fixAll_conjDiag ι hIN _ blockTorusLift_mem (fun i hi j hj hij hIJ => ?_) hperf
  obtain ⟨c, hc, hcij⟩ := hsep i hi j hj hij hIJ
  exact exists_blockTorusLift_ne hc hcij

theorem pieceCore_eq_map_of_conjDiag_of_notMem [Finite G] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) (ι : K →+* F) {N I : Finset (Fin n)} (hIN : I ⊆ N)
    {k : Fin n} (hk : k ∉ N) {κ : Kˣ} (hκ : κ ≠ 1)
    (hperf : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear I)
    {X : Subgroup G} (hXI : X ≤ modelToG e (blockTorus (K := K) I))
    (Φ : blockSpecialLinear (K := F) N →* G) (hker : Φ.ker ≤ center (blockSpecialLinear (K := F) N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)), c.1 ∈ blockTorusParam I →
      ∀ x : blockSpecialLinear (K := F) N,
        Φ (conjDiag ι N c x) = ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) * Φ x *
          ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G)⁻¹) :
    pieceCore e I = ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N)).map Φ :=
  pieceCore_eq_map_of_conjDiag e ι hIN
    (fun _ hi _ hj hij hIJ => exists_mem_blockTorusParam_ne_of_notMem hIN hk hκ hi hj hij hIJ)
    hperf hXI Φ hker hrange hΦ

theorem pieceCore_eq_range_of_conjDiag [Finite G] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) (ι : K →+* F) {N : Finset (Fin n)}
    (hperf : ⁅blockSpecialLinear (K := F) N, blockSpecialLinear (K := F) N⁆ =
      blockSpecialLinear N)
    {X : Subgroup G} (hXN : X ≤ modelToG e (blockTorus (K := K) N))
    (Φ : blockSpecialLinear (K := F) N →* G) (hker : Φ.ker ≤ center (blockSpecialLinear (K := F) N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)), c.1 ∈ blockTorusParam N →
      ∀ x : blockSpecialLinear (K := F) N,
        Φ (conjDiag ι N c x) = ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) * Φ x *
          ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G)⁻¹) :
    pieceCore e N = Φ.range := by
  rw [pieceCore_eq_map_of_conjDiag e ι subset_rfl
    (fun _ hi _ hj _ hIJ => absurd hIJ (by simp [hi, hj])) hperf hXN Φ hker hrange hΦ,
    subgroupOf_self, ← MonoidHom.range_eq_map]

theorem map_eq_map_of_conjDiag [Finite G] [Finite F] (e : L ≃* LinearFlag.projectiveSL n K)
    (ι : K →+* F) {N N' I : Finset (Fin n)} (hIN : I ⊆ N) (hIN' : I ⊆ N')
    (hsep : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → (i ∉ I ∨ j ∉ I) →
      ∃ c ∈ blockTorusParam (K := K) I, c i ≠ c j)
    (hsep' : ∀ i ∈ N', ∀ j ∈ N', i ≠ j → (i ∉ I ∨ j ∉ I) →
      ∃ c ∈ blockTorusParam (K := K) I, c i ≠ c j)
    (hperf : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear I)
    {X X' : Subgroup G} (hXI : X ≤ modelToG e (blockTorus (K := K) I))
    (hXI' : X' ≤ modelToG e (blockTorus (K := K) I))
    (Φ : blockSpecialLinear (K := F) N →* G) (hker : Φ.ker ≤ center (blockSpecialLinear (K := F) N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)), c.1 ∈ blockTorusParam I →
      ∀ x : blockSpecialLinear (K := F) N,
        Φ (conjDiag ι N c x) = ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) * Φ x *
          ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G)⁻¹)
    (Φ' : blockSpecialLinear (K := F) N' →* G)
    (hker' : Φ'.ker ≤ center (blockSpecialLinear (K := F) N'))
    (hrange' : Φ'.range = centralizerPerfectCore X')
    (hΦ' : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)), c.1 ∈ blockTorusParam I →
      ∀ x : blockSpecialLinear (K := F) N',
        Φ' (conjDiag ι N' c x) = ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) * Φ' x *
          ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G)⁻¹) :
    ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N)).map Φ =
      ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N')).map Φ' := by
  rw [← pieceCore_eq_map_of_conjDiag e ι hIN hsep hperf hXI Φ hker hrange hΦ,
    ← pieceCore_eq_map_of_conjDiag e ι hIN' hsep' hperf hXI' Φ' hker' hrange' hΦ']

theorem nonempty_mulEquiv_pieceCore_of_conjDiag [Finite G] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) (ι : K →+* F) {N I : Finset (Fin n)} (hIN : I ⊆ N)
    (hne : I ≠ N)
    (hsep : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → (i ∉ I ∨ j ∉ I) →
      ∃ c ∈ blockTorusParam (K := K) I, c i ≠ c j)
    (hperf : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear I)
    {X : Subgroup G} (hXI : X ≤ modelToG e (blockTorus (K := K) I))
    (Φ : blockSpecialLinear (K := F) N →* G) (hker : Φ.ker ≤ center (blockSpecialLinear (K := F) N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)), c.1 ∈ blockTorusParam I →
      ∀ x : blockSpecialLinear (K := F) N,
        Φ (conjDiag ι N c x) = ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) * Φ x *
          ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G)⁻¹) :
    Nonempty (Matrix.SpecialLinearGroup (Fin I.card) F ≃* pieceCore e I) := by
  set H := (blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear (K := F) N)
  have hinj := injective_comp_subtype_of_ker_le_center hIN hne Φ hker
  have hrangeH : (Φ.comp H.subtype).range = pieceCore e I := by
    rw [MonoidHom.range_comp, range_subtype,
      pieceCore_eq_map_of_conjDiag e ι hIN hsep hperf hXI Φ hker hrange hΦ]
  have e₁ : H ≃* pieceCore e I :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrangeH)
  have e₂ : blockSpecialLinear (K := F) I ≃* H :=
    (Subgroup.subgroupOfEquivOfLe (blockSpecialLinear_mono hIN)).symm
  have e₃ : Matrix.SpecialLinearGroup (Fin I.card) F ≃* blockSpecialLinear (K := F) I :=
    (reindexSpecialLinear I.equivFin).symm.trans
      ((MonoidHom.ofInjective (blockEmbed_injective I)).trans
        (MulEquiv.subgroupCongr (range_blockEmbed I)))
  exact ⟨e₃.trans (e₂.trans e₁)⟩

theorem pieceCore_le_centralizer_pieceCore_of_disjoint [Finite G] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) (ι : K →+* F) {N I J : Finset (Fin n)} (hIN : I ⊆ N)
    (hJN : J ⊆ N) (hIJ : Disjoint I J)
    (hsepI : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → (i ∉ I ∨ j ∉ I) →
      ∃ c ∈ blockTorusParam (K := K) I, c i ≠ c j)
    (hsepJ : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → (i ∉ J ∨ j ∉ J) →
      ∃ c ∈ blockTorusParam (K := K) J, c i ≠ c j)
    (hperfI : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear I)
    (hperfJ : ⁅blockSpecialLinear (K := F) J, blockSpecialLinear (K := F) J⁆ =
      blockSpecialLinear J)
    {X : Subgroup G} (hXI : X ≤ modelToG e (blockTorus (K := K) I))
    (hXJ : X ≤ modelToG e (blockTorus (K := K) J))
    (Φ : blockSpecialLinear (K := F) N →* G) (hker : Φ.ker ≤ center (blockSpecialLinear (K := F) N))
    (hrange : Φ.range = centralizerPerfectCore X)
    (hΦ : ∀ (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) (x : blockSpecialLinear (K := F) N),
      Φ (conjDiag ι N c x) = ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) * Φ x *
        ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G)⁻¹) :
    pieceCore e I ≤ centralizer (pieceCore e J : Set G) := by
  rw [pieceCore_eq_map_of_conjDiag e ι hIN hsepI hperfI hXI Φ hker hrange (fun c _ => hΦ c),
    pieceCore_eq_map_of_conjDiag e ι hJN hsepJ hperfJ hXJ Φ hker hrange (fun c _ => hΦ c)]
  exact map_subgroupOf_le_centralizer_of_disjoint hIJ Φ

end CFSG.SeitzReduction.LinearPilot
