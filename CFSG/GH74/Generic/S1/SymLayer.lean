module

public import CFSG.GH74.Generic.S1.SymLift
public import CFSG.GH74.Generic.S1.FrameDefs

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic

variable {G : Type} [Group G] {F : Type} [Field F]

structure LayerData (y : G) (S : Subgroup (GL (Fin 4) F)) where
  K : Subgroup (CentralizerBar y)
  perf : ⁅K, K⁆ = K
  normal : K.Normal
  perf_le : ∀ P : Subgroup (CentralizerBar y), ⁅P, P⁆ = P → P ≤ K
  exact : LiftExact y K
  iso : ↥K ≃* ↥S

namespace LayerData

variable {y : G} {S : Subgroup (GL (Fin 4) F)} (D : LayerData y S)

instance : D.K.Normal := D.normal

variable [Finite G]

@[expose] noncomputable def liftIso : ↥S ≃* ↥(liftL y D.K) :=
  D.iso.symm.trans (liftEquiv D.exact D.perf).symm

@[expose] noncomputable def ιC : ↥S →* ↥(centralizer ({y} : Set G)) :=
  (liftL y D.K).subtype.comp D.liftIso.toMonoidHom

@[expose] noncomputable def ι : ↥S →* G :=
  (centralizer ({y} : Set G)).subtype.comp D.ιC

theorem ιC_mem (s : ↥S) : D.ιC s ∈ liftL y D.K := (D.liftIso s).2

theorem proj_ιC (s : ↥S) :
    proj y (D.ιC s) = ((D.iso.symm s : ↥D.K) : CentralizerBar y) := by
  have h : piL y D.K (D.liftIso s) = D.iso.symm s := by
    change (liftEquiv D.exact D.perf) ((liftEquiv D.exact D.perf).symm (D.iso.symm s)) = _
    exact MulEquiv.apply_symm_apply _ _
  exact congrArg Subtype.val h

theorem ιC_injective : Function.Injective D.ιC :=
  (Subgroup.subtype_injective _).comp D.liftIso.injective

theorem ι_injective : Function.Injective D.ι :=
  (Subgroup.subtype_injective _).comp D.ιC_injective

theorem ι_mem_cent (s : ↥S) : D.ι s ∈ centralizer ({y} : Set G) := (D.ιC s).2

theorem ι_comm_self (s : ↥S) : D.ι s * y = y * D.ι s :=
  mem_centralizer_singleton_iff.1 (D.ι_mem_cent s)

theorem ι_comm_of {w : G} (hw : w ∈ centralizer ({y} : Set G)) {r : GL (Fin 4) F}
    (hact : ActsAsReflOn D.iso (barOf hw) r) {s : ↥S}
    (hs : (s : GL (Fin 4) F) * r = r * (s : GL (Fin 4) F)) : D.ι s * w = w * D.ι s := by
  have hn := D.normal
  set W : ↥(centralizer ({y} : Set G)) := ⟨w, hw⟩ with hW
  set c : ↥(centralizer ({y} : Set G)) := D.ιC s with hc
  have hWb : proj y W = barOf hw := rfl
  set k : ↥D.K := D.iso.symm s with hk
  have hk' : barOf hw * (k : CentralizerBar y) * (barOf hw)⁻¹ ∈ D.K := hn.conj_mem _ k.2 _
  have hkk : (⟨barOf hw * (k : CentralizerBar y) * (barOf hw)⁻¹, hk'⟩ : ↥D.K) = k := by
    apply D.iso.injective
    have h1 := hact k ⟨_, hk'⟩ rfl
    apply Subtype.ext
    rw [h1]
    have h2 : D.iso k = s := D.iso.apply_symm_apply s
    rw [h2]
    have h3 : r * (s : GL (Fin 4) F) * r⁻¹ = (s : GL (Fin 4) F) := by
      rw [← hs]
      group
    exact h3
  have hconj : barOf hw * (k : CentralizerBar y) * (barOf hw)⁻¹ = (k : CentralizerBar y) :=
    congrArg Subtype.val hkk
  have hLn : (liftL y D.K).Normal := liftL_normal
  have hmem : W * c * W⁻¹ * c⁻¹ ∈ liftL y D.K :=
    (liftL y D.K).mul_mem (hLn.conj_mem c (D.ιC_mem s) W) ((liftL y D.K).inv_mem (D.ιC_mem s))
  have hproj : proj y (W * c * W⁻¹ * c⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hWb, hc, D.proj_ιC s, ← hk, hconj]
    simp
  have h1 : W * c * W⁻¹ * c⁻¹ = 1 := D.exact _ hmem hproj
  have h2 : W * c = c * W := by
    have := congrArg (fun z => z * c * W) h1
    simpa [mul_assoc] using this
  have h3 := congrArg Subtype.val h2
  exact h3.symm

theorem comm_of_ι_comm {w : G} (hw : w ∈ centralizer ({y} : Set G)) {r : GL (Fin 4) F}
    (hact : ActsAsReflOn D.iso (barOf hw) r) {s : ↥S} (hs : D.ι s * w = w * D.ι s) :
    (s : GL (Fin 4) F) * r = r * (s : GL (Fin 4) F) := by
  have hn := D.normal
  set k : ↥D.K := D.iso.symm s with hk
  have h1 : (⟨w, hw⟩ : ↥(centralizer ({y} : Set G))) * D.ιC s =
      D.ιC s * ⟨w, hw⟩ := Subtype.ext hs.symm
  have h2 := congrArg (proj y) h1
  rw [map_mul, map_mul, D.proj_ιC s] at h2
  have h3 : proj y (⟨w, hw⟩ : ↥(centralizer ({y} : Set G))) = barOf hw := rfl
  rw [h3, ← hk] at h2
  have hk' : barOf hw * (k : CentralizerBar y) * (barOf hw)⁻¹ ∈ D.K := hn.conj_mem _ k.2 _
  have hkk : (⟨barOf hw * (k : CentralizerBar y) * (barOf hw)⁻¹, hk'⟩ : ↥D.K) = k := by
    apply Subtype.ext
    show barOf hw * (k : CentralizerBar y) * (barOf hw)⁻¹ = (k : CentralizerBar y)
    rw [h2]
    group
  have h4 := hact k ⟨_, hk'⟩ rfl
  rw [hkk] at h4
  have h5 : D.iso k = s := D.iso.apply_symm_apply s
  rw [h5] at h4
  calc (s : GL (Fin 4) F) * r = r * (s : GL (Fin 4) F) * r⁻¹ * r := by rw [← h4]
    _ = r * (s : GL (Fin 4) F) := by group

theorem le_range_ι {R : Subgroup G} (hR : ⁅R, R⁆ = R) (hRy : R ≤ centralizer ({y} : Set G)) :
    R ≤ D.ι.range := by
  have hRcperf : ⁅R.subgroupOf (centralizer ({y} : Set G)),
      R.subgroupOf (centralizer ({y} : Set G))⁆ = R.subgroupOf (centralizer ({y} : Set G)) := by
    apply Subgroup.map_injective (centralizer ({y} : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hRy, hR]
  have hproj_perf : ⁅(R.subgroupOf (centralizer ({y} : Set G))).map (proj y),
      (R.subgroupOf (centralizer ({y} : Set G))).map (proj y)⁆ =
      (R.subgroupOf (centralizer ({y} : Set G))).map (proj y) := by
    rw [← Subgroup.map_commutator, hRcperf]
  have hle_K := D.perf_le _ hproj_perf
  have hRc_le : R.subgroupOf (centralizer ({y} : Set G)) ≤ D.K.comap (proj y) :=
    fun r hr => hle_K ⟨r, hr, rfl⟩
  have hRc_liftL := perfect_le_liftL hRc_le hRcperf
  intro g hg
  have hgc : (⟨g, hRy hg⟩ : ↥(centralizer ({y} : Set G))) ∈
      R.subgroupOf (centralizer ({y} : Set G)) := hg
  have hgl := hRc_liftL hgc
  refine ⟨D.liftIso.symm ⟨_, hgl⟩, ?_⟩
  change (((D.liftIso (D.liftIso.symm ⟨_, hgl⟩) : ↥(liftL y D.K)) :
    ↥(centralizer ({y} : Set G))) : G) = g
  rw [MulEquiv.apply_symm_apply]

end LayerData

end CFSG.GH74.Generic.S1
