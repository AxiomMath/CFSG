module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TrichotomyDefs
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TrichotomySetup
import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

namespace WreathCase

variable {X : Type*} [Group X] {t : X} {Sg V K : Subgroup X}

private theorem wt_mem_centralizer_map_conj_iff_aux {G : Type*} [Group G] (φ : G ≃* G)
    (L : Subgroup G) (y : G) :
    y ∈ centralizer ((L.map φ.toMonoidHom : Subgroup G) : Set G) ↔
      φ.symm y ∈ centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have h' := h (φ k) (by exact ⟨k, hk, rfl⟩)
    simpa [map_mul] using congrArg φ.symm h'
  · intro h a ha
    obtain ⟨k, hk, rfl⟩ := ha
    have h' := h k hk
    simpa [map_mul] using congrArg φ h'

theorem t_mul_t (H : WreathCase t Sg V K) : t * t = 1 := by
  simpa [pow_two] using H.shape.sq_eq_one

theorem conj_conj (H : WreathCase t Sg V K) (x : X) : t * (t * x * t⁻¹) * t⁻¹ = x := by
  have hsq : MulAut.conj t * MulAut.conj t = 1 := by
    rw [← map_mul, H.t_mul_t, map_one]
  have h := congrFun (congrArg DFunLike.coe hsq) x
  simpa [MulAut.conj_apply] using h

theorem commutator_eq (H : WreathCase t Sg V K) : ⁅K, K⁆ = K := by
  exact Subgroup.isPerfect_iff.mp H.isComponent.1.1

theorem isComponent_map (H : WreathCase t Sg V K) :
    CFSG.IsComponent (K.map (MulAut.conj t).toMonoidHom) := by
  exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) H.isComponent

theorem le_layer (H : WreathCase t Sg V K) : K ≤ CFSG.layer X := by
  exact CFSG.LocalCores.component_le_layer H.isComponent

theorem mem_normalizer_xor (H : WreathCase t Sg V K) (x : X) :
    Xor' (x * t ∈ normalizer (K : Set X)) (x ∈ normalizer (K : Set X)) := by
  have hxA : x ∈ normalizer (K : Set X) ↔ K.map (MulAut.conj x).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq
  have hB_eq : (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj x).toMonoidHom
      = K.map (MulAut.conj (x * t)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [MonoidHom.comp_apply, MulAut.conj_apply, mul_assoc]
  have hxtB : x * t ∈ normalizer (K : Set X) ↔
      (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj x).toMonoidHom = K := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hB_eq]
    rfl
  have hAcomp : CFSG.IsComponent (K.map (MulAut.conj x).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) H.isComponent
  have hBcomp : CFSG.IsComponent
      ((K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj x).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) H.isComponent_map
  have hAB : K.map (MulAut.conj x).toMonoidHom ≠
      (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    intro hab
    exact H.map_ne (Subgroup.map_injective (MulAut.conj x).injective hab).symm
  change Xor (x * t ∈ normalizer (K : Set X)) (x ∈ normalizer (K : Set X))
  rw [xor_def]
  by_cases hx : x ∈ normalizer (K : Set X)
  · refine Or.inr ⟨hx, ?_⟩
    intro hxt
    exact hAB (hxA.mp hx |>.trans (hxtB.mp hxt).symm)
  · refine Or.inl ⟨?_, hx⟩
    have hAK : K.map (MulAut.conj x).toMonoidHom ≠ K := fun h => hx (hxA.mpr h)
    have hAKt : K.map (MulAut.conj x).toMonoidHom
        = K.map (MulAut.conj t).toMonoidHom := by
      rcases H.eq_or_eq _ hAcomp with h | h
      · exact absurd h hAK
      · exact h
    have hBK : (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj x).toMonoidHom = K := by
      rcases H.eq_or_eq _ hBcomp with h | h
      · exact h
      · exact absurd (hAKt.trans h.symm) hAB
    exact hxtB.mpr hBK

theorem normalizer_index_eq_two (H : WreathCase t Sg V K) :
    (normalizer (K : Set X)).index = 2 := by
  exact Subgroup.index_eq_two_iff.mpr ⟨t, fun b => H.mem_normalizer_xor b⟩

theorem normal_normalizer (H : WreathCase t Sg V K) : (normalizer (K : Set X)).Normal := by
  exact Subgroup.normal_of_index_eq_two H.normalizer_index_eq_two

theorem conj_t_mem_normalizer (H : WreathCase t Sg V K) {y : X}
    (hy : y ∈ normalizer (K : Set X)) : t * y * t⁻¹ ∈ normalizer (K : Set X) := by
  exact H.normal_normalizer.conj_mem y hy t

theorem map_conj_le_normalizer (H : WreathCase t Sg V K) :
    K.map (MulAut.conj t).toMonoidHom ≤ normalizer (K : Set X) := by
  have h : K.map (MulAut.conj t).toMonoidHom ≤ centralizer (K : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
      rw [Subgroup.commutator_comm]; exact H.comm)
  exact h.trans (Subgroup.centralizer_le_normalizer (K : Set X))

theorem layer_le_normalizer (H : WreathCase t Sg V K) :
    CFSG.layer X ≤ normalizer (K : Set X) := by
  rw [H.layer_eq]
  exact sup_le Subgroup.le_normalizer H.map_conj_le_normalizer

theorem centralizer_layer_le_normalizer (H : WreathCase t Sg V K) :
    centralizer (CFSG.layer X : Set X) ≤ normalizer (K : Set X) := by
  exact (Subgroup.centralizer_le H.le_layer).trans
    (Subgroup.centralizer_le_normalizer (K : Set X))

theorem mem_centralizer_map_conj_iff (H : WreathCase t Sg V K) (y : X) :
    y ∈ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X) ↔
      t * y * t⁻¹ ∈ centralizer (K : Set X) := by
  rw [wt_mem_centralizer_map_conj_iff_aux (MulAut.conj t) K y, MulAut.conj_symm_apply,
    inv_eq_of_mul_eq_one_right H.t_mul_t]

theorem mem_centralizer_layer_iff (H : WreathCase t Sg V K) (y : X) :
    y ∈ centralizer (CFSG.layer X : Set X) ↔
      y ∈ centralizer (K : Set X) ∧ t * y * t⁻¹ ∈ centralizer (K : Set X) := by
  rw [H.layer_eq]
  constructor
  · intro hy
    have hy' := Subgroup.mem_centralizer_iff.mp hy
    have hyK : y ∈ centralizer (K : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => hy' k (Subgroup.mem_sup_left hk)
    have hyKt : y ∈ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk => hy' k (Subgroup.mem_sup_right hk)
    exact ⟨hyK, H.mem_centralizer_map_conj_iff y |>.mp hyKt⟩
  · intro ⟨hK, hz⟩
    have hKt : y ∈ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X) :=
      H.mem_centralizer_map_conj_iff y |>.mpr hz
    have hAy : K ≤ centralizer ({y} : Set X) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro z hz'
      rw [Set.mem_singleton_iff] at hz'
      subst hz'
      exact (Subgroup.mem_centralizer_iff.mp hK k hk).symm
    have hBy : K.map (MulAut.conj t).toMonoidHom ≤ centralizer ({y} : Set X) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro z hz'
      rw [Set.mem_singleton_iff] at hz'
      subst hz'
      exact (Subgroup.mem_centralizer_iff.mp hKt k hk).symm
    have hsup : K ⊔ K.map (MulAut.conj t).toMonoidHom ≤ centralizer ({y} : Set X) :=
      sup_le hAy hBy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hsup ha) y (Set.mem_singleton y)).symm

end WreathCase

end CFSG.OddStandard.AltStdSec.SwapPartner
