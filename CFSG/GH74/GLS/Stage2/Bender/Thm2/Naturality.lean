module

import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Iso

theorem layer_map_mulEquiv {A B : Type} [Group A] [Group B] (f : A ≃* B) :
    (layer A).map f.toMonoidHom = layer B :=
  CFSG.WholeGroup.layer_map_mulEquiv f

theorem fitting_map_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B] (f : A ≃* B) :
    (fittingSubgroup A).map f.toMonoidHom = fittingSubgroup B :=
  CFSG.WholeGroup.fittingSubgroup_map_mulEquiv f

theorem generalizedFitting_map_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (f : A ≃* B) : (generalizedFitting A).map f.toMonoidHom = generalizedFitting B :=
  CFSG.WholeGroup.generalizedFitting_map_mulEquiv f

variable {G : Type} [Group G]

theorem inSubgroup_map [Finite G] (F : ∀ (K : Type) [Group K], Subgroup K)
    (hF : ∀ (A B : Type) [Group A] [Group B] [Finite A] [Finite B] (e : A ≃* B),
      (F A).map e.toMonoidHom = F B)
    (φ : G ≃* G) (M : Subgroup G) :
    inSubgroup F (M.map φ.toMonoidHom) = (inSubgroup F M).map φ.toMonoidHom := by
  unfold inSubgroup
  let e : ↥M ≃* ↥(M.map φ.toMonoidHom) := MulEquiv.subgroupMap φ M
  have h1 := hF ↥M ↥(M.map φ.toMonoidHom) e
  have hcomp : (M.map φ.toMonoidHom).subtype.comp e.toMonoidHom = φ.toMonoidHom.comp M.subtype := by
    ext x
    rfl
  rw [← h1, Subgroup.map_map, Subgroup.map_map, hcomp]

theorem Fs_map [Finite G] (φ : G ≃* G) (M : Subgroup G) :
    Fs (M.map φ.toMonoidHom) = (Fs M).map φ.toMonoidHom :=
  inSubgroup_map (fun K _ => generalizedFitting K) (fun _ _ _ _ _ _ e => generalizedFitting_map_mulEquiv e) φ M

theorem Op_map [Finite G] (p : ℕ) (φ : G ≃* G) (M : Subgroup G) :
    Op p (M.map φ.toMonoidHom) = (Op p M).map φ.toMonoidHom :=
  inSubgroup_map (pCore p) (fun _ _ _ _ _ _ e => CFSG.pCore_map_iso p e) φ M

theorem pPrimeCoreOf_map [Finite G] (p : ℕ) (φ : G ≃* G) (M : Subgroup G) :
    pPrimeCoreOf p (M.map φ.toMonoidHom) = (pPrimeCoreOf p M).map φ.toMonoidHom :=
  inSubgroup_map (pPrimeCore p) (fun _ _ _ _ _ _ e => CFSG.pPrimeCore_map_iso p e) φ M

theorem mem_normalizer_map_iff (φ : G ≃* G) (K : Subgroup G) (x : G) :
    φ x ∈ normalizer ((K.map φ.toMonoidHom : Subgroup G) : Set G) ↔ x ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (φ y)
    rw [show φ x * φ y * (φ x)⁻¹ = φ (x * y * x⁻¹) by simp [map_mul, map_inv]] at h1
    have h2 : φ (x * y * x⁻¹) ∈ K.map φ.toMonoidHom ↔ x * y * x⁻¹ ∈ K :=
      Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective
    have h3 : φ y ∈ K.map φ.toMonoidHom ↔ y ∈ K := Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective
    rw [h2, h3] at h1
    exact h1
  · intro h w
    obtain ⟨y, rfl⟩ := φ.surjective w
    rw [show φ x * φ y * (φ x)⁻¹ = φ (x * y * x⁻¹) by simp [map_mul, map_inv]]
    have h2 : φ (x * y * x⁻¹) ∈ K.map φ.toMonoidHom ↔ x * y * x⁻¹ ∈ K :=
      Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective
    have h3 : φ y ∈ K.map φ.toMonoidHom ↔ y ∈ K := Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective
    rw [h2, h3]
    exact h y

theorem zStar_map_of_mem [Finite G] (φ : G ≃* G) {M : Subgroup G} {z : G} (h : z ∈ zStar M) :
    φ z ∈ zStar (M.map φ.toMonoidHom) := by
  refine ⟨Subgroup.mem_map_of_mem _ h.1, (mem_normalizer_map_iff φ M z).mpr h.2.1, ?_, ?_⟩
  · rw [pPrimeCoreOf_map]
    exact (mem_normalizer_map_iff φ _ z).mpr h.2.2.1
  · intro kk hkk
    obtain ⟨k', hk', rfl⟩ := hkk
    rw [pPrimeCoreOf_map]
    have h1 := h.2.2.2 k' hk'
    have h2 : ⁅φ k', φ z⁆ = φ ⁅k', z⁆ := (map_commutatorElement φ k' z).symm
    show ⁅φ k', φ z⁆ ∈ (pPrimeCoreOf 2 M).map φ.toMonoidHom
    rw [h2]
    exact Subgroup.mem_map_of_mem _ h1

theorem mem_map_conj_iff (M : Subgroup G) (n x : G) :
    x ∈ M.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * x * n ∈ M := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hm
  · intro hx
    refine ⟨n⁻¹ * x * n, hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

end Iso

end CFSG.GH74.GLS.Stage2.Bender.Thm2
