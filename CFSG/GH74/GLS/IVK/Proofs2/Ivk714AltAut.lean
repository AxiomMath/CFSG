module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

section AltAut

variable {n : ℕ} {X : Type} [Group X]

@[expose] noncomputable def altAutPhi (hn : 7 ≤ n) :
    Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
  MulEquiv.ofBijective
    (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
      Perm (Fin n) →* MulAut (alternatingGroup (Fin n)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by omega) (by omega))

theorem altAutPhi_apply (hn : 7 ≤ n) (σ : Perm (Fin n)) : altAutPhi hn σ = MulAut.conjNormal σ :=
  rfl

@[expose] noncomputable def altAutEquiv (hn : 7 ≤ n) (e : X ≃* alternatingGroup (Fin n)) :
    MulAut X ≃* Perm (Fin n) :=
  (MulAut.congr e).trans (altAutPhi hn).symm

@[expose] noncomputable def psiAlt (e : X ≃* alternatingGroup (Fin n)) : X →* Perm (Fin n) :=
  (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom

theorem psiAlt_apply (e : X ≃* alternatingGroup (Fin n)) (k : X) :
    psiAlt e k = ((e k : alternatingGroup (Fin n)) : Perm (Fin n)) := rfl

theorem psiAlt_injective (e : X ≃* alternatingGroup (Fin n)) : Function.Injective (psiAlt e) :=
  (Subgroup.subtype_injective _).comp e.injective

theorem psiAlt_mem (e : X ≃* alternatingGroup (Fin n)) (k : X) :
    psiAlt e k ∈ alternatingGroup (Fin n) := (e k).2

theorem altAutEquiv_spec (hn : 7 ≤ n) (e : X ≃* alternatingGroup (Fin n)) (y : MulAut X) (k : X) :
    psiAlt e (y k) = altAutEquiv hn e y * psiAlt e k * (altAutEquiv hn e y)⁻¹ := by
  have h1 : altAutPhi hn (altAutEquiv hn e y) = MulAut.congr e y :=
    (altAutPhi hn).apply_symm_apply _
  rw [altAutPhi_apply] at h1
  have h2 : e (y k) = MulAut.congr e y (e k) := by simp [MulAut.congr_apply]
  rw [psiAlt_apply, psiAlt_apply, h2, ← h1, MulAut.conjNormal_apply]

theorem altAutEquiv_unique (hn : 7 ≤ n) (e : X ≃* alternatingGroup (Fin n)) (y : MulAut X)
    (τ : Perm (Fin n)) (h : ∀ k : X, psiAlt e (y k) = τ * psiAlt e k * τ⁻¹) :
    τ = altAutEquiv hn e y := by
  apply (altAutPhi hn).injective
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  obtain ⟨k, rfl⟩ := e.surjective a
  have hl : ((altAutPhi hn τ (e k) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      τ * (e k : Perm (Fin n)) * τ⁻¹ := by
    rw [altAutPhi_apply, MulAut.conjNormal_apply]
  have hr : ((altAutPhi hn (altAutEquiv hn e y) (e k) : alternatingGroup (Fin n)) :
      Perm (Fin n)) = altAutEquiv hn e y * (e k : Perm (Fin n)) * (altAutEquiv hn e y)⁻¹ := by
    rw [altAutPhi_apply, MulAut.conjNormal_apply]
  rw [hl, hr, ← psiAlt_apply, ← altAutEquiv_spec hn e y k]
  exact (h k).symm

theorem altAutEquiv_conj (hn : 7 ≤ n) (e : X ≃* alternatingGroup (Fin n)) (k : X) :
    altAutEquiv hn e (MulAut.conj k) = psiAlt e k := by
  symm
  apply altAutEquiv_unique
  intro x
  simp [psiAlt, MulAut.conj_apply]

theorem fixedSubgroup_map_alt (hn : 7 ≤ n) (e : X ≃* alternatingGroup (Fin n)) (y : MulAut X) :
    (fixedSubgroup X y).map (psiAlt e) =
      centralizer ({altAutEquiv hn e y} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n) := by
  have hψy : ∀ k : X, psiAlt e (y k) = altAutEquiv hn e y * psiAlt e k * (altAutEquiv hn e y)⁻¹ :=
    fun k => altAutEquiv_spec hn e y k
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : y k = k := hk
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, (e k).2⟩
    have := hψy k
    rw [hk'] at this
    calc psiAlt e k * altAutEquiv hn e y =
          altAutEquiv hn e y * psiAlt e k * (altAutEquiv hn e y)⁻¹ * altAutEquiv hn e y := by
          rw [← this]
      _ = altAutEquiv hn e y * psiAlt e k := by group
  · rintro ⟨hxc, hxA⟩
    refine ⟨e.symm ⟨x, hxA⟩, ?_, by simp [psiAlt]⟩
    show y (e.symm ⟨x, hxA⟩) = e.symm ⟨x, hxA⟩
    apply psiAlt_injective e
    rw [hψy]
    have hx : altAutEquiv hn e y * x = x * altAutEquiv hn e y :=
      (Subgroup.mem_centralizer_singleton_iff.1 hxc).symm
    have : psiAlt e (e.symm ⟨x, hxA⟩) = x := by simp [psiAlt]
    rw [this]
    calc altAutEquiv hn e y * x * (altAutEquiv hn e y)⁻¹ =
          x * altAutEquiv hn e y * (altAutEquiv hn e y)⁻¹ := by rw [hx]
      _ = x := by group

theorem innAut_map_alt (hn : 7 ≤ n) (e : X ≃* alternatingGroup (Fin n)) :
    (CFSG.GH74.GLS.IVK.innAut X).map (altAutEquiv hn e).toMonoidHom = alternatingGroup (Fin n) := by
  ext x
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    have : (altAutEquiv hn e).toMonoidHom (MulAut.conj k) = psiAlt e k := altAutEquiv_conj hn e k
    rw [this]
    exact (e k).2
  · intro hx
    refine ⟨MulAut.conj (e.symm ⟨x, hx⟩), ⟨_, rfl⟩, ?_⟩
    have : (altAutEquiv hn e).toMonoidHom (MulAut.conj (e.symm ⟨x, hx⟩)) =
        psiAlt e (e.symm ⟨x, hx⟩) := altAutEquiv_conj hn e _
    rw [this]
    simp [psiAlt]

end AltAut

end CFSG.GH74.GLS.IVK.Proofs2
