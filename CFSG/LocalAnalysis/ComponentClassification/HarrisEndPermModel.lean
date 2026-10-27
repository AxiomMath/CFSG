module

public import CFSG.Sporadic.HeldB.FixedTransport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGField

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.HarrisEnd

open CFSG Subgroup

variable {n : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))}

structure PermAutModel (Y : Type) [Group Y] (P R : Subgroup (Equiv.Perm (Fin n))) where
  θ : Y ≃* P
  Φ : MulAut Y ≃* R
  conj : ∀ y : Y, ((Φ (MulAut.conj y) : R) : Equiv.Perm (Fin n)) = θ y
  apply : ∀ (τ : MulAut Y) (y : Y), ((θ (τ y) : P) : Equiv.Perm (Fin n)) =
    (Φ τ : Equiv.Perm (Fin n)) * θ y * (Φ τ : Equiv.Perm (Fin n))⁻¹

variable {Y : Type} [Group Y]

theorem nonempty_permAutModel (θ : Y ≃* P) (hPR : P ≤ R) (e : R ≃* MulAut P)
    (he : ∀ (r : R) (s : P), ((e r s : P) : Equiv.Perm (Fin n)) = r * s * r⁻¹) :
    Nonempty (PermAutModel Y P R) := by
  refine ⟨⟨θ, (MulAut.congr θ).trans e.symm, fun y => ?_, fun τ y => ?_⟩⟩
  · have h1 : MulAut.congr θ (MulAut.conj y) = e ⟨θ y, hPR (θ y).2⟩ := by
      rw [Sporadic.HeldB.congr_conj]
      ext s
      rw [he]
      simp [MulAut.conj_apply]
    simp only [MulEquiv.trans_apply, h1, MulEquiv.symm_apply_apply]
  · have h := he (((MulAut.congr θ).trans e.symm) τ) (θ y)
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, Sporadic.HeldB.congr_apply',
      MulEquiv.symm_apply_apply] at h
    exact h

namespace PermAutModel

variable (M : PermAutModel Y P R)

theorem mem_innAut_iff (τ : MulAut Y) :
    τ ∈ innAut Y ↔ ((M.Φ τ : R) : Equiv.Perm (Fin n)) ∈ P := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [M.conj]
    exact (M.θ y).2
  · intro h
    refine ⟨M.θ.symm ⟨_, h⟩, M.Φ.injective (Subtype.ext ?_)⟩
    rw [M.conj, MulEquiv.apply_symm_apply]

theorem nonempty_fixedPoints_equiv (τ : MulAut Y) :
    Nonempty (↥(fixedPoints τ) ≃*
      ↥(centralizer {((M.Φ τ : R) : Equiv.Perm (Fin n))} ⊓ P)) := by
  set f : Y →* Equiv.Perm (Fin n) := P.subtype.comp M.θ.toMonoidHom with hf
  have hinj : Function.Injective f := fun a b h => M.θ.injective (Subtype.ext h)
  have hmap : (fixedPoints τ).map f = centralizer {((M.Φ τ : R) : Equiv.Perm (Fin n))} ⊓ P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, (M.θ y).2⟩
      have h1 := M.apply τ y
      rw [show τ y = y from hy] at h1
      change ((M.θ y : P) : Equiv.Perm (Fin n)) * _ = _ * (M.θ y : P)
      calc ((M.θ y : P) : Equiv.Perm (Fin n)) * ((M.Φ τ : R) : Equiv.Perm (Fin n)) =
          (M.Φ τ : Equiv.Perm (Fin n)) * (M.θ y : P) * (M.Φ τ : Equiv.Perm (Fin n))⁻¹ *
            (M.Φ τ : Equiv.Perm (Fin n)) := by rw [← h1]
        _ = _ := by group
    · intro hx
      obtain ⟨hxc, hxP⟩ := mem_inf.mp hx
      refine ⟨M.θ.symm ⟨x, hxP⟩, ?_, by simp [hf]⟩
      change τ (M.θ.symm ⟨x, hxP⟩) = M.θ.symm ⟨x, hxP⟩
      apply M.θ.injective
      apply Subtype.ext
      rw [M.apply, MulEquiv.apply_symm_apply]
      have h1 : x * (M.Φ τ : Equiv.Perm (Fin n)) = (M.Φ τ : Equiv.Perm (Fin n)) * x :=
        mem_centralizer_singleton_iff.mp hxc
      change (M.Φ τ : Equiv.Perm (Fin n)) * x * (M.Φ τ : Equiv.Perm (Fin n))⁻¹ = x
      rw [← h1]
      group
  exact ⟨((fixedPoints τ).equivMapOfInjective f hinj).trans (MulEquiv.subgroupCongr hmap)⟩

end PermAutModel

theorem map_conj_centralizer_inf_of_normalizer {M : Type*} [Group M] {H : Subgroup M} {c : M}
    (hc : c ∈ normalizer (H : Set M)) (y : M) :
    (centralizer {c * y * c⁻¹} ⊓ H).map (MulAut.conj c⁻¹).toMonoidHom = centralizer {y} ⊓ H := by
  ext z
  rw [mem_map, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [mem_inf, mem_centralizer_singleton_iff] at hg
    obtain ⟨hgc, hg⟩ := hg
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine ⟨?_, ?_⟩
    · calc c⁻¹ * g * c * y = c⁻¹ * (g * (c * y * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * y * c⁻¹) * g) * c := by rw [hgc]
        _ = y * (c⁻¹ * g * c) := by group
    · have h1 := (mem_normalizer_iff.mp (inv_mem hc) g).mp hg
      rwa [inv_inv] at h1
  · rintro ⟨hzy, hz⟩
    refine ⟨c * z * c⁻¹, mem_inf.mpr ⟨?_, (mem_normalizer_iff.mp hc z).mp hz⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      calc c * z * c⁻¹ * (c * y * c⁻¹) = c * (z * y) * c⁻¹ := by group
        _ = c * (y * z) * c⁻¹ := by rw [hzy]
        _ = c * y * c⁻¹ * (c * z * c⁻¹) := by group
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group

theorem nonempty_centralizer_conj_equiv' {x r c : Equiv.Perm (Fin n)}
    (hc : c ∈ normalizer (P : Set (Equiv.Perm (Fin n)))) (hx : x = c * r * c⁻¹) :
    Nonempty (↥(centralizer {x} ⊓ P) ≃* ↥(centralizer {r} ⊓ P)) := by
  subst hx
  exact ⟨((centralizer {c * r * c⁻¹} ⊓ P).equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective).trans
      (MulEquiv.subgroupCongr (map_conj_centralizer_inf_of_normalizer hc r))⟩

end CFSG.ComponentClassification.HarrisLit.HarrisEnd
