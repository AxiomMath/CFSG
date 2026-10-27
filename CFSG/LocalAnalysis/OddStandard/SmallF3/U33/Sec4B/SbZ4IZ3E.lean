module

public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H]

@[expose] def z4iD (W : Subgroup H) : Subgroup H := ⁅W, W⁆

@[expose] def z4iVf (W : Subgroup H) : Subgroup H := ⁅z4iD W, z4iD W⁆

@[expose] def z4iFf (W : Subgroup H) : Subgroup H := W ⊓ centralizer (z4iVf W : Set H)

@[expose] def z4iQf (W : Subgroup H) : Subgroup H :=
  ⁅z4iFf W, z4iFf W⁆ ⊔ (W ⊓ centralizer (z4iD W : Set H))

private theorem map_inf_centralizer_of_injective {H' : Type*} [Group H'] (φ : H →* H')
    (hφ : Function.Injective φ) (A B : Subgroup H) :
    (A ⊓ centralizer (B : Set H)).map φ =
      A.map φ ⊓ centralizer ((B.map φ : Subgroup H') : Set H') := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxA, hxC⟩, rfl⟩
    refine ⟨⟨x, hxA, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxC b hb]
  · rintro ⟨⟨x, hxA, rfl⟩, hy⟩
    refine ⟨x, ⟨hxA, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩, rfl⟩
    have hb' := Subgroup.mem_centralizer_iff.mp hy (φ b) ⟨b, hb, rfl⟩
    exact hφ (by rw [map_mul, map_mul]; exact hb')

theorem z4iQf_map {H' : Type*} [Group H'] (φ : H →* H') (hφ : Function.Injective φ)
    (W : Subgroup H) : z4iQf (W.map φ) = (z4iQf W).map φ := by
  have hD : z4iD (W.map φ) = (z4iD W).map φ := by
    simp only [z4iD, Subgroup.map_commutator]
  have hV : z4iVf (W.map φ) = (z4iVf W).map φ := by
    simp only [z4iVf]
    rw [hD, Subgroup.map_commutator]
  have hF : z4iFf (W.map φ) = (z4iFf W).map φ := by
    simp only [z4iFf]
    rw [hV, ← map_inf_centralizer_of_injective φ hφ W (z4iVf W)]
  have hQ1 : ⁅z4iFf (W.map φ), z4iFf (W.map φ)⁆ = (⁅z4iFf W, z4iFf W⁆).map φ := by
    rw [hF, Subgroup.map_commutator]
  have hQ2 : (W.map φ) ⊓ centralizer (z4iD (W.map φ) : Set H') =
      (W ⊓ centralizer (z4iD W : Set H)).map φ := by
    rw [hD, ← map_inf_centralizer_of_injective φ hφ W (z4iD W)]
  simp only [z4iQf]
  rw [hQ1, hQ2, Subgroup.map_sup]

theorem z4iQf_conj_mem {W : Subgroup H} {g : H} (hg : g ∈ normalizer (W : Set H)) {x : H}
    (hx : x ∈ z4iQf W) : g * x * g⁻¹ ∈ z4iQf W := by
  have hmapW : W.map (MulAut.conj g).toMonoidHom = W :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have h := z4iQf_map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective W
  rw [hmapW] at h
  rw [h]
  simpa [MulAut.conj_apply] using Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx

theorem z4iQf_range {P : Type*} [Group P] {H' : Type*} [Group H'] (ψ : P →* H')
    (hψ : Function.Injective ψ) : z4iQf ψ.range = (z4iQf (⊤ : Subgroup P)).map ψ := by
  rw [MonoidHom.range_eq_map]
  exact z4iQf_map ψ hψ ⊤

theorem z4iQf_subtype (W : Subgroup H) :
    z4iQf W = (z4iQf (⊤ : Subgroup W)).map W.subtype := by
  have hW : (⊤ : Subgroup W).map W.subtype = W := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  conv_lhs => rw [← hW]
  exact z4iQf_map W.subtype W.subtype_injective ⊤

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
