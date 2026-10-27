module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

@[expose] def FusedPGL {X : Type} [Group X] (z : X) (E : Subgroup X) (n : X) (q : ℕ) : Prop :=
  ∃ Z : Subgroup X, Z ≤ centralizer (E : Set X) ∧ Z ≤ E ⊔ zpowers n ∧ z ∈ Z ∧ n * n ∈ E ⊔ Z ∧
    ∃ _ : (Z.subgroupOf (E ⊔ zpowers n)).Normal,
      IVK.IsPGL2 (↥(E ⊔ zpowers n) ⧸ Z.subgroupOf (E ⊔ zpowers n)) (fun r => r = q)

theorem FusedPGL.map {X Y : Type} [Group X] [Group Y] (Φ : X ≃* Y) {z : X} {E : Subgroup X} {n : X}
    {q : ℕ} (h : FusedPGL z E n q) :
    FusedPGL (Φ z) (E.map Φ.toMonoidHom) (Φ n) q := by
  obtain ⟨Z, hZC, hZB, hzZ, hsq, hn, F₀, iF, fF, hP, ⟨φ⟩⟩ := h
  have hB : (E ⊔ zpowers n).map Φ.toMonoidHom = E.map Φ.toMonoidHom ⊔ zpowers (Φ n) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  set E' : Subgroup Y := E.map Φ.toMonoidHom with hE'
  set Z' : Subgroup Y := Z.map Φ.toMonoidHom with hZ'
  let e : ↥(E ⊔ zpowers n) ≃* ↥(E' ⊔ zpowers (Φ n)) :=
    (MulEquiv.subgroupMap Φ (E ⊔ zpowers n)).trans (MulEquiv.subgroupCongr hB)
  have he : ∀ x, ((e x : ↥(E' ⊔ zpowers (Φ n))) : Y) = Φ x := fun x => rfl
  have hN : (Z.subgroupOf (E ⊔ zpowers n)).map e.toMonoidHom =
      Z'.subgroupOf (E' ⊔ zpowers (Φ n)) := by
    ext x
    obtain ⟨h, rfl⟩ := e.surjective x
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, he]
    constructor
    · intro hh
      exact Subgroup.mem_map_of_mem _ hh
    · intro hh
      obtain ⟨y, hy, hyh⟩ := Subgroup.mem_map.1 hh
      have : y = (h : X) := Φ.injective hyh
      rw [← this]
      exact hy
  have hn' : (Z'.subgroupOf (E' ⊔ zpowers (Φ n))).Normal := by
    rw [← hN]
    exact hn.map e.toMonoidHom e.surjective
  refine ⟨Z', ?_, ?_, ?_, ?_, hn', F₀, iF, fF, hP, ⟨?_⟩⟩
  · rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    show Φ a * Φ c = Φ c * Φ a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_iff.1 (hZC hc) a ha
  · rw [← hB]
    exact Subgroup.map_mono hZB
  · exact Subgroup.mem_map_of_mem _ hzZ
  · have : E' ⊔ Z' = (E ⊔ Z).map Φ.toMonoidHom := by rw [hE', hZ', Subgroup.map_sup]
    rw [this, ← map_mul]
    exact Subgroup.mem_map_of_mem _ hsq
  · haveI := hn
    haveI := hn'
    exact (QuotientGroup.congr _ _ e hN).symm.trans φ

theorem FusedPGL.inv {X : Type} [Group X] {z : X} {E : Subgroup X} {n : X} {q : ℕ}
    (h : FusedPGL z E n q) : FusedPGL z E n⁻¹ q := by
  rw [FusedPGL, Subgroup.zpowers_inv]
  obtain ⟨Z, hZC, hZB, hzZ, hsq, hn⟩ := h
  refine ⟨Z, hZC, hZB, hzZ, ?_, hn⟩
  rw [← mul_inv_rev]
  exact (E ⊔ Z).inv_mem hsq

end CFSG.GH74.GLS.Stage1.Main
