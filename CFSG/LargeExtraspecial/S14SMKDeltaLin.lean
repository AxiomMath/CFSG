module

public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem finrank_map_add_finrank_inf_ker [FiniteDimensional (ZMod 2) V] (f : V →ₗ[ZMod 2] V)
    (W : Submodule (ZMod 2) V) :
    finrank (ZMod 2) (W.map f) + finrank (ZMod 2) (W ⊓ LinearMap.ker f : Submodule (ZMod 2) V) =
      finrank (ZMod 2) W := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict W)
  rw [LinearMap.range_domRestrict] at h
  have e : LinearMap.ker (f.domRestrict W) = (W ⊓ LinearMap.ker f).comap W.subtype := by
    ext v
    simp
  rw [e, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)] at h
  exact h

theorem sq_sub_one_eq (k : V ≃ₗ[ZMod 2] V) :
    (((k * k : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - 1) =
      ((k : V →ₗ[ZMod 2] V) - 1).comp ((k : V →ₗ[ZMod 2] V) - 1) := by
  ext v
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply,
    Module.End.one_apply, LinearMap.comp_apply, map_sub]
  have h2 : k v + k v = 0 := ZModModule.add_self _
  have : k (k v) - k v - (k v - v) = k (k v) - v + -(k v + k v) + (v + v) := by abel
  rw [this, h2, ZModModule.add_self, neg_zero, add_zero, add_zero]

variable {Q : QuadraticForm (ZMod 2) V}

theorem sub_mem_orthogonal {k : V ≃ₗ[ZMod 2] V} (hk : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {C : Submodule (ZMod 2) V} (hkC : ∀ c ∈ C, k c = c) (v : V) :
    k v - v ∈ LinearMap.BilinForm.orthogonal Q.polarBilin C := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro c hc
  show Q.polarBilin c (k v - v) = 0
  rw [polarBilin_apply_apply, polar_sub_right,
    ← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hk c v, hkC c hc, sub_self]

theorem commute_of_fix {k k' : V ≃ₗ[ZMod 2] V} (hk : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hk' : k' ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {C : Submodule (ZMod 2) V}
    (hC : LinearMap.BilinForm.orthogonal Q.polarBilin C ≤ C) (hkC : ∀ c ∈ C, k c = c)
    (hk'C : ∀ c ∈ C, k' c = c) : k * k' = k' * k := by
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have h1 := hk'C _ (hC (sub_mem_orthogonal hk hkC v))
  have h2 := hkC _ (hC (sub_mem_orthogonal hk' hk'C v))
  rw [map_sub] at h1 h2
  have e1 : k' (k v) = k v - v + k' v := by rw [← h1]; abel
  have e2 : k (k' v) = k' v - v + k v := by rw [← h2]; abel
  rw [e1, e2]
  abel

theorem mul_self_of_fix {k : V ≃ₗ[ZMod 2] V} (hk : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {C : Submodule (ZMod 2) V} (hC : LinearMap.BilinForm.orthogonal Q.polarBilin C ≤ C)
    (hkC : ∀ c ∈ C, k c = c) : k * k = 1 := by
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.coe_one, id]
  have h1 := hkC _ (hC (sub_mem_orthogonal hk hkC v))
  rw [map_sub] at h1
  have e1 : k (k v) = k v - v + k v := by rw [← h1]; abel
  rw [e1, sub_add_eq_add_sub, ZModModule.add_self, zero_sub, ZModModule.neg_eq_self]

theorem finrank_commSpace_le_four [FiniteDimensional (ZMod 2) V]
    (hQ : Q.polarBilin.Nondegenerate) {k : V ≃ₗ[ZMod 2] V}
    (hk : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs : k * k * (k * k) = 1)
    {H : Submodule (ZMod 2) V} (hH : H ≤ fixSpace (k * k))
    (hHc : finrank (ZMod 2) (fixSpace (k * k)) ≤ finrank (ZMod 2) H + 1)
    (hkH : finrank (ZMod 2) (H.map ((k : V →ₗ[ZMod 2] V) - 1)) ≤ 1) :
    finrank (ZMod 2) (commSpace (k * k)) ≤ 4 := by
  set f : V →ₗ[ZMod 2] V := (k : V →ₗ[ZMod 2] V) - 1 with hf
  set H0 : Submodule (ZMod 2) V := H ⊓ LinearMap.ker f with hH0
  set P := LinearMap.BilinForm.orthogonal Q.polarBilin H0 with hP
  have hr : LinearMap.range f ≤ P := by
    rintro _ ⟨v, rfl⟩
    refine sub_mem_orthogonal hk (fun h hh => ?_) v
    have h2 : f h = 0 := hh.2
    rw [hf, LinearMap.sub_apply, sub_eq_zero] at h2
    exact h2
  have hc : commSpace (k * k) ≤ P.map f := by
    rw [commSpace, sq_sub_one_eq, LinearMap.range_comp]
    exact Submodule.map_mono hr
  have hfixP : commSpace (k * k) ≤ P := by
    rintro _ ⟨w, rfl⟩
    refine sub_mem_orthogonal (mul_mem hk hk) (fun h hh => ?_) w
    exact mem_fixSpace.mp (hH hh.1)
  have d1 : finrank (ZMod 2) (P.map f) + finrank (ZMod 2) (P ⊓ LinearMap.ker f :
      Submodule (ZMod 2) V) = finrank (ZMod 2) P := finrank_map_add_finrank_inf_ker f P
  have d2 : finrank (ZMod 2) (H.map f) + finrank (ZMod 2) H0 = finrank (ZMod 2) H :=
    finrank_map_add_finrank_inf_ker f H
  have d3 : finrank (ZMod 2) P = finrank (ZMod 2) V - finrank (ZMod 2) H0 :=
    LinearMap.BilinForm.finrank_orthogonal hQ H0
  have d6 : finrank (ZMod 2) H0 ≤ finrank (ZMod 2) V := Submodule.finrank_le H0
  have hsub : H0 ⊓ commSpace (k * k) ≤ P ⊓ LinearMap.ker f :=
    fun v hv => ⟨hfixP hv.2, hv.1.2⟩
  have d4 := Submodule.finrank_sup_add_finrank_inf_eq H0 (commSpace (k * k))
  have hsup : H0 ⊔ commSpace (k * k) ≤ fixSpace (k * k) :=
    sup_le (inf_le_left.trans hH) (commSpace_le_fixSpace hs)
  have d5 := finrank_commSpace_add_finrank_fixSpace (k * k)
  have e1 := Submodule.finrank_mono hc
  have e2 := Submodule.finrank_mono hsub
  have e3 := Submodule.finrank_mono hsup
  omega

end CFSG.LargeExtraspecial.S14.SMK
