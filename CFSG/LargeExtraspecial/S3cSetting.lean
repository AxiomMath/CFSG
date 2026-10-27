module

public import CFSG.LargeExtraspecial.S3bEleven
public import CFSG.LargeExtraspecial.S3cTheta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def LbarLin (g : G) : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  (S.Lbar g).map S.O.subtype

theorem mem_LbarLin_iff {g : G} {t : S.Qt ≃ₗ[ZMod 2] S.Qt} :
    t ∈ S.LbarLin g ↔ ∃ s ∈ S.Lbar g, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) = t := by
  simp [LbarLin]

theorem coe_mem_LbarLin {g : G} {s : S.O} (hs : s ∈ S.Lbar g) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ S.LbarLin g :=
  S.mem_LbarLin_iff.mpr ⟨s, hs, rfl⟩

theorem le_of_forall_polar_eq_zero {W : Submodule (ZMod 2) S.Qt} (hW : ∀ w ∈ W, S.q w = 0)
    (hWn : finrank (ZMod 2) W = S.width) {x : S.Qt} (hx : ∀ w ∈ W, polar S.q x w = 0) :
    x ∈ W := by
  set X := LinearMap.BilinForm.orthogonal S.q.polarBilin W with hX
  have hWX : W ≤ X := by
    intro w hw
    rw [hX, LinearMap.BilinForm.mem_orthogonal_iff]
    intro w' hw'
    rw [polarBilin_apply_apply, polar, hW _ (W.add_mem hw' hw), hW _ hw', hW _ hw]
    simp
  have h1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
  rw [S.finrank_Qt_eq_two_mul_width, hWn] at h1
  have hXW : X = W := (Submodule.eq_of_le_of_finrank_le hWX (by rw [h1, hWn]; omega)).symm
  have hxX : x ∈ X := by
    rw [hX, LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [polarBilin_apply_apply, polar_comm]
    exact hx w hw
  rwa [hXW] at hxX

theorem transvectionConfig (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) :
    TransvectionConfig S.q (S.cl (g * S.z * g⁻¹)) (S.clSub (S.QG ⊓ S.Qa g)) (S.LbarLin g) := by
  obtain ⟨-, -, hWts, hWn, hC⟩ := (S.lemma_3_11_two hTI hn haQ hne hno).resolve_left hirr
  have htr := (S.lemma_3_11_transvections hTI hn haQ hne hno).resolve_left hirr
  have haW : S.cl (g * S.z * g⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) :=
    S.cl_mem_clSub ⟨haQ, S.conj_z_mem_Qa g⟩ haQ
  refine
    { haW := haW
      ha0 := S.cl_conj_z_ne_zero haQ hne
      totallySingular := hWts
      perp_le := fun x hx => S.le_of_forall_polar_eq_zero hWts hWn hx
      iso := ?_
      fix := ?_
      sq := ?_
      comm := ?_
      perp := ?_
      onW := ?_
      trans := ?_
      faithful := ?_ }
  · intro t ht x
    obtain ⟨s, -, rfl⟩ := S.mem_LbarLin_iff.mp ht
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp s.2 x
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := S.mem_LbarLin_iff.mp ht
    exact S.mem_fixLbar.mp (S.cl_mem_fixLbar_self haQ) s hs
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := S.mem_LbarLin_iff.mp ht
    have h := S.sq_eq_one_of_mem_Lbar haQ hs
    rw [pow_two] at h
    rw [← Subgroup.coe_mul, h]
    rfl
  · intro t ht t' ht'
    obtain ⟨s, hs, rfl⟩ := S.mem_LbarLin_iff.mp ht
    obtain ⟨s', hs', rfl⟩ := S.mem_LbarLin_iff.mp ht'
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, S.Lbar_comm haQ hs hs']
  · intro t ht x hx
    obtain ⟨s, hs, rfl⟩ := S.mem_LbarLin_iff.mp ht
    obtain ⟨w, hw, rfl⟩ := S.exists_cl x
    have hwa : w * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * w :=
      ((S.polar_cl_eq_zero_iff haQ hw).mp hx).symm
    exact S.sub_mem_clSub_of_mem_Lbar haQ hne hs hw hwa
  · intro t ht w hw
    obtain ⟨s, hs, rfl⟩ := S.mem_LbarLin_iff.mp ht
    exact S.sub_mem_span_of_mem_clSub hs hw
  · intro φ hφ
    obtain ⟨s, ⟨hs, hsw⟩, -⟩ := htr φ hφ
    exact ⟨s, S.coe_mem_LbarLin hs, hsw⟩
  · intro t ht hfix
    obtain ⟨s, hs, rfl⟩ := S.mem_LbarLin_iff.mp ht
    rw [hC s hs hfix]
    rfl

end Setting

end CFSG.LargeExtraspecial
