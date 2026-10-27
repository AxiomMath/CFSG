module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignTori

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

local instance f4PilotXiToralNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

variable {K : Type} [Field K]

section Torus

theorem rootChar_mul_left {τ : Tag} (a b : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_one_left {τ : Tag} (v : Fin τ.rank → ℤ) :
    rootChar (1 : Fin τ.rank → Kˣ) v = 1 := by
  simp only [rootChar, Pi.one_apply, one_zpow, Finset.prod_const_one]

theorem rootChar_comp_smul {τ : Tag} (a : Fin τ.rank → Kˣ) (w : WeylGroup τ)
    (v : Fin τ.rank → ℤ) :
    rootChar (fun j => rootChar a (w • (Pi.single j 1 : Fin τ.rank → ℤ))) v =
      rootChar a (w • v) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _
  rw [hw, rootChar_sum]
  conv_lhs => rw [hv, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul, rootChar_zsmul, rootChar_single_one]

variable (K) in
@[expose] noncomputable def kerTorus (γ : Fin (Tag.rank .F4) → ℤ) : Subgroup (ModGL .F4 K) where
  carrier := {g | ∃ a : Fin (Tag.rank .F4) → Kˣ, rootChar a γ = 1 ∧ rootDiagUnit .F4 a = g}
  one_mem' := ⟨1, rootChar_one_left γ, rootDiagUnit_one⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, by rw [rootChar_mul_left, ha, hb, one_mul], rootDiagUnit_mul a b⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, by rw [rootChar_inv_apply, ha, inv_one], ?_⟩
    rw [← mul_eq_one_iff_eq_inv, ← rootDiagUnit_mul, inv_mul_cancel, rootDiagUnit_one]

theorem mem_kerTorus {γ : Fin (Tag.rank .F4) → ℤ} {g : ModGL .F4 K} :
    g ∈ kerTorus K γ ↔ ∃ a : Fin (Tag.rank .F4) → Kˣ, rootChar a γ = 1 ∧ rootDiagUnit .F4 a = g :=
  Iff.rfl

theorem kerTorus_single (i : Fin (Tag.rank .F4)) :
    kerTorus K (Pi.single i 1) = leviTorus K {i} := by
  ext g
  rw [mem_kerTorus, mem_leviTorus]
  simp only [rootChar_single_one, Finset.mem_singleton, forall_eq]

theorem map_conj_canonicalRep_kerTorus (w : WeylGroup .F4) (γ : Fin (Tag.rank .F4) → ℤ) :
    (kerTorus K γ).map (MulAut.conj (canonicalRep (coxeterSystem .F4) K w)).toMonoidHom =
      kerTorus K (w • γ) := by
  ext g
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    set b : Fin (Tag.rank .F4) → Kˣ :=
      fun j => rootChar a (w⁻¹ • (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ)) with hb
    have hab : ∀ v, rootChar b (w • v) = rootChar a v := fun v => by
      rw [hb, rootChar_comp_smul, inv_smul_smul]
    refine ⟨b, by rw [hab, ha], ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact ((rootDiagUnit_eq_conj_canonicalRep_iff b a w).2 hab)
  · rintro ⟨b, hb, rfl⟩
    set a : Fin (Tag.rank .F4) → Kˣ :=
      fun j => rootChar b (w • (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ)) with ha
    have hab : ∀ v, rootChar b (w • v) = rootChar a v := fun v => by
      rw [ha, rootChar_comp_smul]
    refine ⟨rootDiagUnit .F4 a, ⟨a, by rw [← hab, hb], rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact ((rootDiagUnit_eq_conj_canonicalRep_iff b a w).2 hab).symm

end Torus

section Weyl

theorem map_conj_eq_self_of_mem_kerTorus_aux {G : Type*} [Group G] {C : Subgroup G} {n : G}
    (hn : n ∈ C) :
    C.map (MulAut.conj n).toMonoidHom = C := by
  ext g
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hn hx) (inv_mem hn)
  · intro hg
    exact ⟨n⁻¹ * g * n, mul_mem (mul_mem (inv_mem hn) hg) hn, by group⟩

theorem rootSpan_amalgamRoots_singleton_F4 (i : Fin (Tag.rank .F4)) :
    rootSpan .F4 K (amalgamRoots {i}) =
      rootSubgroup .F4 K (Pi.single i 1) ⊔ rootSubgroup .F4 K (-Pi.single i 1) := by
  refine le_antisymm (iSup₂_le fun α hα => ?_) (sup_le ?_ ?_)
  · obtain ⟨j, hj, rfl | rfl⟩ := hα
    · rw [Finset.mem_singleton.1 hj]
      exact le_sup_left
    · rw [Finset.mem_singleton.1 hj]
      exact le_sup_right
  · exact le_iSup₂_of_le (f := fun β (_ : β ∈ amalgamRoots {i}) => rootSubgroup .F4 K β)
      (Pi.single i 1) ⟨i, Finset.mem_singleton_self i, Or.inl rfl⟩ le_rfl
  · exact le_iSup₂_of_le (f := fun β (_ : β ∈ amalgamRoots {i}) => rootSubgroup .F4 K β)
      (-Pi.single i 1) ⟨i, Finset.mem_singleton_self i, Or.inr rfl⟩ le_rfl

theorem exists_weyl_kerTorus {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    ∃ (w : WeylGroup .F4) (i : Fin (Tag.rank .F4)),
      ((CFSG.LieType.Steinberg.Adjoint.iform γ γ = 4 ∧ i = 1) ∨
        (CFSG.LieType.Steinberg.Adjoint.iform γ γ = 2 ∧ i = 2)) ∧ w • γ = Pi.single i 1 ∧
      canonicalRep (coxeterSystem .F4) K w ∈ adjointGroup .F4 K ∧
      (kerTorus K γ).map (MulAut.conj (canonicalRep (coxeterSystem .F4) K w)).toMonoidHom =
        leviTorus K {i} ∧
      (rootSubgroup .F4 K γ).map
          (MulAut.conj (canonicalRep (coxeterSystem .F4) K w)).toMonoidHom =
        rootSubgroup .F4 K (Pi.single i 1) ∧
      (rootSubgroup .F4 K (-γ)).map
          (MulAut.conj (canonicalRep (coxeterSystem .F4) K w)).toMonoidHom =
        rootSubgroup .F4 K (-Pi.single i 1) := by
  have key : ∀ (w : WeylGroup .F4) (i : Fin (Tag.rank .F4)), w • γ = Pi.single i 1 →
      canonicalRep (coxeterSystem .F4) K w ∈ adjointGroup .F4 K ∧
      (kerTorus K γ).map (MulAut.conj (canonicalRep (coxeterSystem .F4) K w)).toMonoidHom =
        leviTorus K {i} ∧
      (rootSubgroup .F4 K γ).map
          (MulAut.conj (canonicalRep (coxeterSystem .F4) K w)).toMonoidHom =
        rootSubgroup .F4 K (Pi.single i 1) ∧
      (rootSubgroup .F4 K (-γ)).map
          (MulAut.conj (canonicalRep (coxeterSystem .F4) K w)).toMonoidHom =
        rootSubgroup .F4 K (-Pi.single i 1) := by
    intro w i hw
    refine ⟨canonicalRep_mem_adjointGroup _ K w, ?_, ?_, ?_⟩
    · rw [map_conj_canonicalRep_kerTorus, hw, kerTorus_single]
    · rw [(canonical_weyl_root_transport .F4 K).2.1 w γ hγ, hw]
    · rw [(canonical_weyl_root_transport .F4 K).2.1 w (-γ) (IsRoot.neg hγ), smul_neg, hw]
  rcases iform_self_eq_two_or_four hγ with h | h
  · obtain ⟨w₁, hw₁⟩ := exists_smul_eq_rootS hγ h
    obtain ⟨w₂, hw₂⟩ := exists_smul_eq_rootS (isRoot_single .F4 (2 : Fin (Tag.rank .F4)))
      (by decide +kernel)
    have hw : (w₂⁻¹ * w₁) • γ = Pi.single 2 1 := by
      rw [mul_smul, hw₁, ← hw₂, inv_smul_smul]
    exact ⟨w₂⁻¹ * w₁, 2, Or.inr ⟨h, rfl⟩, hw, key _ _ hw⟩
  · obtain ⟨w₁, hw₁⟩ := exists_smul_eq_rootR hγ h
    obtain ⟨w₂, hw₂⟩ := exists_smul_eq_rootR (isRoot_single .F4 (1 : Fin (Tag.rank .F4)))
      (by decide +kernel)
    have hw : (w₂⁻¹ * w₁) • γ = Pi.single 1 1 := by
      rw [mul_smul, hw₁, ← hw₂, inv_smul_smul]
    exact ⟨w₂⁻¹ * w₁, 1, Or.inl ⟨h, rfl⟩, hw, key _ _ hw⟩

theorem canonicalRep_mul_pinnedX_mul_inv_eq_single (h2 : (2 : K) = 0)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) {w : WeylGroup .F4} {i : Fin (Tag.rank .F4)}
    (hw : w • γ = Pi.single i 1) (c : K) :
    canonicalRep (coxeterSystem .F4) K w * pinnedX .F4 K γ c *
        (canonicalRep (coxeterSystem .F4) K w)⁻¹ = pinnedX .F4 K (Pi.single i 1) c := by
  rw [canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hγ c, hw]

end Weyl

end CFSG.SeitzReduction.F4Pilot
