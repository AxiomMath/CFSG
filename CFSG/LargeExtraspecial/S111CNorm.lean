module

public import CFSG.LargeExtraspecial.S111CKbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}

omit [Finite G] in
theorem map_conj_inv_eq {h : G} (hAh : A.map (MulAut.conj h).toMonoidHom = A) :
    A.map (MulAut.conj h⁻¹).toMonoidHom = A := by
  have e := map_conj_inv_map_conj A h
  rwa [hAh] at e

omit [Finite G] in
theorem conj_mem_of_map_eq {h x : G} (hAh : A.map (MulAut.conj h).toMonoidHom = A)
    (hx : x ∈ A) : h * x * h⁻¹ ∈ A := by
  rw [← hAh, mem_map_conj_iff]
  simpa [mul_assoc] using hx

theorem ρ_apply_mem_clSub {m : S.M} (hAm : A.map (MulAut.conj (m : G)).toMonoidHom = A)
    {v : S.Qt} (hv : v ∈ S.clSub A) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub A := by
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.ρ_cl m hxQ]
  exact S.cl_mem_clSub (conj_mem_of_map_eq hAm hx) (S.conj_mem_QG m.2 hxQ)

theorem mem_normalizer_ptFix_clSub {m : S.M}
    (hAm : A.map (MulAut.conj (m : G)).toMonoidHom = A) :
    S.ρ m ∈ normalizer (ptFix S (S.clSub A) : Set S.O) := by
  refine mem_normalizer_ptFix (fun w hw => ρ_apply_mem_clSub hAm hw) fun w hw => ?_
  rw [← map_inv]
  exact ρ_apply_mem_clSub (m := m⁻¹) (by rw [coe_inv]; exact map_conj_inv_eq hAm) hw

theorem map_Kbar {m : S.M} (hAm : A.map (MulAut.conj (m : G)).toMonoidHom = A) (k : G) :
    (Kbar S A k).map (MulAut.conj (S.ρ m)).toMonoidHom = Kbar S A ((m : G) * k) := by
  rw [Kbar, Kbar, map_inf _ _ _ (MulAut.conj (S.ρ m)).injective, ← Lbar_mul]
  congr 1
  exact mem_normalizer_iff_map_conj_eq.mp (mem_normalizer_ptFix_clSub hAm)

theorem map_Ybar_le {m : S.M} (hAm : A.map (MulAut.conj (m : G)).toMonoidHom = A) :
    (Ybar S A).map (MulAut.conj (S.ρ m)).toMonoidHom ≤ Ybar S A := by
  rw [Ybar, (gc_map_comap _).l_sSup]
  refine iSup₂_le fun X hX => ?_
  obtain ⟨k, hk, hkz, rfl⟩ := hX
  rw [map_Kbar hAm]
  refine Kbar_le_Ybar ?_ (conj_ne_z' S m.2 hkz)
  rw [mul_conj_z S]
  exact conj_mem_of_map_eq hAm hk

theorem mem_normalizer_Ybar {m : S.M} (hAm : A.map (MulAut.conj (m : G)).toMonoidHom = A) :
    S.ρ m ∈ normalizer (Ybar S A : Set S.O) := by
  refine mem_normalizer_iff_map_conj_eq.mpr ?_
  exact Subgroup.eq_of_le_of_card_ge (map_Ybar_le hAm)
    (card_map_of_injective (MulAut.conj (S.ρ m)).injective).ge

theorem exists_sylow_le_normalizer (haQ : g * S.z * g⁻¹ ∈ S.QG) (C : Cons311 S g) :
    ∃ P : Sylow 2 S.Mbar, S.Lbar g ≤ (P : Subgroup S.Mbar).map S.Mbar.subtype ∧
      (P : Subgroup S.Mbar).map S.Mbar.subtype ≤ normalizer (S.Lbar g : Set S.O) := by
  have := S.isElementaryAbelian_Lbar haQ
  have hL : IsPGroup 2 ((S.Lbar g).subgroupOf S.Mbar) :=
    (CFSG.IsElementaryAbelian.isPGroup 2 (S.Lbar g)).comap_of_injective _ Subtype.val_injective
  obtain ⟨P, hP⟩ := hL.exists_le_sylow
  have hLP : S.Lbar g ≤ (P : Subgroup S.Mbar).map S.Mbar.subtype := fun t ht =>
    ⟨⟨t, S.Lbar_le_Mbar g ht⟩, hP (mem_subgroupOf.mpr ht), rfl⟩
  refine ⟨P, hLP, le_normalizer_of_weaklyClosed (P.isPGroup'.map _) hLP ?_⟩
  rintro _ ⟨x, -, rfl⟩ hle
  obtain ⟨m, hm⟩ := x.2
  have e : S.Mbar.subtype x = S.ρ m := hm.symm
  rw [e, ← Lbar_mul] at hle ⊢
  exact C.weaklyClosed m m.2 hle

end CFSG.LargeExtraspecial.S11
