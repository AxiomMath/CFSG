module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.SuzOddCore.CTIComponents

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Blueprint.NativeSporadic

section Suz


theorem suz_conj_zero {S : Type*} [Group S] (f : S ≃* suzM) (a : S) (ha : orderOf a = 2)
    (hdvd : 20160 ∣ Nat.card (centralizer ({a} : Set S))) :
    ∃ c ∈ suzT, c * suzInv 0 * c⁻¹ = ((f a : suzM) : Equiv.Perm (Fin 1782)) := by
  set a' : Equiv.Perm (Fin 1782) := ((f a : suzM) : Equiv.Perm (Fin 1782))
  have ha' : orderOf a' = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha]
  have hinj : Function.Injective (suzM.subtype.comp f.toMonoidHom) :=
    suzM.subtype_injective.comp f.injective
  have g1 : centralizer ({a} : Set S) ≃*
      (suzM ⊓ Subgroup.centralizer {a'} : Subgroup (Equiv.Perm (Fin 1782))) :=
    ((centralizer ({a} : Set S)).equivMapOfInjective _ hinj).trans
      (MulEquiv.subgroupCongr (centralizer_map_equiv f a))
  obtain ⟨c, hc, h01⟩ := suzM_involution_class (f a).2 ha'
  rcases h01 with h0 | h1
  · exact ⟨c, hc, h0⟩
  · exfalso
    have hmap := map_conj_inf_centralizer (Γ := suzM) (c := c) (suzM_conj_iff hc) (suzInv 1)
    rw [h1] at hmap
    have e2 := (Subgroup.equivMapOfInjective (suzM ⊓ Subgroup.centralizer {suzInv 1})
      (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmap)
    have e3 : invE 1 = suzM ⊓ Subgroup.centralizer {suzInv 1} := by
      rw [invE_eq_centM (by norm_num : 1 < 4), centM, inf_comm]
    have e4 := (g1.trans e2.symm).trans (MulEquiv.subgroupCongr e3.symm)
    rw [Nat.card_congr e4.toEquiv, card_invE (by norm_num : 1 < 4)] at hdvd
    simp [invInnerOrders] at hdvd

theorem suz_exists_model_aux {S : Type*} [Group S] (f : S ≃* suzM) (a : S) (ha : orderOf a = 2)
    (hdvd : 20160 ∣ Nat.card (centralizer ({a} : Set S))) :
    ∃ Ψ : S →* Equiv.Perm (Fin 1782), Function.Injective Ψ ∧ (∀ x, Ψ x ∈ suzM) ∧
      (∀ y ∈ suzM, ∃ x, Ψ x = y) ∧ Ψ a = suzInv 0 := by
  obtain ⟨c, hc, hca⟩ := suz_conj_zero f a ha hdvd
  refine ⟨(MulAut.conj (c⁻¹ : Equiv.Perm (Fin 1782))).toMonoidHom.comp
    (suzM.subtype.comp f.toMonoidHom), ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj (c⁻¹ : Equiv.Perm (Fin 1782))).injective.comp
      (suzM.subtype_injective.comp f.injective)
  · intro x
    have h := (suzM_conj_iff (suzT.inv_mem hc) (f x : Equiv.Perm (Fin 1782))).1 (f x).2
    simpa [MulAut.conj_apply] using h
  · intro y hy
    have h := (suzM_conj_iff hc y).1 hy
    obtain ⟨x, hx⟩ := f.surjective ⟨c * y * c⁻¹, h⟩
    refine ⟨x, ?_⟩
    have hx' : ((f x : suzM) : Equiv.Perm (Fin 1782)) = c * y * c⁻¹ := congrArg Subtype.val hx
    show c⁻¹ * ((f x : suzM) : Equiv.Perm (Fin 1782)) * c⁻¹⁻¹ = y
    rw [hx']
    group
  · show c⁻¹ * ((f a : suzM) : Equiv.Perm (Fin 1782)) * c⁻¹⁻¹ = suzInv 0
    rw [← hca]
    group

end Suz

end CFSG.EvenSporadicStandard.Solomon78
