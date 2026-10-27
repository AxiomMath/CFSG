module

public import CFSG.Sporadic.SuzOddCore.CTIComponents
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSQuot

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Blueprint.NativeSporadic

section Suz


theorem suz_quot2Data : Quot2Data rho0 suzD where
  D_le := suzD_le
  range_le := (Subgroup.normal_subgroupOf_iff_le_normalizer suzD_le).1 suzD_normal
  simple := suzD_simple
  noncomm := suzD_noncomm
  index_two := ⟨1, by rw [card_range_rho0, card_suzD]; norm_num⟩
  ker_two := ⟨2, by rw [card_ker_rho0]; norm_num⟩
  big := by rw [card_ker_rho0, card_suzD]; norm_num

theorem suz_centralizer_equiv {S : Type*} [Group S] (f : S ≃* suzM) (a : S) (ha : orderOf a = 2) :
    Nonempty (centralizer ({a} : Set S) ≃* invE 0) ∨
      Nonempty (centralizer ({a} : Set S) ≃* invE 1) := by
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
  have key : ∀ i < 4, c * suzInv i * c⁻¹ = a' →
      Nonempty ((suzM ⊓ Subgroup.centralizer {a'} : Subgroup (Equiv.Perm (Fin 1782))) ≃*
        invE i) := by
    intro i hi hca
    have hmap := map_conj_inf_centralizer (Γ := suzM) (c := c) (suzM_conj_iff hc) (suzInv i)
    rw [hca] at hmap
    have e2 := (Subgroup.equivMapOfInjective (suzM ⊓ Subgroup.centralizer {suzInv i})
      (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmap)
    have e3 : invE i = suzM ⊓ Subgroup.centralizer {suzInv i} := by
      rw [invE_eq_centM hi, centM, inf_comm]
    exact ⟨e2.symm.trans (MulEquiv.subgroupCongr e3.symm)⟩
  rcases h01 with h0 | h1
  · obtain ⟨g2⟩ := key 0 (by norm_num) h0
    exact Or.inl ⟨g1.trans g2⟩
  · obtain ⟨g2⟩ := key 1 (by norm_num) h1
    exact Or.inr ⟨g1.trans g2⟩

theorem suz_centralizer_equiv_zero {S : Type*} [Group S] (f : S ≃* suzM) (a : S)
    (ha : orderOf a = 2) (hdvd : 20160 ∣ Nat.card (centralizer ({a} : Set S))) :
    Nonempty (centralizer ({a} : Set S) ≃* invE 0) := by
  rcases suz_centralizer_equiv f a ha with h | h1
  · exact h
  · exfalso
    obtain ⟨e⟩ := h1
    rw [Nat.card_congr e.toEquiv, card_invE (by norm_num : 1 < 4)] at hdvd
    simp [invInnerOrders] at hdvd

end Suz

end CFSG.EvenSporadicStandard.Solomon78
