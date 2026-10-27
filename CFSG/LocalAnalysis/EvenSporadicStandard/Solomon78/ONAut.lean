module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.InvolFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.Sporadic.ONOddCore.FullGroup
public import CFSG.Sporadic.ON

public noncomputable section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.ONSchreier CFSG.Sporadic.ONOddCore CFSG.Blueprint.NativeSporadic
  CFSG.ComponentClassification.OuterAutomorphisms

theorem card_centralizer_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (a : X) :
    Nat.card (centralizer ({a} : Set X)) = Nat.card (centralizer ({e a} : Set Y)) := by
  rw [← centralizer_map_equiv e a, Subgroup.card_map_of_injective e.injective]

theorem card_centralizer_conj' {X : Type*} [Group X] (g a : X) :
    Nat.card (centralizer ({g * a * g⁻¹} : Set X)) = Nat.card (centralizer ({a} : Set X)) := by
  have h := card_centralizer_of_mulEquiv (MulAut.conj g) a
  rw [MulAut.conj_apply] at h
  exact h.symm

section Pv

theorem pv_conj_zP (a : Pv) (ha : orderOf a = 2) : ∃ g : Pv, a = g * zP * g⁻¹ := by
  have ha' : orderOf (a : Equiv.Perm (Fin N)) = 2 := by rw [Subgroup.orderOf_coe]; exact ha
  obtain ⟨g, hg, hag⟩ := cti_on_all_involutions_conjugate (a : Equiv.Perm (Fin N)) a.2 ha'
  refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact hag

theorem pv_card_centralizer_zP : Nat.card (centralizer ({zP} : Set Pv)) = 161280 := by
  rw [CFSG.ONSchreier.centralizer_zP, card_subgroupOf, ← onM_eq_centralizer_z, card_onM]

theorem pv_card_centralizer (a : Pv) (ha : orderOf a = 2) :
    Nat.card (centralizer ({a} : Set Pv)) = 161280 := by
  obtain ⟨g, rfl⟩ := pv_conj_zP a ha
  rw [card_centralizer_conj', pv_card_centralizer_zP]

theorem pv_pointwise (σ : MulAut Pv) (a : Pv) (ha : orderOf a = 2)
    (hσ : ∀ y : Pv, y * a = a * y → σ y = y) : σ = 1 ∨ σ = MulAut.conj a := by
  obtain ⟨g, hga⟩ := pv_conj_zP a ha
  have hinv : MulAut.conj g⁻¹ = (MulAut.conj g)⁻¹ := map_inv MulAut.conj g
  set τ : MulAut Pv := MulAut.conj g⁻¹ * σ * MulAut.conj g with hτ
  have hτfix : ∀ m : Pv, (m : Equiv.Perm (Fin N)) ∈ onM → τ m = m := by
    intro m hm
    have hmz : m * zP = zP * m := by
      rw [onM_eq_centralizer_z] at hm
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hm).2)
    have hgm : (g * m * g⁻¹) * a = a * (g * m * g⁻¹) := by
      rw [hga]
      calc g * m * g⁻¹ * (g * zP * g⁻¹) = g * (m * zP) * g⁻¹ := by group
        _ = g * (zP * m) * g⁻¹ := by rw [hmz]
        _ = g * zP * g⁻¹ * (g * m * g⁻¹) := by group
    have h1 := hσ _ hgm
    show (MulAut.conj g⁻¹ * σ * MulAut.conj g) m = m
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, h1]
    group
  have hτmem : τ ∈ {α : MulAut Pv | ∀ m : Pv, (m : Equiv.Perm (Fin N)) ∈ onM → α m = m} :=
    hτfix
  rw [r3e_on_involution_centralizer_pointwise_automorphisms_inner.1] at hτmem
  have hσ' : σ = MulAut.conj g * τ * (MulAut.conj g)⁻¹ := by
    rw [hτ, hinv]
    group
  rcases hτmem with h1 | h1
  · left
    rw [hσ', h1]
    group
  · right
    rw [hσ', h1, hga, map_mul, map_mul, map_inv]

end Pv

section ON

theorem card_outer_Pv_dvd_four : Nat.card (Outer Pv) ∣ 4 := by
  have h := r3e_on_outer_order_divides_four.1
  have e := @equivalence CFSG.Blueprint.NativeSporadic.ON Pv Units.instGroup _ onEquivPv
  rw [← Nat.card_congr e.toEquiv]
  exact h

theorem on_equiv_Pv {Y : Type} [Group Y] (h : IsSporadic Y .ONan) : Nonempty (Y ≃* Pv) := by
  obtain ⟨e⟩ := h
  have e' : Y ≃* CFSG.Blueprint.NativeSporadic.ON := e
  exact ⟨e'.trans onEquivPv⟩

theorem center_eq_bot_on : center CFSG.Blueprint.NativeSporadic.ON = ⊥ := by
  obtain ⟨hfin, -, hsimple⟩ := CFSG.Sporadic.ON.fam_on_simplicity
  refine HypOne.center_eq_bot_of_isSimpleGroup fun hp => ?_
  have h2 := hp.eq_one_or_self_of_dvd 2 (by rw [CFSG.Sporadic.ON.card_ON]; norm_num)
  rw [CFSG.Sporadic.ON.card_ON] at h2
  omega

theorem center_eq_bot_of_isSporadic_on {Y : Type} [Group Y] (h : IsSporadic Y .ONan) :
    center Y = ⊥ := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* CFSG.Blueprint.NativeSporadic.ON := e₀
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : e z ∈ center CFSG.Blueprint.NativeSporadic.ON := by
    rw [mem_center_iff]
    intro m
    obtain ⟨g, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz g]
  rw [center_eq_bot_on, mem_bot] at hz'
  exact mem_bot.2 (e.injective (by rw [hz', map_one]))

theorem even_card_of_isSporadic_on {Y : Type} [Group Y] (h : IsSporadic Y .ONan) :
    2 ∣ Nat.card Y := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* CFSG.Blueprint.NativeSporadic.ON := e₀
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.ON.card_ON]
  norm_num

theorem on_forall_isConj {Y : Type} [Group Y] (h : IsSporadic Y .ONan) (a b : Y)
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  obtain ⟨e⟩ := on_equiv_Pv h
  obtain ⟨g, hg⟩ := pv_conj_zP (e a) (by rw [MulEquiv.orderOf_eq]; exact ha)
  obtain ⟨g', hg'⟩ := pv_conj_zP (e b) (by rw [MulEquiv.orderOf_eq]; exact hb)
  refine isConj_iff.2 ⟨e.symm (g' * g⁻¹), e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg, hg']
  group

theorem on_umovesCond {Y : Type} [Group Y] (h : IsSporadic Y .ONan) : UMovesCond Y := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* CFSG.Blueprint.NativeSporadic.ON := e₀
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  exact umovesCond_of_forall_isConj (even_card_of_isSporadic_on ⟨e₀⟩) (on_forall_isConj ⟨e₀⟩)

theorem on_pointwise {Y : Type} [Group Y] (h : IsSporadic Y .ONan) (σ : MulAut Y) (a : Y)
    (ha : orderOf a = 2) (hσ : ∀ y : Y, y * a = a * y → σ y = y) :
    σ = 1 ∨ σ = MulAut.conj a := by
  obtain ⟨e⟩ := on_equiv_Pv h
  have h1 := pv_pointwise (MulAut.congr e σ) (e a) (by rw [MulEquiv.orderOf_eq]; exact ha)
    (fun y hy => by
      have h2 : σ (e.symm y) = e.symm y := hσ _ (by
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hy)
      show e (σ (e.symm y)) = y
      rw [h2, MulEquiv.apply_symm_apply])
  rcases h1 with h1 | h1
  · left
    exact (MulAut.congr e).injective (h1.trans (map_one _).symm)
  · right
    exact (MulAut.congr e).injective (h1.trans (congr_conj e a).symm)

@[expose] def ONOuterFixedJ1 : Prop :=
  ∀ (Y : Type) [Group Y], IsSporadic Y .ONan → ∀ ν : MulAut Y, ν * ν = 1 →
    (∀ y : Y, ν ≠ MulAut.conj y) → Nonempty (fixSubgroup ν ≃* Carrier .J1)

end ON

end CFSG.EvenSporadicStandard.Solomon78
