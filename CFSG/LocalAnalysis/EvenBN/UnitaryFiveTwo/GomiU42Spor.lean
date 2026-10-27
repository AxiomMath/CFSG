module

public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBase

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy IsoInvariant)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def IsU42Root {D : Type} [Group D] (α : MulAut D) (S : Subgroup D) : Prop :=
  orderOf α = 2 ∧ S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D) ∧
    (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal ∧ IsSimpleGroup S ∧
    (∃ x y : S, x * y ≠ y * x) ∧ Nat.card S = 25920

@[expose] def SporadicU42Free (s : TauCeti.SporadicName) : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → NativeSporadic.IsSporadic D s →
    ∀ (α : MulAut D) (S : Subgroup D), ¬ IsU42Root α S

section U42Root

variable {D : Type} [Group D] {α : MulAut D} {S : Subgroup D}

theorem IsU42Root.isComponent (h : IsU42Root α S) :
    CFSG.IsComponent (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))) := by
  have hs := h.2.2.2.1
  have e := Subgroup.subgroupOfEquivOfLe h.2.1
  have : IsSimpleGroup (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))) :=
    e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := h.2.2.2.2.1
  have hnab : ∃ x y : S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)), x * y ≠ y * x := by
    refine ⟨e.symm a, e.symm b, fun h' => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h'
  exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1, h.2.2.1.isSubnormal⟩

theorem IsU42Root.false_of_comps (h : IsU42Root α S) {Q : (Y : Type) → [Group Y] → Prop}
    (hQ : IsoInvariant Q)
    (hQU : ∀ (Y : Type) [Group Y], IsSimpleGroup Y → (∃ x y : Y, x * y ≠ y * x) →
      Nat.card Y = 25920 → ¬ Q Y)
    (hC : CompsSatisfy (α.toMonoidHom.eqLocus (MonoidHom.id D)) Q) : False :=
  hQU S h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
    (hQ _ _ (Subgroup.subgroupOfEquivOfLe h.2.1).symm (hC _ h.isComponent))

theorem IsU42Root.card_dvd_eqLocus [Finite D] (h : IsU42Root α S) :
    25920 ∣ Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D)) := by
  rw [← h.2.2.2.2.2, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.2.1).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem IsU42Root.center_eq_bot_of_isSimpleGroup (hD : IsSimpleGroup D) (h : IsU42Root α S) :
    center D = ⊥ := by
  obtain ⟨a, b, hab⟩ := h.2.2.2.2.1
  have hnab : ∃ x y : D, x * y ≠ y * x :=
    ⟨a, b, fun h' => hab (Subtype.ext (by simpa only [coe_mul] using h'))⟩
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2

theorem IsU42Root.false_of_inner_comps (hD : IsSimpleGroup D) (h : IsU42Root α S)
    (hin : α ∈ inner D) {Q : (Y : Type) → [Group Y] → Prop} (hQ : IsoInvariant Q)
    (hQU : ∀ (Y : Type) [Group Y], IsSimpleGroup Y → (∃ x y : Y, x * y ≠ y * x) →
      Nat.card Y = 25920 → ¬ Q Y)
    (hC : ∀ t : D, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set D)) Q) : False := by
  obtain ⟨t, ht, rfl⟩ := exists_involution_of_mem_inner (h.center_eq_bot_of_isSimpleGroup hD)
    h.1 hin
  exact h.false_of_comps hQ hQU
    (CompsSatisfy.of_mulEquiv hQ (MulEquiv.subgroupCongr (eqLocus_conj t)) (hC t ht))

theorem IsU42Root.false_of_outer_comps (h : IsU42Root α S) {Q : (Y : Type) → [Group Y] → Prop}
    (hQ : IsoInvariant Q)
    (hQU : ∀ (Y : Type) [Group Y], IsSimpleGroup Y → (∃ x y : Y, x * y ≠ y * x) →
      Nat.card Y = 25920 → ¬ Q Y)
    (hC : CompsSatisfy (CFSG.Sporadic.Schreier.fixSub α) Q) : False :=
  h.false_of_comps hQ hQU
    (CompsSatisfy.of_mulEquiv hQ (MulEquiv.subgroupCongr (eqLocus_eq_fixSub α)) hC)

end U42Root

theorem sporadicU42Free_of_comps {s : TauCeti.SporadicName}
    {Qi Qo : (Y : Type) → [Group Y] → Prop} (hQi : IsoInvariant Qi) (hQo : IsoInvariant Qo)
    (hUi : ∀ (Y : Type) [Group Y], IsSimpleGroup Y → (∃ x y : Y, x * y ≠ y * x) →
      Nat.card Y = 25920 → ¬ Qi Y)
    (hUo : ∀ (Y : Type) [Group Y], IsSimpleGroup Y → (∃ x y : Y, x * y ≠ y * x) →
      Nat.card Y = 25920 → ¬ Qo Y)
    (hin : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set G)) Qi)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ β : MulAut G, orderOf β = 2 → β ∉ inner G →
        CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β) Qo) :
    SporadicU42Free s := by
  intro D _ _ hD hs α S h
  by_cases hα : α ∈ inner D
  · exact h.false_of_inner_comps hD hα hQi hUi (hin D hs)
  · exact h.false_of_outer_comps hQo hUo (hout D hD hs α h.1 hα)

theorem sporadicU42Free_of_card {s : TauCeti.SporadicName} {N : ℕ}
    (hN : Nat.card (NativeSporadic.Carrier s) = N) (hdvd : ¬ 25920 ∣ N) :
    SporadicU42Free s := by
  intro D _ _ _ hs α S h
  obtain ⟨e⟩ := hs
  apply hdvd
  rw [← hN, ← Nat.card_congr e.toEquiv, ← h.2.2.2.2.2]
  exact Subgroup.card_subgroup_dvd_card S

theorem u42_fails_card_dvd {c : ℕ} (hc : ¬ 25920 ∣ c) :
    ∀ (Y : Type) [Group Y], IsSimpleGroup Y → (∃ x y : Y, x * y ≠ y * x) →
      Nat.card Y = 25920 → ¬ Nat.card Y ∣ c :=
  fun _ _ _ _ hY h => hc (hY ▸ h)

theorem u42_fails_not_three_dvd :
    ∀ (Y : Type) [Group Y], IsSimpleGroup Y → (∃ x y : Y, x * y ≠ y * x) →
      Nat.card Y = 25920 → ¬ ¬ 3 ∣ Nat.card Y :=
  fun _ _ _ _ hY h => h (hY ▸ (by norm_num : 3 ∣ 25920))

theorem u42_fails_card_quotient_center_mem {N : Set ℕ} (hN : 25920 ∉ N) :
    ∀ (Y : Type) [Group Y], IsSimpleGroup Y → (∃ x y : Y, x * y ≠ y * x) →
      Nat.card Y = 25920 → ¬ Nat.card (Y ⧸ center Y) ∈ N := by
  intro Y _ hY hnab hcard h
  have hz : center Y = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  have hq : Nat.card (Y ⧸ center Y) = 25920 := by
    rw [← hcard]
    exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hz).trans
      QuotientGroup.quotientBot).toEquiv
  rw [hq] at h
  exact hN h

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
