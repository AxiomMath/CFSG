module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC9a
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.OuterCentQS
public import CFSG.Sporadic.HeldB.OuterFixedCore

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C9

open CFSG Subgroup C311
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def centralizerEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T) (s : S) :
    ↥(centralizer ({s} : Set S)) ≃* ↥(centralizer ({e s} : Set T)) where
  toFun x := ⟨e x.1, mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp x.2])⟩
  invFun y := ⟨e.symm y, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, mem_centralizer_singleton_iff.mp y.2])⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul e x.1 y.1)

theorem fixedSubgroup_conj {S : Type*} [Group S] (s : S) :
    fixedSubgroup (MulAut.conj s) = centralizer ({s} : Set S) := by
  ext x
  change MulAut.conj s x = x ↔ _
  rw [MulAut.conj_apply, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * s = s * x * s⁻¹ * s := by rw [h]
      _ = s * x := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

theorem pPrimeCore_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : pPrimeCore 2 Y = ⊥) : pPrimeCore 2 X = ⊥ := by
  have h1 := pPrimeCore_map_iso 2 e
  rw [h] at h1
  exact (map_eq_bot_iff_of_injective _ e.injective).mp h1


 in
theorem pPrimeCore_eq_bot_of_held_inner {S : Type} [Group S] [Finite S]
    (eHe : S ≃* Blueprint.NativeSporadic.He) {s : S} (hs : orderOf s = 2)
    (L : Subgroup (fixedSubgroup (MulAut.conj s))) (hL : IsPComponent 2 L) :
    pPrimeCore 2 ↥L = ⊥ := by
  let e' : S ≃* Sporadic.HeldB.heP := eHe.trans Sporadic.HeldB.heEquivP
  have hC := (Sporadic.HeldB.ctbhi_held_inner_involution_centralizers_odd_core).2 (e' s)
    (by rw [MulEquiv.orderOf_eq]; exact hs)
  have hC' : pPrimeCore 2 ↥(fixedSubgroup (MulAut.conj s)) = ⊥ :=
    pPrimeCore_eq_bot_of_mulEquiv ((MulEquiv.subgroupCongr (fixedSubgroup_conj s)).trans
      (centralizerEquiv e' s)) hC
  obtain ⟨hsub, -⟩ := (isTwoComponent_iff_isPComponent L).mpr hL
  have h2 := Walter.map_pPrimeCore_le_of_isSubnormal hsub
  rw [hC', le_bot_iff, map_eq_bot_iff_of_injective _ L.subtype_injective] at h2
  exact h2

theorem false_of_held_outer {S : Type} [Group S] [Finite S]
    (eHe : S ≃* Blueprint.NativeSporadic.He) (α : MulAut S) (hα : orderOf α = 2)
    (hinn : α ∉ (MulAut.conj : S →* MulAut S).range) (L : Subgroup (fixedSubgroup α))
    (hL : IsPComponent 2 L) {p f : ℕ}
    (hm : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSL 2 p f) (h9 : p ^ f = 9)
    (hle : pPrimeCore 2 ↥L ≤ center ↥L) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : S ≃* Sporadic.HeldB.heP := eHe.trans Sporadic.HeldB.heEquivP
  obtain ⟨x, hx, hxP, hx2⟩ := Sporadic.HeldB.exists_heConjR_eq
    Sporadic.HeldB.ctbh_full_automorphism_permutation_model.1 (MulAut.congr e' α)
    (by rw [Sporadic.HeldB.orderOf_congr, hα])
    (by rwa [Sporadic.HeldB.congr_mem_range_conj_iff])
  obtain ⟨g, hg, hxg⟩ := Sporadic.HeldB.exists_conj_heAutU x.2 hxP hx2
  let f₁ : fixedSubgroup α ≃* (Sporadic.HeldB.heP ⊓
      centralizer {Sporadic.HeldB.heAutU} : Subgroup _) :=
    ((Sporadic.HeldB.fixedSubgroupCongr e' α).trans (MulEquiv.subgroupCongr (by rw [hx]))).trans
      (Sporadic.HeldB.fixedSubgroupEquivOfConj x hg Sporadic.HeldB.heAutU hxg)
  let f₂ : fixedSubgroup α ≃* Sporadic.HeldB.heOuterC :=
    f₁.trans (MulEquiv.subgroupCongr Sporadic.HeldB.heOuterC_eq.symm)
  set L' := L.map f₂.toMonoidHom with hL'def
  have hL' : IsPComponent 2 L' := isPComponent_map_mulEquiv f₂ hL
  obtain ⟨-, hDq, hidx⟩ := Sporadic.HeldB.ctbh_outer_centralizer_derived_quasisimple
  have hDC := Sporadic.HeldB.heOuterD_le_C
  set N := Sporadic.HeldB.heOuterD.subgroupOf Sporadic.HeldB.heOuterC with hN
  have hN2 : N.index = 2 := hidx
  have : N.Normal := normal_of_index_eq_two hN2
  have : Group.IsSolvable (Sporadic.HeldB.heOuterC ⧸ N) := by
    have : IsCyclic (Sporadic.HeldB.heOuterC ⧸ N) := isCyclic_of_prime_card hN2
    exact Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b
  obtain ⟨hLN, hLN'⟩ :=
    CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient 2 N L' hL'
  have hNq : IsQuasisimple ↥N :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr (subgroupOfEquivOfLe hDC)).2 hDq
  have htop := CatalogueBAlternatingIsometry.pComponent_eq_top_of_quasisimple hNq 2
    (L'.subgroupOf N) hLN'
  have hL'N : L' = N := le_antisymm hLN (subgroupOf_eq_top.mp htop)
  let eLD : ↥L ≃* ↥Sporadic.HeldB.heOuterD :=
    ((L.equivMapOfInjective _ f₂.injective).trans (MulEquiv.subgroupCongr hL'N)).trans
      (subgroupOfEquivOfLe hDC)
  have hcardL : Nat.card ↥L = 7560 := by
    rw [Nat.card_congr eLD.toEquiv, Sporadic.HeldB.card_heOuterD]
  have hZ : Nat.card ↥(center ↥L) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr eLD).toEquiv, Sporadic.HeldB.card_center_heOuterD]
  have hc := card_eq_mul hm h9
  have hO : Nat.card ↥(pPrimeCore 2 ↥L) ≤ 3 := hZ ▸ Subgroup.card_le_of_le hle
  omega

theorem pPrimeCore_eq_bot_of_held {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) (eHe : S ≃* Blueprint.NativeSporadic.He) (α : MulAut S)
    (hα : orderOf α = 2) (L : Subgroup (fixedSubgroup α)) (hL : IsPComponent 2 L) {p f : ℕ}
    (hm : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSL 2 p f) (h9 : p ^ f = 9)
    (hle : pPrimeCore 2 ↥L ≤ center ↥L) : pPrimeCore 2 ↥L = ⊥ := by
  by_cases hinn : α ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hinn
    have hZ : center S = ⊥ := FooteLit.center_eq_bot_of_isSimpleGroup hnab
    have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
      intro s t hst
      have h1 : s⁻¹ * t ∈ center S := by
        rw [mem_center_iff]
        intro g
        have h3 := congrArg (fun φ : MulAut S => φ g) hst
        simp only [MulAut.conj_apply] at h3
        calc g * (s⁻¹ * t) = s⁻¹ * (s * g * s⁻¹) * t := by group
          _ = s⁻¹ * (t * g * t⁻¹) * t := by rw [h3]
          _ = s⁻¹ * t * g := by group
      rw [hZ, mem_bot] at h1
      calc s = s * (s⁻¹ * t) := by rw [h1, mul_one]
        _ = t := by group
    have hs : orderOf s = 2 := by rw [← orderOf_injective _ hinj s]; exact hα
    exact pPrimeCore_eq_bot_of_held_inner eHe hs L hL
  · exact (false_of_held_outer eHe α hα hinn L hL hm h9 hle).elim

end CFSG.ComponentClassification.HarrisLit.C9
