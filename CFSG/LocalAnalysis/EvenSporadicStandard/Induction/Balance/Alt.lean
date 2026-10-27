module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Group
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocalBetween
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingModel
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
  CFSG.ComponentClassification.CatalogueBAlternating
open scoped Classical

theorem normalizer_zpowers_eq_centralizer {H : Type*} [Group H] {v : H} (hv : orderOf v = 2) :
    normalizer (zpowers v : Set H) = centralizer ({v} : Set H) := by
  ext g
  rw [mem_normalizer_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : g * v * g⁻¹ ∈ zpowers v := (h v).1 (mem_zpowers v)
    have hcard : Nat.card (zpowers v) = 2 := by rw [Nat.card_zpowers, hv]
    have hv1 : v ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hv
      exact absurd hv (by norm_num)
    have ha : (⟨g * v * g⁻¹, h1⟩ : zpowers v) ≠ 1 := by
      intro h
      apply hv1
      have := congrArg Subtype.val h
      simp only [OneMemClass.coe_one] at this
      simpa using this
    have hb : (⟨v, mem_zpowers v⟩ : zpowers v) ≠ 1 := by
      intro h
      exact hv1 (congrArg Subtype.val h)
    have := congrArg Subtype.val (eq_of_card_two hcard ha hb)
    simp only at this
    calc g * v = (g * v * g⁻¹) * g := by group
      _ = v * g := by rw [this]
  · intro h x
    have hc : ∀ y ∈ zpowers v, g * y * g⁻¹ = y := by
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      have : Commute g v := h
      exact (this.zpow_right k).mul_inv_cancel
    have hc' : ∀ y ∈ zpowers v, g⁻¹ * y * g = y := by
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      have : Commute g⁻¹ v := Commute.inv_left (show Commute g v from h)
      simpa using (this.zpow_right k).mul_inv_cancel
    constructor
    · intro hx
      rw [hc x hx]
      exact hx
    · intro hx
      have := hc' _ hx
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [e] at this
      rw [← this] at hx
      exact hx

theorem exists_alternating_of_component {H : Type} [Group H] [Finite H] {N : Subgroup H}
    (hN : FStarSimple N) {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) (θ : ↥N ≃* alternatingGroup (Fin n))
    {v : H} (hv : orderOf v = 2) {M : Subgroup H}
    (hM : IsCompIn M (centralizer ({v} : Set H))) :
    ∃ (F : Type) (_ : Fintype F) (_ : DecidableEq F), 5 ≤ Nat.card F ∧
      Nonempty (↥M ≃* alternatingGroup F) := by
  have hF : CFSG.ComponentClassification.GeneralizedFitting.subgroup H = N :=
    (CFSG.generalizedFitting_eq_componentClassification H).symm.trans hN.1
  let e0 : ↥(CFSG.ComponentClassification.GeneralizedFitting.subgroup H) ≃* ↥N :=
    MulEquiv.subgroupCongr hF
  have := hN.isSimpleGroup
  have : IsSimpleGroup ↥(CFSG.ComponentClassification.GeneralizedFitting.subgroup H) :=
    e0.isSimpleGroup
  have hnonab : ∃ a b : ↥(CFSG.ComponentClassification.GeneralizedFitting.subgroup H),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hN.nonabelian
    exact ⟨e0.symm a, e0.symm b, fun h => hab (by simpa using congrArg e0 h)⟩
  obtain ⟨K, hK, e, -⟩ := generalizedFitting_between_alternating_symmetric hnonab hn (e0.trans θ)
  set S : Subgroup H := zpowers v with hSdef
  have hSc : Nat.card S = 2 := by rw [hSdef, Nat.card_zpowers, hv]
  have hS : IsPGroup 2 ↥(S.map e.toMonoidHom) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Subgroup.card_map_of_injective e.injective, hSc]
    norm_num
  have hnorm := normalizer_zpowers_eq_centralizer hv
  let C : Subgroup H := centralizer ({v} : Set H)
  let Ψ : ↥C ≃* ↥(normalizer ((S.map e.toMonoidHom : Subgroup K) : Set K)) :=
    (MulEquiv.subgroupCongr hnorm.symm).trans (normalizerEquiv e S)
  have hP : CFSG.IsPComponent 2 (M.subgroupOf C) :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hM.2
  have hP' := pComponent_map_equiv 2 Ψ _ hP
  obtain ⟨hdeg, hmap, -⟩ := between_normalizer_pComponent K hK 2 (S.map e.toMonoidHom) hS _ hP'
  let ρ : H →* Equiv.Perm (Fin n) := K.subtype.comp e.toMonoidHom
  have hρ : Function.Injective ρ := K.subtype_injective.comp e.injective
  have hcomp : (K.subtype.comp
      (normalizer ((S.map e.toMonoidHom : Subgroup K) : Set K)).subtype).comp Ψ.toMonoidHom =
      ρ.comp C.subtype := by
    ext c
    rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hM.1] at hmap
  refine ⟨↑(MulAction.fixedPoints ↥(S.map e.toMonoidHom) (Fin n)), inferInstance, inferInstance,
    hdeg, ?_⟩
  exact ⟨(M.equivMapOfInjective ρ hρ).trans ((MulEquiv.subgroupCongr hmap).trans
    ((alternatingGroup _).equivMapOfInjective Equiv.Perm.ofSubtype
      Equiv.Perm.ofSubtype_injective).symm)⟩

theorem card_quotient_center_eq {M : Type*} [Group M] [Finite M] [IsSimpleGroup M]
    (hq : CFSG.IsQuasisimple M) : Nat.card (M ⧸ center M) = Nat.card M := by
  obtain ⟨-, -, a, b, hab⟩ := hq
  have hZ : center M = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center M) with h | h
    · exact h
    · exfalso
      have : Subsingleton (M ⧸ center M) := by
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      exact hab (Subsingleton.elim _ _)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center M)
  have hcard : Nat.card (center M) = 1 := by rw [hZ, Subgroup.card_bot]
  rw [hcard, mul_one] at h1
  exact h1.symm

theorem card_alternatingGroup_of_five_le {F : Type*} [Fintype F] [DecidableEq F]
    (h : 5 ≤ Nat.card F) : Nat.card (alternatingGroup F) = (Nat.card F).factorial / 2 := by
  have : Nontrivial F := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  exact nat_card_alternatingGroup

theorem false_of_isAlt {H : Type} [Group H] [Finite H] {N : Subgroup H} (hN : FStarSimple N)
    (hidx : N.index ≤ 2) (hAlt : IsAltType ↥N) {s : TauCeti.SporadicName} {c : ℕ}
    (hc : Nat.card (Carrier s) = c) (hc720 : 720 < c)
    (hcf : ∀ m : ℕ, 5 ≤ m → m.factorial / 2 ≠ c) {v : H} (hv : orderOf v = 2) {M : Subgroup H}
    (hMC : IsCompIn M (centralizer ({v} : Set H))) (hM : OddCover s M) : False := by
  obtain ⟨n, hn5, ⟨θ⟩⟩ := hAlt
  obtain ⟨e⟩ := hM.2.2
  have hcM : c = Nat.card (↥M ⧸ center ↥M) := by rw [← hc]; exact (Nat.card_congr e.toEquiv).symm
  by_cases h6 : n = 6
  · subst h6
    have hNcard : Nat.card N = 360 := by
      have : Nontrivial (Fin 6) := ⟨⟨0, 1, by decide⟩⟩
      rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.card_eq_fintype_card, Nat.factorial]
    have hHcard : Nat.card H ≤ 720 := by
      have h1 := Subgroup.card_mul_index N
      rw [hNcard] at h1
      have h2 : N.index ≤ 2 := hidx
      nlinarith
    have hMcard : Nat.card M ≤ Nat.card H := Subgroup.card_le_card_group M
    have hqc : Nat.card (↥M ⧸ center ↥M) ≤ Nat.card M :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    omega
  · have hn : n = 5 ∨ 7 ≤ n := by omega
    obtain ⟨F, _, _, hF5, ⟨ψ⟩⟩ := exists_alternating_of_component hN hn θ hv hMC
    have : IsSimpleGroup (alternatingGroup F) := alternatingGroup.isSimpleGroup hF5
    have : IsSimpleGroup ↥M := ψ.isSimpleGroup
    have h1 := card_quotient_center_eq hM.1
    have h2 : Nat.card M = (Nat.card F).factorial / 2 := by
      rw [Nat.card_congr ψ.toEquiv]
      exact card_alternatingGroup_of_five_le hF5
    exact hcf (Nat.card F) hF5 (by rw [← h2, ← h1]; exact hcM.symm)

end CFSG.EvenSporadicStandard.Induction.Balance
