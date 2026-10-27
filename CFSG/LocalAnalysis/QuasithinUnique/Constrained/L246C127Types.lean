module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Alg
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace L246C127

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  have hx' : e x ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
  rw [h, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot]
  exact e.injective (hx'.trans (map_one e).symm)

omit [Finite G] in
theorem isAltQuotient_of_equiv {V : Subgroup G} (hV : IsElemAbelian 2 V) {K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥(autI hV K) ≃* alternatingGroup (Fin n)) :
    IsAltQuotient K (Subgroup.centralizer (V : Set G)) n := by
  refine ⟨e.toMonoidHom.comp (toAutI hV K hK), e.surjective.comp (toAutI_surjective hV K hK), ?_⟩
  ext k
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.map_eq_one_iff,
    ← MonoidHom.mem_ker, toAutI_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩

namespace Setting

variable {X T P K : Subgroup G} (S : Setting X T P K)

include S

theorem pCore_le_ker_of_center_eq_bot (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X)
    (hc : Subgroup.center ↥(autI hV K) = ⊥) :
    CFSG.pCore 2 ↥K ≤ (toAutI hV K S.hKN).ker := by
  intro x hx
  have h := S.map_pCore_le_center hV hUV ⟨x, hx, rfl⟩
  rw [hc, Subgroup.mem_bot] at h
  exact h

theorem nonempty_equiv_of_center_eq_bot (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X)
    {Q : Type} [Group Q] (α : ↥K →* Q) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) (hc : Subgroup.center ↥(autI hV K) = ⊥) :
    Nonempty (↥(autI hV K) ≃* Q) := by
  have hπker : (toAutI hV K S.hKN).ker = α.ker := by
    rw [hker]
    exact le_antisymm (S.ker_toAutI_le_pCore hV hUV) (S.pCore_le_ker_of_center_eq_bot hV hUV hc)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective _ (toAutI_surjective hV K S.hKN)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hπker).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα))⟩

theorem noOrderFour_autI_of_types (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X)
    (hchi : (∃ e : ℕ, 1 < e ∧ IsLin2Type K e) ∨ IsAltType K 3 ∨ IsAltType K 5)
    (hc : Subgroup.center ↥(autI hV K) = ⊥) : NoOrderFour ↥(autI hV K) := by
  rcases hchi with ⟨e, he, F, hF, hFin, hcard, α, hα, hker, -⟩ | ⟨α, hα, hker, -⟩ | ⟨α, hα, hker, -⟩
  · have : CharP F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic (k := e)
        Nat.prime_two (by omega) (by rw [Nat.card_eq_fintype_card, hcard])
    obtain ⟨φ⟩ := S.nonempty_equiv_of_center_eq_bot hV hUV α hα hker hc
    exact (noOrderFour_sl2 F).of_mulEquiv φ
  · obtain ⟨φ⟩ := S.nonempty_equiv_of_center_eq_bot hV hUV α hα hker hc
    exact noOrderFour_alt_three.of_mulEquiv φ
  · obtain ⟨φ⟩ := S.nonempty_equiv_of_center_eq_bot hV hUV α hα hker hc
    exact noOrderFour_alt_five.of_mulEquiv φ

theorem degree_eq_three_or_five (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X)
    (hchi : (∃ e : ℕ, 1 < e ∧ IsLin2Type K e) ∨ IsAltType K 3 ∨ IsAltType K 5) {n : ℕ}
    (e : ↥(autI hV K) ≃* alternatingGroup (Fin n)) : n = 3 ∨ n = 5 := by
  rcases alt_degree_cases e (S.isQuasisimple_or_card_three_autI hV hUV) with h3 | h5
  · exact Or.inl h3
  · right
    have hn4 : 4 ≤ Nat.card (Fin n) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
    have hc : Subgroup.center ↥(autI hV K) = ⊥ :=
      center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot hn4)
    have hno := (S.noOrderFour_autI_of_types hV hUV hchi hc).of_mulEquiv e.symm
    by_contra hne
    exact not_noOrderFour_alt (by omega) hno

theorem isEmpty_equiv_sl3 (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X)
    (hchi : (∃ e : ℕ, 1 < e ∧ IsLin2Type K e) ∨ IsAltType K 3 ∨ IsAltType K 5) :
    IsEmpty (↥(autI hV K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  refine ⟨fun e => ?_⟩
  have hc : Subgroup.center ↥(autI hV K) = ⊥ := center_eq_bot_of_mulEquiv e center_sl3_eq_bot
  exact not_noOrderFour_sl3 ((S.noOrderFour_autI_of_types hV hUV hchi hc).of_mulEquiv e.symm)

end Setting

end L246C127

end CFSG.QuasithinUnique
