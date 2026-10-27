module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAllData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem inner_row_of_centralizer {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hin : σ ∈ (MulAut.conj : S →* MulAut S).range) {P : ℕ → Prop}
    (h : ∀ u : S, orderOf u = 2 → ∀ B : Subgroup (centralizer ({u} : Set S)), IsComponent B →
      P (Nat.card (B ⧸ center B))) : P (Nat.card (D ⧸ center D)) := by
  obtain ⟨u, rfl⟩ := hin
  obtain ⟨B, hB, hcard⟩ := SeitzReduction.OmegaPilot.exists_component_centralizer_of_conj u hD
  rw [← hcard]
  exact h u (SeitzReduction.OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB

theorem false_of_not_mem_range {S : Type} [Group S] {σ : MulAut S}
    (h : ∃ g : S, σ = MulAut.conj g) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) : False := by
  obtain ⟨g, hg⟩ := h
  exact hout ⟨g, hg.symm⟩

theorem isComponentOf_map_centralizer {S : Type*} [Group S] {t : S}
    {B : Subgroup ↥(centralizer ({t} : Set S))} (hB : IsComponent B) :
    Assembly.IsComponentOf (B.map (centralizer ({t} : Set S)).subtype)
      (centralizer ({t} : Set S)) := by
  rw [LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    (map_subtype_le B)]
  have h : (B.map (centralizer ({t} : Set S)).subtype).subgroupOf (centralizer ({t} : Set S)) =
      B := Subgroup.comap_map_eq_self_of_injective (centralizer ({t} : Set S)).subtype_injective B
  rw [h]
  exact hB

theorem card_quotient_center_map_centralizer {S : Type*} [Group S] {t : S}
    (B : Subgroup ↥(centralizer ({t} : Set S))) :
    Nat.card (↥(B.map (centralizer ({t} : Set S)).subtype) ⧸
      center ↥(B.map (centralizer ({t} : Set S)).subtype)) = Nat.card (↥B ⧸ center ↥B) :=
  (Nat.card_congr (QuotientGroup.congr _ _
    (B.equivMapOfInjective _ (centralizer ({t} : Set S)).subtype_injective)
    (Subgroup.map_center_eq _)).toEquiv).symm

theorem card_quotient_center_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) : Nat.card (X ⧸ center X) = Nat.card X := by
  have hZ : center X = ⊥ := ComponentClassification.BMCase.center_eq_bot_of_isSimpleGroup hna
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv

theorem nonabelian_of_simple_of_card_ne_prime {X : Type*} [Group X] [IsSimpleGroup X]
    (h : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have : IsMulCommutative X := ⟨⟨fun a b => hc a b⟩⟩
  exact h ((Group.is_simple_iff_prime_card).1 inferInstance)

theorem exists_conj_of_inner_eq_top {T S : Type*} [Group T] [Group S] (e : T ≃* S)
    (h : ComponentClassification.OuterAutomorphisms.inner S = ⊤) (α : MulAut T) :
    ∃ g : T, α = MulAut.conj g :=
  ComponentClassification.BMCase.inner_of_equiv e (fun β => by
    obtain ⟨g, hg⟩ : β ∈ ComponentClassification.OuterAutomorphisms.inner S := h ▸ mem_top β
    exact ⟨g, hg.symm⟩) α

theorem not_forall_congr_eq_conj {G H : Type*} [Group G] [Group H] (θ : G ≃* H) {σ : MulAut G}
    (hσ : σ ∉ (MulAut.conj : G →* MulAut G).range) (x : H) :
    ¬ ∀ p : H, MulAut.congr θ σ p = x * p * x⁻¹ := by
  intro h
  apply hσ
  refine ⟨θ.symm x, MulEquiv.ext fun y => θ.injective ?_⟩
  have h1 := h (θ y)
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← h1]

theorem mul_self_eq_one_of_orderOf_eq_two' {S : Type*} [Group S] {σ : MulAut S}
    (hσ : orderOf σ = 2) : σ * σ = 1 := by
  rw [← sq, ← hσ, pow_orderOf_eq_one]

section Dvd


theorem card_quotient_center_dvd_sporOrd
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder) {S : Type} [Group S] [Finite S]
    {s : TauCeti.SporadicName} (e : S ≃* NativeSporadic.Carrier s) {σ : MulAut S}
    (D : Subgroup (fixedSubgroup σ)) : Nat.card (D ⧸ center D) ∣ AGLEmbedding.sporOrd s := by
  have h := SeitzReduction.OmegaPilot.card_quotient_center_dvd_card_of_fixed D
  rwa [Nat.card_congr e.toEquiv, AGLEmbedding.card_carrier_eq_sporOrd hMcard s] at h

end Dvd

end CFSG.ComponentClassification.CatFC
