module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleQ

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

@[expose] def SingleComponentQuasisimpleAt (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → pPrimeCore 2 Q = ⊥ →
    P (Q ⧸ center Q) →
    ∀ X Y : Subgroup Q, ⁅X, X⁆ = X → ⁅Y, Y⁆ = Y →
      IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X) → IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y) →
      2 ≤ CFSG.Open.pRank 2 X → 2 ≤ CFSG.Open.pRank 2 Y →
      ⁅X, Y⁆ ≤ oddCoreIn X ⊓ oddCoreIn Y →
      (∀ x ∈ X, orderOf x = 2 → ∃ P : Subgroup Q,
        IsTwoComponentIn P (centralizer ({x} : Set Q)) ∧
        P ⊔ oddCoreIn (centralizer ({x} : Set Q)) =
          twoLayerIn (Y ⊓ centralizer ({x} : Set Q)) ⊔ oddCoreIn (centralizer ({x} : Set Q))) →
      (∀ y ∈ Y, orderOf y = 2 → ∃ P : Subgroup Q,
        IsTwoComponentIn P (centralizer ({y} : Set Q)) ∧
        P ⊔ oddCoreIn (centralizer ({y} : Set Q)) =
          twoLayerIn (X ⊓ centralizer ({y} : Set Q)) ⊔ oddCoreIn (centralizer ({y} : Set Q))) →
      False

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem oddCoreIn_top_eq_bot_of_pPrimeCore (hO : pPrimeCore 2 Q = ⊥) :
    oddCoreIn (⊤ : Subgroup Q) = ⊥ := by
  have h := pPrimeCore_map_iso 2 (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q)
  rw [hO] at h
  have h2 : pPrimeCore 2 ↥(⊤ : Subgroup Q) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy' : (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q) y ∈ (⊥ : Subgroup Q) :=
      h ▸ ⟨y, hy, rfl⟩
    rw [mem_bot] at hy' ⊢
    exact (MulEquiv.map_eq_one_iff _).mp hy'
  simp only [oddCoreIn, h2, Subgroup.map_bot]

omit [Finite Q] in
theorem not_isQuasisimple_of_le_oddCoreIn {X : Subgroup Q} (hX : X ≤ oddCoreIn X) :
    ¬ IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X) := by
  intro hXq
  have htop : ∀ x : ↥X, x ∈ pPrimeCore 2 ↥X := fun x => by
    obtain ⟨y, hy, hyx⟩ := hX x.2
    rwa [show y = x from Subtype.ext hyx] at hy
  have hsub : ∀ a b : ↥X ⧸ pPrimeCore 2 ↥X, a = b := fun a b => by
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact QuotientGroup.eq.mpr (htop _)
  obtain ⟨a, b, hab⟩ := hXq.2.2
  apply hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  rw [hsub a' b']

theorem false_of_center_mem_left (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥)
    {X Y : Subgroup Q} (hXp : ⁅X, X⁆ = X) (hXq : IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X))
    (hcomm : ⁅X, Y⁆ ≤ oddCoreIn X ⊓ oddCoreIn Y)
    (hP : ∀ x ∈ X, orderOf x = 2 → ∃ P : Subgroup Q,
      IsTwoComponentIn P (centralizer ({x} : Set Q)) ∧
      P ⊔ oddCoreIn (centralizer ({x} : Set Q)) =
        twoLayerIn (Y ⊓ centralizer ({x} : Set Q)) ⊔ oddCoreIn (centralizer ({x} : Set Q)))
    {x : Q} (hxX : x ∈ X) (hx2 : orderOf x = 2) (hxZ : x ∈ center Q) : False := by
  have hC : centralizer ({x} : Set Q) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr hxZ)
  obtain ⟨P, hPC, heq⟩ := hP x hxX hx2
  rw [hC] at hPC heq
  have hQt : IsQuasisimple ↥(⊤ : Subgroup Q) :=
    isQuasisimple_of_mulEquiv (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q).symm hQ
  have hPt : P = ⊤ := by
    have h1 := CatalogueBAlternatingIsometry.pComponent_eq_top_of_quasisimple hQt 2 _ hPC.2
    exact top_le_iff.mp (Subgroup.subgroupOf_eq_top.mp h1)
  rw [hPt, oddCoreIn_top_eq_bot_of_pPrimeCore hO, sup_bot_eq, sup_bot_eq, inf_top_eq] at heq
  have hY : Y = ⊤ := top_le_iff.mp (heq.le.trans (map_subtype_le _))
  apply not_isQuasisimple_of_le_oddCoreIn (X := X) _ hXq
  calc X = ⁅X, X⁆ := hXp.symm
    _ ≤ ⁅X, Y⁆ := commutator_mono le_rfl (hY ▸ le_top)
    _ ≤ oddCoreIn X := hcomm.trans inf_le_left

theorem false_of_center_mem_right (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥)
    {X Y : Subgroup Q} (hYp : ⁅Y, Y⁆ = Y) (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y))
    (hcomm : ⁅X, Y⁆ ≤ oddCoreIn X ⊓ oddCoreIn Y)
    (hP : ∀ y ∈ Y, orderOf y = 2 → ∃ P : Subgroup Q,
      IsTwoComponentIn P (centralizer ({y} : Set Q)) ∧
      P ⊔ oddCoreIn (centralizer ({y} : Set Q)) =
        twoLayerIn (X ⊓ centralizer ({y} : Set Q)) ⊔ oddCoreIn (centralizer ({y} : Set Q)))
    {y : Q} (hyY : y ∈ Y) (hy2 : orderOf y = 2) (hyZ : y ∈ center Q) : False :=
  false_of_center_mem_left hQ hO hYp hYq (by rw [commutator_comm, inf_comm]; exact hcomm) hP hyY
    hy2 hyZ

theorem singleComponentQuasisimpleFor_of_families
    (hA : SingleComponentQuasisimpleAt
      (fun S _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))))
    (hC : SingleComponentQuasisimpleAt (fun S _ => Milestones.ClassicalRep S))
    (hE : SingleComponentQuasisimpleAt (fun S _ => Blueprint.ExceptionalRep S))
    (hS : SingleComponentQuasisimpleAt (fun S _ => Blueprint.NativeSporadic.SporadicRep S)) :
    SingleComponentQuasisimpleFor := by
  intro Q _ _ hQ hO hcat X Y hXp hYp hXq hYq hXr hYr hcomm hP₁ hP₂
  rcases hcat with ⟨p, -, ⟨e⟩⟩ | hAlt | hCl | hEx | hSp
  · obtain ⟨a, b, hab⟩ := hQ.2.2
    apply hab
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · exact hA Q hQ hO hAlt X Y hXp hYp hXq hYq hXr hYr hcomm hP₁ hP₂
  · exact hC Q hQ hO hCl X Y hXp hYp hXq hYq hXr hYr hcomm hP₁ hP₂
  · exact hE Q hQ hO hEx X Y hXp hYp hXq hYq hXr hYr hcomm hP₁ hP₂
  · exact hS Q hQ hO hSp X Y hXp hYp hXq hYq hXr hYr hcomm hP₁ hP₂

end CFSG.ComponentClassification.Sol76.Sig
