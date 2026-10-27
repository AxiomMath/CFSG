module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterStructCases
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Aut

variable {X : Type*} [Group X] {τ : X}

@[expose] def tauAut (K : Subgroup X) (ht2 : τ * τ = 1) (hK : ∀ x ∈ K, τ * x * τ⁻¹ ∈ K) :
    MulAut ↥K where
  toFun x := ⟨τ * x * τ⁻¹, hK x x.2⟩
  invFun x := ⟨τ * x * τ⁻¹, hK x x.2⟩
  left_inv x := Subtype.ext (conj_conj_of_sq ht2 x)
  right_inv x := Subtype.ext (conj_conj_of_sq ht2 x)
  map_mul' x y := Subtype.ext (by
    show τ * ((x : X) * y) * τ⁻¹ = (τ * x * τ⁻¹) * (τ * y * τ⁻¹)
    group)

theorem tauAut_apply (K : Subgroup X) (ht2 : τ * τ = 1) (hK : ∀ x ∈ K, τ * x * τ⁻¹ ∈ K)
    (x : ↥K) : ((tauAut K ht2 hK x : ↥K) : X) = τ * x * τ⁻¹ := rfl

theorem tauAut_sq (K : Subgroup X) (ht2 : τ * τ = 1) (hK : ∀ x ∈ K, τ * x * τ⁻¹ ∈ K) :
    tauAut K ht2 hK * tauAut K ht2 hK = 1 := by
  ext x
  exact conj_conj_of_sq ht2 x

theorem mem_autCentralizer_tauAut_iff (K : Subgroup X) (ht2 : τ * τ = 1)
    (hK : ∀ x ∈ K, τ * x * τ⁻¹ ∈ K) (x : ↥K) :
    x ∈ autCentralizer (tauAut K ht2 hK) ↔ (x : X) * τ = τ * x := by
  have h : x ∈ autCentralizer (tauAut K ht2 hK) ↔ tauAut K ht2 hK x = x := Iff.rfl
  rw [h, ← Subtype.coe_inj, tauAut_apply]
  constructor
  · intro h
    calc (x : X) * τ = (τ * x * τ⁻¹) * τ := by rw [h]
      _ = τ * x := by group
  · intro h
    rw [← h]
    group

theorem map_autCentralizer_tauAut (K : Subgroup X) (ht2 : τ * τ = 1)
    (hK : ∀ x ∈ K, τ * x * τ⁻¹ ∈ K) :
    (autCentralizer (tauAut K ht2 hK)).map K.subtype = K ⊓ centralizer ({τ} : Set X) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, mem_centralizer_singleton_iff.2
      ((mem_autCentralizer_tauAut_iff K ht2 hK x).1 hx)⟩
  · rintro ⟨hgK, hgc⟩
    exact ⟨⟨g, hgK⟩, (mem_autCentralizer_tauAut_iff K ht2 hK ⟨g, hgK⟩).2
      (mem_centralizer_singleton_iff.1 hgc), rfl⟩

@[expose] noncomputable def autCentralizerEquiv (K : Subgroup X) (ht2 : τ * τ = 1)
    (hK : ∀ x ∈ K, τ * x * τ⁻¹ ∈ K) :
    ↥(autCentralizer (tauAut K ht2 hK)) ≃* ↥(K ⊓ centralizer ({τ} : Set X)) :=
  (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_autCentralizer_tauAut K ht2 hK))

theorem card_autCentralizer_tauAut (K : Subgroup X) (ht2 : τ * τ = 1)
    (hK : ∀ x ∈ K, τ * x * τ⁻¹ ∈ K) :
    Nat.card ↥(autCentralizer (tauAut K ht2 hK)) =
      Nat.card ↥(K ⊓ centralizer ({τ} : Set X)) :=
  Nat.card_congr (autCentralizerEquiv K ht2 hK).toEquiv

end Aut

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
