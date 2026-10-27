module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL34a
public import Certificates.Certificate22611

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.Quasithin.HSType

namespace SCert.SE


theorem pauliE_mul : ∀ p q : Pauli2, pauliE (p * q) = pauliE p * pauliE q :=
  Certificates.certificate22611.1

theorem pauliE_predE : ∀ p : Pauli2, predE (pauliE p) := Certificates.certificate22611.2.1

theorem pauliE_eq_one : ∀ p : Pauli2, pauliE p = 1 → p = 1 :=
  Certificates.certificate22611.2.2.1

theorem not_comm_mod_E : ∀ k : SE, 4 ≤ k.d.val → ¬ predE (k⁻¹ * (gen 6)⁻¹ * k * gen 6) ∨
    ¬ predE (k⁻¹ * (gen 7)⁻¹ * k * gen 7) :=
  Certificates.certificate22611.2.2.2

@[expose] def pauliEHom : Pauli2 →* SE where
  toFun := pauliE
  map_one' := by decide
  map_mul' := pauliE_mul

theorem pauliEHom_injective : Function.Injective pauliEHom :=
  (injective_iff_map_eq_one _).mpr pauliE_eq_one

theorem range_pauliEHom : pauliEHom.range = Esub := by
  refine eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨p, rfl⟩
    exact pauliE_predE p
  · rw [card_Esub, ← Nat.card_congr (MonoidHom.ofInjective pauliEHom_injective).toEquiv,
      Pauli2.card]

@[expose] def EsubEquivPauli2 : Esub ≃* Pauli2 :=
  (MulEquiv.subgroupCongr range_pauliEHom.symm).trans
    (MonoidHom.ofInjective pauliEHom_injective).symm

end SCert.SE

namespace GHSylow

variable {G : Type} [Group G] (D : GHSylow G)

theorem isZ4Q8Q8_E : IsZ4Q8Q8 ↥D.E :=
  ⟨((SE.Esub.equivMapOfInjective D.toG D.toG_injective).symm.trans SE.EsubEquivPauli2).trans
    z4Q8Q8EquivPauli2.symm⟩

end GHSylow

end CFSG.ComponentClassification.GHarris
