module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5InputsB
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Types

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem isKleinFour_of_card_four_sq {X : Subgroup G} (hX4 : Nat.card X = 4)
    (hXsq : ∀ x ∈ X, x * x = 1) : IsKleinFour X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial X := by
    rw [← Finite.one_lt_card_iff_nontrivial, hX4]
    norm_num
  exact ⟨hX4, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg =>
    orderOf_eq_prime (by rw [sq]; exact Subtype.ext (hXsq g g.2)) hg⟩

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem exists_a4_fixed (hFC : Foote5FieldCentralizer) (h𝕊 : FooteSimpleType 𝕊)
    (hD : Foote5AutData 𝕊 Lin) {v : G} (hvS : v ∈ S) (hv2 : v * v = 1)
    (hβ : actG L ε v ∉ Lin) :
    ∃ X : Subgroup 𝕊, (∀ x ∈ X, actG L ε v x = x) ∧
      Nonempty (X ≃* alternatingGroup (Fin 4)) := by
  have hvN := h.S_le hvS
  set β := actG L ε v with hβdef
  have hββ : β * β = 1 := by rw [hβdef, ← actG_mul ε hvN hvN, hv2, actG_one]
  obtain ⟨g, hg⟩ := hD.conj_centralizer (h.Rbar ε) β hβ hββ
  set β' := MulAut.conj g * β * (MulAut.conj g)⁻¹ with hβ'
  have h2 : β = (MulAut.conj g)⁻¹ * β' * MulAut.conj g := by rw [hβ']; group
  have hβ'β' : β' * β' = 1 := by
    calc β' * β' = MulAut.conj g * (β * β) * (MulAut.conj g)⁻¹ := by rw [hβ']; group
      _ = 1 := by rw [hββ]; group
  have hβ'inn : β' ∉ innAut5 𝕊 := by
    intro h1
    apply hβ
    apply hD.inn_le
    rw [h2]
    exact mul_mem (mul_mem (inv_mem ⟨g, rfl⟩) h1) ⟨g, rfl⟩
  obtain ⟨X', hX'fix, ⟨φ'⟩⟩ := (hFC 𝕊 h𝕊).1 β' hβ'β' hβ'inn ⟨h.Rbar ε, hg⟩
  refine ⟨X'.map (MulAut.conj g⁻¹).toMonoidHom, ?_,
    ⟨((X'.equivMapOfInjective _ (MulAut.conj g⁻¹).injective).symm).trans φ'⟩⟩
  rintro _ ⟨x', hx', rfl⟩
  have h1 := hX'fix x' hx'
  show β ((MulAut.conj g⁻¹) x') = (MulAut.conj g⁻¹) x'
  rw [h2, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
    show g * (g⁻¹ * x' * g⁻¹⁻¹) * g⁻¹ = x' by group, h1, ← map_inv, MulAut.conj_apply]

end Sec5

end CFSG.ComponentClassification.Foote5
