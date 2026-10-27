module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldEntrywise
public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

section OddInnerField


theorem fieldCoreAt_of_oddInnerField {τ : Tag} {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    (hNF : ∀ η : MulAut (adjointGroup τ K), ∃! gβ : adjointGroup τ K × (K ≃+* K),
      η = MulAut.conj gβ.1 * entrywiseAdjointAut τ gβ.2)
    {p : ℕ} (hp : p.Prime)
    (hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup τ (fixSubfield σ))))
    {x : MulAut (adjointGroup τ K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range) :
    FieldCoreAt p x := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF x
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup τ K)))) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxp
  obtain ⟨hσp, -, ⟨δ, hδ⟩, -⟩ := odd_Chevalley_inner_field_noninner_prime_local_core_trivial τ hℓ
    hℓ2 hf K hK hNF hp ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxo hαp y σ hyσ
  obtain ⟨hJC, hsimple, hnc, -, hNδ, hnormal, hcent⟩ :=
    odd_entrywise_canonical_core_data hℓ2 (fun η => (hNF η).exists) σ
  exact fieldCoreAt_of_conj (fieldCoreAt_entrywise_of_data hσp hJC hsimple hnc hNδ hnormal hcent
    (hdvd σ hσp)) δ hδ

end OddInnerField

end CFSG.HardMathSupport.Timmesfeld.CrossChar
