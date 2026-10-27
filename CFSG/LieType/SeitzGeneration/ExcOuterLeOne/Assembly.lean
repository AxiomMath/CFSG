module

public import CFSG.LieType.SeitzGeneration.ExcOuterSplit

open CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.CTP
open CFSG.Blueprint.Chevalley
open TauCeti (PrimePower LieTypeIndex)

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne

theorem closure_fixUnion_eq_top_of_fieldAutData' {K : Type} [Group K]
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {p : ℕ} (hp : p.Prime)
    (hd : FieldAutData K p) (E : Subgroup (MulAut K)) [hE : CFSG.IsElementaryAbelian p E]
    (hEc : Nat.card E = p ^ 2) (hout : ¬ ∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk1, hkE⟩ := hd.out_rank E hE hEc
  push Not at hout
  obtain ⟨σ, hσE, hσinn⟩ := hout
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hσ1 : σ ≠ 1 := fun h => hσinn 1 (by rw [h, map_one])
  have hσp : σ ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian σ hσE
  have hσo : IsOuterOfOrder p σ := ⟨orderOf_eq_prime hσp hσ1, hσinn⟩
  have hkp : k ^ p = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hkE
  have hcomm : σ * MulAut.conj k = MulAut.conj k * σ := hcommE σ hσE _ hkE
  have hστ1 : σ * MulAut.conj k ≠ 1 := by
    intro h
    apply hσinn k⁻¹
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left h
  have hστp : (σ * MulAut.conj k) ^ p = 1 := by
    rw [(show Commute σ (MulAut.conj k) from hcomm).mul_pow, hσp, ← map_pow, hkp, map_one, one_mul]
  have hστo : IsOuterOfOrder p (σ * MulAut.conj k) := by
    refine ⟨orderOf_eq_prime hστp hστ1, fun g h => hσinn (g * k⁻¹) ?_⟩
    rw [map_mul, map_inv, ← h, mul_assoc, mul_inv_cancel, mul_one]
  exact closure_fixUnion_eq_top_of_pair hinj hp E hσE hσinn hkE hk1 hkp hcomm
    (hd.center σ hσo) (hd.gen σ _ hσo hστo)

theorem planeGen_outer_of_fieldAutData {d : TauCeti.ValidLieTypeIndex} {P : Type} [Group P]
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) (e : Cat d ≃* P) {p : ℕ}
    (hp : p.Prime) (hd : FieldAutData P p) {E : Subgroup (MulAut (Cat d))}
    (hE : CFSG.Open.IsElemAbelian p E) (hc : Nat.card E = p ^ 2) (hout : ¬ InnerPlane d p E) :
    PlaneGen E := by
  have : Fact p.Prime := ⟨hp⟩
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  have hclos := closure_fixUnion_eq_top_of_fieldAutData' hinj hp hd
    (E.map (MulAut.congr e).toMonoidHom) hc' hout'
  exact planeGen_of_outer_model e ((planeGen_iff_closure_fixUnion _).mpr hclos)


theorem seitzExcOuterNarrowLeOne_of_fieldAutData {τ : Tag} {c : PrimePower → LieTypeIndex}
    {F : LieTypeIndex → Prop} {X : PrimePower → Prop}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hchar : ∀ q, (c q).characteristic = q.p)
    (hinj : ∀ (K : Type) [Field K] [Finite K],
      Function.Injective (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)))
    (hF : ∀ (K : Type) [Field K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → p ≠ ringChar K →
      degCount τ (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 →
      FieldAutData ↥(adjointGroup τ K) p) :
    SeitzExcOuterNarrowForAt F (LeOneRange c X (degCount τ)) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, -, hp5, q, hdq, -, hle⟩
  obtain rfl : d = c q := hdq
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ := exists_catEquiv_adjointGroup hB q hv
  have hpq : p ≠ q.p := fun h => hpd (h.trans (hchar q).symm)
  have hpK : p ≠ ringChar K := by rw [ringChar.eq K q.p]; exact hpq
  have hle' : degCount τ (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 := by rwa [hK]
  exact planeGen_outer_of_fieldAutData (hinj K) e hp (hF K p hp hp5 hpK hle') hE hc hout

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
