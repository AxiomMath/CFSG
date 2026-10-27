module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

theorem exists_inner_of_cyclic_quotient {S N A : Type} [Group S] [Group N] [Group A] [Finite A]
    [IsCyclic A] (e : S ≃* N) (Θ : MulAut N →* A)
    (hker : Θ.ker = (MulAut.conj : N →* MulAut N).range) {p : ℕ} (hp : p.Prime)
    (D : Subgroup (MulAut S)) (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ innerAut S, x ≠ 1 := by
  classical
  let φ : MulAut S →* MulAut N := (MulAut.congr e).toMonoidHom
  let Θ' : MulAut S →* A := Θ.comp φ
  let α : D →* A := Θ'.comp D.subtype
  have hexpα : Monoid.exponent α.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨x, rfl⟩ := α.rangeRestrict_surjective y
    have : (x : D) ^ p = 1 := Subtype.ext (hexp x x.2)
    rw [← map_pow, this, map_one]
  rw [IsCyclic.exponent_eq_card] at hexpα
  have hsplit : Nat.card D = Nat.card α.range * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
  have hrle : Nat.card α.range ≤ p := Nat.le_of_dvd hp.pos hexpα
  have hk1 : 1 < Nat.card α.ker := by
    by_contra hle
    have h1 : Nat.card D ≤ p * 1 := by
      rw [hsplit]
      exact Nat.mul_le_mul hrle (by omega)
    omega
  have hDfin : Finite D := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial α.ker := Finite.one_lt_card_iff_nontrivial.1 hk1
  obtain ⟨⟨d, hdk⟩, hd1⟩ := exists_ne (1 : α.ker)
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  refine ⟨(d : MulAut S), ⟨d.2, ?_⟩, fun h => hd1' (Subtype.ext h)⟩
  have hmem : φ d ∈ Θ.ker := hdk
  rw [hker] at hmem
  obtain ⟨n, hn⟩ := hmem
  refine ⟨e.symm n, ?_⟩
  apply (MulAut.congr e).injective
  change φ _ = φ d
  rw [← hn]
  ext s
  simp [φ, MulAut.congr_apply, MulAut.conj_apply]

theorem lt_pow_three_of_prime {p : ℕ} (hp : p.Prime) : p < p ^ 3 := by
  simpa using Nat.pow_lt_pow_right hp.one_lt (show 1 < 3 by norm_num)

section


theorem defCharOuterRankFamF4 : DefCharOuterRankFam .F4 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv K hK'
  let e : S ≃* adjointGroup .F4 K :=
    e0.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2
    q.exponent_pos K hK .F4 (Or.inl rfl)
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) := Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  obtain ⟨x, hx, hx1⟩ := exists_inner_of_cyclic_quotient e Θ hker hp D hD.2 (hcard ▸ lt_pow_three_of_prime hp)
  exact ⟨x, hx, hx1⟩

theorem defCharOuterRankFamG2 : DefCharOuterRankFam .G2 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv K hK'
  let e : S ≃* adjointGroup .G2 K :=
    e0.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  by_cases h3 : q.p = 3
  · have hchar : CharP K ReeTag.G2.prime := by
      have : CharP K q.p := inferInstance
      rw [show ReeTag.G2.prime = 3 from rfl, ← h3]
      exact this
    have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK, h3]
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form q.exponent_pos K hK3
    have : NeZero (2 * q.exponent) := ⟨by have := q.exponent_pos; omega⟩
    have : IsCyclic (Multiplicative (ZMod (2 * q.exponent))) := inferInstance
    obtain ⟨x, hx, hx1⟩ := exists_inner_of_cyclic_quotient (A := Multiplicative (ZMod (2 * q.exponent)))
      e Θ hker hp D hD.2 (hcard ▸ lt_pow_three_of_prime hp)
    exact ⟨x, hx, hx1⟩
  · obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2
      q.exponent_pos K hK .G2 (Or.inr ⟨rfl, h3⟩)
    have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
    have : Finite (K ≃+* K) :=
      Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
    obtain ⟨x, hx, hx1⟩ := exists_inner_of_cyclic_quotient e Θ hker hp D hD.2
      (hcard ▸ lt_pow_three_of_prime hp)
    exact ⟨x, hx, hx1⟩

end

end CFSG.HardMathSupport.Timmesfeld.DefChar
