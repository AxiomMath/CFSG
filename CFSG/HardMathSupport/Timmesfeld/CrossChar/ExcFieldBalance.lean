module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReduction
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Chevalley.SteinbergBT
  CFSG.HardMathSupport.Timmesfeld.Coordinator

section Balance


theorem isLocallyBalancedAbs_adjoint_of_fieldCore {τ : Tag} (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hr : RankLE2 p (adjointGroup τ K))
    (hfc : ∀ x : MulAut (adjointGroup τ K), orderOf x = p →
      x ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range →
        FieldCoreAt p x) :
    IsLocallyBalancedAbs p 3 (adjointGroup τ K) := by
  have : Finite (ModGL τ K) := finite_modGL
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := τ) (K := K))
  refine isLocallyBalancedAbs_of_fieldCore hp hinj
    (fun D hD hcard hin => false_of_inner_cube_of_rankLE2 hp hinj hr hD hcard hin) ?_
  intro x hxp hxo
  have : Fact p.Prime := ⟨hp⟩
  exact hfc x (orderOf_eq_prime hxp fun h => hxo (by rw [h]; exact one_mem _)) hxo

end Balance

section Arithmetic

variable {K : Type} [Field K] [Finite K]

theorem card_fixSubfield_cast {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) {σ : K ≃+* K} (hσp : orderOf σ = p) :
    ((Nat.card (fixSubfield σ) : ℕ) : ZMod p) = ((Nat.card K : ℕ) : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hdvd, hcard⟩ := card_fixSubfield hℓ hf hK σ
  rw [hσp] at hdvd hcard
  obtain ⟨d, rfl⟩ := hdvd
  rw [Nat.mul_div_cancel_left _ hp.pos] at hcard
  rw [hcard, hK, mul_comm p d, pow_mul, Nat.cast_pow (ℓ ^ d) p, ZMod.pow_card]

theorem not_coprime_card_of_sylowTorus {G : Type*} [Group G] [Finite G] {p m : ℕ}
    (h : SylowTorus G p m) (hp : p.Prime) (hm : 1 ≤ m) : ¬ Nat.Coprime p (Nat.card G) := by
  obtain ⟨E, -, hE⟩ := h.exists_elemAbelian
  have h1 : p ^ m ∣ Nat.card G := hE ▸ Subgroup.card_subgroup_dvd_card E
  exact (Nat.Prime.dvd_iff_not_coprime hp).1 ((dvd_pow_self p (by omega)).trans h1)

end Arithmetic

section Regimes

@[expose] def regimeExcField (c : TauCeti.PrimePower → TauCeti.LieTypeIndex) (a : ℕ → ℕ)
    (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = c q ∧ a (orderOf ((q.card : ℕ) : ZMod p)) = 2 ∧
    p ∣ q.exponent

@[expose] def regimeExcFieldOdd (c : TauCeti.PrimePower → TauCeti.LieTypeIndex) (a : ℕ → ℕ)
    (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = c q ∧ a (orderOf ((q.card : ℕ) : ZMod p)) = 2 ∧
    p ∣ q.exponent ∧ q.p ≠ 2

@[expose] def regimeExcFieldEven (c : TauCeti.PrimePower → TauCeti.LieTypeIndex) (a : ℕ → ℕ)
    (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = c q ∧ a (orderOf ((q.card : ℕ) : ZMod p)) = 2 ∧
    p ∣ q.exponent ∧ q.p = 2

end Regimes

end CFSG.HardMathSupport.Timmesfeld.CrossChar
