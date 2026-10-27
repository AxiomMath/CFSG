module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpRoot
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.FieldRoot

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_le_card_of_pspn_of_ext (hW : ∀ w : W, w * w = 1)
    {K : Type} [Field K] [Finite K] {p e r : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ e) (hr : 1 ≤ r) {L : Subgroup (MulAut W)}
    (θ : ↥L ≃* StatedProj (StatedSp r K))
    {F : Type} [Field F] [Finite F] [Algebra K F] (hF : Module.finrank K F = r) :
    2 ^ (orderOf (2 : ZMod p) * ((p ^ (e * r) - 1) / (2 * (p - 1)))) ≤ Nat.card W := by
  have hfd : FiniteDimensional K F := Module.finite_of_finrank_pos (by omega)
  have hcharF : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  let β : Module.Basis (Fin r) K F := Module.finBasisOfFinrankEq K F hF
  have hsep : Algebra.IsSeparable K F := inferInstance
  have htr : Function.Surjective (Algebra.trace K F) := Algebra.trace_surjective K F
  have hcardF : Nat.card F = p ^ (e * r) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := F), hF, hK, ← pow_mul]
  have hker : (θ.toMonoidHom).ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    exact θ.injective
  have key := two_pow_le_card_of_field_root hW hp2 θ.toMonoidHom θ.surjective
    (by rw [hker]; exact bot_le)
    (by rw [hker, Subgroup.card_bot]; exact (Fact.out : p.Prime).not_dvd_one)
    (uProj β) (uProj_injective β (by omega) htr) (tProj β) (tProj_conj β)
  rwa [hcardF] at key

theorem two_pow_le_card_of_pspn (hW : ∀ w : W, w * w = 1)
    {K : Type} [Field K] [Finite K] {p e r : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ e) (hr : 1 ≤ r) {L : Subgroup (MulAut W)}
    (θ : ↥L ≃* StatedProj (StatedSp r K)) :
    2 ^ (orderOf (2 : ZMod p) * ((p ^ (e * r) - 1) / (2 * (p - 1)))) ≤ Nat.card W := by
  have : NeZero r := ⟨by omega⟩
  exact two_pow_le_card_of_pspn_of_ext hW hp2 hK hr θ (F := FiniteField.Extension K p r)
    (FiniteField.finrank_extension K p r)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
