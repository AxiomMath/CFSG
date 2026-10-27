module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OuterBound

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family

theorem card_le_of_autInner {S : Type} [Group S]
    (hAut : ∀ φ : S ≃* S, ∃ s : S, ∀ x, φ x = s * x * s⁻¹) (B : Subgroup (MulAut S)) :
    Nat.card B ≤ 1 * Nat.card ↥(B ⊓ (MulAut.conj : S →* MulAut S).range) := by
  have htop : (MulAut.conj : S →* MulAut S).range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro φ
    obtain ⟨s, hs⟩ := hAut φ
    exact ⟨s, MulEquiv.ext fun x => by rw [MulAut.conj_apply]; exact (hs x).symm⟩
  rw [htop, inf_top_eq, one_mul]

theorem exclusion_of_heisCfg_of_outer {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)} (hL : CFSG.IsQuasisimple ↥L)
    (hirr : IsIrrOn L) (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥)
    (hEel : CFSG.Quasithin.IsElemAbelian2 E) {S : Type} [Group S] (e : CQ L ≃* S) {k : ℕ}
    (hOut : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ k * Nat.card ↥(B ⊓ (MulAut.conj : S →* MulAut S).range))
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    {x y : Fin n → S} {z : S} (h : HeisCfg p n x y z) (hy : ∀ i, y i ^ p = 1)
    (hlt : k * (Nat.card (Subgroup.center ↥L) * Nat.card S) < 2 ^ (p ^ n * orderOf (2 : ZMod p))) :
    Nat.card E * Nat.card (fixV E) < Nat.card W :=
  exclusion_of_card_lt_of_outer hW hL hirr hE hEne hEel e hOut
    (hlt.trans_le (two_pow_le_card_of_heisCfg_centerQuotient hW e hp2 hZ h hy))

theorem exclusion_of_heisCfg_of_outer_of_inv_seven {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)} (hL : CFSG.IsQuasisimple ↥L)
    (hirr : IsIrrOn L) (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥)
    (hEel : CFSG.Quasithin.IsElemAbelian2 E) {S : Type} [Group S] (e : CQ L ≃* S) {k : ℕ}
    (hOut : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ k * Nat.card ↥(B ⊓ (MulAut.conj : S →* MulAut S).range))
    {n : ℕ} (hZ : ¬ 7 ∣ Nat.card (Subgroup.center ↥L))
    {x y : Fin n → S} {z : S} (h : HeisCfg 7 n x y z) (hy : ∀ i, y i ^ 7 = 1)
    {g : S} (hg : g * z * g⁻¹ = z⁻¹)
    (hlt : k * (Nat.card (Subgroup.center ↥L) * Nat.card S) < 2 ^ (2 * (7 ^ n * 3))) :
    Nat.card E * Nat.card (fixV E) < Nat.card W :=
  exclusion_of_card_lt_of_outer hW hL hirr hE hEne hEel e hOut
    (hlt.trans_le (two_pow_le_card_of_heisCfg_centerQuotient_of_inv_seven hW e hZ h hy hg))

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
