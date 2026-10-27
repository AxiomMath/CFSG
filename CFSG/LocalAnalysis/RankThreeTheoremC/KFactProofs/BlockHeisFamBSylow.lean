module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisHomC
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SigmaDich

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.GroupTheory.WeirSylow
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

theorem heisB_exists_elemAbelian_of_sigmaModel {p : ℕ} (hp : p.Prime) {G : Type} [Group G]
    [Finite G] {e a N : ℕ} (ha : 1 ≤ a) (hm : p ≤ N / e)
    (h : ∀ P : Sylow p G, Nonempty (P ≃* sigmaModel p e a N)) :
    ∃ A : Subgroup G, IsMulCommutative A ∧ (∀ x ∈ A, x ^ p = 1) ∧ Nat.card A = p ^ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hL : 1 < (Nat.digits p (N / e)).length := by
    rw [Nat.lt_digits_length_iff hp.one_lt]
    simpa using hm
  have hne : N / e ≠ 0 := by have := hp.pos; omega
  let i₁ : Fin (Nat.digits p (N / e)).length := ⟨(Nat.digits p (N / e)).length - 1, by omega⟩
  have hi₁ : 1 ≤ (i₁ : ℕ) := by
    show 1 ≤ (Nat.digits p (N / e)).length - 1
    omega
  have hpos : 0 < (Nat.digits p (N / e))[i₁] := by
    have hlast := Nat.getLast_digit_ne_zero p hne
    have heq : (Nat.digits p (N / e))[i₁] =
        (Nat.digits p (N / e)).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hne) := by
      rw [List.getLast_eq_getElem]
      rfl
    rw [heq]
    exact Nat.pos_of_ne_zero hlast
  let j₁ : Fin (Nat.digits p (N / e))[i₁] := ⟨0, hpos⟩
  obtain ⟨E, hE, hEcard⟩ := SigmaDich.exists_elemAbelian_wreathTower hp ha i₁ hi₁
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p G))
  obtain ⟨φ⟩ := h S
  let Ψ : wreathTower p (Multiplicative (ZMod (p ^ a))) i₁ →* G :=
    (S : Subgroup G).subtype.comp (φ.symm.toMonoidHom.comp (SigmaDich.sigmaEmbed p e a N i₁ j₁))
  have hΨ : Function.Injective Ψ :=
    Subtype.coe_injective.comp
      (φ.symm.injective.comp (SigmaDich.sigmaEmbed_injective p e a N i₁ j₁))
  have hE' := (isElemAbelian_map_iff_of_injective Ψ hΨ E).2 hE
  exact ⟨E.map Ψ, hE'.1, hE'.2, by rw [Subgroup.card_map_of_injective hΨ]; exact hEcard⟩

theorem heisB_lt_of_sigmaModel {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {G : Type} [Group G]
    [Finite G] {e a N : ℕ} (ha : 1 ≤ a) (h : ∀ P : Sylow p G, Nonempty (P ≃* sigmaModel p e a N))
    (hrk : ∀ A : Subgroup G, IsMulCommutative A → (∀ x ∈ A, x ^ p = 1) → Nat.card A ≤ p ^ 3) :
    N / e < p := by
  by_contra hm
  push Not at hm
  obtain ⟨A, hA, hAp, hAc⟩ := heisB_exists_elemAbelian_of_sigmaModel hp ha hm h
  have h1 := hrk A hA hAp
  rw [hAc] at h1
  have h2 : p ^ 3 < p ^ p := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

theorem heisB_sylowShape_of_mulEquiv {p : ℕ} [Fact p.Prime] {G H M : Type*} [Group G] [Group H]
    [Group M] [Finite H] (φ : G ≃* H) (hH : ∀ P : Sylow p H, Nonempty (↥P ≃* M)) :
    ∀ S : Sylow p G, Nonempty (↥S ≃* M) :=
  sylowShape_of_injective φ.toMonoidHom φ.injective (by rw [Nat.card_congr φ.toEquiv]) hH

theorem heisB_one_le_padicValNat {p q : ℕ} [hp : Fact p.Prime] (hq : 1 < q) (hpq : ¬ p ∣ q) :
    1 ≤ padicValNat p (q ^ orderOf (q : ZMod p) - 1) := by
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  have hepos : 0 < orderOf (q : ZMod p) := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    exact ⟨p - 1, Nat.sub_pos_of_lt hp.out.one_lt, ZMod.pow_card_sub_one_eq_one hq0⟩
  have h1 : 1 < q ^ orderOf (q : ZMod p) := Nat.one_lt_pow hepos.ne' hq
  refine one_le_padicValNat_of_dvd (by omega) ?_
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1.le, Nat.cast_pow, pow_orderOf_eq_one,
    Nat.cast_one, sub_self]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
