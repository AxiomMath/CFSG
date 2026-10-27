module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem isElemAbelian_of_le {A : Type*} [Group A] {p : ℕ} {E F : Subgroup A}
    (hF : IsElemAbelian p F) (h : E ≤ F) : IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hF h

theorem hasE9_of_isElemAbelian_pow {A : Type*} [Group A] {E : Subgroup A} {n : ℕ}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ n) (hn : 2 ≤ n) : HasE9 A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3
    (show 3 ^ 2 ∣ Nat.card E from hc ▸ pow_dvd_pow 3 hn)
  have hle : S.map E.subtype ≤ E := Subgroup.map_subtype_le S
  exact ⟨S.map E.subtype, isElemAbelian_of_le hE hle,
    by rw [Subgroup.card_map_of_injective E.subtype_injective, hS]⟩

theorem hasE9_of_model_psp {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) : HasE9 Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨⟨A, hA, hAc⟩, -⟩ := CFSG.LieType.unique_even_symplectic_prime_field_three_rank
    (K := F) (n := n) (by omega)
  have hA' : IsElemAbelian 3 A :=
    ⟨inferInstance, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩
  exact hasE9_of_mulEquiv e.symm (hasE9_of_isElemAbelian_pow hA' hAc hn)

end CFSG.AGLEmbedding.BlockCyc
