module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ0A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

@[expose] def z4iVc (K : Subgroup H) (t τ l : H) : Subgroup H := K ⊔ z4iT3 t τ l

namespace ZEData

variable {Q Y V V' B K : Subgroup H} {ρ t τ l : H}

theorem K_le_Vc (K : Subgroup H) (t τ l : H) : K ≤ z4iVc K t τ l := by
  show K ≤ K ⊔ z4iT3 t τ l
  exact le_sup_left

theorem T3_le_Vc (K : Subgroup H) (t τ l : H) : z4iT3 t τ l ≤ z4iVc K t τ l := by
  show z4iT3 t τ l ≤ K ⊔ z4iT3 t τ l
  exact le_sup_right

theorem Q_le_Vc (h : ZEData Q Y V V' B K ρ t τ l) : Q ≤ z4iVc K t τ l :=
  h.Q_le_K.trans (K_le_Vc K t τ l)

theorem mem_Vc_iff (h : ZEData Q Y V V' B K ρ t τ l) {x : H} :
    x ∈ z4iVc K t τ l ↔ ∃ k ∈ K, ∃ s ∈ z4iT3 t τ l, x = k * s := by
  show x ∈ K ⊔ z4iT3 t τ l ↔ ∃ k ∈ K, ∃ s ∈ z4iT3 t τ l, x = k * s
  exact mem_sup_iff_of_normalizes (H := K) (K := z4iT3 t τ l) h.T3_norm_K

theorem card_Vc (h : ZEData Q Y V V' B K ρ t τ l) : Nat.card (z4iVc K t τ l) = 2048 := by
  have hinf : K ⊓ z4iT3 t τ l = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    exact Subgroup.mem_bot.mpr (h.T3_inf_K x hx.2 hx.1)
  have hcard := card_sup_eq_mul (H := K) (K := z4iT3 t τ l) h.T3_norm_K hinf
  show Nat.card ↥(K ⊔ z4iT3 t τ l) = 2048
  rw [hcard, h.card_K, h.card_T3]

theorem Vc_pgroup (h : ZEData Q Y V V' B K ρ t τ l) : IsPGroup 2 (z4iVc K t τ l) :=
  IsPGroup.of_card (n := 11) (by rw [card_Vc h]; norm_num)

end ZEData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
