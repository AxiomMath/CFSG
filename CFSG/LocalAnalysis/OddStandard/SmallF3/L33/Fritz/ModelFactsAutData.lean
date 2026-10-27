module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutNorm

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier CFSG.Blueprint

namespace IsL33Model

variable {L : Type} [Group L] {M : AutModel L (Equiv.Perm (Fin 26))}

theorem elG1_inner (h : IsL33Model M) : ∃ a : L, ∀ u : L, h.elG1 u = a * u * a⁻¹ :=
  (liftA_inner_iff M h.P_le_A h.modelG1_mem_A).2 (by rw [h.P_eq]; exact model_inner_mem.2.2.1)

theorem elG2_inner (h : IsL33Model M) : ∃ a : L, ∀ u : L, h.elG2 u = a * u * a⁻¹ :=
  (liftA_inner_iff M h.P_le_A h.modelG2_mem_A).2
    (by rw [h.P_eq]; exact model_inner_mem.2.2.2.1)

end IsL33Model

structure FritzData (L : Type) [Group L] where
  x : L
  y : L
  k : MulAut L
  g₁ : MulAut L
  g₂ : MulAut L
  x_pow_eight : x ^ 8 = 1
  x_pow_four_ne_one : x ^ 4 ≠ 1
  y_sq : y ^ 2 = 1
  y_conj : y * x * y⁻¹ = x ^ 3
  card_xy : Nat.card (Subgroup.closure ({x, y} : Set L)) = 16
  k_sq : k ^ 2 = 1
  k_outer : ¬ ∃ a : L, ∀ u : L, k u = a * u * a⁻¹
  k_x : k x = x * x ^ 4
  k_y : k y = y
  d_sq : (MulAut.conj (x * y) * k) ^ 2 = 1
  d_outer : ¬ ∃ a : L, ∀ u : L, (MulAut.conj (x * y) * k) u = a * u * a⁻¹
  card_T : Nat.card (Subgroup.closure ({MulAut.conj x, MulAut.conj y, k} : Set (MulAut L))) = 32
  card_centralizer_k : Nat.card (Subgroup.centralizer ({k} : Set (MulAut L))) = 48
  card_fixed_k : Nat.card {a : L // k a = a} = 24
  g₁_inner : ∃ a : L, ∀ u : L, g₁ u = a * u * a⁻¹
  g₂_inner : ∃ a : L, ∀ u : L, g₂ u = a * u * a⁻¹
  g₁_pow : g₁ ^ 3 = 1
  g₁_z : g₁ (x ^ 4) = y
  g₁_y : g₁ y = x ^ 4 * y
  g₁_k : g₁ * k * g₁⁻¹ = k
  g₂_pow : g₂ ^ 3 = 1
  g₂_z : g₂ (x ^ 4) = x ^ 2 * y
  g₂_w : g₂ (x ^ 2 * y) = x ^ 4 * (x ^ 2 * y)
  g₂_zk : g₂ * (MulAut.conj (x ^ 4) * k) * g₂⁻¹ = MulAut.conj (x ^ 4) * k
  k_fixed : ∀ n ∈ Subgroup.normalizer
      (Subgroup.closure ({MulAut.conj (x ^ 4), MulAut.conj y, k} : Set (MulAut L)) :
        Set (MulAut L)), n * k * n⁻¹ = k
  zk_fixed : ∀ n ∈ Subgroup.normalizer
      (Subgroup.closure ({MulAut.conj (x ^ 4), MulAut.conj (x ^ 2 * y), k} : Set (MulAut L)) :
        Set (MulAut L)), n * (MulAut.conj (x ^ 4) * k) * n⁻¹ = MulAut.conj (x ^ 4) * k

theorem l33_nonempty_fritzData
    {L : Type} [Group L] (hL : LieModel L .PSL 3 3 1) : Nonempty (FritzData L) := by
  obtain ⟨M, h⟩ := exists_isL33Model hL
  exact ⟨{
    x := h.elX
    y := h.elY
    k := h.elK
    g₁ := h.elG1
    g₂ := h.elG2
    x_pow_eight := h.elX_pow_eight
    x_pow_four_ne_one := h.elX_pow_four_ne_one
    y_sq := h.elY_sq
    y_conj := h.elY_conj
    card_xy := h.card_closure_elXY
    k_sq := h.elK_sq
    k_outer := h.elK_outer
    k_x := h.elK_x
    k_y := h.elK_y
    d_sq := h.elD_sq
    d_outer := h.elD_outer
    card_T := h.card_closure_elT
    card_centralizer_k := h.card_centralizer_elK
    card_fixed_k := h.card_fixed_elK
    g₁_inner := h.elG1_inner
    g₂_inner := h.elG2_inner
    g₁_pow := h.elG1_pow
    g₁_z := h.elG1_z
    g₁_y := h.elG1_y
    g₁_k := h.elG1_k
    g₂_pow := h.elG2_pow
    g₂_z := h.elG2_z
    g₂_w := h.elG2_w
    g₂_zk := h.elG2_zk
    k_fixed := h.elK_fixed
    zk_fixed := h.elZK_fixed }⟩

end CFSG.OddStandard.SmallF3.L33
