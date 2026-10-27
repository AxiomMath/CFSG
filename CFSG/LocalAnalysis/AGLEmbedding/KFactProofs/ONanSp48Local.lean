module

public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Grp

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.Open

structure Sp48Local (T A E T0 : Subgroup Hh) (t1 t2 w s f : Hh) : Prop where
  card_T : Nat.card T = 3 ^ 5
  T0_eq : T0 = T ⊓ (SemidirectProduct.rightHom (N := Sp8) (G := Multiplicative (ZMod 3))
    (φ := phi)).ker
  card_T0 : Nat.card T0 = 3 ^ 4
  E_eq : E = centerOf T
  card_E : Nat.card E = 3 ^ 2
  E_pow : ∀ z ∈ E, z ^ 3 = 1
  A_le : A ≤ T
  A_pow : ∀ a ∈ A, a ^ 3 = 1
  A_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  card_A : Nat.card A = 3 ^ 3
  E_le_A : E ≤ A
  t1_mem : t1 ∈ T0
  t2_mem : t2 ∈ T0
  f_mem : f ∈ T
  order_t1 : orderOf t1 = 9
  order_t2 : orderOf t2 = 9
  comm_t : t1 * t2 = t2 * t1
  inf_t : Subgroup.zpowers t1 ⊓ Subgroup.zpowers t2 = ⊥
  orbit : ∀ a ∈ A, a ∉ E → ∀ W : Fin 3 → Subgroup Hh,
    ∃ u ∈ T0, ∀ i, (Subgroup.zpowers a).map (MulAut.conj u).toMonoidHom ≠ W i
  lattice : ∀ U : Subgroup Hh, E ≤ U → U ≤ T →
    (∀ b ∈ ({t1, t2, w, s, f} : Set Hh), ∀ x ∈ U, b * x * b⁻¹ ∈ U) →
      U = E ∨ U = A ∨ U = T0 ∨ U = T
  norm_T : ∀ b ∈ ({t1, t2, w, s, f} : Set Hh), ∀ x ∈ T, b * x * b⁻¹ ∈ T
  norm_E : ∀ b ∈ ({t1, t2, w, s, f} : Set Hh), ∀ x ∈ E, b * x * b⁻¹ ∈ E
  rank : ∀ F : Subgroup Hh, F ≤ T0 → IsElemAbelian 3 F → Nat.card F ≤ 9

end CFSG.AGLEmbedding.KFactProofs.Sp48
