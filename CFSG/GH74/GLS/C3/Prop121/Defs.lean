module

public import CFSG.GH74.GLS.C3.Layer2.Config

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup CFSG.GH74.GLS

structure Stage3Base {G : Type} [Group G] (n : ℕ) (x : G) (K Q : Subgroup G) (t u : G) : Prop where
  x_sq : x ^ 2 = 1
  x_ne : x ≠ 1
  x_mem : x ∈ Q
  Q_card : Nat.card Q = 4
  Q_sq : ∀ q ∈ Q, q ^ 2 = 1
  Q_comm : ∀ q ∈ Q, ∀ r ∈ Q, q * r = r * q
  K_alt : Nonempty (K ≃* alternatingGroup (Fin n))
  K_comm_Q : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k
  K_inf_Q : ∀ k ∈ K, k ∈ Q → k = 1
  t_order : orderOf t = 3
  t_norm_Q : ∀ q ∈ Q, t * q * t⁻¹ ∈ Q
  t_comm_K : ∀ k ∈ K, t * k = k * t
  tx_cube : (t * x) ^ 3 = 1
  u_sq : u ^ 2 = 1
  u_comm_x : u * x = x * u
  u_inv_t : u * t * u⁻¹ = t⁻¹
  u_norm_K : ∀ k ∈ K, u * k * u⁻¹ ∈ K
  u_not_KQ : ∀ k ∈ K, ∀ q ∈ Q, u ≠ k * q
  u_nc_Q : ∃ q ∈ Q, u * q ≠ q * u

structure Stage3Loc {G : Type} [Group G] (n : ℕ) (x : G) (K Q : Subgroup G) (t u g : G) : Prop
    extends Stage3Base n x K Q t u where
  g_sq : g ^ 2 = 1
  g_Q : ∀ q ∈ Q, g * q * g⁻¹ ∈ K
  gt_K : g * t * g⁻¹ ∈ K

structure ThreeLocalCore {G : Type} [Group G] (K : Subgroup G) (t u : G) (L : Subgroup G) :
    Prop where
  K_le_L : K ≤ L
  u_norm_L : ∀ l ∈ L, u * l * u⁻¹ ∈ L
  u_not_mem_L : u ∉ L
  L_comm_t : ∀ l ∈ L, l * t = t * l
  C_eq : ∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l
  zpowers_inf_L : ∀ (i : ℤ), t ^ i ∈ L → t ^ i = 1
  N_eq : ∀ w : G, w * t * w⁻¹ = t⁻¹ → ∃ i : ℤ, ∃ l ∈ L, w = t ^ i * l * u

structure ThreeLocal {G : Type} [Group G] (n : ℕ) (K : Subgroup G) (t u g : G) (L : Subgroup G)
    (Θ : ↥(L ⊔ zpowers u) ≃* Equiv.Perm (Fin (n + 1))) : Prop
    extends ThreeLocalCore K t u L where
  alt : ∀ y : ↥(L ⊔ zpowers u), (y : G) ∈ L ↔ Equiv.Perm.sign (Θ y) = 1
  stab : ∀ y : ↥(L ⊔ zpowers u), (y : G) ∈ K ⊔ zpowers u ↔ Θ y 0 = 0
  threeCycle : ∃ h : g * t * g⁻¹ ∈ L ⊔ zpowers u, (Θ ⟨g * t * g⁻¹, h⟩).IsThreeCycle

@[expose] def S_stage3Loc : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G ≤ 4 → ∀ n ∈ ({5, 6, 7} : Finset ℕ),
    ∀ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfig n x K T Q S a →
      IsApproxTo G (alternatingGroup (Fin (n + 4))) → ∃ t u g : G, Stage3Loc n x K Q t u g

@[expose] def S_lemma123 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G ≤ 4 → ∀ n ∈ ({5, 6, 7} : Finset ℕ),
    ∀ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfig n x K T Q S a →
      IsApproxTo G (alternatingGroup (Fin (n + 4))) →
        ∀ t u g : G, Stage3Loc n x K Q t u g →
          ∃ (L : Subgroup G) (Θ : ↥(L ⊔ zpowers u) ≃* Equiv.Perm (Fin (n + 1))),
            ThreeLocal n K t u g L Θ

end CFSG.GH74.GLS.C3.Prop121
