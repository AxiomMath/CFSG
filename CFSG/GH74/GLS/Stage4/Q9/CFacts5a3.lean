module

public import CFSG.GH74.GLS.Stage4.Q9.CFacts5a2
public import CFSG.GH74.GLS.Stage4.Q9.Key5

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

theorem orderOf_conj_eq_of_conj {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g
    (show SemiconjBy g x (g * x * g⁻¹) by simp [SemiconjBy, mul_assoc])).symm

namespace Q9Setting

variable {G : Type} [Group G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁]
  [Field F₂] (S : Q9Setting G z K₁ K₂ F₁ F₂)

include S

theorem z_ne_t : z ≠ S.t := by
  intro h
  apply S.t_notin
  rw [← h]
  exact mem_sup_left S.z_mem₁

theorem z_comm_t : z * S.t = S.t * z := by
  have := mem_centralizer_singleton_iff.mp S.t_mem
  exact this.symm

variable [Finite G]

theorem key5_Hs
    : ∀ x ∈ K₁ ⊓ S.Hs, orderOf x = 5 → centralizer ({x} : Set G) ≤ centralizer ({z} : Set G) := by
  intro x hxK hx5
  have hxK' := hxK
  obtain ⟨hx, hxH⟩ := hxK
  have hxt : S.t * x = x * S.t := S.t_comm_of_mem_Hs hxH
  have hxz : z * x = x * z := S.z_comm₁ hx
  obtain ⟨h, hh16, hth, hh8, hhx⟩ := S.exists_h16
  obtain ⟨Pb, hPbK, hPb3, hPb9⟩ := S.sylow3_K₂
  have : Finite F₂ := Nat.finite_of_card_ne_zero (by rw [S.card₂]; norm_num)
  exact key5 (z := z) (t := S.t) (x := x) (h := h) S.z_ord S.t_ord S.z_comm_t S.z_ne_t hx5 hxz hxt
    S.one_class S.card_C_prime_dvd S.card_C_five.le S.card_G_three.le hh16 hth hh8 (hhx x hx hxt)
    (S.card_C_inf_centralizer_five_two x hxK' hx5) (S.oddC_x5 x hxK' hx5) K₂
    (fun k hk => (S.comm x hx k hk).symm) S.z_mem₂ (fun k hk => (S.comm z S.z_mem₁ k hk))
    Pb hPbK hPb3 hPb9 S.card₂ S.φ₂ (S.htns_x5 x hxH (fun h1 => by
      have := hx5; rw [h1, orderOf_one] at this; omega))

theorem hK5₁
    : ∀ x ∈ K₁, orderOf x = 5 → centralizer ({x} : Set G) ≤ centralizer ({z} : Set G) := by
  intro x hx hx5
  obtain ⟨k, hk, hxk⟩ := S.conj_x5_into_Hs x hx hx5
  have hx'K : k * x * k⁻¹ ∈ K₁ := mul_mem (mul_mem hk hx) (inv_mem hk)
  have hx'5 : orderOf (k * x * k⁻¹) = 5 := by rw [orderOf_conj_eq_of_conj, hx5]
  have h := S.key5_Hs (k * x * k⁻¹) ⟨hx'K, hxk⟩ hx'5
  intro g hg
  have hgx := mem_centralizer_singleton_iff.mp hg
  have hg' : k * g * k⁻¹ ∈ centralizer ({k * x * k⁻¹} : Set G) := by
    refine mem_centralizer_singleton_iff.mpr ?_
    calc k * g * k⁻¹ * (k * x * k⁻¹) = k * (g * x) * k⁻¹ := by group
      _ = k * (x * g) * k⁻¹ := by rw [hgx]
      _ = k * x * k⁻¹ * (k * g * k⁻¹) := by group
  have hzk : k * z = z * k := (S.comm k hk z S.z_mem₂)
  have := mem_centralizer_singleton_iff.mp (h hg')
  refine mem_centralizer_singleton_iff.mpr ?_
  have hzk' : z = k⁻¹ * z * k := by
    calc z = k⁻¹ * (k * z) := by group
      _ = k⁻¹ * (z * k) := by rw [hzk]
      _ = k⁻¹ * z * k := by group
  calc g * z = k⁻¹ * (k * g * k⁻¹) * k * z := by group
    _ = k⁻¹ * ((k * g * k⁻¹) * z) * k := by
        have : k * z = z * k := hzk
        calc k⁻¹ * (k * g * k⁻¹) * k * z = k⁻¹ * (k * g * k⁻¹) * (k * z) := by group
          _ = k⁻¹ * (k * g * k⁻¹) * (z * k) := by rw [this]
          _ = k⁻¹ * ((k * g * k⁻¹) * z) * k := by group
    _ = k⁻¹ * (z * (k * g * k⁻¹)) * k := by rw [this]
    _ = z * g := by
        calc k⁻¹ * (z * (k * g * k⁻¹)) * k = (k⁻¹ * z * k) * g := by group
          _ = z * g := by rw [← hzk']

theorem hK5₂
    : ∀ x ∈ K₂, orderOf x = 5 → centralizer ({x} : Set G) ≤ centralizer ({z} : Set G) :=
  S.swap.hK5₁

theorem hK5
    : ∀ x : G, (x ∈ K₁ ∨ x ∈ K₂) → orderOf x = 5 →
    centralizer ({x} : Set G) ≤ centralizer ({z} : Set G) ∧
      ∀ e : G, e ∈ centralizer ({x} : Set G) → orderOf e = 2 →
        (∀ c ∈ centralizer ({x} : Set G), e * c = c * e) → e = z := by
  intro x hx hx5
  rcases hx with hx | hx
  · refine ⟨S.hK5₁ x hx hx5, ?_⟩
    intro e he he2 hec
    have heC : e ∈ centralizer ({z} : Set G) := S.hK5₁ x hx hx5 he
    have hK₂x := S.K₂_le_centralizer_of_mem₁ hx
    have : e ∈ K₁ := S.centralizer_K₂_le_K₁ e heC (fun k hk => hec k (hK₂x hk))
    exact S.K₁_involution e this he2
  · refine ⟨S.hK5₂ x hx hx5, ?_⟩
    intro e he he2 hec
    have heC : e ∈ centralizer ({z} : Set G) := S.hK5₂ x hx hx5 he
    have hK₁x : K₁ ≤ centralizer ({x} : Set G) := S.swap.K₂_le_centralizer_of_mem₁ hx
    have : e ∈ K₂ := S.centralizer_K₁_le_K₂ e heC (fun k hk => hec k (hK₁x hk))
    exact S.K₂_involution e this he2

end Q9Setting

end CFSG.GH74.GLS.Stage4.Q9
