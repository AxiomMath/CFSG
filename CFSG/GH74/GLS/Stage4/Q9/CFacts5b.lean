module

public import CFSG.GH74.GLS.Stage4.Q9.CFacts5a3
public import CFSG.GH74.GLS.Stage4.Q9.Sylow5

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

namespace Q9Setting

variable {G : Type} [Group G] [Finite G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁]
  [Field F₂] (S : Q9Setting G z K₁ K₂ F₁ F₂)

include S

omit [Finite G] in
theorem as_normalizes : ∀ h ∈ S.Hs, S.as * h * S.as⁻¹ ∈ S.Hs := fun h hh =>
  (Subgroup.mem_normalizer_iff.mp S.as_mem h).mp hh

theorem sylow5 :
    (Nat.card G).factorization 5 = 2 ∧
    (∀ g : G, orderOf g = 5 → ∃ h : G, h * g * h⁻¹ ∈ K₁ ∨ h * g * h⁻¹ ∈ K₂) ∧
    (∀ g : G, (∃ k : ℕ, orderOf g = 5 ^ k) → orderOf g = 1 ∨ orderOf g = 5) := by
  obtain ⟨x₁, hx₁, hx₁H, ho₁⟩ := S.exists_x5
  obtain ⟨x₂, hx₂, hx₂H, ho₂⟩ := S.exists_x5'
  have h1 := card5_and_conj5 S.z_ord K₁ K₂ S.le_centralizer₁ S.le_centralizer₂ S.inter_eq S.normal₁
    S.normal₂ S.comm S.card_C_five S.hK5 x₁ x₂ hx₁ hx₂ ho₁ ho₂ S.Hs hx₁H hx₂H S.Hs_iso S.as S.as_ord
    S.as_normalizes (fun h hh h1 => S.tns S.as S.as_mem S.as_ord h hh h1)
  have h2 := pElement5_order S.z_ord K₁ K₂ S.le_centralizer₁ S.le_centralizer₂ S.inter_eq S.normal₁
    S.normal₂ S.comm S.card_C_five S.hK5 x₁ x₂ hx₁ hx₂ ho₁ ho₂ S.Hs hx₁H hx₂H S.Hs_iso S.as S.as_ord
    S.as_normalizes (fun h hh h1 => S.tns S.as S.as_mem S.as_ord h hh h1)
  exact ⟨h1.1, h1.2, h2⟩

theorem card_centralizer_five_K₁ :
    ∀ x ∈ K₁, orderOf x = 5 →
    Nat.card ↥(centralizer ({x} : Set G)) = 7200 := by
  intro x hx hx5
  obtain ⟨k, hk, hxk⟩ := S.conj_x5_into_Hs x hx hx5
  have hx'K : k * x * k⁻¹ ∈ K₁ := mul_mem (mul_mem hk hx) (inv_mem hk)
  have hx'5 : orderOf (k * x * k⁻¹) = 5 := by rw [orderOf_conj_eq_of_conj, hx5]
  rw [card_centralizer_eq_of_isConj (isConj_iff.mpr ⟨k, rfl⟩ : IsConj x (k * x * k⁻¹))]
  have hle := S.hK5₁ _ hx'K hx'5
  have := S.card_C_inf_centralizer_five _ ⟨hx'K, hxk⟩ hx'5
  rwa [inf_eq_left.mpr hle] at this

theorem card_centralizer_five :
    ∀ r : G, orderOf r = 5 →
    Nat.card ↥(centralizer ({r} : Set G)) = 7200 := by
  intro r hr
  obtain ⟨-, hconj, -⟩ := S.sylow5
  obtain ⟨h, hh⟩ := hconj r hr
  have hx5 : orderOf (h * r * h⁻¹) = 5 := by rw [orderOf_conj_eq_of_conj, hr]
  rw [card_centralizer_eq_of_isConj (isConj_iff.mpr ⟨h, rfl⟩ : IsConj r (h * r * h⁻¹))]
  rcases hh with hh | hh
  · exact S.card_centralizer_five_K₁ _ hh hx5
  · exact S.swap.card_centralizer_five_K₁ _ hh hx5

theorem h27
    : ∀ r : G, orderOf r = 5 → ¬ 27 ∣ Nat.card ↥(centralizer ({r} : Set G)) := by
  intro r hr
  rw [S.card_centralizer_five r hr]
  norm_num

end Q9Setting

end CFSG.GH74.GLS.Stage4.Q9
