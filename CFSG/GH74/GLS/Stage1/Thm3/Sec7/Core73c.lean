module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Core73

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.C73

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec7

variable {G : Type*} [Group G]

theorem data_of_quat [Finite G] {X W : Subgroup G} {z : G} (hX2 : IsPGroup 2 ↥X) (hWX : W ≤ X)
    (hi : W.relIndex X = 2) (hW8 : 8 ≤ Nat.card ↥W) (hz : z ∈ X) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hq : ∃ N : ℕ, ∃ _ : NeZero N, Nonempty (↥X ≃* QuaternionGroup N)) :
    ∃ (a b : G) (M : ℕ), Q.QG a b M ∧ a ∈ X ∧ b ∈ X ∧
      (∀ x ∈ X, ∃ k : ℕ, x = a ^ k ∨ x = a ^ k * b) ∧ z = a ^ M ∧ 4 ∣ M ∧ 4 ≤ M ∧
      Nat.card ↥X = 4 * M := by
  obtain ⟨N, hNZ, ⟨e⟩⟩ := hq
  obtain ⟨a, b, haX, hbX, hQG, hgen⟩ := Q.quat_gens e
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 hNZ.out
  have hzaN : z = a ^ N := hQG.eq_aN_of_involution hN1 hgen hz hz2 hz1
  have h16 : 16 ≤ Nat.card ↥X := by
    have := A.card_eq_two_mul_of_relIndex_two hWX hi
    omega
  have h4 : 4 ∣ N := A.four_dvd_of_card hX2 e h16
  exact ⟨a, b, N, hQG, haX, hbX, hgen, hzaN, h4, Nat.le_of_dvd (Nat.pos_of_ne_zero hNZ.out) h4,
    A.card_quat e⟩

theorem not_isCyclic_of_quat {X : Subgroup G}
    (hq : ∃ N : ℕ, ∃ _ : NeZero N, Nonempty (↥X ≃* QuaternionGroup N)) (h8 : 8 ≤ Nat.card ↥X) :
    ¬ IsCyclic ↥X := by
  obtain ⟨N, hNZ, ⟨e⟩⟩ := hq
  obtain ⟨a, b, haX, hbX, hQG, -⟩ := Q.quat_gens e
  have := A.card_quat e
  exact hQG.not_isCyclic (by omega) haX hbX

theorem center_map_eq {X : Subgroup G} {a b z : G} {N : ℕ} (h : Q.QG a b N) (hN : 2 ≤ N)
    (haX : a ∈ X) (hbX : b ∈ X) (hgen : ∀ x ∈ X, ∃ k : ℕ, x = a ^ k ∨ x = a ^ k * b)
    (hz : z = a ^ N) : (center ↥X).map X.subtype = zpowers z := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hyc : ∀ w ∈ X, (y : G) * w = w * y := by
      intro w hw
      have := (Subgroup.mem_center_iff.1 hy) ⟨w, hw⟩
      exact (congrArg Subtype.val this).symm
    rcases h.center_cases hN haX hbX hgen y.2 hyc with h1 | h1
    · show (y : G) ∈ zpowers z
      rw [h1]; exact one_mem _
    · show (y : G) ∈ zpowers z
      rw [h1, ← hz]; exact mem_zpowers z
  · rw [zpowers_le]
    refine ⟨⟨z, by rw [hz]; exact X.pow_mem haX N⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
    intro g
    apply Subtype.ext
    show (g : G) * z = z * g
    obtain ⟨k, hk | hk⟩ := hgen g g.2
    · rw [hk, hz]; exact ((Commute.refl a).pow_pow k N).eq
    · rw [hk, hz]
      calc a ^ k * b * a ^ N = a ^ k * (b * a ^ N) := by group
        _ = a ^ k * (a ^ N * b) := by rw [h.b_aN]
        _ = a ^ N * (a ^ k * b) := by
          rw [← mul_assoc, ← mul_assoc, ((Commute.refl a).pow_pow k N).eq]

theorem comm_aux {x y z : G} (hz : z * z = 1) (hxx : x * x = z) (hzy : z * y = y * z)
    (h : y * x * y⁻¹ = x⁻¹) : y * x = x * y * z := by
  have hxi : x⁻¹ = x * z := by
    have : x * (x * z) = 1 := by rw [← mul_assoc, hxx, hz]
    exact inv_eq_of_mul_eq_one_right this
  have h1 : y * x = x⁻¹ * y := by
    calc y * x = (y * x * y⁻¹) * y := by group
      _ = x⁻¹ * y := by rw [h]
  rw [h1, hxi]
  calc x * z * y = x * (z * y) := by group
    _ = x * (y * z) := by rw [hzy]
    _ = x * y * z := by group

theorem sq_not_mem_zpowers {z w : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hw : w * w = z) :
    w ∉ zpowers z := by
  intro h
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
  rcases B.zpow_of_sq_eq_one hz2 k with h1 | h1
  · rw [← hk, h1] at hw
    exact hz1 (by simpa using hw.symm)
  · rw [← hk, h1] at hw
    rw [hz2] at hw
    exact hz1 hw.symm

namespace Ctx73

variable {z t : G} {S P₁ P₂ Q₁ Q₂ S₁ : Subgroup G} (c : Ctx73 z t S P₁ P₂ Q₁ Q₂ S₁)

include c

theorem exists_g [Finite G] (Y : Subgroup G) (hYS : Y ≤ S) (hY2 : Y.relIndex S = 2)
    (hPY : P₁ ⊔ P₂ ≤ Y) {v₂ : G} (hv₂ : v₂ ∈ Q₁) (hv₂P : v₂ ∉ P₂) (hv₂sq : v₂ * v₂ = z)
    (hv₂Y : v₂ ∉ Y)
    (hnm : ∀ y ∈ Y, (y ∈ P₁ ⊔ Q₁ → y ∈ P₂ ⊔ Q₂) ∧ (y ∈ P₂ ⊔ Q₂ → y ∈ P₁ ⊔ Q₁))
    {v₁ : G} (hv₁ : v₁ ∈ P₁) (hv₁sq : v₁ * v₁ = z) :
    ∃ g : G, (∀ x ∈ S, x * (v₁ * v₂) = (v₁ * v₂) * x → g⁻¹ * x * g ∈ S) ∧
      g⁻¹ * z * g ∉ P₁ ⊔ P₂ := by
  have hv₂S : v₂ ∈ S := c.S₁S (c.Q₁S₁ hv₂)
  have hv₁S : v₁ ∈ S := c.P₁S hv₁
  have hvS : v₁ * v₂ ∈ S := S.mul_mem hv₁S hv₂S
  have hvY : v₁ * v₂ ∉ Y := by
    intro h
    apply hv₂Y
    have := Y.mul_mem (Y.inv_mem (hPY (mem_sup_left hv₁))) h
    simpa using this
  have hcomm : v₂ * v₁ = v₁ * v₂ := c.Q₁P₁ v₂ hv₂ v₁ hv₁
  have hv2 : (v₁ * v₂) * (v₁ * v₂) = 1 := by
    calc v₁ * v₂ * (v₁ * v₂) = v₁ * (v₂ * v₁) * v₂ := by group
      _ = v₁ * (v₁ * v₂) * v₂ := by rw [hcomm]
      _ = (v₁ * v₁) * (v₂ * v₂) := by group
      _ = 1 := by rw [hv₁sq, hv₂sq]; exact c.z_sq
  obtain ⟨g, hgY, hgC⟩ := c.tr Y (v₁ * v₂) hYS hY2 hvS hvY hv2
  refine ⟨g, hgC, ?_⟩
  have hz1 : g⁻¹ * z * g ≠ z := by
    intro hgz
    have hv : v₁ * v₂ ∈ P₁ ⊔ Q₁ := (P₁ ⊔ Q₁).mul_mem (mem_sup_left hv₁) (mem_sup_right hv₂)
    have hvn : v₁ * v₂ ∉ P₂ ⊔ Q₂ := by
      intro h
      have h1 : v₂ ∈ P₂ ⊔ Q₂ := by
        have e : v₂ = v₁⁻¹ * (v₁ * v₂) := by group
        rw [e]
        exact (P₂ ⊔ Q₂).mul_mem ((P₂ ⊔ Q₂).inv_mem (mem_sup_right (c.P₁Q₂ hv₁))) h
      exact hv₂P (c.Q₁_inf_PQ₂ ⟨h1, hv₂⟩)
    rcases c.mix _ hv hvn g hgz (hYS hgY) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 ((hnm _ hgY).1 h1)
    · exact h2 ((hnm _ hgY).2 h1)
  intro h
  exact hz1 (c.nf _ h (isConj_iff.2 ⟨g⁻¹, by simp⟩))

theorem pass [Finite G] {T : Subgroup G} {w g v : G} (hTcyc : IsCyclic ↥T) (hTS : T ≤ S)
    (hzT : z ∈ T) (hT3 : 3 ≤ Nat.card ↥T) (hwS : w ∈ S) (hw2 : w * w = 1)
    (hwinv : ∀ x ∈ T, w * x * w⁻¹ = x⁻¹) (hwT : w ∉ T) (hvT : ∀ x ∈ T, x * v = v * x)
    (hvw : w * v = v * w) (hg : ∀ x ∈ S, x * v = v * x → g⁻¹ * x * g ∈ S)
    (hzg : g⁻¹ * z * g ∉ P₁ ⊔ P₂) :
    2 * Nat.card ↥T ≤ (P₁ ⊔ P₂).relIndex S ∧ Nat.card ↥(T ⊔ zpowers w) = 2 * Nat.card ↥T ∧
      (∀ x ∈ T ⊔ zpowers w, g⁻¹ * x * g ∈ P₁ ⊔ P₂ → x = 1) ∧
      (∀ x ∈ T ⊔ zpowers w, g⁻¹ * x * g ∈ S) := by
  have hDle : T ⊔ zpowers w ≤ S ⊓ centralizer ({v} : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      exact ⟨hTS hx, Subgroup.mem_centralizer_singleton_iff.2 (hvT x hx)⟩
    · rw [zpowers_le]
      exact ⟨hwS, Subgroup.mem_centralizer_singleton_iff.2 hvw⟩
  have hDg : ∀ x ∈ T ⊔ zpowers w, g⁻¹ * x * g ∈ S := by
    intro x hx
    obtain ⟨hxS, hxc⟩ := hDle hx
    exact hg x hxS (Subgroup.mem_centralizer_singleton_iff.1 hxc)
  obtain ⟨htriv, hcard⟩ :=
    B.core73D c.PnS hTcyc (c.S2.to_le hTS) hzT c.z_sq c.z_ne hT3 hw2 hwinv hDg hzg
  have hwn : zpowers w ≤ normalizer (T : Set G) := by
    rw [zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; rw [hwinv x hx]; exact T.inv_mem hx
    · intro hx
      have hu := hwinv _ hx
      have : w * (w * x * w⁻¹) * w⁻¹ = x := by
        have h1 : w⁻¹ * w⁻¹ = 1 := by rw [← mul_inv_rev, hw2, inv_one]
        calc w * (w * x * w⁻¹) * w⁻¹ = (w * w) * x * (w⁻¹ * w⁻¹) := by group
          _ = x := by rw [hw2, h1]; group
      rw [this] at hu
      rw [hu]; exact T.inv_mem hx
  have h1 := A.card_sup_mul_card_inf hwn
  have hw1 : w ≠ 1 := fun h => hwT (h ▸ T.one_mem)
  have hord : orderOf w = 2 := orderOf_eq_prime (by simpa [pow_two] using hw2) hw1
  have hcw : Nat.card ↥(zpowers w) = 2 := by rw [Nat.card_zpowers, hord]
  have hbot : T ⊓ zpowers w = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxw⟩
    rw [Subgroup.mem_bot]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hxw
    rcases B.zpow_of_sq_eq_one hw2 k with h | h
    · exact h
    · exfalso; apply hwT; rw [← h]; exact hxT
  rw [hbot, Subgroup.card_bot, hcw] at h1
  have hc2 : Nat.card ↥(T ⊔ zpowers w) = 2 * Nat.card ↥T := by omega
  refine ⟨?_, hc2, htriv, hDg⟩
  rw [← hc2]
  exact hcard

end Ctx73

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.C73
