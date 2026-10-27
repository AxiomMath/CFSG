module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx22

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem V₁_inf_V₂_eq (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    Vof S K₁ W₂ ⊓ Vof S K₂ W₁ = zpowers z := by
  apply le_antisymm
  · intro g hg
    have hgP : g ∈ Pof S K₁ ⊓ Pof S K₂ := Subgroup.mem_inf.2 ⟨hg.1.2, hg.2.2⟩
    rw [hs.P_inf hII] at hgP
    exact hgP
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨hs.z_mem_V₁ hII hq hk2 hk, hs.z_mem_V₂ hII hq hrec hk2 hk⟩

theorem V₁V₂_relIndex (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    (Vof S K₁ W₂ ⊔ Vof S K₂ W₁).relIndex (Aof S K₁ W₂ h) = 2 := by
  have hcomm : ∀ a ∈ Vof S K₁ W₂, ∀ b ∈ Vof S K₂ W₁, a * b = b * a :=
    fun a ha b hb => hs.P_comm hII a ha.2 b hb.2
  have h1 := M.card_sup_mul_card_inf (A := Vof S K₁ W₂) (B := Vof S K₂ W₁)
    (M.le_normalizer_of_commute hcomm)
  have hz2 : Nat.card ↥(zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hs.z_sq) hs.z_ne
  rw [hs.V₁_inf_V₂_eq hII hq hrec hk2 hk, hz2, hk, hs.V₂_card_eq hII hq hrec hk] at h1
  have hMA : Vof S K₁ W₂ ⊔ Vof S K₂ W₁ ≤ Aof S K₁ W₂ h :=
    sup_le le_sup_left (hs.V₂_le_A hII hq hrec hk)
  have h2 : Nat.card ↥(Vof S K₁ W₂ ⊔ Vof S K₂ W₁) *
      (Vof S K₁ W₂ ⊔ Vof S K₂ W₁).relIndex (Aof S K₁ W₂ h) = Nat.card ↥(Aof S K₁ W₂ h) :=
    Basic.card_mul_relIndex_of_le hMA
  rw [hs.card_A hII hq hrec hk] at h2
  have hpos : 0 < Nat.card ↥(Vof S K₁ W₂ ⊔ Vof S K₂ W₁) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h2, ← h1])

theorem y_inv_mod_U (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {y : G} (hyS : y ∈ S)
    (hyV₁ : ∀ c ∈ Vof S K₁ W₂, y * c * y⁻¹ = c⁻¹)
    (hyV₂ : ∀ c ∈ Vof S K₂ W₁, y * c * y⁻¹ = c⁻¹) :
    ∀ a ∈ Aof S K₁ W₂ h, (y * a * y⁻¹) * a ∈ U := by
  intro a ha
  have hcomm : ∀ a ∈ Vof S K₁ W₂, ∀ b ∈ Vof S K₂ W₁, a * b = b * a :=
    fun a ha b hb => hs.P_comm hII a ha.2 b hb.2
  have haaM : a * a ∈ Vof S K₁ W₂ ⊔ Vof S K₂ W₁ :=
    Basic.mul_self_mem_of_relIndex_two (hs.V₁V₂_relIndex hII hq hrec hk2 hk) ha
  have hinvM : y * (a * a) * y⁻¹ = (a * a)⁻¹ := by
    obtain ⟨v₁, hv₁, v₂, hv₂, hv⟩ := Basic.mem_sup_of_commute' hcomm haaM
    rw [hv]
    have hc : v₁ * v₂ = v₂ * v₁ := hcomm v₁ hv₁ v₂ hv₂
    calc y * (v₁ * v₂) * y⁻¹ = (y * v₁ * y⁻¹) * (y * v₂ * y⁻¹) := by group
      _ = v₁⁻¹ * v₂⁻¹ := by rw [hyV₁ v₁ hv₁, hyV₂ v₂ hv₂]
      _ = (v₂ * v₁)⁻¹ := by rw [mul_inv_rev]
      _ = (v₁ * v₂)⁻¹ := by rw [hc]
  have hda : y * a * y⁻¹ ∈ Aof S K₁ W₂ h := hs.A_normS hII hq hrec hyS ha
  have hc : a * (y * a * y⁻¹) = (y * a * y⁻¹) * a := hs.A_comm hII hq hrec a ha _ hda
  have hb2 : ((y * a * y⁻¹) * a) * ((y * a * y⁻¹) * a) = 1 := by
    calc ((y * a * y⁻¹) * a) * ((y * a * y⁻¹) * a)
        = (y * a * y⁻¹) * (a * (y * a * y⁻¹)) * a := by group
      _ = (y * a * y⁻¹) * ((y * a * y⁻¹) * a) * a := by rw [hc]
      _ = (y * (a * a) * y⁻¹) * (a * a) := by group
      _ = (a * a)⁻¹ * (a * a) := by rw [hinvM]
      _ = 1 := by group
  exact hs.A_inv_mem_U hII hq hrec (mul_mem hda ha) hb2

theorem y'_inv_mod_U (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {y : G}
    (hy : ∀ a ∈ Aof S K₁ W₂ h, (y * a * y⁻¹) * a ∈ U) :
    ∀ a ∈ Aof S K₁ W₂ h, ((h⁻¹ * y * h) * a * (h⁻¹ * y * h)⁻¹) * a ∈ U := by
  intro a ha
  have ha₁ : h * a * h⁻¹ ∈ Aof S K₁ W₂ h := (hs.A_conj hII hq hrec hk ha).1
  have h2 := hs.U_conj_h (hy _ ha₁)
  have e : ((h⁻¹ * y * h) * a * (h⁻¹ * y * h)⁻¹) * a =
      h⁻¹ * ((y * (h * a * h⁻¹) * y⁻¹) * (h * a * h⁻¹)) * h := by group
  rw [e]
  exact h2

theorem g_mod_U (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {y : G}
    (hyW : y ∈ Wsub S U) (hy : ∀ a ∈ Aof S K₁ W₂ h, (y * a * y⁻¹) * a ∈ U) :
    ∀ a ∈ Aof S K₁ W₂ h, ∃ c ∈ U,
      ((h⁻¹ * y * h) * y) * a * ((h⁻¹ * y * h) * y)⁻¹ = a * c := by
  intro a ha
  have hy' := hs.y'_inv_mod_U hII hq hrec hk hy
  have hy'W : h⁻¹ * y * h ∈ Wsub S U := hs.W_conj_h hyW
  have hb₂U : (y * a * y⁻¹) * a ∈ U := hy a ha
  have hb₃U : ((h⁻¹ * y * h) * a * (h⁻¹ * y * h)⁻¹) * a ∈ U := hy' a ha
  have hcomm₂ : (h⁻¹ * y * h) * ((y * a * y⁻¹) * a) = ((y * a * y⁻¹) * a) * (h⁻¹ * y * h) :=
    ((Subgroup.mem_centralizer_iff.1 hy'W.2) _ hb₂U).symm
  have hda : y * a * y⁻¹ ∈ Aof S K₁ W₂ h := hs.A_normS hII hq hrec hyW.1 ha
  have hcomm₃ : a * ((y * a * y⁻¹) * a) = ((y * a * y⁻¹) * a) * a :=
    hs.A_comm hII hq hrec a ha _ (mul_mem hda ha)
  refine ⟨((y * a * y⁻¹) * a) * (((h⁻¹ * y * h) * a * (h⁻¹ * y * h)⁻¹) * a)⁻¹,
    mul_mem hb₂U (inv_mem hb₃U), ?_⟩
  generalize h⁻¹ * y * h = p at *
  generalize hb₂ : (y * a * y⁻¹) * a = b₂ at *
  generalize hb₃ : (p * a * p⁻¹) * a = b₃ at *
  have e2 : y * a * y⁻¹ = b₂ * a⁻¹ := by rw [← hb₂]; group
  have e3 : p * a * p⁻¹ = b₃ * a⁻¹ := by rw [← hb₃]; group
  have e4 : p * b₂ * p⁻¹ = b₂ := by rw [hcomm₂]; group
  calc (p * y) * a * (p * y)⁻¹ = p * (y * a * y⁻¹) * p⁻¹ := by group
    _ = p * (b₂ * a⁻¹) * p⁻¹ := by rw [e2]
    _ = (p * b₂ * p⁻¹) * (p * a * p⁻¹)⁻¹ := by group
    _ = b₂ * (b₃ * a⁻¹)⁻¹ := by rw [e4, e3]
    _ = (b₂ * a) * b₃⁻¹ := by group
    _ = (a * b₂) * b₃⁻¹ := by rw [← hcomm₃]
    _ = a * (b₂ * b₃⁻¹) := by group

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
