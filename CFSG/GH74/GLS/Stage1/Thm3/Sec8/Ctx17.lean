module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx10
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx11

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem u_mem_V₂V₁ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∃ w₁ ∈ Vof S K₂ W₁, ∃ w₂ ∈ Vof S K₁ W₂, u = w₁ * w₂ :=
  Basic.decomp_of_involution_mem_sup (z := z) (u := u) (W₁ := W₁) (W₂ := W₂)
    (V₁ := Vof S K₁ W₂) (V₂ := Vof S K₂ W₁) hs.z_sq hs.W₁_max.2.1 hs.W₂_max.2.1
    inf_le_left inf_le_left (hs.V₁_pgroup hII) (hs.V₂_pgroup hII) (hs.four_le_V₁ hII hq)
    (hs.four_le_V₂ hII hq)
    (fun b hb a ha => hs.W₁_norm b ((hs.Q₂_le_S1 hII) (hs.W₂_le_Q₂ hb)) a ha)
    (fun a ha b hb => hs.W₂_norm a ((hs.Q₁_le_S1) (hs.W₁_le_Q₁ ha)) b hb)
    (fun x hx1 hx2 => by
      have hx : x ∈ Qof S K₁ ⊓ Qof S K₂ := ⟨hs.W₁_le_Q₁ hx1, hs.W₂_le_Q₂ hx2⟩
      rw [hs.Q_inf_Q hII] at hx
      exact (M.mem_zpowers_of_sq hs.z_sq).1 hx)
    (hs.U_le hs.u_mem) (hs.four_sq u hs.u_mem)

theorem u_decomp (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∃ v₁ ∈ Vof S K₁ W₂, ∃ v₂ ∈ Vof S K₂ W₁, u = v₁ * v₂ ∧ v₁ * v₁ = z ∧ v₂ * v₂ = z := by
  have hu : u ∈ Vof S K₁ W₂ ⊔ Vof S K₂ W₁ := by
    obtain ⟨w₁, hw₁, w₂, hw₂, huw⟩ := hs.u_mem_V₂V₁ hII hq
    rw [huw, sup_comm]
    exact Subgroup.mul_mem_sup hw₁ hw₂
  have hcomm : ∀ a ∈ Vof S K₁ W₂, ∀ b ∈ Vof S K₂ W₁, a * b = b * a :=
    fun a ha b hb => hs.P_comm hII a ha.2 b hb.2
  obtain ⟨v₁, hv₁, v₂, hv₂, huv⟩ := Basic.mem_sup_of_commute' hcomm hu
  have hu2 : u * u = 1 := hs.four_sq u hs.u_mem
  have hc : v₁ * v₂ = v₂ * v₁ := hs.P_comm hII v₁ hv₁.2 v₂ hv₂.2
  have h1 : (v₁ * v₁) * (v₂ * v₂) = 1 := by
    calc (v₁ * v₁) * (v₂ * v₂) = v₁ * (v₁ * v₂) * v₂ := by group
      _ = v₁ * (v₂ * v₁) * v₂ := by rw [hc]
      _ = (v₁ * v₂) * (v₁ * v₂) := by group
      _ = u * u := by rw [← huv]
      _ = 1 := hu2
  have hv₁sq : v₁ * v₁ ∈ Pof S K₁ ⊓ Pof S K₂ := by
    have h2 : v₁ * v₁ ∈ Pof S K₂ := by
      have : v₁ * v₁ = (v₂ * v₂)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact inv_mem (mul_mem hv₂.2 hv₂.2)
    exact Subgroup.mem_inf.2 ⟨mul_mem hv₁.2 hv₁.2, h2⟩
  rw [hs.P_inf hII] at hv₁sq
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hs.z_sq
  rcases (M.mem_zpowers_of_sq hs.z_sq).1 hv₁sq with h0 | hz
  · exfalso
    have hv₂sq : v₂ * v₂ = 1 := by rw [h0, one_mul] at h1; exact h1
    have hv₁' : v₁ = 1 ∨ v₁ = z := (hs.gq_P hII hq (Or.inl rfl)).uniq v₁ hv₁.2 h0
    have hv₂' : v₂ = 1 ∨ v₂ = z := (hs.gq_P hII hq (Or.inr rfl)).uniq v₂ hv₂.2 hv₂sq
    apply hs.u_ne
    rw [huv]
    rcases hv₁' with h₁ | h₁ <;> rcases hv₂' with h₂ | h₂ <;> rw [h₁, h₂]
    · simp
    · simp [Subgroup.mem_zpowers]
    · simp [Subgroup.mem_zpowers]
    · rw [hs.z_sq]; exact one_mem _
  · refine ⟨v₁, hv₁, v₂, hv₂, huv, hz, ?_⟩
    rw [hz] at h1
    have := eq_inv_of_mul_eq_one_right h1
    rw [this, hz']

theorem exists_y₁ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    ∃ y₁ ∈ Pof S K₁, y₁ * y₁ = z ∧ (∀ c ∈ Vof S K₁ W₂, y₁ * c * y₁⁻¹ = c⁻¹) ∧
      y₁ ∉ Vof S K₁ W₂ := by
  have hGQ := hs.gq_P hII hq (Or.inl rfl)
  have hV := hs.card_V₁ hII hq
  have hjP : Nat.card ↥(Pof S K₁) = 2 ^ (k + 1) := by rw [← hV, hk]; ring
  have h4 := hs.four_le_V₁ hII hq
  obtain ⟨y₁, hy₁P, hy₁V⟩ : ∃ y₁ ∈ Pof S K₁, y₁ ∉ Vof S K₁ W₂ := by
    by_contra hcon
    push Not at hcon
    have hle : Pof S K₁ ≤ Vof S K₁ W₂ := hcon
    have := Subgroup.card_le_of_le hle
    have hpos : 0 < Nat.card ↥(Vof S K₁ W₂) := Nat.card_pos
    omega
  obtain ⟨h1, h2⟩ := hGQ.outside_cyclic hjP (inf_le_right : Vof S K₁ W₂ ≤ Pof S K₁) hs.V₁_cyclic hV
    h4 hy₁P hy₁V
  exact ⟨y₁, hy₁P, h1, h2, hy₁V⟩

theorem exists_y₂ (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    ∃ y₂ ∈ Pof S K₂, y₂ * y₂ = z ∧ (∀ c ∈ Vof S K₂ W₁, y₂ * c * y₂⁻¹ = c⁻¹) ∧
      y₂ ∉ Vof S K₂ W₁ := by
  have hGQ := hs.gq_P hII hq (Or.inr rfl)
  have hV := hs.card_V₂ hII hq
  have hV₂ := hs.V₂_card_eq hII hq hrec hk
  have hjP : Nat.card ↥(Pof S K₂) = 2 ^ (k + 1) := by rw [← hV, hV₂]; ring
  have h4 := hs.four_le_V₂ hII hq
  obtain ⟨y₂, hy₂P, hy₂V⟩ : ∃ y₂ ∈ Pof S K₂, y₂ ∉ Vof S K₂ W₁ := by
    by_contra hcon
    push Not at hcon
    have hle : Pof S K₂ ≤ Vof S K₂ W₁ := hcon
    have := Subgroup.card_le_of_le hle
    have hpos : 0 < Nat.card ↥(Vof S K₂ W₁) := Nat.card_pos
    omega
  obtain ⟨h1, h2⟩ := hGQ.outside_cyclic hjP (inf_le_right : Vof S K₂ W₁ ≤ Pof S K₂) hs.V₂_cyclic hV
    h4 hy₂P hy₂V
  exact ⟨y₂, hy₂P, h1, h2, hy₂V⟩

theorem y₁_conj_u (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y₁ : G}
    (hy₁P : y₁ ∈ Pof S K₁) (hy₁inv : ∀ c ∈ Vof S K₁ W₂, y₁ * c * y₁⁻¹ = c⁻¹) :
    y₁ * u * y₁⁻¹ = u * z := by
  obtain ⟨v₁, hv₁, v₂, hv₂, huv, h1, h2⟩ := hs.u_decomp hII hq
  have hy₁v₂ : y₁ * v₂ * y₁⁻¹ = v₂ := by
    rw [hs.P_comm hII y₁ hy₁P v₂ hv₂.2]; group
  have hv₂S : v₂ ∈ S := hv₂.2.1
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hs.z_sq
  have hvz : v₁⁻¹ * z = v₁ := by rw [← h1]; group
  have hv₁inv : v₁⁻¹ = v₁ * z := by
    have := eq_mul_inv_of_mul_eq hvz
    rw [this, hz']
  rw [huv]
  calc y₁ * (v₁ * v₂) * y₁⁻¹ = (y₁ * v₁ * y₁⁻¹) * (y₁ * v₂ * y₁⁻¹) := by group
    _ = v₁⁻¹ * v₂ := by rw [hy₁inv v₁ hv₁, hy₁v₂]
    _ = (v₁ * z) * v₂ := by rw [hv₁inv]
    _ = (v₁ * v₂) * z := by rw [mul_assoc, hs.z_comm hII hv₂S, ← mul_assoc]

theorem y₂_conj_u (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y₂ : G}
    (hy₂P : y₂ ∈ Pof S K₂) (hy₂inv : ∀ c ∈ Vof S K₂ W₁, y₂ * c * y₂⁻¹ = c⁻¹) :
    y₂ * u * y₂⁻¹ = u * z := by
  obtain ⟨v₁, hv₁, v₂, hv₂, huv, h1, h2⟩ := hs.u_decomp hII hq
  have hy₂v₁ : y₂ * v₁ * y₂⁻¹ = v₁ := by
    rw [(hs.P_comm hII v₁ hv₁.2 y₂ hy₂P).symm]; group
  have hv₁S : v₁ ∈ S := hv₁.2.1
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hs.z_sq
  have hvz : v₂⁻¹ * z = v₂ := by rw [← h2]; group
  have hv₂inv : v₂⁻¹ = v₂ * z := by
    have := eq_mul_inv_of_mul_eq hvz
    rw [this, hz']
  rw [huv]
  calc y₂ * (v₁ * v₂) * y₂⁻¹ = (y₂ * v₁ * y₂⁻¹) * (y₂ * v₂ * y₂⁻¹) := by group
    _ = v₁ * v₂⁻¹ := by rw [hy₂inv v₂ hv₂, hy₂v₁]
    _ = v₁ * (v₂ * z) := by rw [hv₂inv]
    _ = (v₁ * v₂) * z := by rw [← mul_assoc]

theorem z₁_cases (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    h⁻¹ * z * h = u ∨ h⁻¹ * z * h = u * z := by
  have hz'U : h⁻¹ * z * h ∈ U := hs.hz_inv_mem_U
  have hz'1 : h⁻¹ * z * h ≠ 1 := by
    intro h1
    apply hs.z_ne
    have e : z = h * (h⁻¹ * z * h) * h⁻¹ := by group
    rw [e, h1]; group
  rcases hs.U_elems _ hz'U with h1 | h1 | h1 | h1
  · exact absurd h1 hz'1
  · exact absurd h1 hs.h_move
  · exact Or.inl h1
  · exact Or.inr h1

theorem conj_z₁ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y : G} (hyS : y ∈ S)
    (hy : y * u * y⁻¹ = u * z) : y * (h⁻¹ * z * h) * y⁻¹ = (h⁻¹ * z * h) * z := by
  have hyz : y * z * y⁻¹ = z := by
    rw [← hs.z_comm hII hyS]; group
  rcases hs.z₁_cases hII with h1 | h1
  · rw [h1]; exact hy
  · rw [h1]
    calc y * (u * z) * y⁻¹ = (y * u * y⁻¹) * (y * z * y⁻¹) := by group
      _ = (u * z) * z := by rw [hy, hyz]

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
