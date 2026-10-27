module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx24

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem W_cent_U (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {w : G} (hw : w ∈ Wsub S U) {c : G}
    (hc : c ∈ U) : w * c * w⁻¹ = c := by
  have := (Subgroup.mem_centralizer_iff.1 hw.2) c hc
  rw [← this]; group

theorem A_pow_four (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) {a : G}
    (ha : a ∈ Aof S K₁ W₂ h) : a * a * (a * a) = 1 := by
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hs.A_mem hII hq hrec ha
  have h1 : a₁ ^ 4 = 1 := by
    have := Basic.pow_card_of_mem ha₁
    rw [hk] at this
    norm_num at this
    exact this
  have h2 : a₂ ^ 4 = 1 := by
    have := hs.V_pow hk a₂ ha₂
    norm_num at this
    exact this
  have hc : a₁ * a₂ = a₂ * a₁ :=
    hs.A_comm hII hq hrec _ (Subgroup.mem_sup_left ha₁) _ (Subgroup.mem_sup_right ha₂)
  have hc' : Commute a₁ a₂ := hc
  have h4 : (a₁ * a₂) ^ 4 = 1 := by rw [hc'.mul_pow, h1, h2, one_mul]
  rw [← Basic.pow_four_eq]
  exact h4

theorem eps_mem_U (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) {w : G}
    (hw : w ∈ Wsub S U) {a : G} (ha : a ∈ Aof S K₁ W₂ h) : (w * a * w⁻¹) * a⁻¹ ∈ U := by
  have hp : w * a * w⁻¹ ∈ Aof S K₁ W₂ h := hs.A_normS hII hq hrec hw.1 ha
  have he : (w * a * w⁻¹) * a⁻¹ ∈ Aof S K₁ W₂ h := mul_mem hp (inv_mem ha)
  have ha2U : a * a ∈ U :=
    hs.A_inv_mem_U hII hq hrec (mul_mem ha ha) (hs.A_pow_four hII hq hrec hk ha)
  have hfix : w * (a * a) * w⁻¹ = a * a := hs.W_cent_U hw ha2U
  have hpa : (w * a * w⁻¹) * a⁻¹ = a⁻¹ * (w * a * w⁻¹) := hs.A_comm hII hq hrec _ hp _ (inv_mem ha)
  have hsq : ((w * a * w⁻¹) * a⁻¹) * ((w * a * w⁻¹) * a⁻¹) = 1 := by
    calc ((w * a * w⁻¹) * a⁻¹) * ((w * a * w⁻¹) * a⁻¹)
        = (w * a * w⁻¹) * (a⁻¹ * (w * a * w⁻¹)) * a⁻¹ := by group
      _ = (w * a * w⁻¹) * ((w * a * w⁻¹) * a⁻¹) * a⁻¹ := by rw [← hpa]
      _ = (w * (a * a) * w⁻¹) * (a * a)⁻¹ := by group
      _ = 1 := by rw [hfix]; group
  exact hs.A_inv_mem_U hII hq hrec he hsq

theorem conj2 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) {v v' : G}
    (hv : v ∈ Wsub S U) (hv' : v' ∈ Wsub S U) {a : G} (ha : a ∈ Aof S K₁ W₂ h) :
    (v * v') * a * (v * v')⁻¹ =
      (((v' * a * v'⁻¹) * a⁻¹) * ((v * a * v⁻¹) * a⁻¹)) * a := by
  have hε' := hs.eps_mem_U hII hq hrec hk hv' ha
  calc (v * v') * a * (v * v')⁻¹ = v * ((((v' * a * v'⁻¹) * a⁻¹)) * a) * v⁻¹ := by group
    _ = (v * ((v' * a * v'⁻¹) * a⁻¹) * v⁻¹) * (v * a * v⁻¹) := by group
    _ = ((v' * a * v'⁻¹) * a⁻¹) * (v * a * v⁻¹) := by rw [hs.W_cent_U hv hε']
    _ = (((v' * a * v'⁻¹) * a⁻¹) * ((v * a * v⁻¹) * a⁻¹)) * a := by group

theorem W_sq_mem_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) {w : G}
    (hw : w ∈ Wsub S U) : w * w ∈ Aof S K₁ W₂ h := by
  rw [← hs.cent_eq hII hq hrec]
  refine Subgroup.mem_inf.2 ⟨mul_mem hw.1 hw.1, Subgroup.mem_centralizer_iff.2 (fun a ha => ?_)⟩
  have h1 := hs.conj2 hII hq hrec hk hw hw ha
  have hεU := hs.eps_mem_U hII hq hrec hk hw ha
  have hsq : ((w * a * w⁻¹) * a⁻¹) * ((w * a * w⁻¹) * a⁻¹) = 1 := hs.four_sq _ hεU
  have h2 : (w * w) * a * (w * w)⁻¹ = a := by
    rw [h1, hsq, one_mul]
  calc a * (w * w) = ((w * w) * a * (w * w)⁻¹) * (w * w) := by rw [h2]
    _ = (w * w) * a := by group

theorem W_comm_mem_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) {w w' : G}
    (hw : w ∈ Wsub S U) (hw' : w' ∈ Wsub S U) : w * w' * w⁻¹ * w'⁻¹ ∈ Aof S K₁ W₂ h := by
  rw [← hs.cent_eq hII hq hrec]
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_iff.2 (fun a ha => ?_)⟩
  · exact mul_mem (mul_mem (mul_mem hw.1 hw'.1) (inv_mem hw.1)) (inv_mem hw'.1)
  ·
    have hF : ∀ a' ∈ Aof S K₁ W₂ h, (w * w') * a' * (w * w')⁻¹ = (w' * w) * a' * (w' * w)⁻¹ := by
      intro a' ha'
      have hεw := hs.eps_mem_U hII hq hrec hk hw ha'
      have hεw' := hs.eps_mem_U hII hq hrec hk hw' ha'
      rw [hs.conj2 hII hq hrec hk hw hw' ha', hs.conj2 hII hq hrec hk hw' hw ha',
        hs.four_comm _ hεw' _ hεw]
    set c := w * w' * w⁻¹ * w'⁻¹ with hc
    have hca : c * a * c⁻¹ = a := by
      have hw'w : (w' * w)⁻¹ * a * (w' * w) ∈ Aof S K₁ W₂ h := by
        have := hs.A_normS hII hq hrec (inv_mem (mul_mem hw'.1 hw.1)) ha
        rwa [inv_inv] at this
      have h1 := hF _ hw'w
      calc c * a * c⁻¹ = (w * w') * ((w' * w)⁻¹ * a * (w' * w)) * (w * w')⁻¹ := by
            rw [hc]; group
        _ = (w' * w) * ((w' * w)⁻¹ * a * (w' * w)) * (w' * w)⁻¹ := h1
        _ = a := by group
    calc a * c = (c * a * c⁻¹) * c := by rw [hca]
      _ = c * a := by group

theorem relIndex_W₀_W (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hSne : S ≠ S1 S K₁)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) :
    (Wsub S U ⊓ S1 S K₁).relIndex (Wsub S U) = 2 := by
  obtain ⟨y₁, hy₁P, -, hy₁inv, -⟩ := hs.exists_y₁ hII hq hk
  obtain ⟨w₀, hw₀W, hw₀n⟩ := hs.exists_W_not_S1 hII hq hSne hy₁P hy₁inv
  have hS1S := hs.relIndex_S1_S hSne
  refine Basic.relIndex_eq_two_of_mul (s₀ := w₀) hw₀W (fun h' => hw₀n h'.2) ?_
  intro b hb hbn
  have hbn' : b ∉ S1 S K₁ := fun h' => hbn (Subgroup.mem_inf.2 ⟨hb, h'⟩)
  have hw₀inv : w₀⁻¹ ∉ S1 S K₁ := fun h' => hw₀n (by simpa using inv_mem h')
  have h1 := Basic.mul_inv_mem_of_relIndex_two hS1S hb.1 (inv_mem hw₀W.1) hbn' hw₀inv
  rw [inv_inv] at h1
  exact Subgroup.mem_inf.2 ⟨mul_mem hb hw₀W, h1⟩

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
