module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Main1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Hom

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

theorem pow_three_of_orderOf {y : Y} (hy : orderOf y = 3) : y ^ 3 = 1 := by
  have h := pow_orderOf_eq_one y
  rwa [hy] at h

theorem le_B_CBK (K B : Subgroup Y) : CBK K B ≤ B := inf_le_left

theorem cent_CBK {B K : Subgroup Y} {x β : Y} (hB : IsElemAbelian 3 B) (hxB : x ∈ B)
    (hβ : β ∈ CBK K B) :
    Cent K β ∧ Cent (cj x K) β ∧ Cent (cj (x * x) K) β := by
  obtain ⟨hβB, hβC⟩ := hβ
  have hK : Cent K β := fun l hl => Subgroup.mem_centralizer_iff.1 hβC l hl
  have hβx : β * x = x * β := isElemAbelian_commute hB hβB hxB
  have h2 : Cent (cj x K) β := cent_cj hβx hK
  have h3 : Cent (cj (x * x) K) β := by
    rw [show cj (x * x) K = cj x (cj x K) from cj_mul x x K]
    exact cent_cj hβx h2
  exact ⟨hK, h2, h3⟩

theorem F0_bound [Finite Y] {B K U₀ : Subgroup Y} {x y₀ : Y} (hB : IsElemAbelian 3 B)
    (hxB : x ∈ B)
    (hKK₂ : ElemCommute K (cj x K)) (hKK₃ : ElemCommute K (cj (x * x) K))
    (hy₀K : y₀ ∈ K) (hy₀3 : orderOf y₀ = 3) (hy₀nc : ∃ z ∈ K, z * y₀ ≠ y₀ * z)
    (hU₀K : U₀ ≤ K) (hU₀ne : U₀ ≠ ⊥) (hU₀p : IsPGroup 2 U₀) (hy₀U : cj y₀ U₀ = U₀)
    (hmax : ∀ F : Subgroup Y, IsElemAbelian 3 F →
      (∃ W : Subgroup Y, W ≠ ⊥ ∧ IsPGroup 2 W ∧ F ≤ Subgroup.normalizer (W : Set Y)) →
      Nat.card F ≤ Nat.card B) :
    27 * Nat.card (CBK K B) ≤ Nat.card B := by
  have hy₀3' : y₀ ^ 3 = 1 := pow_three_of_orderOf hy₀3
  have hy₁3 : orderOf (x * y₀ * x⁻¹) = 3 := orderOf_conj3 hy₀3 x
  have hy₂3 : orderOf ((x * x) * y₀ * (x * x)⁻¹) = 3 := orderOf_conj3 hy₀3 (x * x)
  have hnc₁ := noncentral_conj x hy₀nc
  have hnc₂ := noncentral_conj (x * x) hy₀nc
  have hy₁K : x * y₀ * x⁻¹ ∈ cj x K := conj_mem_cj x hy₀K
  have hy₂K : (x * x) * y₀ * (x * x)⁻¹ ∈ cj (x * x) K := conj_mem_cj (x * x) hy₀K
  have f23 : ElemCommute (cj x K) (cj (x * x) K) := commute_K₂_K₃ hKK₂
  have hB₀B : IsElemAbelian 3 (CBK K B) := isElemAbelian_mono hB (le_B_CBK K B)
  have hB₀c : ∀ β ∈ CBK K B, Cent K β ∧ Cent (cj x K) β ∧ Cent (cj (x * x) K) β :=
    fun β hβ => cent_CBK hB hxB hβ
  have hMs := ms_data hy₀K hKK₂ hKK₃
  have hzz : ElemCommute (Subgroup.zpowers (x * y₀ * x⁻¹))
      (Subgroup.zpowers ((x * x) * y₀ * (x * x)⁻¹)) := hMs.1
  have hzE : ElemCommute (Subgroup.zpowers y₀)
      (Subgroup.zpowers (x * y₀ * x⁻¹) ⊔ Subgroup.zpowers ((x * x) * y₀ * (x * x)⁻¹)) := hMs.2
  have hB₀y : ElemCommute (CBK K B) (Subgroup.zpowers y₀) := by
    intro β hβ c hc
    exact ((hB₀c β hβ).1 c (Subgroup.zpowers_le.2 hy₀K hc)).symm
  have hB₀y₁ : ElemCommute (CBK K B) (Subgroup.zpowers (x * y₀ * x⁻¹)) := by
    intro β hβ c hc
    exact ((hB₀c β hβ).2.1 c (Subgroup.zpowers_le.2 hy₁K hc)).symm
  have hB₀y₂ : ElemCommute (CBK K B) (Subgroup.zpowers ((x * x) * y₀ * (x * x)⁻¹)) := by
    intro β hβ c hc
    exact ((hB₀c β hβ).2.2 c (Subgroup.zpowers_le.2 hy₂K hc)).symm
  have hB₀E : ElemCommute (CBK K B) (Subgroup.zpowers y₀ ⊔ (Subgroup.zpowers (x * y₀ * x⁻¹) ⊔
      Subgroup.zpowers ((x * x) * y₀ * (x * x)⁻¹))) :=
    commutes_sup_right hB₀y (commutes_sup_right hB₀y₁ hB₀y₂)
  have hE₀ele : IsElemAbelian 3 (Subgroup.zpowers y₀ ⊔ (Subgroup.zpowers (x * y₀ * x⁻¹) ⊔
      Subgroup.zpowers ((x * x) * y₀ * (x * x)⁻¹))) :=
    isElemAbelian_sup (isElemAbelian_zpowers 3 hy₀3')
      (isElemAbelian_sup (isElemAbelian_zpowers 3 (pow_three_of_orderOf hy₁3))
        (isElemAbelian_zpowers 3 (pow_three_of_orderOf hy₂3)) hzz) hzE
  have hinter : CBK K B ⊓ (Subgroup.zpowers y₀ ⊔ (Subgroup.zpowers (x * y₀ * x⁻¹) ⊔
      Subgroup.zpowers ((x * x) * y₀ * (x * x)⁻¹))) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgB, hgE⟩ := hg
    obtain ⟨h1, h2, h3⟩ := hB₀c g hgB
    rw [Subgroup.mem_bot]
    exact E_eq_one hy₀K hKK₂ hKK₃ hy₀3 hy₀nc hy₁3 hnc₁ hy₂3 hnc₂ hgE h1 h2 h3
  have hcardE := card_E_eq hy₀K hKK₂ hKK₃ hy₀3 hy₀nc hy₁3 hnc₁ hy₂3 hnc₂
  have hcardF : Nat.card ↥(CBK K B ⊔ (Subgroup.zpowers y₀ ⊔ (Subgroup.zpowers (x * y₀ * x⁻¹) ⊔
      Subgroup.zpowers ((x * x) * y₀ * (x * x)⁻¹)))) = Nat.card (CBK K B) * 27 := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := CBK K B)
      (B := Subgroup.zpowers y₀ ⊔ (Subgroup.zpowers (x * y₀ * x⁻¹) ⊔
        Subgroup.zpowers ((x * x) * y₀ * (x * x)⁻¹))) (commutes_normalizer hB₀E)
    rw [hinter, Subgroup.card_bot, mul_one, hcardE] at h
    exact h
  have hU₀W : U₀ ≤ WU x U₀ := le_trans le_sup_left le_sup_left
  have hW_ne : WU x U₀ ≠ ⊥ := by
    intro hW
    apply hU₀ne
    rw [hW] at hU₀W
    exact le_bot_iff.1 hU₀W
  have hU3 : ElemCommute U₀ (cj (x * x) U₀) := elemCommute_of_le hU₀K (cj_mono (x * x) hU₀K) hKK₃
  have hUx : ElemCommute U₀ (cj x U₀) := elemCommute_of_le hU₀K (cj_mono x hU₀K) hKK₂
  have hx3 : ElemCommute (cj x U₀) (cj (x * x) U₀) :=
    elemCommute_of_le (cj_mono x hU₀K) (cj_mono (x * x) hU₀K) f23
  have hW_p : IsPGroup 2 ↥(WU x U₀) :=
    isPGroup_sup (isPGroup_sup hU₀p (isPGroup_cj hU₀p x) hUx) (isPGroup_cj hU₀p (x * x))
      (commutes_sup_left hU3 hx3)
  have hF_norm : CBK K B ⊔ (Subgroup.zpowers y₀ ⊔ (Subgroup.zpowers (x * y₀ * x⁻¹) ⊔
      Subgroup.zpowers ((x * x) * y₀ * (x * x)⁻¹))) ≤
      Subgroup.normalizer ((WU x U₀ : Subgroup Y) : Set Y) := by
    apply sup_le
    · intro β hβ
      exact gen_B0 hB hxB (le_B_CBK K B hβ) (hB₀c β hβ).1 hU₀K
    · apply sup_le
      · exact Subgroup.zpowers_le.2 (gen_y hKK₂ hKK₃ hy₀K hy₀U hU₀K)
      · apply sup_le
        · exact Subgroup.zpowers_le.2 (gen_y1 hKK₂ hKK₃ hy₀K hy₀U hU₀K)
        · exact Subgroup.zpowers_le.2 (gen_y2 hKK₂ hKK₃ hy₀K hy₀U hU₀K)
  have hEF := isElemAbelian_sup hB₀B hE₀ele hB₀E
  have h := hmax _ hEF ⟨WU x U₀, hW_ne, hW_p, hF_norm⟩
  rw [hcardF] at h
  rw [mul_comm]
  exact h

end CFSG.LocalAnalysis.GLTheoremA.I114
