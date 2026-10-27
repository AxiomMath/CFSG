module

public import CFSG.GH74.GLS.LU.Local.FiveL84b
public import CFSG.GH74.GLS.LU.Local.FiveL85b

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L84d

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg2.W_le_normalizer_K1 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    zpowers w₁ ⊔ zpowers (t * w₁ * t⁻¹) ≤ normalizer (K₁ : Set G) := by
  refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer c.b66.w₁_mem))
    (Subgroup.zpowers_le.mpr ?_)
  apply mem_normalizer_of_cjL_eq
  apply cjL_eq_of_comm
  intro a ha
  exact (c.hc.comm a ha _ c.w₂_mem).symm

theorem Cfg2.sup_eq_K2 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {P Q : Subgroup G} (hP : P ≤ K₂)
    (hQ : Q ≤ K₂) (hPc : Nat.card ↥P = 5) (hQc : Nat.card ↥Q = 5) (hne : P ≠ Q) : P ⊔ Q = K₂ := by
  have ht2 : t * t = 1 := c.hs.t_sq
  have hK12 : cjL t K₁ = K₂ := c.hs.t_swap
  have hK21 : cjL t K₂ = K₁ := by rw [← hK12, cjL_cjL, ht2, cjL_one]
  have hP1 : cjL t P ≤ K₁ := by
    have := cjL_mono t hP
    rwa [hK21] at this
  have hQ1 : cjL t Q ≤ K₁ := by
    have := cjL_mono t hQ
    rwa [hK21] at this
  have h := c.sup_eq_K1 hP1 hQ1 (by rw [card_cjL]; exact hPc) (by rw [card_cjL]; exact hQc)
    (fun h => hne ((cjL_inj t).mp h))
  have hback : P ⊔ Q = cjL t (cjL t (P ⊔ Q)) := by rw [cjL_cjL, ht2, cjL_one]
  rw [hback, cjL_sup, h, hK12]

theorem Cfg3.not_cent_Y (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) {A : Subgroup G} (hAz : z ∈ A)
    (hA : ∀ a ∈ A, ∀ y ∈ Y, a * y = y * a) : False := by
  have hy : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Y = ⊥ := eq_bot_iff.mpr fun y hy => by
      have := hall y hy
      rw [Subgroup.mem_bot]; exact this
    have h25 := c.b83.Y_card
    rw [this, Subgroup.card_bot] at h25
    omega
  obtain ⟨y, hyY, hy1⟩ := hy
  have h1 := c.z_inv_Y y hyY
  have h2 : z * y * z⁻¹ = y := by
    calc z * y * z⁻¹ = (y * z) * z⁻¹ := by rw [hA z hAz y hyY]
      _ = y := by group
  have h3 : y = y⁻¹ := h2.symm.trans h1
  have hsq : y * y = 1 := by
    calc y * y = y * y⁻¹ := by rw [← h3]
      _ = 1 := by group
  have h5 : y ^ 5 = 1 := c.b83.Y_ab.2 y hyY
  apply hy1
  calc y = y ^ 5 * (y * y)⁻¹ * (y * y)⁻¹ := by group
    _ = 1 := by rw [h5, hsq]; simp

theorem Cfg3.eq_XX_of_comm_Y (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) {w : G}
    (hw : w ∈ zpowers w₁ ⊔ zpowers (t * w₁ * t⁻¹))
    (hRY : ∀ a ∈ cjL w (XX t X₁), ∀ b ∈ Y, a * b = b * a) : cjL w (XX t X₁) = XX t X₁ := by
  have hwN : w ∈ NN z u := c.W_le_NN hw
  have hXY : ∀ a ∈ XX t X₁, ∀ b ∈ Y, a * b = b * a := c.XX_comm
  have hX1Y : ∀ a ∈ X₁, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    hXY a ((le_sup_left : X₁ ≤ XX t X₁) ha) b hb
  have hX2Y : ∀ a ∈ XB t X₁, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    hXY a ((le_sup_right : XB t X₁ ≤ XX t X₁) ha) b hb
  have hA : cjL w X₁ ≤ K₁ := by
    have h1 : cjL w X₁ ≤ cjL w K₁ := cjL_mono w c.b82.X₁_syl.1
    rwa [cjL_eq_of_mem_normalizer (c.W_le_normalizer_K1 hw)] at h1
  have hB : cjL w (XB t X₁) ≤ K₂ := by
    have h1 : cjL w (XB t X₁) ≤ cjL w K₂ := cjL_mono w c.X2_le_K2
    rwa [cjL_eq_of_mem_normalizer (c.W_le_normalizer_K2 hw)] at h1
  have hAH : HInv H (cjL w X₁) := c.hinv_X1.conj (c.cjL_H hwN)
  have hBH : HInv H (cjL w (XB t X₁)) := c.hinv_X2.conj (c.cjL_H hwN)
  have hAc : Nat.card ↥(cjL w X₁) = 5 := by rw [card_cjL]; exact c.card_X1
  have hBc : Nat.card ↥(cjL w (XB t X₁)) = 5 := by rw [card_cjL]; exact c.card_X2
  have hAY : ∀ a ∈ cjL w X₁, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    hRY a ((le_sup_left : cjL w X₁ ≤ cjL w X₁ ⊔ cjL w (XB t X₁)).trans
      (by rw [XX, cjL_sup]) ha) b hb
  have hBY : ∀ a ∈ cjL w (XB t X₁), ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    hRY a ((le_sup_right : cjL w (XB t X₁) ≤ cjL w X₁ ⊔ cjL w (XB t X₁)).trans
      (by rw [XX, cjL_sup]) ha) b hb
  have hA1 : cjL w X₁ = X₁ := by
    rcases c.invSyl_K1 hA hAc hAH with h | h
    · exact h
    · exfalso
      have hne : X₁ ≠ cjL w₁ X₁ := fun h' => c.w₁_not_normalizes_X1 h'.symm
      have hsup := c.sup_eq_K1 (P := X₁) (Q := cjL w₁ X₁) c.b82.X₁_syl.1
        (by
          have h1 : cjL w₁ X₁ ≤ cjL w₁ K₁ := cjL_mono w₁ c.b82.X₁_syl.1
          rwa [cjL_eq_of_mem_normalizer (Subgroup.le_normalizer c.b66.w₁_mem)] at h1)
        c.card_X1 ((card_cjL w₁ X₁).trans c.card_X1) hne
      apply c.not_cent_Y (A := K₁) c.hc.z_mem₁
      intro a ha b hb
      rw [← hsup] at ha
      have hcl : X₁ ⊔ cjL w₁ X₁ ≤ centralizer ((Y : Subgroup G) : Set G) := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · rw [Subgroup.mem_centralizer_iff]; exact fun y hy => (hX1Y x hx y hy).symm
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [← h] at hx
          exact (hAY x hx y hy).symm
      exact (Subgroup.mem_centralizer_iff.mp (hcl ha) b hb).symm
  have hB1 : cjL w (XB t X₁) = XB t X₁ := by
    rcases c.invSyl_K2 hB hBc hBH with h | h
    · exact h
    · exfalso
      have hw₂K : t * w₁ * t⁻¹ ∈ K₂ := c.w₂_mem
      have hne : XB t X₁ ≠ cjL (t * w₁ * t⁻¹) (XB t X₁) := by
        intro h'
        have hsw : cjL w₁ X₁ = X₁ := by
          have h1 : cjL t (cjL (t * w₁ * t⁻¹) (XB t X₁)) = cjL w₁ X₁ := by
            show cjL t (cjL (t * w₁ * t⁻¹) (cjL t X₁)) = cjL w₁ X₁
            rw [cjL_cjL, cjL_cjL]
            have e : t * (t * w₁ * t⁻¹) * t = (t * t) * w₁ := by group
            rw [e, c.hs.t_sq, one_mul]
          have h2 : cjL t (XB t X₁) = X₁ := by
            show cjL t (cjL t X₁) = X₁
            rw [cjL_cjL, c.hs.t_sq, cjL_one]
          rw [← h1, ← h', h2]
        exact c.w₁_not_normalizes_X1 hsw
      have hsup := c.sup_eq_K2 (P := XB t X₁) (Q := cjL (t * w₁ * t⁻¹) (XB t X₁)) c.X2_le_K2
        (by
          have h1 : cjL (t * w₁ * t⁻¹) (XB t X₁) ≤ cjL (t * w₁ * t⁻¹) K₂ :=
            cjL_mono _ c.X2_le_K2
          rwa [cjL_eq_of_mem_normalizer (Subgroup.le_normalizer hw₂K)] at h1)
        c.card_X2 ((card_cjL _ _).trans c.card_X2) hne
      apply c.not_cent_Y (A := K₂) c.hc.z_mem₂
      intro a ha b hb
      rw [← hsup] at ha
      have hcl : XB t X₁ ⊔ cjL (t * w₁ * t⁻¹) (XB t X₁) ≤ centralizer ((Y : Subgroup G) : Set G) := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · rw [Subgroup.mem_centralizer_iff]; exact fun y hy => (hX2Y x hx y hy).symm
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [← h] at hx
          exact (hBY x hx y hy).symm
      exact (Subgroup.mem_centralizer_iff.mp (hcl ha) b hb).symm
  rw [XX, cjL_sup, hA1]
  show X₁ ⊔ cjL w (XB t X₁) = X₁ ⊔ XB t X₁
  rw [hB1]

end L84d

end CFSG.GH74.GLS.LU.Local.Five
