module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cCtx

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

namespace Sec11cCnt

variable {z : G} {R T C D Q1 Q2 : Subgroup G} {a x : G}

private theorem sec11_key117_le8k {V W C Q' : Subgroup G} {k : ℕ}
    (hV : Nat.card V ≤ 2 * Nat.card ↥(V ⊓ W))
    (hcount : 2 * Nat.card ↥(V ⊓ W) ≤ Nat.card C * Nat.card Q')
    (hQ' : Nat.card Q' ≤ 8) (hk : Nat.card C ≤ k) :
    Nat.card V ≤ 8 * k :=
  calc Nat.card V ≤ Nat.card C * Nat.card Q' := hV.trans hcount
    _ ≤ k * 8 := Nat.mul_le_mul hk hQ'
    _ = 8 * k := Nat.mul_comm k 8

private theorem sec11_key117_le4k {V W C Q' : Subgroup G} {k : ℕ}
    (hV : Nat.card V ≤ 4 * Nat.card ↥(V ⊓ W))
    (hcount : 2 * Nat.card ↥(V ⊓ W) ≤ Nat.card C * Nat.card Q')
    (hQ' : Nat.card Q' ≤ 4) (hk : Nat.card C ≤ k) :
    Nat.card V ≤ 8 * k := by
  have hstep : Nat.card V ≤ 2 * (2 * Nat.card ↥(V ⊓ W)) := by
    rw [show (4 : ℕ) * Nat.card ↥(V ⊓ W) =
      2 * (2 * Nat.card ↥(V ⊓ W)) by ring] at hV
    exact hV
  have h1 : Nat.card V ≤ 2 * (Nat.card C * Nat.card Q') :=
    hstep.trans (Nat.mul_le_mul_left 2 hcount)
  have h2 : 2 * (Nat.card C * Nat.card Q') ≤ 2 * (k * 4) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul hk hQ')
  calc Nat.card V ≤ 2 * (k * 4) := h1.trans h2
    _ = 8 * k := by ring

theorem caseI [Finite G] (h : Sec11cCnt G z R T C D Q1 Q2 a x) {V : Subgroup G}
    (hVTD : V ≤ T ⊔ D) (hV : IsElemAbelianMod z V) {k : ℕ}
    (hk : Nat.card ↥(D ⊓ (V ⊔ (Q1 ⊔ Q2))) ≤ k) :
    V ≤ D ⊔ (Q1 ⊔ Q2) ∨ Nat.card V ≤ 8 * k := by
  classical
  have hP : Sec11cProj G z D (Q1 ⊔ Q2) V := h.proj (hVTD.trans h.TD_le) hV
  have hWx : ∀ w ∈ D ⊔ (Q1 ⊔ Q2), x * w * x⁻¹ ∈ D ⊔ (Q1 ⊔ Q2) :=
    fun w hw => h.DQ_norm x (h.T_le h.cnt.x_mem) w hw
  have hcov : ∀ g ∈ V, g ∈ D ⊔ (Q1 ⊔ Q2) ∨
      ∃ w ∈ D ⊔ (Q1 ⊔ Q2), g = a * w ∨ g = x * w ∨ g = a * x * w :=
    fun g hg => h.cover g (hVTD hg)
  rcases sec11_type_cases (V := V) (W := D ⊔ (Q1 ⊔ Q2)) (a := a) (x := x)
      h.cnt.x_sq hWx hcov with hVW | hSwap | hBase | hBoth
  · exact Or.inl hVW
  ·
    obtain ⟨g, hgV, ⟨w, hw, hgform⟩, hVbound⟩ := hSwap
    have hgR : g ∈ R := hVTD.trans h.TD_le hgV
    have hgz : g * z = z * g := h.R_z g hgR
    have hs2 : ∀ q ∈ Q2, g * q * g⁻¹ ∈ Q1 := by
      intro q hq
      have hq' : w * q * w⁻¹ ∈ Q2 := h.DQ_normQ2 hw q hq
      rcases hgform with hg | hg
      · rw [hg]
        have he : a * w * q * (a * w)⁻¹ = a * (w * q * w⁻¹) * a⁻¹ := by group
        rw [he]
        exact h.cnt.a_swap _ hq'
      · rw [hg]
        have he : a * x * w * q * (a * x * w)⁻¹ =
            a * (x * (w * q * w⁻¹) * x⁻¹) * a⁻¹ := by group
        rw [he]
        exact h.cnt.a_swap _ (h.cnt.x_norm2 _ hq')
    have hQ'card : Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) ≤ 8 :=
      sec11_card_Qg_swap h.cnt.z_sq h.cnt.z_ne h.cnt.Q_comm h.cnt.Q_inf
        h.cnt.Q1_card hgz hs2
    have hcount := hP.count h.cnt.z_sq h.cnt.z_ne hgV
    exact Or.inr (sec11_key117_le8k (V := V) (W := D ⊔ (Q1 ⊔ Q2))
      (C := D ⊓ (V ⊔ (Q1 ⊔ Q2))) (Q' := sec11Qg z g (Q1 ⊔ Q2))
      hVbound hcount hQ'card hk)
  ·
    obtain ⟨g, hgV, ⟨w, hw, hgeq⟩, hVbound⟩ := hBase
    have hgR : g ∈ R := hVTD.trans h.TD_le hgV
    have hgz : g * z = z * g := h.R_z g hgR
    have hzc1 : ∀ q ∈ Q1, q * z = z * q := fun q hq => h.cnt.z_cent q (h.cnt.Q1_le hq)
    have hzc2 : ∀ q ∈ Q2, q * z = z * q := fun q hq => h.cnt.z_cent q (h.cnt.Q2_le hq)
    have hn1 : ∀ q ∈ Q1, g * q * g⁻¹ ∈ Q1 := by
      intro q hq
      have hq' : w * q * w⁻¹ ∈ Q1 := h.DQ_normQ1 hw q hq
      rw [hgeq]
      have he : x * w * q * (x * w)⁻¹ = x * (w * q * w⁻¹) * x⁻¹ := by group
      rw [he]
      exact h.cnt.x_norm1 _ hq'
    have hn2 : ∀ q ∈ Q2, g * q * g⁻¹ ∈ Q2 := by
      intro q hq
      have hq' : w * q * w⁻¹ ∈ Q2 := h.DQ_normQ2 hw q hq
      rw [hgeq]
      have he : x * w * q * (x * w)⁻¹ = x * (w * q * w⁻¹) * x⁻¹ := by group
      rw [he]
      exact h.cnt.x_norm2 _ hq'
    have ht1 : ∃ y ∈ Q1, g * y * g⁻¹ * y⁻¹ ∉ zpowers z := by
      obtain ⟨y, hy, hyw⟩ := h.nt1 hw
      exact ⟨y, hy, by rw [hgeq]; exact hyw⟩
    have ht2 : ∃ y ∈ Q2, g * y * g⁻¹ * y⁻¹ ∉ zpowers z := by
      obtain ⟨y, hy, hyw⟩ := h.nt2 hw
      exact ⟨y, hy, by rw [hgeq]; exact hyw⟩
    have hQ'card : Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) ≤ 8 :=
      sec11_card_Qg_base h.cnt.z_sq h.cnt.z_ne h.cnt.Q_comm h.cnt.Q_inf
        h.cnt.Q1_card h.cnt.Q2_card hzc1 hzc2 hgz hn1 hn2 ht1 ht2
    have hcount := hP.count h.cnt.z_sq h.cnt.z_ne hgV
    exact Or.inr (sec11_key117_le8k (V := V) (W := D ⊔ (Q1 ⊔ Q2))
      (C := D ⊓ (V ⊔ (Q1 ⊔ Q2))) (Q' := sec11Qg z g (Q1 ⊔ Q2))
      hVbound hcount hQ'card hk)
  ·
    obtain ⟨g1, hg1V, g2, hg2V, hg1form, hg2base, hVbound⟩ := hBoth
    obtain ⟨w1, hw1, hg1ab⟩ := hg1form
    obtain ⟨w2, hw2, hg2eq⟩ := hg2base
    have hg1R : g1 ∈ R := hVTD.trans h.TD_le hg1V
    have hg2R : g2 ∈ R := hVTD.trans h.TD_le hg2V
    have hg1z : g1 * z = z * g1 := h.R_z g1 hg1R
    have hg2z : g2 * z = z * g2 := h.R_z g2 hg2R
    have hzc1 : ∀ q ∈ Q1, q * z = z * q := fun q hq => h.cnt.z_cent q (h.cnt.Q1_le hq)
    have hzc2 : ∀ q ∈ Q2, q * z = z * q := fun q hq => h.cnt.z_cent q (h.cnt.Q2_le hq)
    have hs2 : ∀ q ∈ Q2, g1 * q * g1⁻¹ ∈ Q1 := by
      intro q hq
      have hq' : w1 * q * w1⁻¹ ∈ Q2 := h.DQ_normQ2 hw1 q hq
      rcases hg1ab with hg | hg
      · rw [hg]
        have he : a * w1 * q * (a * w1)⁻¹ = a * (w1 * q * w1⁻¹) * a⁻¹ := by group
        rw [he]
        exact h.cnt.a_swap _ hq'
      · rw [hg]
        have he : a * x * w1 * q * (a * x * w1)⁻¹ =
            a * (x * (w1 * q * w1⁻¹) * x⁻¹) * a⁻¹ := by group
        rw [he]
        exact h.cnt.a_swap _ (h.cnt.x_norm2 _ hq')
    have hn1 : ∀ q ∈ Q1, g2 * q * g2⁻¹ ∈ Q1 := by
      intro q hq
      have hq' : w2 * q * w2⁻¹ ∈ Q1 := h.DQ_normQ1 hw2 q hq
      rw [hg2eq]
      have he : x * w2 * q * (x * w2)⁻¹ = x * (w2 * q * w2⁻¹) * x⁻¹ := by group
      rw [he]
      exact h.cnt.x_norm1 _ hq'
    have hn2 : ∀ q ∈ Q2, g2 * q * g2⁻¹ ∈ Q2 := by
      intro q hq
      have hq' : w2 * q * w2⁻¹ ∈ Q2 := h.DQ_normQ2 hw2 q hq
      rw [hg2eq]
      have he : x * w2 * q * (x * w2)⁻¹ = x * (w2 * q * w2⁻¹) * x⁻¹ := by group
      rw [he]
      exact h.cnt.x_norm2 _ hq'
    have ht1 : ∃ y ∈ Q1, g2 * y * g2⁻¹ * y⁻¹ ∉ zpowers z := by
      obtain ⟨y, hy, hyw⟩ := h.nt1 hw2
      exact ⟨y, hy, by rw [hg2eq]; exact hyw⟩
    have hQ'card : Nat.card ↥(sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2)) ≤ 4 :=
      sec11_card_Qg_pair h.cnt.z_sq h.cnt.z_ne h.cnt.Q_comm h.cnt.Q_inf
        h.cnt.Q1_card h.cnt.Q2_card hzc1 hzc2 hg1z hg2z hs2 hn1 hn2 ht1
    have hcount := hP.count_pair h.cnt.z_sq h.cnt.z_ne hg1V hg2V
    exact Or.inr (sec11_key117_le4k (V := V) (W := D ⊔ (Q1 ⊔ Q2))
      (C := D ⊓ (V ⊔ (Q1 ⊔ Q2)))
      (Q' := sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2))
      hVbound hcount hQ'card hk)

end Sec11cCnt

end CFSG.OddStandard.SmallF3.Omega
