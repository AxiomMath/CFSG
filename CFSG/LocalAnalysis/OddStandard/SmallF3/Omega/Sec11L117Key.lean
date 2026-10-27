module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Cnt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Cos
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Qg

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec11_C_inf_eq {z : G} {C Q Q' : Subgroup G} (hCinf : C ⊓ Q = zpowers z)
    (hle : Q' ≤ Q) (hzQ' : z ∈ Q') : C ⊓ Q' = zpowers z := by
  have hzC : z ∈ C := by
    have hz : z ∈ C ⊓ Q := by rw [hCinf]; exact Subgroup.mem_zpowers z
    exact (Subgroup.mem_inf.mp hz).1
  apply le_antisymm
  · exact (inf_le_inf le_rfl hle).trans (le_of_eq hCinf)
  · exact le_inf (Subgroup.zpowers_le_of_mem hzC) (Subgroup.zpowers_le_of_mem hzQ')

private theorem sec11_key117_le8 {V W C Q' : Subgroup G}
    (hV : Nat.card V ≤ 2 * Nat.card ↥(V ⊓ W))
    (hcount : 2 * Nat.card ↥(V ⊓ W) ≤ Nat.card C * Nat.card Q')
    (hQ' : Nat.card Q' ≤ 8) (hC : 0 < Nat.card C) (hW : Nat.card W = 16 * Nat.card C) :
    Nat.card V < Nat.card W := by
  have h1 : Nat.card V ≤ Nat.card C * Nat.card Q' := hV.trans hcount
  have h2 : Nat.card C * Nat.card Q' ≤ Nat.card C * 8 := Nat.mul_le_mul_left _ hQ'
  have h3 : Nat.card C * 8 < 16 * Nat.card C := by
    have h := Nat.mul_lt_mul_of_pos_left (show (8 : ℕ) < 16 by norm_num) hC
    rwa [mul_comm (Nat.card C) 16] at h
  calc Nat.card V ≤ Nat.card C * Nat.card Q' := h1
    _ ≤ Nat.card C * 8 := h2
    _ < 16 * Nat.card C := h3
    _ = Nat.card W := hW.symm

private theorem sec11_key117_le4 {V W C Q' : Subgroup G}
    (hV : Nat.card V ≤ 4 * Nat.card ↥(V ⊓ W))
    (hcount : 2 * Nat.card ↥(V ⊓ W) ≤ Nat.card C * Nat.card Q')
    (hQ' : Nat.card Q' ≤ 4) (hC : 0 < Nat.card C) (hW : Nat.card W = 16 * Nat.card C) :
    Nat.card V < Nat.card W := by
  have h1 : Nat.card V ≤ 2 * (Nat.card C * Nat.card Q') := by
    rw [show (4 : ℕ) * Nat.card ↥(V ⊓ W) = 2 * (2 * Nat.card ↥(V ⊓ W)) by ring] at hV
    exact hV.trans (Nat.mul_le_mul_left 2 hcount)
  have h2 : 2 * (Nat.card C * Nat.card Q') ≤ Nat.card C * 8 := by
    rw [show 2 * (Nat.card C * Nat.card Q') = Nat.card C * (2 * Nat.card Q') by ring]
    exact Nat.mul_le_mul_left _ (by omega)
  have h3 : Nat.card C * 8 < 16 * Nat.card C := by
    have h := Nat.mul_lt_mul_of_pos_left (show (8 : ℕ) < 16 by norm_num) hC
    rwa [mul_comm (Nat.card C) 16] at h
  calc Nat.card V ≤ 2 * (Nat.card C * Nat.card Q') := h1
    _ ≤ Nat.card C * 8 := h2
    _ < 16 * Nat.card C := h3
    _ = Nat.card W := hW.symm

theorem sec11_inf_le_CQg {z g : G} {C Q V : Subgroup G}
    (hg : ∀ c ∈ C, g * c * g⁻¹ * c⁻¹ ∈ zpowers z) (hn : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hcomm : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c) (hQz : ∀ q ∈ Q, q * z = z * q)
    (hgV : g ∈ V) (hV : IsElemAbelianMod z V) :
    V ⊓ (C ⊔ Q) ≤ C ⊔ sec11Qg z g Q := by
  intro v hv
  rw [Subgroup.mem_inf] at hv
  obtain ⟨hvV, hvCQ⟩ := hv
  obtain ⟨c, hc, q, hq, hcq⟩ := exists_mul_of_mem_sup_of_commute hcomm hvCQ
  have hqg : q ∈ sec11Qg z g Q := by
    refine sec11_mem_Qg_of_mul hg hn hcomm hc hq (hQz q hq) ?_
    rw [← hcq]
    exact (hV g hgV v hvV).1
  have hsum : c * q ∈ C ⊔ sec11Qg z g Q := Subgroup.mul_mem_sup hc hqg
  rwa [hcq.symm] at hsum

theorem sec11_inf_le_CQg_pair {z g1 g2 : G} {C Q V : Subgroup G}
    (hg1 : ∀ c ∈ C, g1 * c * g1⁻¹ * c⁻¹ ∈ zpowers z) (hn1 : ∀ q ∈ Q, g1 * q * g1⁻¹ ∈ Q)
    (hg2 : ∀ c ∈ C, g2 * c * g2⁻¹ * c⁻¹ ∈ zpowers z) (hn2 : ∀ q ∈ Q, g2 * q * g2⁻¹ ∈ Q)
    (hcomm : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c) (hQz : ∀ q ∈ Q, q * z = z * q)
    (hg1V : g1 ∈ V) (hg2V : g2 ∈ V) (hV : IsElemAbelianMod z V) :
    V ⊓ (C ⊔ Q) ≤ C ⊔ (sec11Qg z g1 Q ⊓ sec11Qg z g2 Q) := by
  intro v hv
  rw [Subgroup.mem_inf] at hv
  obtain ⟨hvV, hvCQ⟩ := hv
  obtain ⟨c, hc, q, hq, hcq⟩ := exists_mul_of_mem_sup_of_commute hcomm hvCQ
  have hq1 : q ∈ sec11Qg z g1 Q := by
    refine sec11_mem_Qg_of_mul hg1 hn1 hcomm hc hq (hQz q hq) ?_
    rw [← hcq]
    exact (hV g1 hg1V v hvV).1
  have hq2 : q ∈ sec11Qg z g2 Q := by
    refine sec11_mem_Qg_of_mul hg2 hn2 hcomm hc hq (hQz q hq) ?_
    rw [← hcq]
    exact (hV g2 hg2V v hvV).1
  have hsum : c * q ∈ C ⊔ (sec11Qg z g1 Q ⊓ sec11Qg z g2 Q) :=
    Subgroup.mul_mem_sup hc ⟨hq1, hq2⟩
  rwa [hcq.symm] at hsum

theorem sec11_key117_abstract [Finite G] {z : G} {T C Q1 Q2 : Subgroup G} {a x : G}
    (h : Sec11Cnt G z T C Q1 Q2 a x) {V : Subgroup G} (hVT : V ≤ T)
    (hV : IsElemAbelianMod z V) :
    V ≤ C ⊔ (Q1 ⊔ Q2) ∨ Nat.card V < Nat.card ↥(C ⊔ (Q1 ⊔ Q2)) := by
  classical
  have hQT : Q1 ⊔ Q2 ≤ T := sup_le h.Q1_le h.Q2_le
  have hzCQ : z ∈ C ⊓ (Q1 ⊔ Q2) := by rw [h.C_inf]; exact Subgroup.mem_zpowers z
  have hzC : z ∈ C := (Subgroup.mem_inf.mp hzCQ).1
  have hzQ : z ∈ Q1 ⊔ Q2 := (Subgroup.mem_inf.mp hzCQ).2
  have hQz : ∀ q ∈ Q1 ⊔ Q2, q * z = z * q := fun q hq => h.z_cent q (hQT hq)
  have hzc1 : ∀ q ∈ Q1, q * z = z * q := fun q hq => hQz q (Subgroup.mem_sup_left hq)
  have hzc2 : ∀ q ∈ Q2, q * z = z * q := fun q hq => hQz q (Subgroup.mem_sup_right hq)
  have hcover : ∀ g ∈ V, g ∈ C ⊔ (Q1 ⊔ Q2) ∨
      ∃ w ∈ C ⊔ (Q1 ⊔ Q2), g = a * w ∨ g = x * w ∨ g = a * x * w :=
    fun g hg => h.cover g (hVT hg)
  rcases sec11_type_cases (V := V) (W := C ⊔ (Q1 ⊔ Q2)) (a := a) (x := x)
      h.x_sq (fun w hw => h.W_norm x h.x_mem w hw) hcover with hVW | hSwap | hBase | hBoth
  · exact Or.inl hVW
  ·
    obtain ⟨g, hgV, ⟨w, hw, hgform⟩, hVbound⟩ := hSwap
    have hgT : g ∈ T := hVT hgV
    have hgz : g * z = z * g := h.z_cent g hgT
    have hs2 : ∀ q ∈ Q2, g * q * g⁻¹ ∈ Q1 := by
      intro q hq
      have hq' : w * q * w⁻¹ ∈ Q2 := h.W_normQ2 hw q hq
      rcases hgform with hg | hg
      · rw [hg]
        have he : a * w * q * (a * w)⁻¹ = a * (w * q * w⁻¹) * a⁻¹ := by group
        rw [he]
        exact h.a_swap _ hq'
      · rw [hg]
        have he : a * x * w * q * (a * x * w)⁻¹ =
            a * (x * (w * q * w⁻¹) * x⁻¹) * a⁻¹ := by group
        rw [he]
        exact h.a_swap _ (h.x_norm2 _ hq')
    have hQ'card : Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) ≤ 8 :=
      sec11_card_Qg_swap h.z_sq h.z_ne h.Q_comm h.Q_inf h.Q1_card hgz hs2
    have hH : V ⊓ (C ⊔ (Q1 ⊔ Q2)) ≤ C ⊔ sec11Qg z g (Q1 ⊔ Q2) :=
      sec11_inf_le_CQg (z := z) (g := g) (C := C) (Q := Q1 ⊔ Q2) (V := V)
        (h.comm_C_T g hgT) (h.T_normQ g hgT) h.C_Q hQz hgV hV
    have hQ'le : sec11Qg z g (Q1 ⊔ Q2) ≤ Q1 ⊔ Q2 := sec11Qg_le z g (Q1 ⊔ Q2)
    have hzQ' : z ∈ sec11Qg z g (Q1 ⊔ Q2) := sec11_z_mem_Qg hzQ hgz
    have hinf' : C ⊓ sec11Qg z g (Q1 ⊔ Q2) = zpowers z :=
      sec11_C_inf_eq h.C_inf hQ'le hzQ'
    have hcount : 2 * Nat.card ↥(V ⊓ (C ⊔ (Q1 ⊔ Q2))) ≤
        Nat.card C * Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) :=
      sec11_two_mul_card_le (C := C) (Q' := sec11Qg z g (Q1 ⊔ Q2))
        (H := V ⊓ (C ⊔ (Q1 ⊔ Q2)))
        (fun c hc q hq => h.C_Q c hc q (hQ'le hq)) hinf' h.z_sq h.z_ne hH
    exact Or.inr (sec11_key117_le8 (V := V) (W := C ⊔ (Q1 ⊔ Q2)) (C := C)
      (Q' := sec11Qg z g (Q1 ⊔ Q2)) hVbound hcount hQ'card Nat.card_pos h.card_W)
  ·
    obtain ⟨g, hgV, ⟨w, hw, hgeq⟩, hVbound⟩ := hBase
    have hgT : g ∈ T := hVT hgV
    have hgz : g * z = z * g := h.z_cent g hgT
    have hn1 : ∀ q ∈ Q1, g * q * g⁻¹ ∈ Q1 := by
      intro q hq
      have hq' : w * q * w⁻¹ ∈ Q1 := h.W_normQ1 hw q hq
      rw [hgeq]
      have he : x * w * q * (x * w)⁻¹ = x * (w * q * w⁻¹) * x⁻¹ := by group
      rw [he]
      exact h.x_norm1 _ hq'
    have hn2 : ∀ q ∈ Q2, g * q * g⁻¹ ∈ Q2 := by
      intro q hq
      have hq' : w * q * w⁻¹ ∈ Q2 := h.W_normQ2 hw q hq
      rw [hgeq]
      have he : x * w * q * (x * w)⁻¹ = x * (w * q * w⁻¹) * x⁻¹ := by group
      rw [he]
      exact h.x_norm2 _ hq'
    have ht1 : ∃ y ∈ Q1, g * y * g⁻¹ * y⁻¹ ∉ zpowers z := by
      obtain ⟨y, hy, hyw⟩ := h.nt1 hw
      exact ⟨y, hy, by rw [hgeq]; exact hyw⟩
    have ht2 : ∃ y ∈ Q2, g * y * g⁻¹ * y⁻¹ ∉ zpowers z := by
      obtain ⟨y, hy, hyw⟩ := h.nt2 hw
      exact ⟨y, hy, by rw [hgeq]; exact hyw⟩
    have hQ'card : Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) ≤ 8 :=
      sec11_card_Qg_base h.z_sq h.z_ne h.Q_comm h.Q_inf h.Q1_card h.Q2_card
        hzc1 hzc2 hgz hn1 hn2 ht1 ht2
    have hH : V ⊓ (C ⊔ (Q1 ⊔ Q2)) ≤ C ⊔ sec11Qg z g (Q1 ⊔ Q2) :=
      sec11_inf_le_CQg (z := z) (g := g) (C := C) (Q := Q1 ⊔ Q2) (V := V)
        (h.comm_C_T g hgT) (h.T_normQ g hgT) h.C_Q hQz hgV hV
    have hQ'le : sec11Qg z g (Q1 ⊔ Q2) ≤ Q1 ⊔ Q2 := sec11Qg_le z g (Q1 ⊔ Q2)
    have hzQ' : z ∈ sec11Qg z g (Q1 ⊔ Q2) := sec11_z_mem_Qg hzQ hgz
    have hinf' : C ⊓ sec11Qg z g (Q1 ⊔ Q2) = zpowers z :=
      sec11_C_inf_eq h.C_inf hQ'le hzQ'
    have hcount : 2 * Nat.card ↥(V ⊓ (C ⊔ (Q1 ⊔ Q2))) ≤
        Nat.card C * Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) :=
      sec11_two_mul_card_le (C := C) (Q' := sec11Qg z g (Q1 ⊔ Q2))
        (H := V ⊓ (C ⊔ (Q1 ⊔ Q2)))
        (fun c hc q hq => h.C_Q c hc q (hQ'le hq)) hinf' h.z_sq h.z_ne hH
    exact Or.inr (sec11_key117_le8 (V := V) (W := C ⊔ (Q1 ⊔ Q2)) (C := C)
      (Q' := sec11Qg z g (Q1 ⊔ Q2)) hVbound hcount hQ'card Nat.card_pos h.card_W)
  ·
    obtain ⟨g1, hg1V, g2, hg2V, hg1form, hg2base, hVbound⟩ := hBoth
    obtain ⟨w1, hw1, hg1ab⟩ := hg1form
    obtain ⟨w2, hw2, hg2eq⟩ := hg2base
    have hg1T : g1 ∈ T := hVT hg1V
    have hg2T : g2 ∈ T := hVT hg2V
    have hg1z : g1 * z = z * g1 := h.z_cent g1 hg1T
    have hg2z : g2 * z = z * g2 := h.z_cent g2 hg2T
    have hs2 : ∀ q ∈ Q2, g1 * q * g1⁻¹ ∈ Q1 := by
      intro q hq
      have hq' : w1 * q * w1⁻¹ ∈ Q2 := h.W_normQ2 hw1 q hq
      rcases hg1ab with hg | hg
      · rw [hg]
        have he : a * w1 * q * (a * w1)⁻¹ = a * (w1 * q * w1⁻¹) * a⁻¹ := by group
        rw [he]
        exact h.a_swap _ hq'
      · rw [hg]
        have he : a * x * w1 * q * (a * x * w1)⁻¹ =
            a * (x * (w1 * q * w1⁻¹) * x⁻¹) * a⁻¹ := by group
        rw [he]
        exact h.a_swap _ (h.x_norm2 _ hq')
    have hn1 : ∀ q ∈ Q1, g2 * q * g2⁻¹ ∈ Q1 := by
      intro q hq
      have hq' : w2 * q * w2⁻¹ ∈ Q1 := h.W_normQ1 hw2 q hq
      rw [hg2eq]
      have he : x * w2 * q * (x * w2)⁻¹ = x * (w2 * q * w2⁻¹) * x⁻¹ := by group
      rw [he]
      exact h.x_norm1 _ hq'
    have hn2 : ∀ q ∈ Q2, g2 * q * g2⁻¹ ∈ Q2 := by
      intro q hq
      have hq' : w2 * q * w2⁻¹ ∈ Q2 := h.W_normQ2 hw2 q hq
      rw [hg2eq]
      have he : x * w2 * q * (x * w2)⁻¹ = x * (w2 * q * w2⁻¹) * x⁻¹ := by group
      rw [he]
      exact h.x_norm2 _ hq'
    have ht1 : ∃ y ∈ Q1, g2 * y * g2⁻¹ * y⁻¹ ∉ zpowers z := by
      obtain ⟨y, hy, hyw⟩ := h.nt1 hw2
      exact ⟨y, hy, by rw [hg2eq]; exact hyw⟩
    have hQ'card : Nat.card ↥(sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2)) ≤ 4 :=
      sec11_card_Qg_pair h.z_sq h.z_ne h.Q_comm h.Q_inf h.Q1_card h.Q2_card
        hzc1 hzc2 hg1z hg2z hs2 hn1 hn2 ht1
    have hH : V ⊓ (C ⊔ (Q1 ⊔ Q2)) ≤
        C ⊔ (sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2)) :=
      sec11_inf_le_CQg_pair (z := z) (g1 := g1) (g2 := g2) (C := C) (Q := Q1 ⊔ Q2)
        (V := V) (h.comm_C_T g1 hg1T) (h.T_normQ g1 hg1T)
        (h.comm_C_T g2 hg2T) (h.T_normQ g2 hg2T) h.C_Q hQz hg1V hg2V hV
    have hQ'le : sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2) ≤ Q1 ⊔ Q2 :=
      inf_le_left.trans (sec11Qg_le z g1 (Q1 ⊔ Q2))
    have hzQ' : z ∈ sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2) :=
      ⟨sec11_z_mem_Qg hzQ hg1z, sec11_z_mem_Qg hzQ hg2z⟩
    have hinf' : C ⊓ (sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2)) = zpowers z :=
      sec11_C_inf_eq h.C_inf hQ'le hzQ'
    have hcount : 2 * Nat.card ↥(V ⊓ (C ⊔ (Q1 ⊔ Q2))) ≤
        Nat.card C * Nat.card ↥(sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2)) :=
      sec11_two_mul_card_le (C := C)
        (Q' := sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2))
        (H := V ⊓ (C ⊔ (Q1 ⊔ Q2)))
        (fun c hc q hq => h.C_Q c hc q (hQ'le hq)) hinf' h.z_sq h.z_ne hH
    exact Or.inr (sec11_key117_le4 (V := V) (W := C ⊔ (Q1 ⊔ Q2)) (C := C)
      (Q' := sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2))
      hVbound hcount hQ'card Nat.card_pos h.card_W)

end CFSG.OddStandard.SmallF3.Omega
