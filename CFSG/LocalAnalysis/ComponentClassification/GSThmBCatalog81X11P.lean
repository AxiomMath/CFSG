module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Frontier
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11Ex

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

abbrev PPv (h : Hyp59 H) (v : H) : Subgroup H := h.P ⊔ conjugate h.P v

theorem S_le_normalizer_P : h.S ≤ normalizer (h.P : Set H) := fun s hs =>
  Eight.mem_normalizer_of_conj_mem fun c hc => by
    have := h.toHyp52.conj_mem_P' (inv_mem hs) hc
    rwa [inv_inv] at this

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

theorem eq_one_or_a_of_mem_center_P (d : Data H₁) {π : H} (hπ : π ∈ h.P)
    (hc : ∀ q ∈ h.P, π * q = q * π) : π = 1 ∨ π = h.a := by
  obtain ⟨β, hP⟩ := d.pres
  have h4 := hP.four_le
  refine d.eq_one_or_a_of_comm hπ (hc _ hP.b_mem) (mem_zpowers _) (fun h1 => ?_) (fun h1 => ?_)
    (hc _ hP.p_mem)
  · rw [h1, orderOf_one] at h4
    omega
  · rw [h1, h.orderOf_a] at h4
    omega

variable {d : Data H₁} {v : H} (hv : d.IsV v)
include hv

theorem Pv_le_S : conjugate h.P v ≤ h.S := h.toHyp52.sec8_conjugate_P_le_S hv.mem_N

theorem z_mem_Pv : d.z ∈ conjugate h.P v := by
  rw [mem_conjugate_iff, ← hv.conj_a, show v * (v⁻¹ * h.a * v) * v⁻¹ = h.a by group]
  exact h.toHyp52.a_mem_P

theorem P_inf_Pv : h.P ⊓ conjugate h.P v = ⊥ := by
  by_contra hne
  obtain ⟨w, hw, hw1, hwZ⟩ := Seven.exists_mem_center_of_normal h.toHyp52.isPGroup_S
    (inf_le_left.trans inf_le_left)
    (fun t ht x hx => mem_inf.mpr ⟨h.toHyp52.conj_mem_P' ht (mem_inf.mp hx).1,
      h.toHyp52.sec8_conj_mem_conjugate_P hv.mem_N ht (mem_inf.mp hx).2⟩) hne
  obtain ⟨hwP, hwv⟩ := mem_inf.mp hw
  have hwa : w = h.a := by
    have hx : w ∈ h.P ⊓ centralizer (h.S : Set H) :=
      mem_inf.mpr ⟨hwP, mem_centralizer_iff.mpr fun t ht => hwZ t ht⟩
    rw [H₁.C_eq] at hx
    rcases mem_zpowers_two h.orderOf_a hx with h1 | h1
    · exact absurd h1 hw1
    · exact h1
  rw [hwa, mem_conjugate_iff, show v * h.a * v⁻¹ = d.z by rw [← hv.conj_z]; group] at hwv
  have hz := (h.toHyp52.D_inf_P_eq_bot H₁.center_J) ▸ mem_inf.mpr ⟨d.z_D, hwv⟩
  have h2 := d.z_ord
  rw [mem_bot.mp hz, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem comm_P_Pv {π π' : H} (hπ : π ∈ h.P) (hπ' : π' ∈ conjugate h.P v) :
    π * π' = π' * π := by
  have hπS : π ∈ h.S := (mem_inf.mp hπ).1
  have h1 : π * π' * π⁻¹ * π'⁻¹ ∈ h.P ⊓ conjugate h.P v := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [show π * π' * π⁻¹ * π'⁻¹ = π * (π' * π⁻¹ * π'⁻¹) by group]
      exact mul_mem hπ (h.toHyp52.conj_mem_P' (Pv_le_S hv hπ') (inv_mem hπ))
    · exact mul_mem (h.toHyp52.sec8_conj_mem_conjugate_P hv.mem_N hπS hπ') (inv_mem hπ')
  rw [P_inf_Pv hv, mem_bot] at h1
  calc π * π' = π * π' * π⁻¹ * π'⁻¹ * (π' * π) := by group
    _ = π' * π := by rw [h1, one_mul]

theorem card_PPv : Nat.card (h.PPv v) = Nat.card h.P * Nat.card h.P := by
  rw [PPv, Seven.card_sup_of_commute (fun _ hx _ hy => comm_P_Pv hv hx hy) (P_inf_Pv hv),
    Eight.card_conjugate']

theorem PPv_le_S : h.PPv v ≤ h.S := sup_le inf_le_left (Pv_le_S hv)

theorem mem_PPv_iff {x : H} :
    x ∈ h.PPv v ↔ ∃ π ∈ h.P, ∃ π' ∈ conjugate h.P v, π * π' = x := by
  rw [← SetLike.mem_coe, PPv,
    coe_mul_of_right_le_normalizer_left _ _ ((Pv_le_S hv).trans h.S_le_normalizer_P)]
  rfl

theorem conj_mem_PPv {t x : H} (ht : t ∈ h.S) (hx : x ∈ h.PPv v) : t * x * t⁻¹ ∈ h.PPv v := by
  obtain ⟨π, hπ, π', hπ', rfl⟩ := (mem_PPv_iff hv).mp hx
  rw [show t * (π * π') * t⁻¹ = (t * π * t⁻¹) * (t * π' * t⁻¹) by group]
  exact mul_mem (mem_sup_left (h.toHyp52.conj_mem_P' ht hπ))
    (mem_sup_right (h.toHyp52.sec8_conj_mem_conjugate_P hv.mem_N ht hπ'))

theorem conj_v_mem_PPv {x : H} (hx : x ∈ h.PPv v) : v⁻¹ * x * v ∈ h.PPv v := by
  obtain ⟨π, hπ, π', hπ', rfl⟩ := (mem_PPv_iff hv).mp hx
  rw [show v⁻¹ * (π * π') * v = (v⁻¹ * π * v) * (v⁻¹ * π' * v) by group]
  refine mul_mem (mem_sup_right ?_) (mem_sup_left ?_)
  · rw [mem_conjugate_iff, show v * (v⁻¹ * π * v) * v⁻¹ = π by group]
    exact hπ
  · rw [mem_conjugate_iff] at hπ'
    have := h.toHyp52.conj_mem_P' (inv_mem hv.sq_mem) hπ'
    rwa [show (v * v)⁻¹ * (v * π' * v⁻¹) * (v * v)⁻¹⁻¹ = v⁻¹ * π' * v by group] at this

theorem U_le_normalizer_PPv : h.U81 v ≤ normalizer (h.PPv v : Set H) :=
  sup_le (fun s hs => Eight.mem_normalizer_of_conj_mem fun c hc => by
      have := conj_mem_PPv hv (inv_mem hs) hc
      rwa [inv_inv] at this)
    (zpowers_le.mpr (Eight.mem_normalizer_of_conj_mem fun c hc => conj_v_mem_PPv hv hc))

theorem asigma_not_mem_PPv (I : In81) (hst : d.Stage7 v) : h.a * d.sigma ∉ h.PPv v := by
  intro hmem
  have hu := (mem_inf.mp (asigma_mem_ZF I hst.facts)).2
  have hvF : v ∈ normalizer (h.F32 : Set H) := h.normalizer_S_le_normalizer_F32 hv.mem_N
  obtain ⟨π, hπ, π', hπ', he⟩ := (mem_PPv_iff hv).mp hmem
  have hcommP : ∀ q ∈ h.P, (h.a * d.sigma) * q = q * (h.a * d.sigma) := fun q hq =>
    (mem_centralizer_iff.mp hu q (hst.P_le_F hq)).symm
  have hcommPv : ∀ q ∈ conjugate h.P v, (h.a * d.sigma) * q = q * (h.a * d.sigma) := by
    intro q hq
    have hqF : q ∈ h.F32 :=
      (mem_normalizer_iff.mp hvF q).mpr (hst.P_le_F (mem_conjugate_iff.mp hq))
    exact (mem_centralizer_iff.mp hu q hqF).symm
  have hπZ : ∀ q ∈ h.P, π * q = q * π := by
    intro q hq
    have h1 := hcommP q hq
    rw [← he] at h1
    have h2 := comm_P_Pv hv hq hπ'
    have : π * q * π' = q * π * π' := by
      calc π * q * π' = π * (q * π') := by group
        _ = π * (π' * q) := by rw [h2]
        _ = q * (π * π') := by rw [mul_assoc] at h1; exact h1
        _ = q * π * π' := by group
    exact mul_right_cancel this
  have hπ'Z : ∀ q ∈ conjugate h.P v, π' * q = q * π' := by
    intro q hq
    have h1 := hcommPv q hq
    rw [← he] at h1
    have h2 := comm_P_Pv hv hπ hq
    have : π * (π' * q) = π * (q * π') := by
      calc π * (π' * q) = π * π' * q := by group
        _ = q * (π * π') := h1
        _ = (q * π) * π' := by group
        _ = (π * q) * π' := by rw [h2]
        _ = π * (q * π') := by group
    exact mul_left_cancel this
  have hπ'P : v * π' * v⁻¹ ∈ h.P := mem_conjugate_iff.mp hπ'
  have hπ'c : ∀ q ∈ h.P, v * π' * v⁻¹ * q = q * (v * π' * v⁻¹) := by
    intro q hq
    have hq' : v⁻¹ * q * v ∈ conjugate h.P v := by
      rw [mem_conjugate_iff, show v * (v⁻¹ * q * v) * v⁻¹ = q by group]
      exact hq
    have h1 := hπ'Z _ hq'
    calc v * π' * v⁻¹ * q = v * (π' * (v⁻¹ * q * v)) * v⁻¹ := by group
      _ = v * ((v⁻¹ * q * v) * π') * v⁻¹ := by rw [h1]
      _ = q * (v * π' * v⁻¹) := by group
  have hzv : v⁻¹ * h.a * v = d.z := hv.conj_a
  have hσ : d.sigma ∈ h.D ⊔ h.P := by
    have hσe : d.sigma = h.a⁻¹ * (π * π') := by rw [he, inv_mul_cancel_left]
    have hπ'D : π' ∈ h.D ⊔ h.P := by
      rcases eq_one_or_a_of_mem_center_P d hπ'P hπ'c with h1 | h1
      · have : π' = 1 := by
          calc π' = v⁻¹ * (v * π' * v⁻¹) * v := by group
            _ = 1 := by rw [h1]; group
        rw [this]
        exact one_mem _
      · have : π' = d.z := by
          calc π' = v⁻¹ * (v * π' * v⁻¹) * v := by group
            _ = d.z := by rw [h1, hzv]
        rw [this]
        exact mem_sup_left d.z_D
    rw [hσe]
    exact mul_mem (mem_sup_right (inv_mem h.toHyp52.a_mem_P))
      (mul_mem (mem_sup_right hπ) hπ'D)
  exact d.sigma_not_mem_DP I.cf1 I.cf2 hst.facts hσ

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
