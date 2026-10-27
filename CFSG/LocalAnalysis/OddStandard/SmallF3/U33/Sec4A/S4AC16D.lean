module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15F

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem c16_t_not_cent (h : L41GPh15 t L S x₁ x₂ lam rho) :
    ∃ f ∈ l41Y t x₁ x₂ rho, f * t ≠ t * f := by
  by_contra hcon
  push Not at hcon
  have hle : l41Y t x₁ x₂ rho ≤ l41Y t x₁ x₂ rho ⊓ invCent t :=
    fun f hf => Subgroup.mem_inf.mpr ⟨hf, mem_invCent_iff.mpr (hcon f hf)⟩
  have hcard := Subgroup.card_le_of_le hle
  rw [h.yfacts.cent_Y_t, m11_card_Y h.toL41GPh10, n4_card_four h.toCtx0] at hcard
  norm_num at hcard

theorem c16_relIndex_Q1_Q (h : L41GPh15 t L S x₁ x₂ lam rho) :
    (l41Q1 t x₁ x₂ rho).relIndex (l41Q t x₁ x₂ rho) = 2 := by
  have hle : l41Q1 t x₁ x₂ rho ≤ l41Q t x₁ x₂ rho := q15_Q1_le_Q h.toL41GPh8
  have hcard := Subgroup.relIndex_mul_card (H := l41Q1 t x₁ x₂ rho)
    (K := l41Q t x₁ x₂ rho)
  rw [inf_eq_left.mpr hle, h.q1facts.card_Q1, q14_card_Q h.toL41GPh10] at hcard
  norm_num at hcard
  omega

theorem c16_relIndex_Q_V1 (h : L41GPh15 t L S x₁ x₂ lam rho) :
    (l41Q t x₁ x₂ rho).relIndex (l41V1 t x₁ x₂ rho lam) = 2 := by
  have hle : l41Q t x₁ x₂ rho ≤ l41V1 t x₁ x₂ rho lam := by
    rw [q15_V1_eq h.q1facts.Q_eq]
    exact le_sup_left
  have hcard := Subgroup.relIndex_mul_card (H := l41Q t x₁ x₂ rho)
    (K := l41V1 t x₁ x₂ rho lam)
  rw [inf_eq_left.mpr hle, q14_card_Q h.toL41GPh10, h.q1facts.card_V1] at hcard
  norm_num at hcard
  omega

theorem c16_cent_Q_Y (h : L41GPh15 t L S x₁ x₂ lam rho)
    (hRQ : l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
      l41R t x₁ x₂ rho) :
    l41Q t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
      l41R t x₁ x₂ rho := by
  let Y : Subgroup G := l41Y t x₁ x₂ rho
  let Q : Subgroup G := l41Q t x₁ x₂ rho
  let Q₁ : Subgroup G := l41Q1 t x₁ x₂ rho
  let R : Subgroup G := l41R t x₁ x₂ rho
  let C : Subgroup G := Q ⊓ centralizer ((Y : Subgroup G) : Set G)
  have hRQ' : Q₁ ⊓ centralizer ((Y : Subgroup G) : Set G) = R := hRQ
  have hRC : R ≤ C := by
    refine le_inf (q14_R_le_Q h.toL41GPh8) ?_
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact m13_comm_R h.toL41GPh10 (m13_Y_le_R t x₁ x₂ rho hy) hr
  have hCQ1R : C ⊓ Q₁ ≤ R := by
    have h1 : C ⊓ Q₁ ≤ Q₁ ⊓ centralizer ((Y : Subgroup G) : Set G) :=
      le_inf inf_le_right (inf_le_left.trans inf_le_right)
    rwa [hRQ'] at h1
  have hρM : rho ∈ l41M t x₁ x₂ rho := q14_rho_mem_M h.toL41GPh8
  have hρY : rho ∈ normalizer ((Y : Subgroup G) : Set G) :=
    q14_mem_normalizer_Y h.toL41GPh10 hρM
  have hnC : ∀ d ∈ C, rho * d * rho⁻¹ ∈ C := by
    intro d hd
    obtain ⟨hdQ, hdcent⟩ := Subgroup.mem_inf.mp hd
    refine Subgroup.mem_inf.mpr ⟨q14_conj_Q hρM hdQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hdcent ⊢
    intro y hy
    have hy' : rho⁻¹ * y * rho ∈ Y := (Subgroup.mem_normalizer_iff''.mp hρY y).mp hy
    have hcomm := hdcent _ hy'
    calc y * (rho * d * rho⁻¹) = rho * ((rho⁻¹ * y * rho) * d) * rho⁻¹ := by group
      _ = rho * (d * (rho⁻¹ * y * rho)) * rho⁻¹ := by rw [hcomm]
      _ = (rho * d * rho⁻¹) * y := by group
  have hfixC : ∀ d ∈ C, rho * d * rho⁻¹ = d → d = 1 := by
    intro d hd hfix
    obtain ⟨hdQ, hdcent⟩ := Subgroup.mem_inf.mp hd
    have hdcentQ : d ∈ centralizer ({rho} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact n4_comm_of_conj_eq hfix
    have hdt : d ∈ zpowers t := by
      rw [← q14_cent_Q_rho h.toL41GPh10]
      exact Subgroup.mem_inf.mpr ⟨hdQ, hdcentQ⟩
    rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hdt with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨f, hf, hft⟩ := c16_t_not_cent h
      rw [Subgroup.mem_centralizer_iff] at hdcent
      rw [h1] at hdcent
      exact hft (hdcent f hf)
  have hmodC : Nat.card C % 3 = 1 :=
    q14_card_mod_three (q15_rho_cube h.toL41GPh1) hnC hfixC
  have hrelC : R.relIndex C ≤ 2 := by
    by_cases hCR : C ≤ R
    · rw [Subgroup.relIndex_eq_one.mpr hCR]
      norm_num
    · obtain ⟨a, haC, haR⟩ := SetLike.not_le_iff_exists.mp hCR
      have haQ1 : a ∉ Q₁ := fun ha => haR (hCQ1R (Subgroup.mem_inf.mpr ⟨haC, ha⟩))
      refine relIndex_le_two_of_forall hRC a haC ?_
      intro n hn
      have haQ : a⁻¹ ∈ Q := (Subgroup.mem_inf.mp (C.inv_mem haC)).1
      have hnQ : n ∈ Q := (Subgroup.mem_inf.mp hn).1
      rcases mem_or_mem_or_mul_mem_of_relIndex_two (q15_Q1_le_Q h.toL41GPh8)
        (c16_relIndex_Q1_Q h) haQ hnQ with h1 | h2 | h3
      · exact absurd (by simpa using Q₁.inv_mem h1) haQ1
      · exact Or.inl (hCQ1R (Subgroup.mem_inf.mpr ⟨hn, h2⟩))
      · exact Or.inr (hCQ1R (Subgroup.mem_inf.mpr ⟨C.mul_mem (C.inv_mem haC) hn, h3⟩))
  have hcard := Subgroup.relIndex_mul_card (H := R) (K := C)
  rw [inf_eq_left.mpr hRC, h.rfacts.card_R] at hcard
  have hjne : R.relIndex C ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcard
    rw [← hcard] at hmodC
    norm_num at hmodC
  have hj : R.relIndex C = 1 := by
    have hcases : R.relIndex C = 1 ∨ R.relIndex C = 2 := by omega
    rcases hcases with h1 | h2
    · exact h1
    · exfalso
      rw [h2] at hcard
      rw [← hcard] at hmodC
      norm_num at hmodC
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hj) hRC

theorem c16_V1_cent_K (h : L41GPh15 t L S x₁ x₂ lam rho) {v : G}
    (hv : v ∈ l41V1 t x₁ x₂ rho lam) (hK : ∀ k ∈ fourGrp x₁ x₂, v * k = k * v) :
    v ∈ l41Q t x₁ x₂ rho := by
  let Q : Subgroup G := l41Q t x₁ x₂ rho
  let V : Subgroup G := l41V1 t x₁ x₂ rho lam
  have hQV : Q ≤ V := by
    change Q ≤ l41V1 t x₁ x₂ rho lam
    rw [q15_V1_eq h.q1facts.Q_eq]
    exact le_sup_left
  have hlamV : lam ∈ V := by
    change lam ∈ l41V1 t x₁ x₂ rho lam
    rw [q15_V1_eq h.q1facts.Q_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)
  rcases mem_or_mem_or_mul_mem_of_relIndex_two hQV (c16_relIndex_Q_V1 h) hv hlamV with
    hvQ | hlamQ | hvlQ
  · exact hvQ
  · exfalso
    have hc := c16_Q_cent_K h hlamQ (n4_y_mem_four x₁ x₂)
    exact (n4_lam_moves h.toCtx0) (by rw [hc]; group)
  · exfalso
    have hvcomm : Commute v (x₁ ^ 2) := hK _ (n4_y_mem_four x₁ x₂)
    have hvlcomm : Commute (v * lam) (x₁ ^ 2) :=
      c16_Q_cent_K h hvlQ (n4_y_mem_four x₁ x₂)
    have hlamcomm : Commute lam (x₁ ^ 2) := by
      have h : Commute (v⁻¹ * (v * lam)) (x₁ ^ 2) := hvcomm.inv_left.mul_left hvlcomm
      have hv' : v⁻¹ * (v * lam) = lam := by group
      rw [hv'] at h
      exact h
    exact (n4_lam_moves h.toCtx0) (by rw [hlamcomm.eq]; group)

theorem c16_cent_V1_Y (h : L41GPh15 t L S x₁ x₂ lam rho)
    (hRQ : l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
      l41R t x₁ x₂ rho) :
    l41V1 t x₁ x₂ rho lam ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
      l41R t x₁ x₂ rho := by
  let Y : Subgroup G := l41Y t x₁ x₂ rho
  let Q : Subgroup G := l41Q t x₁ x₂ rho
  let Q₁ : Subgroup G := l41Q1 t x₁ x₂ rho
  let R : Subgroup G := l41R t x₁ x₂ rho
  let V : Subgroup G := l41V1 t x₁ x₂ rho lam
  have hRQ' : Q₁ ⊓ centralizer ((Y : Subgroup G) : Set G) = R := hRQ
  have hQV : Q ≤ V := by
    change Q ≤ l41V1 t x₁ x₂ rho lam
    rw [q15_V1_eq h.q1facts.Q_eq]
    exact le_sup_left
  have hcentQ : Q ⊓ centralizer ((Y : Subgroup G) : Set G) = l41R t x₁ x₂ rho :=
    c16_cent_Q_Y h hRQ'
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨hvV, hvcent⟩ := Subgroup.mem_inf.mp hv
    have hvcent' : v ∈ centralizer ((Y : Subgroup G) : Set G) := hvcent
    have hK : ∀ k ∈ fourGrp x₁ x₂, v * k = k * v := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff] at hvcent
      exact (hvcent k (m11_fourGrp_le_Y h.toL41GPh10 hk)).symm
    have hvQ : v ∈ Q := c16_V1_cent_K h hvV hK
    have hvR : v ∈ Q ⊓ centralizer ((Y : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hvQ, hvcent'⟩
    rwa [hcentQ] at hvR
  · intro r hr
    refine Subgroup.mem_inf.mpr ⟨hQV (q14_R_le_Q h.toL41GPh8 hr), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact m13_comm_R h.toL41GPh10 (m13_Y_le_R t x₁ x₂ rho hy) hr

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
