module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316Z1

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fzl_Z_eq_om1_phiT {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hPf : FzPFacts t tau rho E W Q T P)
    (h8 : FzZ8 Z E P) : ∀ g, g ∈ Z ↔ g ∈ fzlPhi T ∧ g ^ 2 = 1 := by
  intro g
  constructor
  · intro hg
    obtain ⟨e, he, heq⟩ := h.Z_sqrt g hg
    have heT : e ∈ T := h.RT (h.QR (h.WQ (h.EW he)))
    have hsq : e ^ 2 ∈ fzlPhi T := fzl_sq_mem_phi heT
    exact ⟨by rw [← heq]; exact hsq, h.Z_sq g hg⟩
  · rintro ⟨hgPhi, hg2⟩
    exact h8.om1 g (fzl_phi_T_le_P h hPf hgPhi) hg2

theorem fzl_phi_R_eq_E {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hPf : FzPFacts t tau rho E W Q T P)
    (h8 : FzZ8 Z E P) : fzlPhi R = E := by
  refine le_antisymm ?_ ?_
  · intro g hg
    exact hPf.PW g (fzl_phi_R_le_P h hPf hg)
      ((fzl_phi_le_of_elem h.R_comm h.R_sq) hg)
  · intro e he
    obtain ⟨p, hp, hpe⟩ := h8.sq e he
    have hpR : p ∈ R := h.QR (hPf.PQ hp)
    have hsq : p ^ 2 ∈ fzlPhi R := fzl_sq_mem_phi hpR
    rwa [hpe] at hsq

theorem fzl_Q_eq_cent_E {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hPf : FzPFacts t tau rho E W Q T P)
    (h8 : FzZ8 Z E P) : ∀ g, g ∈ Q ↔ g ∈ T ∧ ∀ e ∈ E, g * e = e * g := by
  have hQ_cent : ∀ q ∈ Q, ∀ e ∈ E, q * e = e * q := by
    intro q hq e he
    have heP : e ∈ P := hPf.EP he
    rcases hPf.Q_eq q hq with hqP | htqP
    · exact h8.comm q hqP e heP
    · have h1 : (t * q) * e = e * (t * q) := h8.comm (t * q) htqP e heP
      have h2 : t * e = e * t := h.W_comm t h.t_mem e (h.EW he)
      have h3 : t * (q * e) = t * (e * q) := by
        calc t * (q * e) = (t * q) * e := by group
          _ = e * (t * q) := h1
          _ = (e * t) * q := by group
          _ = (t * e) * q := by rw [h2]
          _ = t * (e * q) := by group
      exact mul_left_cancel h3
  have hex : ∃ e ∈ E, e ^ 2 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hEZ : E ≤ Z := fun e he => h.E_invol e he (hcon e he)
    have hcard : Nat.card E ≤ Nat.card Z := Subgroup.card_le_of_le hEZ
    rw [h.card_E, h.card_Z] at hcard
    omega
  let C : Subgroup G := Subgroup.centralizer (E : Set G)
  have hQ_le_C : Q ≤ C := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hQ_cent q hq e he).symm
  have htau_notC : tau ∉ C := by
    intro htauC
    rw [Subgroup.mem_centralizer_iff] at htauC
    obtain ⟨e, he, he2⟩ := hex
    have h1 : tau * e = e * tau := (htauC e he).symm
    have h2 : tau * e * tau⁻¹ = e⁻¹ := h.tau_W e (h.EW he)
    have h3 : tau * e * tau⁻¹ = e := by rw [h1]; group
    have heq : e = e⁻¹ := h3.symm.trans h2
    apply he2
    have hee : e * e = 1 := by
      nth_rw 1 [heq]
      exact inv_mul_cancel e
    simpa [pow_two] using hee
  have hlam_notC : lam ∉ C := by
    intro hlamC
    rw [Subgroup.mem_centralizer_iff] at hlamC
    obtain ⟨e, he, hne1, _⟩ := h.lam_E.2
    apply hne1
    have h1 : lam * e = e * lam := (hlamC e he).symm
    rw [h1]; group
  have hlamtau_notC : lam * tau ∉ C := by
    intro hltC
    rw [Subgroup.mem_centralizer_iff] at hltC
    obtain ⟨e, he, _, hne2⟩ := h.lam_E.2
    apply hne2
    have h1 : (lam * tau) * e = e * (lam * tau) := (hltC e he).symm
    have h2 : (lam * tau) * e * (lam * tau)⁻¹ = e := by rw [h1]; group
    have h3 : (lam * tau) * e * (lam * tau)⁻¹ = (lam * e * lam⁻¹)⁻¹ := by
      have htau : tau * e * tau⁻¹ = e⁻¹ := h.tau_W e (h.EW he)
      calc (lam * tau) * e * (lam * tau)⁻¹
          = lam * (tau * e * tau⁻¹) * lam⁻¹ := by group
        _ = lam * e⁻¹ * lam⁻¹ := by rw [htau]
        _ = (lam * e * lam⁻¹)⁻¹ := by group
    have heq : (lam * e * lam⁻¹)⁻¹ = e := by rw [← h3]; exact h2
    calc lam * e * lam⁻¹ = ((lam * e * lam⁻¹)⁻¹)⁻¹ := by group
      _ = e⁻¹ := by rw [heq]
  intro g
  constructor
  · intro hg
    exact ⟨h.RT (h.QR hg), hQ_cent g hg⟩
  · rintro ⟨hgT, hgc⟩
    have hgC : g ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (hgc e he).symm
    rcases fzl_T_gen h g hgT with hgQ | hq | hq | hq
    · exact hgQ
    · exfalso
      have hqC : tau⁻¹ * g ∈ C := hQ_le_C hq
      apply htau_notC
      have : tau = g * (tau⁻¹ * g)⁻¹ := by group
      rw [this]
      exact C.mul_mem hgC (C.inv_mem hqC)
    · exfalso
      have hqC : lam⁻¹ * g ∈ C := hQ_le_C hq
      apply hlam_notC
      have : lam = g * (lam⁻¹ * g)⁻¹ := by group
      rw [this]
      exact C.mul_mem hgC (C.inv_mem hqC)
    · exfalso
      have hqC : (lam * tau)⁻¹ * g ∈ C := hQ_le_C hq
      apply hlamtau_notC
      have : lam * tau = g * ((lam * tau)⁻¹ * g)⁻¹ := by group
      rw [this]
      exact C.mul_mem hgC (C.inv_mem hqC)

end CFSG.OddStandard.SmallF3.FritzII
