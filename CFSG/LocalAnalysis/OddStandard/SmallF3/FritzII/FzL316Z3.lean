module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316Z2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma fzl_pow_four_of_sq {x : G} (h : x ^ 2 = 1) : x ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h, one_pow]

theorem fzl_W_eq_om2 {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hPf : FzPFacts t tau rho E W Q T P)
    (h8 : FzZ8 Z E P) : ∀ g, g ∈ W ↔ g ∈ Q ∧ g ^ 4 = 1 := by
  intro g
  constructor
  · intro hgW
    refine ⟨h.WQ hgW, ?_⟩
    rcases h.W_split g hgW with hgE | htgE
    · exact h.E_exp g hgE
    · have hg_eq : g = t * (t * g) := by
        rw [← mul_assoc, ← pow_two, h.t_sq, one_mul]
      rw [hg_eq]
      have hcomm : Commute t (t * g) := h.W_comm t h.t_mem (t * g) (h.EW htgE)
      rw [hcomm.mul_pow 4, fzl_pow_four_of_sq h.t_sq, one_mul]
      exact h.E_exp (t * g) htgE
  · rintro ⟨hgQ, hg4⟩
    rcases hPf.Q_eq g hgQ with hgP | htgP
    · exact h.EW (h8.om2 g hgP hg4)
    · set p : G := t * g with hpdef
      have hpP : p ∈ P := htgP
      have hg_eq : g = t * p := by
        rw [hpdef, ← mul_assoc, ← pow_two, h.t_sq, one_mul]
      have hpQ : p ∈ Q := hPf.PQ hpP
      have hpT : p ∈ T := h.RT (h.QR hpQ)
      obtain ⟨z, hzZ, hz⟩ := h.T_t p⁻¹ (T.inv_mem hpT)
      have hz' : p⁻¹ * t * p = t * z := by simpa using hz
      have htp : t * p = p * t * z := by
        have hh := congrArg (fun x => p * x) hz'
        simpa [mul_assoc] using hh
      have htz : t * z = z * t := h.W_comm t h.t_mem z (h.EW (h.ZE hzZ))
      have hpz : p * z = z * p := by
        have hzp : p * z * p⁻¹ = z := h.R_Z p (h.QR hpQ) z hzZ
        calc p * z = (p * z * p⁻¹) * p := by group
          _ = z * p := by rw [hzp]
      have hp2z : Commute (p ^ 2) z := by
        show p ^ 2 * z = z * p ^ 2
        rw [pow_two]
        calc p * p * z = p * (p * z) := by group
          _ = p * (z * p) := by rw [hpz]
          _ = (p * z) * p := by group
          _ = (z * p) * p := by rw [hpz]
          _ = z * (p * p) := by group
      have hzt : t * z * t = z := by
        calc t * z * t = z * t * t := by rw [htz]
          _ = z * (t * t) := by group
          _ = z := by rw [← pow_two, h.t_sq, mul_one]
      have hg2 : g ^ 2 = p ^ 2 * z := by
        rw [hg_eq, pow_two]
        calc (t * p) * (t * p) = (p * t * z) * (t * p) := by rw [htp]
          _ = p * (t * z * t) * p := by group
          _ = (p * z) * p := by rw [hzt]
          _ = p ^ 2 * z := by
            have h2 : (p * z) * p = p * (p * z) := by
              calc (p * z) * p = p * (z * p) := by group
                _ = p * (p * z) := by rw [hpz.symm]
            rw [h2, pow_two]
            group
      have hg4sq : g ^ 4 = p ^ 4 := by
        rw [show g ^ 4 = (g ^ 2) ^ 2 by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul], hg2,
          hp2z.mul_pow 2, h.Z_sq z hzZ, mul_one, ← pow_mul]
      have hp4 : p ^ 4 = 1 := by rw [← hg4sq]; exact hg4
      rw [hg_eq]
      exact W.mul_mem h.t_mem (h.EW (h8.om2 p hpP hp4))

theorem fzl_canon_of_Z8 {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hPf : FzPFacts t tau rho E W Q T P)
    (h8 : FzZ8 Z E P) : FzCanon T W := by
  have hT : FzCanon T T := fzl_canon_self T
  have hPhiT : FzCanon T (fzlPhi T) := fzl_canon_phi hT
  have hZ : FzCanon T Z := fzl_canon_pow hPhiT 2 (fzl_Z_eq_om1_phiT h hPf h8)
  have hR : FzCanon T R := fzl_canon_cent hZ (fzl_R_eq_cent_Z h)
  have hPhiR : FzCanon T (fzlPhi R) := fzl_canon_phi hR
  have hE : FzCanon T E := by
    rw [← fzl_phi_R_eq_E h hPf h8]
    exact hPhiR
  have hQ : FzCanon T Q := fzl_canon_cent hE (fzl_Q_eq_cent_E h hPf h8)
  exact fzl_canon_pow hQ 4 (fzl_W_eq_om2 h hPf h8)

end CFSG.OddStandard.SmallF3.FritzII
