module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316E

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem fzl_cent_of_mem_R {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) {r : G} (hr : r ∈ R) :
    ∀ z ∈ Z, r * z = z * r := by
  intro z hz
  have hz' : r * z * r⁻¹ = z := h.R_Z r hr z hz
  calc r * z = (r * z * r⁻¹) * r := by group
    _ = z * r := by rw [hz']

private theorem fzl_mem_centralizer_Z_of_mem_R {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) {r : G} (hr : r ∈ R) :
    r ∈ Subgroup.centralizer (Z : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (fzl_cent_of_mem_R h hr z hz).symm

private theorem fzl_sq_mem_of_mul_Q {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) {x q : G} (hx : x ∈ T) (hx2 : x ^ 2 ∈ Q)
    (hq : q ∈ Q) : (x * q) ^ 2 ∈ Q := by
  have key : (x * q) ^ 2 = (x * q * x⁻¹) * x ^ 2 * q := by
    rw [pow_two, pow_two]
    group
  rw [key]
  exact Q.mul_mem (Q.mul_mem (h.nrm_Q x hx q hq) hx2) hq

theorem fzl_T_gen {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) :
    ∀ g ∈ T, g ∈ Q ∨ tau⁻¹ * g ∈ Q ∨ lam⁻¹ * g ∈ Q ∨ (lam * tau)⁻¹ * g ∈ Q := by
  have hcardR : Nat.card R = 2 * Nat.card Q := by rw [h.card_R, h.card_Q]
  have hcardT : Nat.card T = 2 * Nat.card R := by rw [h.card_T, h.card_R]
  have hlamR : lam ∉ R := by
    rintro hR
    obtain ⟨z, hz, hz'⟩ := h.lam_Z
    exact hz' (h.R_Z lam hR z hz)
  have hQR := fzl_index_two_cosets h.QR hcardR h.tau_R h.tau_notin_Q
  have hRT := fzl_index_two_cosets h.RT hcardT h.lam_T hlamR
  intro g hg
  rcases hRT g hg with hgR | hgR
  · rcases hQR g hgR with hgQ | hgQ
    · exact Or.inl hgQ
    · exact Or.inr (Or.inl hgQ)
  · rcases hQR (lam⁻¹ * g) hgR with hq | hq
    · exact Or.inr (Or.inr (Or.inl hq))
    · refine Or.inr (Or.inr (Or.inr ?_))
      have hkey : (lam * tau)⁻¹ * g = tau⁻¹ * (lam⁻¹ * g) := by group
      rwa [hkey]

theorem fzl_R_eq_cent_Z {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) :
    ∀ g, g ∈ R ↔ g ∈ T ∧ ∀ z ∈ Z, g * z = z * g := by
  intro g
  constructor
  · intro hgR
    exact ⟨h.RT hgR, fzl_cent_of_mem_R h hgR⟩
  · rintro ⟨hgT, hgc⟩
    have hgC : g ∈ Subgroup.centralizer (Z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      exact fun z hz => (hgc z hz).symm
    rcases fzl_T_gen h g hgT with hgQ | hgQ | hgQ | hgQ
    · exact h.QR hgQ
    · have hg_eq : tau * (tau⁻¹ * g) = g := by group
      rw [← hg_eq]
      exact R.mul_mem h.tau_R (h.QR hgQ)
    · exfalso
      obtain ⟨z, hz, hzne⟩ := h.lam_Z
      have hqC : lam⁻¹ * g ∈ Subgroup.centralizer (Z : Set G) :=
        fzl_mem_centralizer_Z_of_mem_R h (h.QR hgQ)
      have hlamC : lam ∈ Subgroup.centralizer (Z : Set G) := by
        have heq : lam = g * (lam⁻¹ * g)⁻¹ := by group
        rw [heq]
        exact Subgroup.mul_mem _ hgC (Subgroup.inv_mem _ hqC)
      rw [Subgroup.mem_centralizer_iff] at hlamC
      apply hzne
      have hcomm : lam * z = z * lam := (hlamC z hz).symm
      calc lam * z * lam⁻¹ = (z * lam) * lam⁻¹ := by rw [hcomm]
        _ = z := by group
    · exfalso
      obtain ⟨z, hz, hzne⟩ := h.lam_Z
      have hqC : (lam * tau)⁻¹ * g ∈ Subgroup.centralizer (Z : Set G) :=
        fzl_mem_centralizer_Z_of_mem_R h (h.QR hgQ)
      have htauC : tau ∈ Subgroup.centralizer (Z : Set G) :=
        fzl_mem_centralizer_Z_of_mem_R h h.tau_R
      have hlamC : lam ∈ Subgroup.centralizer (Z : Set G) := by
        have heq : lam = g * ((lam * tau)⁻¹ * g)⁻¹ * tau⁻¹ := by group
        rw [heq]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgC (Subgroup.inv_mem _ hqC))
          (Subgroup.inv_mem _ htauC)
      rw [Subgroup.mem_centralizer_iff] at hlamC
      apply hzne
      have hcomm : lam * z = z * lam := (hlamC z hz).symm
      calc lam * z * lam⁻¹ = (z * lam) * lam⁻¹ := by rw [hcomm]
        _ = z := by group

theorem fzl_T_elem {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) :
    (∀ g ∈ T, ∀ g' ∈ T, ⁅g, g'⁆ ∈ Q) ∧ ∀ g ∈ T, g ^ 2 ∈ Q := by
  have htau2Q : tau ^ 2 ∈ Q := by
    rcases h.tau_sq with h1 | h1
    · rw [h1]; exact Q.one_mem
    · rw [h1]; exact h.WQ h.t_mem
  have hlam2Q : lam ^ 2 ∈ Q := by rw [h.lam_sq]; exact Q.one_mem
  have hltau2Q : (lam * tau) ^ 2 ∈ Q := by
    have hcomm : Commute lam tau := h.tau_lam.symm
    rw [hcomm.mul_pow 2]
    exact Q.mul_mem hlam2Q htau2Q
  have hsq : ∀ g ∈ T, g ^ 2 ∈ Q := by
    intro g hg
    rcases fzl_T_gen h g hg with hgQ | hgQ | hgQ | hgQ
    · rw [pow_two]; exact Q.mul_mem hgQ hgQ
    · have hg_eq : g = tau * (tau⁻¹ * g) := by group
      rw [hg_eq]
      exact fzl_sq_mem_of_mul_Q h (h.RT h.tau_R) htau2Q hgQ
    · have hg_eq : g = lam * (lam⁻¹ * g) := by group
      rw [hg_eq]
      exact fzl_sq_mem_of_mul_Q h h.lam_T hlam2Q hgQ
    · have hg_eq : g = (lam * tau) * ((lam * tau)⁻¹ * g) := by group
      rw [hg_eq]
      exact fzl_sq_mem_of_mul_Q h (T.mul_mem h.lam_T (h.RT h.tau_R)) hltau2Q hgQ
  refine ⟨?_, hsq⟩
  intro g hg g' hg'
  exact fzl_comm_mem_of_sq (hsq g hg) (hsq g' hg') (hsq (g * g') (T.mul_mem hg hg'))
    (fun n hn => by
      have := h.nrm_Q g'⁻¹ (T.inv_mem hg') n hn
      simpa using this)

theorem fzl_canon_of_phiQ {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hΦ : fzlPhi Q = W) : FzCanon T W := by
  have hT_comm : ∀ a ∈ T, ∀ b ∈ T, ⁅a, b⁆ ∈ Q := (fzl_T_elem h).1
  have hT_sq : ∀ a ∈ T, a ^ 2 ∈ Q := (fzl_T_elem h).2
  have hPhiT_le_Q : fzlPhi T ≤ Q := fzl_phi_le_of_elem hT_comm hT_sq
  have hQT : Q ≤ T := le_trans h.QR h.RT
  have hW_le_PhiT : W ≤ fzlPhi T := by
    rw [← hΦ]
    exact fzl_phi_mono hQT
  have hZ_char : ∀ g, g ∈ Z ↔
      g ∈ fzlPhi T ∧ g ^ 2 = 1 ∧ ∀ s ∈ fzlPhi T, g * s = s * g := by
    intro g
    constructor
    · intro hg
      refine ⟨hW_le_PhiT (h.EW (h.ZE hg)), h.Z_sq g hg, ?_⟩
      intro s hs
      have hsQ : s ∈ Q := hPhiT_le_Q hs
      have hsz : s * g * s⁻¹ = g := h.R_Z s (h.QR hsQ) g hg
      have hcomm : s * g = g * s := by
        calc s * g = (s * g * s⁻¹) * s := by group
          _ = g * s := by rw [hsz]
      exact hcomm.symm
    · rintro ⟨hgPhi, hg2, hgcent⟩
      have hgQ : g ∈ Q := hPhiT_le_Q hgPhi
      have hgW : g ∈ W := by
        refine h.CW g ?_
        intro w hw
        exact hgcent w (hW_le_PhiT hw)
      rcases h.W_split g hgW with hgE | htgE
      · exact h.E_invol g hgE hg2
      · exfalso
        obtain ⟨n, hnQ, hnW⟩ := h.lam_Q
        set c : G := ⁅lam, n⁆ with hcdef
        have hcW : c ∉ W := by rw [hcdef]; exact hnW
        have hcQ : c ∈ Q := by
          rw [hcdef, commutatorElement_def]
          exact Q.mul_mem (h.nrm_Q lam h.lam_T n hnQ) (Q.inv_mem hnQ)
        have hcR : c ∈ R := h.QR hcQ
        have hcPhi : c ∈ fzlPhi T := by
          rw [hcdef]
          exact fzl_comm_mem_phi h.lam_T (hQT hnQ)
        have hcg : c * g * c⁻¹ = g := by
          have hgc : g * c = c * g := hgcent c hcPhi
          rw [← hgc]; group
        have htg2 : (t * g) ^ 2 = 1 := by
          have hcomm : Commute t g := h.W_comm t h.t_mem g hgW
          rw [hcomm.mul_pow 2, h.t_sq, hg2, one_mul]
        have htgZ : t * g ∈ Z := h.E_invol (t * g) htgE htg2
        set z : G := t * g with hzdef
        have hgz : g = t * z := by
          rw [hzdef]
          rw [← mul_assoc, ← pow_two, h.t_sq, one_mul]
        have hzt : c * (t * z) * c⁻¹ = t * z := by
          rw [← hgz]
          exact hcg
        have hzt' : c * (t * z) * c⁻¹ = (c * t * c⁻¹) * z := by
          have hcz : c * z * c⁻¹ = z := h.R_Z c hcR z htgZ
          calc c * (t * z) * c⁻¹ = (c * t * c⁻¹) * (c * z * c⁻¹) := by group
            _ = (c * t * c⁻¹) * z := by rw [hcz]
        have hct : c * t * c⁻¹ = t := by
          have h2 : (c * t * c⁻¹) * z = t * z := by rw [← hzt', hzt]
          have h3 := congrArg (· * z⁻¹) h2
          simpa [mul_assoc] using h3
        exact (h.Q_t c hcQ hcW) hct
  have hcanonPhiT : FzCanon T (fzlPhi T) := fzl_canon_phi (fzl_canon_self T)
  have hcanonZ : FzCanon T Z := fzl_canon_pow_comm hcanonPhiT hcanonPhiT 2 hZ_char
  have hcanonR : FzCanon T R := fzl_canon_cent hcanonZ (fzl_R_eq_cent_Z h)
  have hcanonPhiR : FzCanon T (fzlPhi R) := fzl_canon_phi hcanonR
  have hPhiR : fzlPhi R = W := by
    refine le_antisymm (fzl_phi_le_of_elem h.R_comm h.R_sq) ?_
    rw [← hΦ]
    exact fzl_phi_mono h.QR
  simpa [hPhiR] using hcanonPhiR

end CFSG.OddStandard.SmallF3.FritzII
