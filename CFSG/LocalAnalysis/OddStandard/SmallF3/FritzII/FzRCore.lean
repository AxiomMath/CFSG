module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRTr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRM2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRC2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRC3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316P2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S T₂ : Subgroup G}
  {x₁ x₂ lam rho tau : G}

private lemma fzrAux_comm_of_conj {G : Type*} [Group G] {a b : G}
    (h : a * b * a⁻¹ = b) : a * b = b * a := by
  calc a * b = (a * b * a⁻¹) * a := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = b * a := by rw [h]

theorem fzr_fusion_core
    [IsSimpleGroup G]
    (hctx : Ctx t L S x₁ x₂ lam rho tau) (hT : IsFzT2 t x₁ x₂ S T₂) (hsyl : FzSylow T₂)
    {Z E W Q R P X : Subgroup G} (h : FzStr t tau lam rho Z E W Q R T₂)
    (hP : FzPFacts t tau rho E W Q T₂ P) (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hXP : X ≤ P) (hX : ∀ x : G, x ∈ X ↔ x ∈ P ∧ x * x = 1) (hX16 : Nat.card X = 16)
    {s : G} (hs : s = tau ∨ s = t * tau) (hsX : ∀ x ∈ X, s * x = x * s) : False := by
  have hPT : P ≤ T₂ := hP.PQ.trans (h.QR.trans h.RT)
  have htT : t ∈ T₂ := h.RT (h.QR (h.WQ h.t_mem))
  have htauT : tau ∈ T₂ := h.RT h.tau_R
  have hlT : lam ∈ T₂ := h.lam_T
  have ht2 : t * t = 1 := by simpa [pow_two] using h.t_sq
  have htau2 : tau * tau = 1 := by simpa [pow_two] using hP.tau_sq1
  have hl2 : lam * lam = 1 := by simpa [pow_two] using h.lam_sq
  have httau : t * tau = tau * t := (fzrAux_comm_of_conj h.tau_t).symm
  have htl : t * lam = lam * t := (fzrAux_comm_of_conj h.lam_t).symm
  have htaul : tau * lam = lam * tau := h.tau_lam
  have hst : s * t = t * s := by
    rcases hs with h' | h'
    · rw [h']; exact fzrAux_comm_of_conj h.tau_t
    · rw [h']; exact ((Commute.refl t).mul_left httau.symm).eq
  have hsl : s * lam = lam * s := by
    rcases hs with h' | h'
    · rw [h']; exact htaul
    · rw [h']
      exact ((show Commute t lam from htl).mul_left (show Commute tau lam from htaul)).eq
  have hsr : s * rho = rho * s := by
    rcases hs with h' | h'
    · rw [h']; exact h.tau_rho
    · rw [h']
      exact ((show Commute t rho from (fzrAux_comm_of_conj h.rho_t).symm).mul_left
        (show Commute tau rho from h.tau_rho)).eq
  have hs2 : s * s = 1 := by
    rcases hs with h' | h'
    · rw [h']; exact htau2
    · rw [h']
      simpa [pow_two, ht2, htau2] using (show Commute t tau from httau).mul_pow 2
  have hsT : s ∈ T₂ := by
    rcases hs with h' | h'
    · rw [h']; exact htauT
    · rw [h']; exact T₂.mul_mem htT htauT
  have hsP : s ∉ P := by
    intro hsP
    have hsQ : s ∈ Q := hP.PQ hsP
    rcases hs with h' | h'
    · rw [h'] at hsQ; exact h.tau_notin_Q hsQ
    · rw [h'] at hsQ
      have htQ : t ∈ Q := h.WQ h.t_mem
      have htauQ : tau ∈ Q := by
        have hmem : t * (t * tau) ∈ Q := Q.mul_mem htQ hsQ
        have heq : t * (t * tau) = tau := by rw [← mul_assoc, ht2, one_mul]
        rwa [heq] at hmem
      exact h.tau_notin_Q htauQ
  have hsXn : s ∉ X := fun hx => hsP (hXP hx)
  have hl1 : lam ≠ 1 := by
    intro hl1
    obtain ⟨z, hz, hzne⟩ := h.lam_Z
    exact hzne (by rw [hl1]; group)
  have hls1 : lam * s ≠ 1 := by
    intro hls1
    have hlam_eq : lam = s⁻¹ := eq_inv_of_mul_eq_one_left hls1
    obtain ⟨z, hz, hzne⟩ := h.lam_Z
    apply hzne
    have hsR : s ∈ R := by
      rcases hs with h' | h'
      · rw [h']; exact h.tau_R
      · rw [h']; exact R.mul_mem (h.QR (h.WQ h.t_mem)) h.tau_R
    have hz' : s⁻¹ * z * (s⁻¹)⁻¹ = z := h.R_Z s⁻¹ (R.inv_mem hsR) z hz
    rw [hlam_eq]
    exact hz'
  have hsL : s ∉ twoCore t ⊔ L := by
    intro hsL
    have htC : t ∈ twoCore t ⊔ L := Subgroup.mem_sup_left hctx.hyp.mem_twoCore
    rcases hs with h' | h'
    · rw [h'] at hsL; exact hctx.tau_not_mem hsL
    · rw [h'] at hsL
      have htauC : tau ∈ twoCore t ⊔ L := by
        have hmem : t * (t * tau) ∈ twoCore t ⊔ L :=
          (twoCore t ⊔ L).mul_mem htC hsL
        have heq : t * (t * tau) = tau := by rw [← mul_assoc, ht2, one_mul]
        rwa [heq] at hmem
      exact hctx.tau_not_mem htauC
  have hXT : X ≤ T₂ := hXP.trans hPT
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x :=
    fun x hx y hy => hPc x (hXP hx) y (hXP hy)
  have hXsq : ∀ x ∈ X, x * x = 1 := fun x hx => ((hX x).mp hx).2
  have hP2 : IsPGroup 2 P := hT.isPGroup.to_le hPT
  obtain ⟨M, hMT, hMidx, hPM, hsM, hlM, _ht_notM, hM_form⟩ :=
    fzr_index2_M (T := T₂) (P := P) (Q := Q) (t := t) (tau := tau) (s := s) (l := lam)
      hP.PQ (h.QR.trans h.RT) hP.nrm_P hP.card_P h.card_T hP.Q_eq (fzl_T_gen h)
      htT htauT hlT ht2 htau2 hl2 httau htl htaul hs
  obtain ⟨x, hxM⟩ :=
    fzr_transfer (fzr_nonabelian_of_wreath hctx.wreath) hsyl hMT hMidx htT ht2
  have hu2 : (x⁻¹ * t * x) * (x⁻¹ * t * x) = 1 := by
    calc (x⁻¹ * t * x) * (x⁻¹ * t * x) = x⁻¹ * (t * t) * x := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨p, hp, hu | hu | hu | hu⟩ := hM_form (x⁻¹ * t * x) hxM
  · have hp2 : p * p = 1 := by rw [hu] at hu2; exact hu2
    have hpX : p ∈ X := (hX p).mpr ⟨hp, hp2⟩
    exact (fzr_nc_of_mem_X hctx hT.isPGroup hT.S_le hXT hXc hXsq hX16 hsT hs2 hsX hsXn hpX)
      ⟨x, hu⟩
  · have huT : p * s ∈ T₂ := T₂.mul_mem (hPT hp) hsT
    have hu2' : (p * s) * (p * s) = 1 := by rw [hu] at hu2; exact hu2
    have hunX : p * s ∉ X := by
      intro hmem
      have hpXs : p * s ∈ P := hXP hmem
      have hsP' : s ∈ P := by
        have hmem' : p⁻¹ * (p * s) ∈ P := P.mul_mem (P.inv_mem hp) hpXs
        have heq : p⁻¹ * (p * s) = s := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        rwa [heq] at hmem'
      exact hsP hsP'
    have huX : ∀ y ∈ X, (p * s) * y = y * (p * s) := by
      intro y hy
      have hyP : y ∈ P := hXP hy
      calc (p * s) * y = p * (s * y) := by rw [mul_assoc]
        _ = p * (y * s) := by rw [hsX y hy]
        _ = (p * y) * s := by rw [← mul_assoc]
        _ = (y * p) * s := by rw [hPc p hp y hyP]
        _ = y * (p * s) := by rw [mul_assoc]
    exact (fzr_nc_of_cent_X hctx hT.isPGroup hT.S_le hXT hXc hXsq hX16 huT hu2' huX hunX)
      ⟨x, hu⟩
  · have hnc : ¬ ∃ g : G, g⁻¹ * t * g = p * lam :=
      fzr_nc_lam hctx hP2 hP.nrm_P_rho (fun q hq => hP.nrm_P lam hlT q hq)
        h.rho_ord hl2 hl1 h.lam_rho hP.rho_fpf hp
    exact hnc ⟨x, hu⟩
  · have hnc : ¬ ∃ g : G, g⁻¹ * t * g = p * (lam * s) :=
      fzr_nc_lam_s hctx hT.isPGroup hT.S_le hPT hP.nrm_P hP.nrm_P_rho
        h.rho_ord hP.rho_fpf hlT hl2 h.lam_rho hsT hs2 hst hsl hsr hsL hls1
        hXT hXc hXsq hX16 hsX hsXn hp
    exact hnc ⟨x, hu⟩

end CFSG.OddStandard.SmallF3.FritzII
