module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410N0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410NA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410NB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316P2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup _root_.Certificates

variable {G : Type} [Group G] [Finite G]

private lemma fz410_std_comm_of_conj {t g : G} (hgt : g * t * g⁻¹ = t) : g * t = t * g := by
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [hgt]

private lemma fz410_std_mem_E_iff {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (pf : FzPFacts t tau rho E W Q T P) :
    ∀ p ∈ P, p ∈ E ↔ t * p * t⁻¹ = p := by
  intro p hp
  constructor
  · intro hpE
    have hcomm : p * t = t * p := h.W_comm p (h.EW hpE) t h.t_mem
    calc t * p * t⁻¹ = p * t * t⁻¹ := by rw [hcomm]
      _ = p := by group
  · intro hconj
    have htp : t * p = p * t := by
      calc t * p = t * p * t⁻¹ * t := by group
        _ = p * t := by rw [hconj]
    by_cases hpW : p ∈ W
    · exact pf.PW p hp hpW
    · exfalso
      have hpQ : p ∈ Q := pf.PQ hp
      have hconj2 : p * t * p⁻¹ = t := by
        calc p * t * p⁻¹ = t * p * p⁻¹ := by rw [htp.symm]
          _ = t := by group
      exact h.Q_t p hpQ hpW hconj2

private lemma fz410_std_card_fix {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (pf : FzPFacts t tau rho E W Q T P)
    {emb : FzL410.A → G} (E0 : Fz410Coord P emb) :
    Nat.card {a : FzL410.A // t * emb a * t⁻¹ = emb a} = 16 := by
  have hcent := fz410_std_mem_E_iff h pf
  have hbij : Function.Bijective
      (fun a : {a : FzL410.A // t * emb a * t⁻¹ = emb a} =>
        (⟨emb a.1, (hcent (emb a.1) (E0.emb_mem a.1)).mpr a.2⟩ : ↥E)) := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply Subtype.ext
      apply E0.inj
      exact Subtype.ext_iff.mp hab
    · intro e
      obtain ⟨a, ha⟩ := (E0.mem e.1).mp (pf.EP e.2)
      refine ⟨⟨a, ?_⟩, ?_⟩
      · rw [ha]
        exact (hcent e.1 (pf.EP e.2)).mp e.2
      · apply Subtype.ext
        exact ha
  rw [Nat.card_eq_of_bijective _ hbij]
  exact h.card_E

private lemma fz410_std_card_fix2 {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (pf : FzPFacts t tau rho E W Q T P)
    {emb : FzL410.A → G} (E0 : Fz410Coord P emb) :
    Nat.card {a : FzL410.A // t * emb a * t⁻¹ = emb a ∧ (2 : ℕ) • a = 0} = 4 := by
  have hcent := fz410_std_mem_E_iff h pf
  have hsq : ∀ a : FzL410.A, (2 : ℕ) • a = 0 ↔ (emb a) ^ 2 = 1 := by
    intro a
    have h := E0.emb_nsmul 2 a
    constructor
    · intro ha
      rw [ha, E0.emb_zero] at h
      exact h.symm
    · intro ha
      rw [ha, ← E0.emb_zero] at h
      exact E0.inj _ _ h
  have hbij : Function.Bijective
      (fun a : {a : FzL410.A // t * emb a * t⁻¹ = emb a ∧ (2 : ℕ) • a = 0} =>
        (⟨emb a.1, h.E_invol (emb a.1)
          ((hcent (emb a.1) (E0.emb_mem a.1)).mpr a.2.1)
          ((hsq a.1).mp a.2.2)⟩ : ↥Z)) := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply Subtype.ext
      apply E0.inj
      exact Subtype.ext_iff.mp hab
    · intro z
      obtain ⟨a, ha⟩ := (E0.mem z.1).mp (pf.EP (h.ZE z.2))
      refine ⟨⟨a, ?_, ?_⟩, ?_⟩
      · rw [ha]
        exact (hcent z.1 (pf.EP (h.ZE z.2))).mp (h.ZE z.2)
      · apply (hsq a).mpr
        rw [ha]
        exact h.Z_sq z.1 z.2
      · apply Subtype.ext
        exact ha
  rw [Nat.card_eq_of_bijective _ hbij]
  exact h.card_Z

theorem fzl410_emb (hN : FzL410.NormSpec) (hA : FzL410.StageA) (hB : FzL410.StageB)
    {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (pf : FzPFacts t tau rho E W Q T P) (htP : t ∉ P)
    (φ₀ : ↥P ≃* Multiplicative FzL410.A) :
    ∃ (s : G) (emb : FzL410.A → G), (s = tau ∨ s = t * tau) ∧ Fz410Emb P t s lam rho emb := by
  have ht_mem_T : t ∈ T := h.RT (h.QR (h.WQ h.t_mem))
  have htn : ∀ p ∈ P, t * p * t⁻¹ ∈ P := pf.nrm_P t ht_mem_T
  have htau_n : ∀ p ∈ P, tau * p * tau⁻¹ ∈ P := pf.nrm_P tau (h.RT h.tau_R)
  have hln : ∀ p ∈ P, lam * p * lam⁻¹ ∈ P := pf.nrm_P lam h.lam_T
  have htr : t * rho = rho * t := (fz410_std_comm_of_conj h.rho_t).symm
  obtain ⟨emb0, E0⟩ := fzl410_N0 hN h.rho_ord pf.nrm_P_rho pf.rho_fpf φ₀
  have hfix : Nat.card {a : FzL410.A // t * emb0 a * t⁻¹ = emb0 a} = 16 :=
    fz410_std_card_fix h pf E0.toFz410Coord
  have hfix2 : Nat.card {a : FzL410.A // t * emb0 a * t⁻¹ = emb0 a ∧ (2 : ℕ) • a = 0} = 4 :=
    fz410_std_card_fix2 h pf E0.toFz410Coord
  obtain ⟨emb1, E1⟩ := fzl410_NA hA E0 h.t_sq htn htr hfix hfix2
  have hsinv : ∀ a, FzL410.tt a = a → tau * emb1 a * tau⁻¹ = (emb1 a)⁻¹ := by
    intro a ha
    have hfixa : t * emb1 a * t⁻¹ = emb1 a := by
      have hcj := E1.cj_t a
      rw [ha] at hcj
      exact hcj
    have hmemE : emb1 a ∈ E :=
      (fz410_std_mem_E_iff h pf (emb1 a) (E1.emb_mem a)).mpr hfixa
    exact h.tau_W (emb1 a) (h.EW hmemE)
  have hlt : lam * t = t * lam := fz410_std_comm_of_conj h.lam_t
  have htau_t : tau * t = t * tau := fz410_std_comm_of_conj h.tau_t
  obtain ⟨s, emb, hs, Eemb⟩ :=
    fzl410_NB (s := tau) (emb := emb1) hB E1 pf.tau_sq1 htau_n h.tau_rho htau_t hsinv
      h.lam_sq hln h.lam_rho hlt h.tau_lam.symm
  exact ⟨s, emb, hs, Eemb⟩

end CFSG.OddStandard.SmallF3.FritzII
