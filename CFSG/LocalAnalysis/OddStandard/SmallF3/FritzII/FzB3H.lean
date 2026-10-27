module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Cop
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3F

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t q tau lam rho u : G} {Z E X W R T : Subgroup G}

private lemma fzbs_3h_conj_t {g r : G} (hg : g * t * g⁻¹ = t)
    (hr : r * t * r⁻¹ = t * u ^ 2) :
    (g * r * g⁻¹) * t * (g * r * g⁻¹)⁻¹ = t * (g * u ^ 2 * g⁻¹) := by
  have hginv : g⁻¹ * t * g = t := by
    have h := congrArg (fun x => g⁻¹ * x * g) hg
    have h2 : g⁻¹ * (g * t * g⁻¹) * g = t := by group
    rw [h2] at h
    exact h.symm
  rw [show (g * r * g⁻¹) * t * (g * r * g⁻¹)⁻¹
        = g * (r * (g⁻¹ * t * g) * r⁻¹) * g⁻¹ by group, hginv, hr,
      show g * (t * u ^ 2) * g⁻¹ = (g * t * g⁻¹) * (g * u ^ 2 * g⁻¹) by group, hg]

private lemma fzbs_3h_y_mem (hS : FzbsStr t q tau lam rho u Z E X W R T) {r₃ y : G}
    (hy : y = 1 ∨ y = r₃ ∨ y = rho * r₃ * rho⁻¹ ∨ y = rho ^ 2 * r₃ * (rho ^ 2)⁻¹)
    (hr₃ : r₃ ∈ ⁅R, zpowers rho⁆) : y ∈ ⁅R, zpowers rho⁆ := by
  rcases hy with h | h | h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact hr₃
  · rw [h]; exact fzbs_P_rho hS hr₃
  · rw [h]
    have hh : rho ^ 2 * r₃ * (rho ^ 2)⁻¹ = rho * (rho * r₃ * rho⁻¹) * rho⁻¹ := by
      simp only [pow_two, mul_inv_rev]; group
    rw [hh]
    exact fzbs_P_rho hS (fzbs_P_rho hS hr₃)

private lemma fzbs_3h_decomp_step (hS : FzbsStr t q tau lam rho u Z E X W R T) {y p : G}
    (hyP : y ∈ ⁅R, zpowers rho⁆) (hp : p ∈ ⁅R, zpowers rho⁆)
    (hyp : y * t * y⁻¹ = p * t * p⁻¹) :
    ∃ m : G, m ∈ X ∧ m ∈ ⁅R, zpowers rho⁆ ∧ p = y * m := by
  refine ⟨y⁻¹ * p, ?_, ?_, by group⟩
  · refine fzbs_P_ker hS ((⁅R, zpowers rho⁆).mul_mem ((⁅R, zpowers rho⁆).inv_mem hyP) hp) ?_
    calc (y⁻¹ * p) * t * (y⁻¹ * p)⁻¹ = y⁻¹ * (p * t * p⁻¹) * y := by group
      _ = y⁻¹ * (y * t * y⁻¹) * y := by rw [← hyp]
      _ = t := by group
  · exact (⁅R, zpowers rho⁆).mul_mem ((⁅R, zpowers rho⁆).inv_mem hyP) hp

private lemma fzbs_3h_mem_normalizer_of_conj_mem {H : Subgroup G} {g : G}
    (h : ∀ y ∈ H, g * y * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    show g * y * g⁻¹ ∈ H
    exact h y hy
  · exact le_of_eq (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).symm

theorem fzbs_P_decomp (hS : FzbsStr t q tau lam rho u Z E X W R T) {r₃ : G}
    (hr₃ : r₃ ∈ ⁅R, zpowers rho⁆) (hr₃t : r₃ * t * r₃⁻¹ = t * u ^ 2) {p : G}
    (hp : p ∈ ⁅R, zpowers rho⁆) :
    ∃ y m : G, (y = 1 ∨ y = r₃ ∨ y = rho * r₃ * rho⁻¹ ∨ y = rho ^ 2 * r₃ * (rho ^ 2)⁻¹) ∧
      m ∈ X ∧ m ∈ ⁅R, zpowers rho⁆ ∧ p = y * m := by
  have htt : t * t = 1 := by rw [← pow_two]; exact hS.t_sq
  have hzZ : t * (p * t * p⁻¹) ∈ Z := hS.R_t p (fzbs_P_le_R hS hp)
  have hpt : p * t * p⁻¹ = t * (t * (p * t * p⁻¹)) := by
    rw [← mul_assoc, htt, one_mul]
  rcases fzbs_Z_orbit hS (hS.E_sq u hS.u_mem) hS.u_sq_ne hzZ with h1 | h2 | h3 | h4
  · have hp_eq : p * t * p⁻¹ = t := by rw [hpt, h1, mul_one]
    have hyp : (1 : G) * t * 1⁻¹ = p * t * p⁻¹ := by
      rw [one_mul, inv_one, mul_one, hp_eq]
    obtain ⟨m, hmX, hmP, hpm⟩ := fzbs_3h_decomp_step hS (one_mem _) hp hyp
    exact ⟨1, m, Or.inl rfl, hmX, hmP, by simpa using hpm⟩
  · have hp_eq : p * t * p⁻¹ = t * u ^ 2 := by rw [hpt, h2]
    have hyp : r₃ * t * r₃⁻¹ = p * t * p⁻¹ := hr₃t.trans hp_eq.symm
    obtain ⟨m, hmX, hmP, hpm⟩ := fzbs_3h_decomp_step hS hr₃ hp hyp
    exact ⟨r₃, m, Or.inr (Or.inl rfl), hmX, hmP, by simpa using hpm⟩
  · have hp_eq : p * t * p⁻¹ = t * (rho * u ^ 2 * rho⁻¹) := by rw [hpt, h3]
    have hyt := fzbs_3h_conj_t (g := rho) (r := r₃) hS.rho_t hr₃t
    have hyp : (rho * r₃ * rho⁻¹) * t * (rho * r₃ * rho⁻¹)⁻¹ = p * t * p⁻¹ :=
      hyt.trans hp_eq.symm
    obtain ⟨m, hmX, hmP, hpm⟩ :=
      fzbs_3h_decomp_step hS (fzbs_P_rho hS hr₃) hp hyp
    exact ⟨rho * r₃ * rho⁻¹, m, Or.inr (Or.inr (Or.inl rfl)), hmX, hmP, by simpa using hpm⟩
  · have hp_eq : p * t * p⁻¹ = t * (rho ^ 2 * u ^ 2 * (rho ^ 2)⁻¹) := by rw [hpt, h4]
    have hrho2_t : rho ^ 2 * t * (rho ^ 2)⁻¹ = t := by
      rw [show rho ^ 2 * t * (rho ^ 2)⁻¹ = rho * (rho * t * rho⁻¹) * rho⁻¹ by
        simp only [pow_two, mul_inv_rev]; group, hS.rho_t, hS.rho_t]
    have hyt := fzbs_3h_conj_t (g := rho ^ 2) (r := r₃) hrho2_t hr₃t
    have hyp : (rho ^ 2 * r₃ * (rho ^ 2)⁻¹) * t * (rho ^ 2 * r₃ * (rho ^ 2)⁻¹)⁻¹ =
        p * t * p⁻¹ := hyt.trans hp_eq.symm
    have hyP := fzbs_3h_y_mem hS (Or.inr (Or.inr (Or.inr rfl))) hr₃
    obtain ⟨m, hmX, hmP, hpm⟩ := fzbs_3h_decomp_step hS hyP hp hyp
    exact ⟨rho ^ 2 * r₃ * (rho ^ 2)⁻¹, m, Or.inr (Or.inr (Or.inr rfl)), hmX, hmP,
      by simpa using hpm⟩

theorem fzbs_P_sq (hS : FzbsStr t q tau lam rho u Z E X W R T) {r₃ : G}
    (hr₃ : r₃ ∈ ⁅R, zpowers rho⁆) (hr₃t : r₃ * t * r₃⁻¹ = t * u ^ 2) (hr₃2 : r₃ ^ 2 ∈ E)
    {p : G} (hp : p ∈ ⁅R, zpowers rho⁆) : p ^ 2 ∈ E := by
  obtain ⟨y, m, hy, hmX, _, hpm⟩ := fzbs_P_decomp hS hr₃ hr₃t hp
  have hyP := fzbs_3h_y_mem hS hy hr₃
  have hy2E : y ^ 2 ∈ E := by
    rcases hy with h | h | h | h
    · rw [h]; simpa using (one_mem E : (1 : G) ∈ E)
    · rw [h]; exact hr₃2
    · rw [h]
      have h1 := hS.rho_E (r₃ ^ 2) hr₃2
      rwa [show (rho * r₃ * rho⁻¹) ^ 2 = rho * r₃ ^ 2 * rho⁻¹ by
        simp only [pow_two, mul_inv_rev]; group]
    · rw [h]
      have h1 := hS.rho_E (r₃ ^ 2) hr₃2
      have h2 := hS.rho_E (rho * r₃ ^ 2 * rho⁻¹) h1
      rwa [show (rho ^ 2 * r₃ * (rho ^ 2)⁻¹) ^ 2
            = rho * (rho * r₃ ^ 2 * rho⁻¹) * rho⁻¹ by
        simp only [pow_two, mul_inv_rev]; group]
  have hmZ : m ^ 2 ∈ Z := (hS.X_iff m (hS.XW hmX)).mp hmX
  have hmE : m ^ 2 ∈ E := hS.ZE hmZ
  have hcZ : y⁻¹ * m * y * m⁻¹ ∈ Z := by
    have h := fzbs_comm_X hS (R.inv_mem (fzbs_P_le_R hS hyP)) hmX
    simpa using h
  have hcE : y⁻¹ * m * y * m⁻¹ ∈ E := hS.ZE hcZ
  have hp2 : p ^ 2 = y ^ 2 * (y⁻¹ * m * y * m⁻¹) * m ^ 2 := by
    rw [hpm]; simp only [pow_two]; group
  rw [hp2]
  exact E.mul_mem (E.mul_mem hy2E hcE) hmE

theorem fzbs_P_comm (hS : FzbsStr t q tau lam rho u Z E X W R T)
    (hsq : ∀ p ∈ ⁅R, zpowers rho⁆, p ^ 2 ∈ E) {a b : G} (ha : a ∈ ⁅R, zpowers rho⁆)
    (hb : b ∈ ⁅R, zpowers rho⁆) : ⁅a, b⁆ ∈ E := by
  have h1 : (a * b) ^ 2 ∈ E := hsq (a * b) ((⁅R, zpowers rho⁆).mul_mem ha hb)
  have h2 : b⁻¹ * (a ^ 2)⁻¹ * b ∈ E := by
    have h := fzbs_R_E hS (R.inv_mem (fzbs_P_le_R hS hb)) (E.inv_mem (hsq a ha))
    simpa using h
  have h3 : (b ^ 2)⁻¹ ∈ E := E.inv_mem (hsq b hb)
  have heq : ⁅a, b⁆ = (a * b) ^ 2 * (b⁻¹ * (a ^ 2)⁻¹ * b) * (b ^ 2)⁻¹ := by
    rw [commutatorElement_def]; simp only [pow_two]; group
  rw [heq]
  exact E.mul_mem (E.mul_mem h1 h2) h3

theorem fzbs_t_notin_P (hS : FzbsStr t q tau lam rho u Z E X W R T)
    (hsq : ∀ p ∈ ⁅R, zpowers rho⁆, p ^ 2 ∈ E) : t ∉ ⁅R, zpowers rho⁆ := by
  intro htP
  have hρR : rho ∈ Subgroup.normalizer (R : Set G) :=
    fzbs_3h_mem_normalizer_of_conj_mem (fun r hr => hS.rho_R r hr)
  have hPeq : ⁅⁅R, zpowers rho⁆, zpowers rho⁆ = ⁅R, zpowers rho⁆ :=
    CFSG.OddStandard.SmallF3.HarrisU33.S4B.commutator_commutator_zpowers_eq
      (A := R) (ρ := rho) hS.rho_cube hS.pgroup_R hρR
  have htP' : t ∈ ⁅⁅R, zpowers rho⁆, zpowers rho⁆ := by
    rw [hPeq]; exact htP
  have hnorm := fzl_norm_mem (Q := ⁅R, zpowers rho⁆) (Φ := E) hS.rho_cube
    (fun p hp => fzbs_P_rho hS hp)
    (fun a ha b hb => fzbs_P_comm hS hsq ha hb)
    (fzbs_E_le_P hS) htP'
  have hrho2_t : rho ^ 2 * t * (rho ^ 2)⁻¹ = t := by
    rw [show rho ^ 2 * t * (rho ^ 2)⁻¹ = rho * (rho * t * rho⁻¹) * rho⁻¹ by
      simp only [pow_two, mul_inv_rev]; group, hS.rho_t, hS.rho_t]
  rw [hS.rho_t, hrho2_t] at hnorm
  have htt : t * t = 1 := by rw [← pow_two]; exact hS.t_sq
  rw [show t * t * t = t by rw [htt, one_mul]] at hnorm
  exact hS.t_notin_E hnorm

theorem fzbs_P_X (hS : FzbsStr t q tau lam rho u Z E X W R T) (htP : t ∉ ⁅R, zpowers rho⁆)
    {x : G} (hx : x ∈ X) (hxP : x ∈ ⁅R, zpowers rho⁆) : x ∈ E := by
  rcases hS.X_split x hx with h | h
  · exact h
  · exfalso
    have htxP : t * x ∈ ⁅R, zpowers rho⁆ := fzbs_E_le_P hS h
    have hxinvP : x⁻¹ ∈ ⁅R, zpowers rho⁆ := (⁅R, zpowers rho⁆).inv_mem hxP
    have hmem : (t * x) * x⁻¹ ∈ ⁅R, zpowers rho⁆ :=
      (⁅R, zpowers rho⁆).mul_mem htxP hxinvP
    rw [mul_assoc, mul_inv_cancel, mul_one] at hmem
    exact htP hmem

end CFSG.OddStandard.SmallF3.FritzII
