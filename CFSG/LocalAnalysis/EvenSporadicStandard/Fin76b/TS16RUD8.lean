module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3UExt
public import Certificates.Certificate27826
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43CoverBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.U16

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.EvenSporadicStandard.M24Std.CU43

@[expose] def invIx (j : ℕ) : ℕ := ((List.range 8).find? fun k => mulTab j k == 0).getD 0

@[expose] def cj (j : ℕ) : ℕ := mulTab (mulTab j 5) (invIx j)

section Facts

theorem mulTab_lt (j k : ℕ) : mulTab j k < 8 := by
  unfold mulTab
  omega

theorem invIx_spec : ∀ j < 8, invIx j < 8 ∧ mulTab j (invIx j) = 0 ∧ mulTab (invIx j) j = 0 := by
  decide +kernel

@[expose] def InV (k : ℕ) : Prop := k = 0 ∨ k = 2 ∨ k = 5 ∨ k = 7

instance : DecidablePred InV := fun k => by unfold InV; infer_instance

theorem InV_mul : ∀ j < 8, ∀ k < 8, InV j → InV k → InV (mulTab j k) := by decide +kernel

theorem InV_inv : ∀ j < 8, InV j → InV (invIx j) := by decide +kernel

theorem cj_ne_zero : ∀ j < 8, cj j ≠ 0 := by decide +kernel

theorem cj_eq_five : ∀ j < 8, cj j = 5 ↔ InV j := by decide +kernel

theorem cj_lt (j : ℕ) : cj j < 8 := mulTab_lt _ _

end Facts

theorem d8_mul {j k : ℕ} (hj : j < 8) (hk : k < 8) : tP j * tP k = tP (mulTab j k) := by
  have h := Certificates.certificate27826.1
  simp only [d8Check, List.all_eq_true, List.mem_range] at h
  exact (eqA_iff (rep_compA (rep_tArr j) (rep_tArr k)) (rep_tArr (mulTab j k))).1 (h j hj k hk)

theorem tP_inv_eq {j : ℕ} (hj : j < 8) : (tP j)⁻¹ = tP (invIx j) := by
  obtain ⟨h1, h2, -⟩ := invIx_spec j hj
  apply inv_eq_of_mul_eq_one_right
  rw [d8_mul hj h1, h2, tP_zero]

theorem tP_conj_five {j : ℕ} (hj : j < 8) : tP j * tP 5 * (tP j)⁻¹ = tP (cj j) := by
  obtain ⟨h1, -, -⟩ := invIx_spec j hj
  rw [tP_inv_eq hj, d8_mul hj (by norm_num), d8_mul (mulTab_lt _ _) h1]
  rfl

theorem rho_facts : rhoPerm * rhoPerm = 1 ∧ ∃ g ∈ P, rhoPerm = g * tP 5 := by
  have h := Certificates.certificate27826.2
  simp only [rhoCosetCheck, Bool.and_eq_true] at h
  obtain ⟨hsq, h5⟩ := h
  refine ⟨(eqA_iff (rep_compA rep_rhoArr rep_rhoArr) rep_idA).1 hsq, ?_⟩
  have := (inP_iff (rep_compA rep_rhoArr (rep_tArr_inv (by norm_num : 5 < 8)))).1 h5
  exact ⟨_, this, by group⟩

theorem rho_sq : rhoPerm * rhoPerm = 1 := rho_facts.1

theorem rho_coset : ∃ g ∈ P, rhoPerm = g * tP 5 := rho_facts.2

theorem P_le_U43Ext : P ≤ U43Ext := by
  intro x hx
  rw [P_eq_range] at hx
  exact Subgroup.subset_closure (Or.inl hx)

theorem rho_mem_U43Ext : rhoPerm ∈ U43Ext := Subgroup.subset_closure (Or.inr rfl)

theorem rho_not_mem_P : rhoPerm ∉ P := by
  intro h
  obtain ⟨g, hg, hρ⟩ := rho_coset
  have : tP 5 ∈ P := by
    have e : tP 5 = g⁻¹ * rhoPerm := by rw [hρ]; group
    rw [e]
    exact P.mul_mem (P.inv_mem hg) h
  exact absurd ((tP_mem_P_iff (by norm_num)).1 this) (by norm_num)

theorem mem_U43Ext_iff {x : Equiv.Perm (Fin 820)} :
    x ∈ U43Ext ↔ x ∈ P ∨ ∃ g ∈ P, x = g * rhoPerm := by
  constructor
  · exact mem_U43Ext
  · rintro (hx | ⟨g, hg, rfl⟩)
    · exact P_le_U43Ext hx
    · exact U43Ext.mul_mem (P_le_U43Ext hg) rho_mem_U43Ext

@[expose] noncomputable def U43ExtStar : Subgroup (Equiv.Perm (Fin 820)) where
  carrier := {x | ∃ g ∈ P, ∃ k, k < 8 ∧ InV k ∧ x = g * tP k}
  one_mem' := ⟨1, P.one_mem, 0, by norm_num, Or.inl rfl, by rw [tP_zero, mul_one]⟩
  mul_mem' := by
    rintro _ _ ⟨g, hg, k, hk, hkV, rfl⟩ ⟨g', hg', k', hk', hk'V, rfl⟩
    refine ⟨g * (tP k * g' * (tP k)⁻¹), P.mul_mem hg (tP_normalizes hg'), mulTab k k',
      mulTab_lt _ _, InV_mul k hk k' hk' hkV hk'V, ?_⟩
    rw [← d8_mul hk hk']
    group
  inv_mem' := by
    rintro _ ⟨g, hg, k, hk, hkV, rfl⟩
    have hik : invIx k < 8 := (invIx_spec k hk).1
    refine ⟨(tP k)⁻¹ * g⁻¹ * tP k, ?_, invIx k, hik, InV_inv k hk hkV, ?_⟩
    · have := tP_normalizes (k := invIx k) (P.inv_mem hg)
      rwa [← tP_inv_eq hk] at this
    · rw [← tP_inv_eq hk]
      group

theorem P_le_U43ExtStar : P ≤ U43ExtStar := fun x hx =>
  ⟨x, hx, 0, by norm_num, Or.inl rfl, by rw [tP_zero, mul_one]⟩

theorem U43ExtStar_le_R : U43ExtStar ≤ R := by
  rintro _ ⟨g, hg, k, hk, -, rfl⟩
  exact mem_R_iff.2 ⟨g, hg, k, hk, rfl⟩

theorem U43Ext_le_U43ExtStar : U43Ext ≤ U43ExtStar := by
  intro x hx
  rcases mem_U43Ext_iff.1 hx with hx | ⟨g, hg, rfl⟩
  · exact P_le_U43ExtStar hx
  · obtain ⟨g', hg', hρ⟩ := rho_coset
    rw [hρ]
    refine ⟨g * g', P.mul_mem hg hg', 5, by norm_num, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    group

theorem conj_rho_eq {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) {j : ℕ} (hj : j < 8) :
    ∃ q ∈ P, (g * tP j) * rhoPerm * (g * tP j)⁻¹ = q * tP (cj j) := by
  obtain ⟨g', hg', hρ⟩ := rho_coset
  have hR : g * tP j ∈ R := mem_R_iff.2 ⟨g, hg, j, hj, rfl⟩
  have hA : (g * tP j) * g' * (g * tP j)⁻¹ ∈ P := conj_mem_P hR hg'
  have hcj := cj_lt j
  have hq : tP (cj j) * g⁻¹ * (tP (cj j))⁻¹ ∈ P := tP_normalizes (P.inv_mem hg)
  refine ⟨((g * tP j) * g' * (g * tP j)⁻¹) * (g * (tP (cj j) * g⁻¹ * (tP (cj j))⁻¹)),
    P.mul_mem hA (P.mul_mem hg hq), ?_⟩
  rw [hρ]
  calc (g * tP j) * (g' * tP 5) * (g * tP j)⁻¹
      = ((g * tP j) * g' * (g * tP j)⁻¹) * (g * (tP j * tP 5 * (tP j)⁻¹) * g⁻¹) := by group
    _ = ((g * tP j) * g' * (g * tP j)⁻¹) * (g * tP (cj j) * g⁻¹) := by rw [tP_conj_five hj]
    _ = _ := by group

theorem conj_mem_U43Ext {x : Equiv.Perm (Fin 820)} (hx : x ∈ U43ExtStar) {k : Equiv.Perm (Fin 820)}
    (hk : k ∈ U43Ext) : x * k * x⁻¹ ∈ U43Ext := by
  obtain ⟨g, hg, j, hj, hjV, rfl⟩ := hx
  have hR : g * tP j ∈ R := mem_R_iff.2 ⟨g, hg, j, hj, rfl⟩
  have hconjP : ∀ p ∈ P, (g * tP j) * p * (g * tP j)⁻¹ ∈ P := fun p hp => conj_mem_P hR hp
  rcases mem_U43Ext_iff.1 hk with hk | ⟨p, hp, rfl⟩
  · exact P_le_U43Ext (hconjP k hk)
  · obtain ⟨q, hq, hqe⟩ := conj_rho_eq hg hj
    obtain ⟨g', hg', hρ⟩ := rho_coset
    have hc5 : cj j = 5 := (cj_eq_five j hj).2 hjV
    rw [hc5] at hqe
    have e2 : tP 5 = g'⁻¹ * rhoPerm := by rw [hρ]; group
    rw [mem_U43Ext_iff]
    right
    refine ⟨((g * tP j) * p * (g * tP j)⁻¹) * q * g'⁻¹,
      P.mul_mem (P.mul_mem (hconjP p hp) hq) (P.inv_mem hg'), ?_⟩
    calc (g * tP j) * (p * rhoPerm) * (g * tP j)⁻¹
        = ((g * tP j) * p * (g * tP j)⁻¹) * ((g * tP j) * rhoPerm * (g * tP j)⁻¹) := by group
      _ = ((g * tP j) * p * (g * tP j)⁻¹) * (q * tP 5) := by rw [hqe]
      _ = _ := by rw [e2]; group

theorem normalizer_U43Ext {r : Equiv.Perm (Fin 820)} (hr : r ∈ R)
    (hn : ∀ k ∈ U43Ext, r * k * r⁻¹ ∈ U43Ext) : r ∈ U43ExtStar := by
  obtain ⟨g, hg, j, hj, rfl⟩ := mem_R_iff.1 hr
  have h1 := hn rhoPerm rho_mem_U43Ext
  obtain ⟨q, hq, hqe⟩ := conj_rho_eq hg hj
  obtain ⟨g', hg', hρ⟩ := rho_coset
  have hcj := cj_lt j
  rw [hqe] at h1
  have hc5 : cj j = 5 := by
    rcases mem_U43Ext_iff.1 h1 with hP | ⟨p, hp, hpe⟩
    · exfalso
      have : tP (cj j) ∈ P := by
        have e : tP (cj j) = q⁻¹ * (q * tP (cj j)) := by group
        rw [e]
        exact P.mul_mem (P.inv_mem hq) hP
      exact cj_ne_zero j hj ((tP_mem_P_iff hcj).1 this)
    · by_contra hne
      apply tP_mul_inv_not_mem hcj (by norm_num : 5 < 8) hne
      have e : tP (cj j) * (tP 5)⁻¹ = q⁻¹ * p * g' := by
        have e2 : q * tP (cj j) = p * (g' * tP 5) := by rw [hpe, hρ]
        calc tP (cj j) * (tP 5)⁻¹ = q⁻¹ * (q * tP (cj j)) * (tP 5)⁻¹ := by group
          _ = q⁻¹ * (p * (g' * tP 5)) * (tP 5)⁻¹ := by rw [e2]
          _ = q⁻¹ * p * g' := by group
      rw [e]
      exact P.mul_mem (P.mul_mem (P.inv_mem hq) hp) hg'
  exact ⟨g, hg, j, hj, (cj_eq_five j hj).1 hc5, rfl⟩

end CFSG.EvenSporadicStandard.Fin76b.U16
