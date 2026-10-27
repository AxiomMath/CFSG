module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Act
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410N2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Perm

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

namespace Fz410Set

variable {G : Type} [Group G] [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}
  (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)

section Helpers

include D

private theorem isOm_index_two {A : Subgroup G} (hA : Fz410IsOm E P Q A) :
    ∃ a ∈ A, a ∉ E ∧ ∀ b ∈ A, a * b ∈ E ∨ b ∈ E := by
  have hmul := Subgroup.relIndex_mul_card E A
  rw [inf_eq_left.2 hA.E_le, hA.card, D.str.card_E] at hmul
  have h2 : E.relIndex A = 2 := by omega
  exact Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp h2

private theorem isOm_inf_W {A : Subgroup G} (hA : Fz410IsOm E P Q A) (hAW : A ≠ W) :
    ∀ b ∈ A, b ∈ W → b ∈ E := by
  intro b hbA hbW
  by_contra hbE
  obtain ⟨a, haA, haE, hab⟩ := D.isOm_index_two hA
  have haW : a ∈ W := by
    rcases hab b hbA with h | h
    · have := W.mul_mem (D.str.EW h) (W.inv_mem hbW)
      simpa using this
    · exact absurd h hbE
  have hAW' : A ≤ W := by
    intro c hc
    rcases hab c hc with h | h
    · have := W.mul_mem (W.inv_mem haW) (D.str.EW h)
      simpa using this
    · exact D.str.EW h
  apply hAW
  have h1 := D.str.card_W
  have h2 := hA.card
  have h3 := D.str.card_E
  exact Subgroup.eq_of_le_of_card_ge hAW' (by omega)

private theorem conj_E_mem {x e : G} (hx : x ∈ Q) (he : e ∈ E) : x * e * x⁻¹ ∈ E := by
  have h := D.facts.rq x (D.str.QR hx) e (D.str.WQ (D.str.EW he))
  have := E.mul_mem h he
  simpa using this

private theorem sq_mem_E {x : G} (hx : x ∈ Q) : x ^ 2 ∈ E :=
  D.str.ZE (D.facts.sqZ x (D.str.QR hx))

end Helpers

variable (Φ : ↥(fz410M R E) →* Equiv.Perm (Fz410Om E P Q))
  (hΦ : ∀ (n : ↥(fz410M R E)) (A : Fz410Om E P Q), (Φ n A).1 = fz410Cj (n : G) A.1)

include D hΦ

@[expose] def Wom : Fz410Om E P Q := ⟨W, D.W_isOm⟩

theorem act_W (n : ↥(fz410M R E)) (hn : (n : G) ∈ fzN2 t x₁ x₂) : Φ n D.Wom = D.Wom := by
  apply Subtype.ext
  rw [hΦ n D.Wom]
  show fz410Cj (n : G) W = W
  have hnW : (n : G) ∈ normalizer (W : Set G) := by
    rw [D.hW]
    exact hn
  ext x
  rw [mem_fz410Cj]
  have := Subgroup.mem_normalizer_iff.mp ((normalizer (W : Set G)).inv_mem hnW) x
  simpa using this.symm

theorem act_rho_ne_one : Φ ⟨rho, D.rho_mem_M⟩ ≠ 1 := by
  intro h1
  have hcard : Nat.card (Fz410Om E P Q) = 4 := D.card_Om
  haveI : Finite (Fz410Om E P Q) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Nontrivial (Fz410Om E P Q) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨A₁, hA₁⟩ := exists_ne D.Wom
  have hA₁W : A₁.1 ≠ W := fun h => hA₁ (Subtype.ext h)
  have hfix : ∀ x ∈ A₁.1, rho * x * rho⁻¹ ∈ A₁.1 := by
    intro x hx
    have h2 : (Φ ⟨rho, D.rho_mem_M⟩ A₁).1 = A₁.1 := by rw [h1]; rfl
    rw [hΦ ⟨rho, D.rho_mem_M⟩ A₁] at h2
    have h3 : rho * x * rho⁻¹ ∈ fz410Cj rho A₁.1 := by
      rw [mem_fz410Cj]
      simpa [mul_assoc] using hx
    rwa [h2] at h3
  obtain ⟨a, haA, haE, hab⟩ := D.isOm_index_two A₁.2
  have haQ : a ∈ Q := A₁.2.le_Q haA
  have hbA : rho * a * rho⁻¹ ∈ A₁.1 := hfix a haA
  have hρE : rho ∈ normalizer (E : Set G) := (Subgroup.mem_inf.mp D.rho_mem_M).2
  rcases hab _ hbA with hE | hE
  · have h5 : rho * a * rho⁻¹ * a⁻¹ ∈ W := by
      have h6 : rho * a * rho⁻¹ * a⁻¹ =
          (a⁻¹ * (a * (rho * a * rho⁻¹)) * a⁻¹⁻¹) * (a⁻¹ * a⁻¹) := by group
      rw [h6]
      apply W.mul_mem
      · exact D.str.EW (D.conj_E_mem (Q.inv_mem haQ) hE)
      · have : a⁻¹ * a⁻¹ = (a ^ 2)⁻¹ := by group
        rw [this]
        exact W.inv_mem (D.str.EW (D.sq_mem_E haQ))
    have haW : a ∈ W := D.str.rho_QW a haQ h5
    exact haE (D.isOm_inf_W A₁.2 hA₁W a haA haW)
  · apply haE
    exact (Subgroup.mem_normalizer_iff.mp hρE a).mpr hE

theorem act_rho_pow : Φ ⟨rho, D.rho_mem_M⟩ ^ 3 = 1 := by
  rw [← map_pow]
  have h : (⟨rho, D.rho_mem_M⟩ : ↥(fz410M R E)) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using D.str.rho_ord
  rw [h, map_one]

theorem act_lam_sq : Φ ⟨lam, D.lam_mem_M⟩ ^ 2 = 1 := by
  rw [← map_pow]
  have h : (⟨lam, D.lam_mem_M⟩ : ↥(fz410M R E)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using D.str.lam_sq
  rw [h, map_one]

theorem act_lam_rho : Φ ⟨lam, D.lam_mem_M⟩ * Φ ⟨rho, D.rho_mem_M⟩ * (Φ ⟨lam, D.lam_mem_M⟩)⁻¹ =
    (Φ ⟨rho, D.rho_mem_M⟩)⁻¹ := by
  have h : (⟨lam, D.lam_mem_M⟩ : ↥(fz410M R E)) * ⟨rho, D.rho_mem_M⟩ * ⟨lam, D.lam_mem_M⟩⁻¹ =
      ⟨rho, D.rho_mem_M⟩⁻¹ := by
    apply Subtype.ext
    simpa using D.str.lam_rho
  calc Φ ⟨lam, D.lam_mem_M⟩ * Φ ⟨rho, D.rho_mem_M⟩ * (Φ ⟨lam, D.lam_mem_M⟩)⁻¹
      = Φ (⟨lam, D.lam_mem_M⟩ * ⟨rho, D.rho_mem_M⟩ * ⟨lam, D.lam_mem_M⟩⁻¹) := by
        rw [map_mul, map_mul, map_inv]
    _ = Φ (⟨rho, D.rho_mem_M⟩⁻¹) := by rw [h]
    _ = (Φ ⟨rho, D.rho_mem_M⟩)⁻¹ := map_inv Φ _

theorem ker_le (n : ↥(fz410M R E)) (hn : Φ n = 1) : (n : G) ∈ R := by
  have hcard : Nat.card (Fz410Om E P Q) = 4 := D.card_Om
  haveI : Finite (Fz410Om E P Q) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hnN2 : (n : G) ∈ fzN2 t x₁ x₂ := by
    have h1 : fz410Cj (n : G) W = W := by
      have h0 : (Φ n D.Wom).1 = (D.Wom).1 := by rw [hn]; rfl
      rw [hΦ n D.Wom] at h0
      exact h0
    show (n : G) ∈ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G)
    rw [← D.hW, Subgroup.mem_normalizer_iff]
    intro h
    have h2 : (n : G) * h * (n : G)⁻¹ ∈ fz410Cj (n : G) W ↔ h ∈ W := by
      rw [mem_fz410Cj]
      have : (n : G)⁻¹ * ((n : G) * h * (n : G)⁻¹) * n = h := by group
      rw [this]
    rw [h1] at h2
    exact h2.symm
  obtain ⟨r, hr, i, j, hi, hj, hnrij⟩ := D.N2_decomp (n : G) hnN2
  have hrM : r ∈ fz410M R E := D.R_le_M hr
  have hsub : n = ⟨r, hrM⟩ * ⟨rho, D.rho_mem_M⟩ ^ i * ⟨lam, D.lam_mem_M⟩ ^ j := by
    apply Subtype.ext
    simpa using hnrij
  have hr1 : Φ ⟨r, hrM⟩ = 1 := D.act_R Φ hΦ ⟨r, hrM⟩ hr
  have hprod : Φ ⟨rho, D.rho_mem_M⟩ ^ i * Φ ⟨lam, D.lam_mem_M⟩ ^ j = 1 := by
    have h2 : Φ n = Φ ⟨r, hrM⟩ * Φ ⟨rho, D.rho_mem_M⟩ ^ i * Φ ⟨lam, D.lam_mem_M⟩ ^ j := by
      rw [hsub, map_mul, map_mul, map_pow, map_pow]
    rw [hn, hr1, one_mul] at h2
    exact h2.symm
  obtain ⟨hi0, hj0⟩ := fz410_perm_faithful hcard D.Wom
    (D.act_W Φ hΦ ⟨rho, D.rho_mem_M⟩ D.rho_mem_N2)
    (D.act_W Φ hΦ ⟨lam, D.lam_mem_M⟩ D.lam_mem_N2) (D.act_rho_pow Φ hΦ)
    (D.act_rho_ne_one Φ hΦ) (D.act_lam_sq Φ hΦ) (D.act_lam_rho Φ hΦ) i j hi hj hprod
  subst hi0
  subst hj0
  rw [hnrij]
  simpa using hr

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
