module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecPermBridge
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPerm

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup AltStdBal

section Generic

variable {X : Type} [Group X] {A : Subgroup X} {n : ℕ} (e : A ≃* alternatingGroup (Fin n))

omit [Group X] in
theorem card_compl_fin (S : Finset (Fin n)) : Sᶜ.card = n - S.card := by
  rw [Finset.card_compl, Fintype.card_fin]

theorem corr_comm {T₁ T₂ : Subgroup (Equiv.Perm (Fin n))}
    (hcomm : ∀ g ∈ T₁, ∀ h ∈ T₂, g * h = h * g) :
    ∀ r ∈ corr (X := X) e T₁, ∀ b ∈ corr (X := X) e T₂, r * b = b * r := by
  intro r hr b hb
  obtain ⟨hrA, hrT⟩ := mem_corr.1 hr
  obtain ⟨hbA, hbT⟩ := mem_corr.1 hb
  have h1 : e ⟨r, hrA⟩ * e ⟨b, hbA⟩ = e ⟨b, hbA⟩ * e ⟨r, hrA⟩ :=
    Subtype.ext (hcomm _ hrT _ hbT)
  have h2 : (⟨r, hrA⟩ * ⟨b, hbA⟩ : A) = ⟨b, hbA⟩ * ⟨r, hrA⟩ := by
    apply e.injective
    rw [map_mul, map_mul]
    exact h1
  exact congrArg Subtype.val h2

theorem corr_le_centralizer_corr {T₁ T₂ : Subgroup (Equiv.Perm (Fin n))}
    (hcomm : ∀ g ∈ T₁, ∀ h ∈ T₂, g * h = h * g) :
    corr (X := X) e T₂ ≤ A ⊓ centralizer (corr (X := X) e T₁ : Set X) := by
  intro b hb
  refine Subgroup.mem_inf.2 ⟨corr_le e T₂ hb, ?_⟩
  rw [mem_centralizer_iff]
  intro r hr
  exact corr_comm e hcomm r hr b hb

theorem t_mem_centralizer_corr {t : X} (h : ExactShape t A n) (T : Subgroup (Equiv.Perm (Fin n))) :
    t ∈ centralizer (corr (X := X) e T : Set X) := by
  rw [mem_centralizer_iff]
  intro r hr
  exact mem_centralizer_singleton_iff.1 (h.le_cent (corr_le e T hr))

theorem exists_equiv_corr_altSub (S : Finset (Fin n)) :
    Nonempty (corr (X := X) e (altSub S) ≃* alternatingGroup (Fin S.card)) :=
  ⟨(corrEquiv e (altSub_le_alternatingGroup S)).trans (altSubEquiv S)⟩

end Generic

section Hyps

variable {X : Type} [Group X] {A : Subgroup X} {n : ℕ} {t : X} (e : A ≃* alternatingGroup (Fin n))
  (hn : 8 ≤ n) (h : ExactShape t A n)

include hn h in
theorem hnorm_of_perm {R' T : Subgroup (Equiv.Perm (Fin n))} (hR' : R' ≤ alternatingGroup (Fin n))
    (hRT : ∀ σ ∈ centralizer (R' : Set (Equiv.Perm (Fin n))),
      σ ∈ normalizer (T : Set (Equiv.Perm (Fin n)))) :
    centralizer ({t} : Set X) ⊓ centralizer (corr (X := X) e R' : Set X) ≤
      normalizer (corr (X := X) e T : Set X) := by
  intro c hc
  obtain ⟨hct, hcR⟩ := Subgroup.mem_inf.1 hc
  have hcN := h.cent_le_norm hct
  exact mem_normalizer_corr e hn hcN (hRT _ (rho_mem_centralizer e hn hR' hcN hcR))

include hn h in
theorem hcc_of_perm {R' T : Subgroup (Equiv.Perm (Fin n))} (hR' : R' ≤ alternatingGroup (Fin n))
    (hT : T ≤ alternatingGroup (Fin n))
    (htriv : ∀ σ ∈ centralizer (T : Set (Equiv.Perm (Fin n))),
      σ ∈ centralizer (R' : Set (Equiv.Perm (Fin n))) → σ = 1) :
    centralizer (corr (X := X) e T : Set X) ⊓ centralizer ({t} : Set X) ⊓
      centralizer (corr (X := X) e R' : Set X) ≤ zpowers t := by
  intro c hc
  obtain ⟨⟨hcB, hct⟩, hcR⟩ := (Subgroup.mem_inf.1 hc).imp_left Subgroup.mem_inf.1
  have hcN := h.cent_le_norm hct
  refine mem_zpowers_of_rho_eq_one e hn h hct (htriv _ ?_ ?_)
  · exact rho_mem_centralizer e hn hT hcN hcB
  · exact rho_mem_centralizer e hn hR' hcN hcR

include hn h in
theorem hcc_of_perm_le {R' T : Subgroup (Equiv.Perm (Fin n))} (hR' : R' ≤ alternatingGroup (Fin n))
    (hT : T ≤ alternatingGroup (Fin n))
    (hle : ∀ σ ∈ centralizer (T : Set (Equiv.Perm (Fin n))),
      σ ∈ centralizer (R' : Set (Equiv.Perm (Fin n))) → σ ∈ R') :
    centralizer (corr (X := X) e T : Set X) ⊓ centralizer ({t} : Set X) ⊓
      centralizer (corr (X := X) e R' : Set X) ≤ zpowers t ⊔ corr (X := X) e R' := by
  intro c hc
  obtain ⟨⟨hcB, hct⟩, hcR⟩ := (Subgroup.mem_inf.1 hc).imp_left Subgroup.mem_inf.1
  have hcN := h.cent_le_norm hct
  have hσR : rho e hn ⟨c, hcN⟩ ∈ R' :=
    hle _ (rho_mem_centralizer e hn hT hcN hcB) (rho_mem_centralizer e hn hR' hcN hcR)
  set a₀ : A := e.symm ⟨rho e hn ⟨c, hcN⟩, hR' hσR⟩ with ha₀
  have hea₀ : e a₀ = ⟨rho e hn ⟨c, hcN⟩, hR' hσR⟩ := by simp [ha₀]
  have ha₀R : (a₀ : X) ∈ corr e R' := by
    apply mem_corr_of_mem
    rw [hea₀]
    exact hσR
  have ha₀C : (a₀ : X) ∈ centralizer ({t} : Set X) := h.le_cent a₀.2
  have hrho : rho e hn ⟨(a₀ : X), Subgroup.le_normalizer a₀.2⟩ = rho e hn ⟨c, hcN⟩ := by
    rw [rho_of_mem e hn a₀ (Subgroup.le_normalizer a₀.2), hea₀]
  have hca : c * (a₀ : X)⁻¹ ∈ centralizer ({t} : Set X) := mul_mem hct (inv_mem ha₀C)
  have hker : rho e hn ⟨c * (a₀ : X)⁻¹, h.cent_le_norm hca⟩ = 1 := by
    have : (⟨c * (a₀ : X)⁻¹, h.cent_le_norm hca⟩ : normalizer (A : Set X)) =
        ⟨c, hcN⟩ * (⟨(a₀ : X), Subgroup.le_normalizer a₀.2⟩)⁻¹ := rfl
    rw [this, map_mul, map_inv, hrho, mul_inv_cancel]
  have hz : c * (a₀ : X)⁻¹ ∈ zpowers t := mem_zpowers_of_rho_eq_one e hn h hca hker
  have : c = (c * (a₀ : X)⁻¹) * a₀ := by group
  rw [this]
  exact mul_mem_sup hz ha₀R

end Hyps

end CFSG.OddStandard.AltStdSec
