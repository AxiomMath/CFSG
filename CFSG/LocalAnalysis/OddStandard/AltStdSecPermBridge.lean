module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalAct
public import CFSG.LocalAnalysis.OddStandard.AltStdSecDefs

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup AltStdBal

section Corr

variable {X : Type} [Group X] {A : Subgroup X} {n : ℕ}

@[expose] def corr (e : A ≃* alternatingGroup (Fin n)) (T : Subgroup (Equiv.Perm (Fin n))) :
    Subgroup X :=
  ((T.comap (alternatingGroup (Fin n)).subtype).map e.symm.toMonoidHom).map A.subtype

theorem mem_corr {e : A ≃* alternatingGroup (Fin n)} {T : Subgroup (Equiv.Perm (Fin n))}
    {x : X} :
    x ∈ corr e T ↔
      ∃ ha : x ∈ A, ((e ⟨x, ha⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈ T := by
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨(e.symm b).2, ?_⟩
    have hb' : (b : Equiv.Perm (Fin n)) ∈ T := hb
    simpa using hb'
  · rintro ⟨ha, hT⟩
    exact ⟨⟨x, ha⟩, ⟨e ⟨x, ha⟩, hT, by simp⟩, rfl⟩

theorem mem_corr_of_mem {e : A ≃* alternatingGroup (Fin n)} {T : Subgroup (Equiv.Perm (Fin n))}
    {a : A} (h : ((e a : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈ T) :
    (a : X) ∈ corr e T :=
  mem_corr.2 ⟨a.2, h⟩

theorem corr_le (e : A ≃* alternatingGroup (Fin n)) (T : Subgroup (Equiv.Perm (Fin n))) :
    corr e T ≤ A := fun _ hx => (mem_corr.1 hx).1

theorem corr_mono (e : A ≃* alternatingGroup (Fin n)) {T T' : Subgroup (Equiv.Perm (Fin n))}
    (h : T ≤ T') : corr (X := X) e T ≤ corr e T' := fun _ hx => by
  obtain ⟨ha, hT⟩ := mem_corr.1 hx
  exact mem_corr.2 ⟨ha, h hT⟩

noncomputable def corrEquiv (e : A ≃* alternatingGroup (Fin n))
    {T : Subgroup (Equiv.Perm (Fin n))} (hT : T ≤ alternatingGroup (Fin n)) :
    (corr (X := X) e T) ≃* T :=
  (Subgroup.equivMapOfInjective _ A.subtype A.subtype_injective).symm.trans <|
    (Subgroup.equivMapOfInjective _ e.symm.toMonoidHom e.symm.injective).symm.trans <|
      Subgroup.subgroupOfEquivOfLe hT

end Corr

section Rho

variable {X : Type} [Group X] {A : Subgroup X} {n : ℕ} (e : A ≃* alternatingGroup (Fin n))
  (hn : 8 ≤ n)

theorem rho_conj_apply {x : X} (hx : x ∈ normalizer (A : Set X)) (a b : A)
    (hab : (b : X) = x * a * x⁻¹) :
    rho e hn ⟨x, hx⟩ * (e a : Equiv.Perm (Fin n)) * (rho e hn ⟨x, hx⟩)⁻¹ =
      (e b : Equiv.Perm (Fin n)) := by
  have h1 := rho_conj e hn ⟨x, hx⟩ (e a)
  have h2 : (⟨x * ((e.symm (e a) : A) : X) * x⁻¹,
      (mem_normalizer_iff.mp hx _).mp (e.symm (e a)).2⟩ : A) = b := by
    apply Subtype.ext
    simp [hab]
  rw [h2] at h1
  exact h1

theorem mem_normalizer_corr {T : Subgroup (Equiv.Perm (Fin n))} {c : X}
    (hc : c ∈ normalizer (A : Set X))
    (hT : rho e hn ⟨c, hc⟩ ∈ normalizer (T : Set (Equiv.Perm (Fin n)))) :
    c ∈ normalizer (corr e T : Set X) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxA, hxT⟩ := mem_corr.1 hx
    have hcx : c * x * c⁻¹ ∈ A := (mem_normalizer_iff.1 hc x).1 hxA
    refine mem_corr.2 ⟨hcx, ?_⟩
    have h1 := rho_conj_apply e hn hc ⟨x, hxA⟩ ⟨c * x * c⁻¹, hcx⟩ rfl
    rw [← h1]
    exact (mem_normalizer_iff.1 hT _).1 hxT
  · intro hx
    obtain ⟨hcx, hxT⟩ := mem_corr.1 hx
    have hxA : x ∈ A := (mem_normalizer_iff.1 hc x).2 hcx
    refine mem_corr.2 ⟨hxA, ?_⟩
    have h1 := rho_conj_apply e hn hc ⟨x, hxA⟩ ⟨c * x * c⁻¹, hcx⟩ rfl
    rw [← h1] at hxT
    exact (mem_normalizer_iff.1 hT _).2 hxT

theorem rho_mem_centralizer {T : Subgroup (Equiv.Perm (Fin n))}
    (hTalt : T ≤ alternatingGroup (Fin n)) {c : X} (hc : c ∈ normalizer (A : Set X))
    (hcT : c ∈ centralizer (corr e T : Set X)) :
    rho e hn ⟨c, hc⟩ ∈ centralizer (T : Set (Equiv.Perm (Fin n))) := by
  rw [mem_centralizer_iff]
  intro g hg
  set a₀ : A := e.symm ⟨g, hTalt hg⟩ with ha₀
  have hea₀ : e a₀ = ⟨g, hTalt hg⟩ := by simp [ha₀]
  have ha₀T : (a₀ : X) ∈ corr e T := by
    apply mem_corr_of_mem
    rw [hea₀]
    exact hg
  have hcomm : (a₀ : X) * c = c * a₀ := mem_centralizer_iff.1 hcT _ ha₀T
  have hab : (a₀ : X) = c * a₀ * c⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hcomm
  have h1 := rho_conj_apply e hn hc a₀ a₀ hab
  rw [hea₀] at h1
  have h2 : rho e hn ⟨c, hc⟩ * g = g * rho e hn ⟨c, hc⟩ := by
    have h3 : rho e hn ⟨c, hc⟩ * g * (rho e hn ⟨c, hc⟩)⁻¹ = g := h1
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3
  exact h2.symm

theorem mem_zpowers_of_rho_eq_one {t : X} (h : ExactShape t A n) {c : X}
    (hc : c ∈ centralizer ({t} : Set X))
    (h1 : rho e hn ⟨c, h.cent_le_norm hc⟩ = 1) : c ∈ zpowers t := by
  have hcA : c ∈ centralizer (A : Set X) :=
    (rho_eq_one_iff e hn ⟨c, h.cent_le_norm hc⟩).1 h1
  rw [← h.cent_cent]
  exact Subgroup.mem_inf.2 ⟨hcA, hc⟩

end Rho

end CFSG.OddStandard.AltStdSec
