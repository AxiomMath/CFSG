module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47Perm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

private lemma conj_mem_closure_of_forall {m : G} {s : Set G}
    (h : ∀ x ∈ s, m * x * m⁻¹ ∈ s) {b : G} (hb : b ∈ Subgroup.closure s) :
    m * b * m⁻¹ ∈ Subgroup.closure s := by
  induction hb using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (h x hx)
  | one => simpa using Subgroup.one_mem (Subgroup.closure s)
  | mul x y hx hy ihx ihy =>
      rw [show m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) by group]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih =>
      rw [show m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ih

theorem Sec4FSetup.actHom_eq_one_iff (h : Sec4FSetup t L S z A B φ)
    (m : ↥(normalizer (A : Set G))) : h.actHom m = 1 ↔ (m : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro hm1
    exact (h.mem_centralizer_iff_realizes_one).mpr (by simpa [hm1] using h.actHom_spec m)
  · intro hm
    exact (h.eq_actHom m.2 ((h.mem_centralizer_iff_realizes_one).mp hm)).symm

theorem Sec4FSetup.actHom_none_iff (h : Sec4FSetup t L S z A B φ)
    (m : ↥(normalizer (A : Set G))) :
    h.actHom m none = none ↔ (m : G) ∈ centralizer ({t} : Set G) := by
  have hspec : (m : G) * t * (m : G)⁻¹ = sec4MPt t φ (h.actHom m none) := by
    have := h.actHom_spec m none
    rwa [h.pt_none] at this
  constructor
  · intro hnone
    rw [Subgroup.mem_centralizer_singleton_iff]
    have ht : (m : G) * t * (m : G)⁻¹ = t := by rw [hspec, hnone, h.pt_none]
    rw [← mul_inv_eq_iff_eq_mul]
    exact ht
  · intro hm
    apply h.pt_injective
    have ht : (m : G) * t * (m : G)⁻¹ = t := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hm]
      group
    rw [← hspec, ht, h.pt_none]

theorem Sec4FSetup.alt_le_range (h : Sec4FSetup t L S z A B φ) :
    alternatingGroup (Option (Fin 7)) ≤ h.actHom.range := by
  refine sec4S47_alt_le (R := h.actHom.range) (by decide : 3 ≤ Fintype.card (Fin 7)) ?_ ?_
  · intro q
    obtain ⟨m, ν, hm, hν, hνnone⟩ := h.exists_move_pt q
    exact ⟨h.actHom ⟨m, hm⟩, MonoidHom.mem_range.mpr ⟨⟨m, hm⟩, rfl⟩, by
      rw [← h.eq_actHom hm hν]; exact hνnone⟩
  · intro σ hσ
    obtain ⟨m, hm, hreal⟩ := h.exists_realizes_alt hσ
    exact MonoidHom.mem_range.mpr ⟨⟨m, hm⟩, (h.eq_actHom hm hreal).symm⟩

theorem Sec4FSetup.conj_mem_B (h : Sec4FSetup t L S z A B φ) {m b : G}
    (hm : m ∈ normalizer (A : Set G)) (hb : b ∈ B) : m * b * m⁻¹ ∈ B := by
  let ΔΔ : Set G := {x | ∃ p q : Option (Fin 7), x = sec4MPt t φ p * sec4MPt t φ q}
  have hΔΔB : ΔΔ ⊆ (B : Set G) := by
    rintro x ⟨p, q, rfl⟩
    rw [sec4MPt_mul h.data p q]
    exact h.data.bdata.perm.mem (isEvenVec_add (sec4MV_even p) (sec4MV_even q))
  have hBle : B ≤ Subgroup.closure ΔΔ := by
    rw [← h.data.bdata.perm.closure_conjClassIn (v := sec4MW 0) (sec4MW_even 0)
      (Or.inr (Or.inr (sec4MW_weight 0)))]
    refine (Subgroup.closure_le (Subgroup.closure ΔΔ)).mpr ?_
    rintro x hx
    rw [h.data.bdata.perm.conjClassIn_eq (sec4MW_even 0)] at hx
    obtain ⟨w, hw, hwt, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := exists_sec4MW_of_weight_six hw (hwt.trans (sec4MW_weight 0))
    have hmul : φ (sec4MW i) = sec4MPt t φ none * sec4MPt t φ (some i) := by
      rw [sec4MPt_mul h.data none (some i)]
      simp [sec4MV]
    rw [hmul]
    exact Subgroup.subset_closure ⟨none, some i, rfl⟩
  have hBcl : B = Subgroup.closure ΔΔ :=
    le_antisymm hBle ((Subgroup.closure_le B).mpr hΔΔB)
  have hconj : ∀ x ∈ ΔΔ, m * x * m⁻¹ ∈ ΔΔ := by
    rintro x ⟨p, q, rfl⟩
    refine ⟨h.actHom ⟨m, hm⟩ p, h.actHom ⟨m, hm⟩ q, ?_⟩
    rw [show m * (sec4MPt t φ p * sec4MPt t φ q) * m⁻¹
        = (m * sec4MPt t φ p * m⁻¹) * (m * sec4MPt t φ q * m⁻¹) by group,
      h.actHom_spec ⟨m, hm⟩ p, h.actHom_spec ⟨m, hm⟩ q]
  rw [hBcl] at hb ⊢
  exact conj_mem_closure_of_forall hconj hb

theorem Sec4FSetup.conj_t_mem_B (h : Sec4FSetup t L S z A B φ) {m : G}
    (hm : m ∈ normalizer (A : Set G)) : m * t * m⁻¹ * t⁻¹ ∈ B := by
  have hspec : m * t * m⁻¹ = sec4MPt t φ (h.actHom ⟨m, hm⟩ none) := by
    have := h.actHom_spec ⟨m, hm⟩ none
    rwa [h.pt_none] at this
  have htinv : t⁻¹ = sec4MPt t φ none := by
    rw [inv_eq_of_mul_eq_one_right h.t_sq]
    exact h.pt_none.symm
  rw [hspec, htinv, sec4MPt_mul h.data (h.actHom ⟨m, hm⟩ none) none]
  exact h.data.bdata.perm.mem
    (isEvenVec_add (sec4MV_even (h.actHom ⟨m, hm⟩ none)) (sec4MV_even none))

end CFSG.OddStandard.SmallF3.Omega
