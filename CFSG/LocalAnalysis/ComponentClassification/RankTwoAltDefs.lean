module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypIITransport

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup

@[expose] def fourEmb {n : ℕ} (h : 4 ≤ n) : Fin 4 ↪ Fin n := Fin.castLEEmb h

theorem fourEmb_apply {n : ℕ} (h : 4 ≤ n) (i : Fin 4) : ((fourEmb h i : Fin n) : ℕ) = i := rfl

@[expose] def kleinFour : Subgroup (Perm (Fin 4)) :=
  closure {swap 0 1 * swap 2 3, swap 0 2 * swap 1 3}

@[expose] noncomputable def rootV (n : ℕ) : Subgroup (alternatingGroup (Fin n)) :=
  if h : 4 ≤ n then
    (kleinFour.map (viaEmbeddingHom (fourEmb h))).comap (alternatingGroup (Fin n)).subtype
  else ⊥

@[expose] noncomputable def rootAlt (n : ℕ) : Subgroup (alternatingGroup (Fin n)) :=
  if h : 4 ≤ n then
    ((alternatingGroup (Fin 4)).map (viaEmbeddingHom (fourEmb h))).comap
      (alternatingGroup (Fin n)).subtype
  else ⊥

abbrev StabO {n : ℕ} (π : Perm (Fin n)) : Prop :=
  ∀ i : Fin n, 4 ≤ (π i : ℕ) ↔ 4 ≤ (i : ℕ)

@[expose] def restrictO {n : ℕ} (π : Perm (Fin n)) : Perm (Fin n) :=
  if h : StabO π then ofSubtype (π.subtypePerm (p := fun i : Fin n => 4 ≤ (i : ℕ)) h) else 1

theorem restrictO_of_stabO {n : ℕ} {π : Perm (Fin n)} (h : StabO π) :
    restrictO π = ofSubtype (π.subtypePerm (p := fun i : Fin n => 4 ≤ (i : ℕ)) h) := by
  unfold restrictO
  exact dite_eq_left h

theorem restrictO_apply_of_ge {n : ℕ} {π : Perm (Fin n)} (h : StabO π) {i : Fin n}
    (hi : 4 ≤ (i : ℕ)) : restrictO π i = π i := by
  rw [restrictO_of_stabO h, ofSubtype_apply_of_mem (p := fun i : Fin n => 4 ≤ (i : ℕ)) _ hi,
    subtypePerm_apply]

theorem restrictO_apply_of_lt {n : ℕ} {π : Perm (Fin n)} (h : StabO π) {i : Fin n}
    (hi : (i : ℕ) < 4) : restrictO π i = i := by
  rw [restrictO_of_stabO h,
    ofSubtype_apply_of_not_mem (p := fun i : Fin n => 4 ≤ (i : ℕ)) _ (by show ¬ 4 ≤ (i : ℕ); omega)]

theorem kleinFour_le_alternatingGroup : kleinFour ≤ alternatingGroup (Fin 4) := by
  rw [kleinFour, closure_le]
  rintro x (rfl | rfl) <;> exact mem_alternatingGroup.mpr (by decide)

theorem mem_rootV_iff {n : ℕ} (h : 4 ≤ n) (σ : alternatingGroup (Fin n)) :
    σ ∈ rootV n ↔ ∃ k ∈ kleinFour, viaEmbeddingHom (fourEmb h) k = (σ : Perm (Fin n)) := by
  rw [rootV, dite_eq_left h, mem_comap, Subgroup.coe_subtype, mem_map]

theorem mem_rootAlt_iff {n : ℕ} (h : 4 ≤ n) (σ : alternatingGroup (Fin n)) :
    σ ∈ rootAlt n ↔
      ∃ k ∈ alternatingGroup (Fin 4), viaEmbeddingHom (fourEmb h) k = (σ : Perm (Fin n)) := by
  rw [rootAlt, dite_eq_left h, mem_comap, Subgroup.coe_subtype, mem_map]

theorem rootV_le_rootAlt (n : ℕ) : rootV n ≤ rootAlt n := by
  by_cases h : 4 ≤ n
  · intro σ hσ
    obtain ⟨k, hk, hkσ⟩ := (mem_rootV_iff h σ).mp hσ
    exact (mem_rootAlt_iff h σ).mpr ⟨k, kleinFour_le_alternatingGroup hk, hkσ⟩
  · rw [rootV, dite_eq_right h]
    exact bot_le

end CFSG.ComponentClassification.RankTwoAlt
