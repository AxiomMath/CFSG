module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.Uniqueness.SU.SU13TA9PermE

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup

@[expose] def nua : Perm (Fin 9) := swap 1 2

@[expose] def nub : Perm (Fin 9) := swap 4 5

@[expose] def nuc : Perm (Fin 9) := swap 7 8

@[expose] def pr2 : Perm (Fin 9) := swap 0 3 * swap 1 4 * swap 2 5

@[expose] def SS : List (Perm (Fin 9)) := [pa, pa⁻¹, pb, pb⁻¹, pc, pc⁻¹]

@[expose] def Gam : List (Perm (Fin 9)) := [1, nuc, pw, pw * nuc, pw * pw, pw * pw * nuc]

@[expose] def Lam2 : List (Perm (Fin 9)) := [1, nua, pr2, pr2 * nua]

@[expose] def Lam3 : List (Perm (Fin 9)) := [1, nub]

@[expose] def InE (x : Perm (Fin 9)) : Prop := ∃ i j k : Fin 3, x = toP i j k

instance : DecidablePred InE := fun x => by unfold InE; infer_instance

theorem three_cycle_mem : ∀ i j k : Fin 3, (toP i j k).support.card = 3 → toP i j k ∈ SS := by
  decide

theorem mem_SS_of_conj {σ τ : Perm (Fin 9)} (hτ : τ.support.card = 3) (h : InE (σ * τ * σ⁻¹)) :
    σ * τ * σ⁻¹ ∈ SS := by
  obtain ⟨i, j, k, hijk⟩ := h
  have hc : (toP i j k).support.card = 3 := by
    rw [← hijk, Equiv.Perm.card_support_conj, hτ]
  rw [hijk]
  exact three_cycle_mem i j k hc

theorem card_support_pa : pa.support.card = 3 := by decide

theorem card_support_pb : pb.support.card = 3 := by decide

theorem card_support_pc : pc.support.card = 3 := by decide

theorem disjoint_pa_pc : Equiv.Perm.Disjoint pa pc := fun x => by fin_cases x <;> decide

theorem disjoint_pb_pc : Equiv.Perm.Disjoint pb pc := fun x => by fin_cases x <;> decide

theorem disjoint_pb_pa : Equiv.Perm.Disjoint pb pa := fun x => by fin_cases x <;> decide

theorem mem_SS_cases {α : Perm (Fin 9)} (h : α ∈ SS) :
    α = pa ∨ α = pa⁻¹ ∨ α = pb ∨ α = pb⁻¹ ∨ α = pc ∨ α = pc⁻¹ := by
  simpa [SS] using h

theorem gam_lookup {γ : Perm (Fin 9)} (hγ : γ ∈ SS) : ∃ l ∈ Gam, l * pc * l⁻¹ = γ := by
  rcases mem_SS_cases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pw, by simp [Gam], by decide⟩
  · exact ⟨pw * nuc, by simp [Gam], by decide⟩
  · exact ⟨pw * pw, by simp [Gam], by decide⟩
  · exact ⟨pw * pw * nuc, by simp [Gam], by decide⟩
  · exact ⟨1, by simp [Gam], by decide⟩
  · exact ⟨nuc, by simp [Gam], by decide⟩

theorem gam_norm {l : Perm (Fin 9)} (hl : l ∈ Gam) : ∀ i j k : Fin 3, InE (l⁻¹ * toP i j k * l) := by
  simp only [Gam, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem lam2_lookup {α : Perm (Fin 9)} (hα : α ∈ SS) (hd : ∀ x : Fin 9, α x = x ∨ pc x = x) :
    ∃ l ∈ Lam2, l * pa * l⁻¹ = α := by
  rcases mem_SS_cases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by simp [Lam2], by decide⟩
  · exact ⟨nua, by simp [Lam2], by decide⟩
  · exact ⟨pr2, by simp [Lam2], by decide⟩
  · exact ⟨pr2 * nua, by simp [Lam2], by decide⟩
  · exact absurd (hd 6) (by decide)
  · exact absurd (hd 6) (by decide)

theorem lam2_comm_pc {l : Perm (Fin 9)} (hl : l ∈ Lam2) : l * pc * l⁻¹ = pc := by
  simp only [Lam2, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> decide

theorem lam2_norm {l : Perm (Fin 9)} (hl : l ∈ Lam2) : ∀ i j k : Fin 3, InE (l⁻¹ * toP i j k * l) := by
  simp only [Lam2, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> decide

theorem lam3_lookup {β : Perm (Fin 9)} (hβ : β ∈ SS) (hda : ∀ x : Fin 9, β x = x ∨ pa x = x)
    (hdc : ∀ x : Fin 9, β x = x ∨ pc x = x) : ∃ l ∈ Lam3, l * pb * l⁻¹ = β := by
  rcases mem_SS_cases hβ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (hda 0) (by decide)
  · exact absurd (hda 0) (by decide)
  · exact ⟨1, by simp [Lam3], by decide⟩
  · exact ⟨nub, by simp [Lam3], by decide⟩
  · exact absurd (hdc 6) (by decide)
  · exact absurd (hdc 6) (by decide)

theorem lam3_comm {l : Perm (Fin 9)} (hl : l ∈ Lam3) : l * pa * l⁻¹ = pa ∧ l * pc * l⁻¹ = pc := by
  simp only [Lam3, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> decide

theorem conj_inv_of_conj_eq {l x : Perm (Fin 9)} (h : l * x * l⁻¹ = x) : l⁻¹ * x * l = x := by
  calc l⁻¹ * x * l = l⁻¹ * (l * x * l⁻¹) * l := by rw [h]
    _ = x := by group

theorem exists_decomp {σ : Perm (Fin 9)} (ha : InE (σ * pa * σ⁻¹)) (hb : InE (σ * pb * σ⁻¹))
    (hc : InE (σ * pc * σ⁻¹)) :
    ∃ l₁ ∈ Gam, ∃ l₂ ∈ Lam2, ∃ l₃ ∈ Lam3, ∃ i j k : Fin 3,
      σ = l₁ * l₂ * l₃ * toP i j k := by
  obtain ⟨l₁, hl₁, hl₁c⟩ := gam_lookup (mem_SS_of_conj card_support_pc hc)
  set σ₁ := l₁⁻¹ * σ with hσ₁
  have h1c : σ₁ * pc * σ₁⁻¹ = pc := by
    calc σ₁ * pc * σ₁⁻¹ = l₁⁻¹ * (σ * pc * σ⁻¹) * l₁ := by rw [hσ₁]; group
      _ = l₁⁻¹ * (l₁ * pc * l₁⁻¹) * l₁ := by rw [hl₁c]
      _ = pc := by group
  have h1a : InE (σ₁ * pa * σ₁⁻¹) := by
    have : σ₁ * pa * σ₁⁻¹ = l₁⁻¹ * (σ * pa * σ⁻¹) * l₁ := by rw [hσ₁]; group
    rw [this]
    obtain ⟨i, j, k, h⟩ := ha
    rw [h]
    exact gam_norm hl₁ i j k
  have h1a_disj : ∀ x, (σ₁ * pa * σ₁⁻¹) x = x ∨ pc x = x := by
    have := disjoint_pa_pc.conj σ₁
    rw [h1c] at this
    exact this
  obtain ⟨l₂, hl₂, hl₂a⟩ := lam2_lookup (mem_SS_of_conj card_support_pa h1a) h1a_disj
  set σ₂ := l₂⁻¹ * σ₁ with hσ₂
  have h2a : σ₂ * pa * σ₂⁻¹ = pa := by
    calc σ₂ * pa * σ₂⁻¹ = l₂⁻¹ * (σ₁ * pa * σ₁⁻¹) * l₂ := by rw [hσ₂]; group
      _ = l₂⁻¹ * (l₂ * pa * l₂⁻¹) * l₂ := by rw [hl₂a]
      _ = pa := by group
  have h2c : σ₂ * pc * σ₂⁻¹ = pc := by
    calc σ₂ * pc * σ₂⁻¹ = l₂⁻¹ * (σ₁ * pc * σ₁⁻¹) * l₂ := by rw [hσ₂]; group
      _ = l₂⁻¹ * pc * l₂ := by rw [h1c]
      _ = pc := conj_inv_of_conj_eq (lam2_comm_pc hl₂)
  have h2b : InE (σ₂ * pb * σ₂⁻¹) := by
    have : σ₂ * pb * σ₂⁻¹ = l₂⁻¹ * (l₁⁻¹ * (σ * pb * σ⁻¹) * l₁) * l₂ := by rw [hσ₂, hσ₁]; group
    rw [this]
    obtain ⟨i, j, k, h⟩ := hb
    rw [h]
    obtain ⟨i', j', k', h'⟩ := gam_norm hl₁ i j k
    rw [h']
    exact lam2_norm hl₂ i' j' k'
  have h2b_disj_a : ∀ x, (σ₂ * pb * σ₂⁻¹) x = x ∨ pa x = x := by
    have := disjoint_pb_pa.conj σ₂
    rw [h2a] at this
    exact this
  have h2b_disj_c : ∀ x, (σ₂ * pb * σ₂⁻¹) x = x ∨ pc x = x := by
    have := disjoint_pb_pc.conj σ₂
    rw [h2c] at this
    exact this
  obtain ⟨l₃, hl₃, hl₃b⟩ := lam3_lookup (mem_SS_of_conj card_support_pb h2b) h2b_disj_a h2b_disj_c
  set σ₃ := l₃⁻¹ * σ₂ with hσ₃
  have h3a : σ₃ * pa * σ₃⁻¹ = pa := by
    calc σ₃ * pa * σ₃⁻¹ = l₃⁻¹ * (σ₂ * pa * σ₂⁻¹) * l₃ := by rw [hσ₃]; group
      _ = l₃⁻¹ * pa * l₃ := by rw [h2a]
      _ = pa := conj_inv_of_conj_eq (lam3_comm hl₃).1
  have h3c : σ₃ * pc * σ₃⁻¹ = pc := by
    calc σ₃ * pc * σ₃⁻¹ = l₃⁻¹ * (σ₂ * pc * σ₂⁻¹) * l₃ := by rw [hσ₃]; group
      _ = l₃⁻¹ * pc * l₃ := by rw [h2c]
      _ = pc := conj_inv_of_conj_eq (lam3_comm hl₃).2
  have h3b : σ₃ * pb * σ₃⁻¹ = pb := by
    calc σ₃ * pb * σ₃⁻¹ = l₃⁻¹ * (σ₂ * pb * σ₂⁻¹) * l₃ := by rw [hσ₃]; group
      _ = l₃⁻¹ * (l₃ * pb * l₃⁻¹) * l₃ := by rw [hl₃b]
      _ = pb := by group
  have hcomm : ∀ x : Perm (Fin 9), σ₃ * x * σ₃⁻¹ = x → Commute σ₃ x := fun x h =>
    (mul_inv_eq_iff_eq_mul.mp h)
  obtain ⟨i, j, k, hijk⟩ := exists_toP_of_commute (hcomm pa h3a) (hcomm pb h3b) (hcomm pc h3c)
  refine ⟨l₁, hl₁, l₂, hl₂, l₃, hl₃, i, j, k, ?_⟩
  rw [← hijk, hσ₃, hσ₂, hσ₁]
  group

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
