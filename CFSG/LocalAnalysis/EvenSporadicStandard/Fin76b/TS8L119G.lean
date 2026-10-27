module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119A

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G} (c : OI13Ctx L z t T E B β S α σ)

include c

theorem Zs_card : Nat.card ↥c.Zs = 4 := by
  have hset : (c.Zs : Set G) = {1, t, α, α * t} := by
    ext a
    simp only [SetLike.mem_coe, c.mem_Zs, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hcard : Nat.card ↥c.Zs = (c.Zs : Set G).ncard := rfl
  rw [hcard, hset]
  have f01 : (1 : G) ≠ t := fun h => c.h.t_ne h.symm
  have f02 : (1 : G) ≠ α := fun h => c.hα.ne_one h.symm
  have f03 : (1 : G) ≠ α * t := fun h => (c.h.alpha_t_ne c.hα).1 h.symm
  have f12 : t ≠ α := fun h => c.hα.ne_t h.symm
  have f13 : t ≠ α * t := fun h =>
    c.hα.ne_one (mul_right_cancel (h.symm.trans (one_mul t).symm))
  have f23 : α ≠ α * t := fun h => c.h.t_ne (mul_left_cancel ((mul_one α).trans h)).symm
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_singleton]
  all_goals first
    | exact Set.toFinite _
    | simp [f01, f02, f03, f12, f13, f23, f01.symm, f02.symm, f03.symm, f12.symm, f13.symm,
        f23.symm]

theorem comm_Qs_mem {q q' : G} (hq : q ∈ c.Qs) (hq' : q' ∈ c.Qs) :
    q * q' * q⁻¹ * q'⁻¹ ∈ c.Zs := by
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := c.Qs_eq_prod hq
  obtain ⟨w₁', hw₁', w₂', hw₂', rfl⟩ := c.Qs_eq_prod hq'
  have hA : w₁ * w₁' * w₁⁻¹ * w₁'⁻¹ ∈ c.Zs := c.comm_W1_mem hw₁ hw₁'
  have hB : w₂ * w₂' * w₂⁻¹ * w₂'⁻¹ ∈ c.Zs := c.comm_W2_mem hw₂ hw₂'
  have hw12 : w₁' * w₁ ∈ c.Qs := mul_mem (c.W1_le_Qs hw₁') (c.W1_le_Qs hw₁)
  have e1 : w₂ * w₁' = w₁' * w₂ := (c.W1_comm_W2 hw₁' hw₂).symm
  have e2 : w₁ * w₂' = w₂' * w₁ := c.W1_comm_W2 hw₁ hw₂'
  have hcen : (w₂ * w₂' * w₂⁻¹ * w₂'⁻¹) * (w₁' * w₁) = (w₁' * w₁) * (w₂ * w₂' * w₂⁻¹ * w₂'⁻¹) :=
    c.Zs_comm_Qs hB hw12
  have key : w₁ * w₂ * (w₁' * w₂') =
      (w₁ * w₁' * w₁⁻¹ * w₁'⁻¹) * (w₂ * w₂' * w₂⁻¹ * w₂'⁻¹) * (w₁' * w₂' * (w₁ * w₂)) := by
    calc w₁ * w₂ * (w₁' * w₂') = w₁ * (w₂ * w₁') * w₂' := by group
      _ = w₁ * (w₁' * w₂) * w₂' := by rw [e1]
      _ = (w₁ * w₁') * (w₂ * w₂') := by group
      _ = ((w₁ * w₁' * w₁⁻¹ * w₁'⁻¹) * (w₁' * w₁)) *
            ((w₂ * w₂' * w₂⁻¹ * w₂'⁻¹) * (w₂' * w₂)) := by group
      _ = (w₁ * w₁' * w₁⁻¹ * w₁'⁻¹) * ((w₁' * w₁) * (w₂ * w₂' * w₂⁻¹ * w₂'⁻¹)) * (w₂' * w₂) := by
          group
      _ = (w₁ * w₁' * w₁⁻¹ * w₁'⁻¹) * ((w₂ * w₂' * w₂⁻¹ * w₂'⁻¹) * (w₁' * w₁)) * (w₂' * w₂) := by
          rw [← hcen]
      _ = (w₁ * w₁' * w₁⁻¹ * w₁'⁻¹) * (w₂ * w₂' * w₂⁻¹ * w₂'⁻¹) *
            ((w₁' * w₁) * (w₂' * w₂)) := by group
      _ = (w₁ * w₁' * w₁⁻¹ * w₁'⁻¹) * (w₂ * w₂' * w₂⁻¹ * w₂'⁻¹) *
            (w₁' * (w₁ * w₂') * w₂) := by group
      _ = (w₁ * w₁' * w₁⁻¹ * w₁'⁻¹) * (w₂ * w₂' * w₂⁻¹ * w₂'⁻¹) *
            (w₁' * (w₂' * w₁) * w₂) := by rw [e2]
      _ = (w₁ * w₁' * w₁⁻¹ * w₁'⁻¹) * (w₂ * w₂' * w₂⁻¹ * w₂'⁻¹) *
            (w₁' * w₂' * (w₁ * w₂)) := by group
  have e3 : w₁ * w₂ * (w₁' * w₂') * (w₁ * w₂)⁻¹ * (w₁' * w₂')⁻¹ =
      (w₁ * w₁' * w₁⁻¹ * w₁'⁻¹) * (w₂ * w₂' * w₂⁻¹ * w₂'⁻¹) := by
    rw [key]
    group
  rw [e3]
  exact mul_mem hA hB

theorem sq_Qs_mem {q : G} (hq : q ∈ c.Qs) : q * q ∈ c.Zs := by
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := c.Qs_eq_prod hq
  have e : w₂ * w₁ = w₁ * w₂ := (c.W1_comm_W2 hw₁ hw₂).symm
  have e' : w₁ * w₂ * (w₁ * w₂) = (w₁ * w₁) * (w₂ * w₂) := by
    calc w₁ * w₂ * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
      _ = w₁ * (w₁ * w₂) * w₂ := by rw [e]
      _ = (w₁ * w₁) * (w₂ * w₂) := by group
  rw [e']
  exact mul_mem (c.sq_W1_mem hw₁) (c.sq_W2_mem hw₂)

theorem card_innE : Nat.card ↥(innAutE E) = 16 := by
  let conjE : ↥E →* MulAut ↥E := MulAut.conj
  have h1 := Subgroup.card_ker_mul_card_range conjE
  have ht : t ∈ E := c.h.t_mem_E
  have hker : (conjE.ker : Set ↥E) = {1, ⟨t, ht⟩} := by
    ext e
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro he
      have hcomm : ∀ f ∈ E, f * (e : G) = e * f := by
        intro f hf
        have he' : (MulAut.conj e : MulAut ↥E) = 1 := he
        have := congrArg (fun φ : MulAut ↥E => ((φ ⟨f, hf⟩ : ↥E) : G)) he'
        have h5 : (e : G) * f * (e : G)⁻¹ = f := by
          simpa [MulAut.conj_apply] using this
        calc f * (e : G) = (e * f * (e : G)⁻¹) * e := by rw [h5]
          _ = e * f := by group
      rcases c.h.oe.econfig.center e e.2 hcomm with h2 | h2
      · exact Or.inl (Subtype.ext h2)
      · exact Or.inr (Subtype.ext h2)
    · rintro (rfl | rfl)
      · exact map_one conjE
      · refine MulEquiv.ext fun f => ?_
        apply Subtype.ext
        show t * (f : G) * t⁻¹ = f
        have := c.h.t_comm_E (e := (f : G)) f.2
        calc t * (f : G) * t⁻¹ = (t * f) * t⁻¹ := rfl
          _ = f := by rw [← this]; group
  have h2 : Nat.card conjE.ker = 2 := by
    have h3 : Nat.card ↥(conjE.ker : Set ↥E) = 2 := by
      rw [Nat.card_coe_set_eq, hker]
      exact Set.ncard_pair (fun h => c.h.t_ne (congrArg Subtype.val h).symm)
    exact h3
  have hE : Nat.card ↥E = 32 := c.h.wf.card_E
  show Nat.card conjE.range = 16
  rw [h2, hE] at h1
  omega

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
