module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def sec4D₀ (T T₁ T₂ : Subgroup G) : Set G :=
  {d | d ∈ classD T ∧ d ∈ sec4R T T₁ T₂ ∧ d ∉ T}

theorem conj_mem_classD {T : Subgroup G} {d : G} (hd : d ∈ classD T) (g : G) :
    g * d * g⁻¹ ∈ classD T := by
  obtain ⟨k, t, ht, ht1, hdk⟩ := hd
  refine ⟨k * g⁻¹, t, ht, ht1, ?_⟩
  rw [hdk]
  group

end Defs

section Closure

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.sec4D₀_subset (h : Sec4Hyp T T₁ a T₂) :
    sec4D₀ T T₁ T₂ ⊆ (sec4N T T₁ T₂ : Set G) := by
  rintro d ⟨hdD, hdR, hdT⟩
  rcases h.mem_or_mem_sec4N_of_mem_sec4R ⟨hdD, sec4R_le_normalizer_left hdR⟩ hdR with h1 | h1
  · exact absurd h1 hdT
  · exact h1

omit [Finite G] in
theorem Sec4Hyp.normIn_mid_le_closure (h : Sec4Hyp T T₁ a T₂) :
    normIn T₁ T ≤ Subgroup.closure (sec4D₀ T T₁ T₂) := by
  intro l hl
  by_cases hl1 : l = 1
  · rw [hl1]
    exact Subgroup.one_mem _
  obtain ⟨x, hx⟩ := h.pair.conj
  refine Subgroup.subset_closure ⟨mem_classD_of_mem_conjSubgroup (hx ▸ (mem_normIn.1 hl).1) hl1,
    normIn_mid_le_sec4R hl, fun hlT => hl1 ?_⟩
  have : l ∈ T ⊓ T₁ := ⟨hlT, (mem_normIn.1 hl).1⟩
  rwa [h.sec3.cfg.inf, Subgroup.mem_bot] at this

omit [Finite G] in
theorem Sec4Hyp.normIn_right_le_closure (h : Sec4Hyp T T₁ a T₂) :
    normIn T₂ T ≤ Subgroup.closure (sec4D₀ T T₁ T₂) := by
  intro l hl
  by_cases hl1 : l = 1
  · rw [hl1]
    exact Subgroup.one_mem _
  obtain ⟨g, hg⟩ := h.conj
  refine Subgroup.subset_closure ⟨mem_classD_of_mem_conjSubgroup (hg ▸ (mem_normIn.1 hl).1) hl1,
    normIn_right_le_sec4R hl, fun hlT => hl1 ?_⟩
  have : l ∈ T ⊓ T₂ := ⟨hlT, (mem_normIn.1 hl).1⟩
  rwa [h.inf_left_eq_bot, Subgroup.mem_bot] at this

theorem Sec4Hyp.normIn_left_le_closure (h : Sec4Hyp T T₁ a T₂) :
    normIn T T₁ ≤ Subgroup.closure (sec4D₀ T T₁ T₂) := by
  have hT := h.pair.wc
  obtain ⟨x, hx⟩ := h.pair.conj
  obtain ⟨y, hyT₁, hyN⟩ : ∃ y ∈ T₁, y ∉ Subgroup.normalizer (T : Set G) := by
    by_contra hcon
    have hle : T₁ ≤ Subgroup.normalizer (T : Set G) := fun y hy => by
      by_contra hy'
      exact hcon ⟨y, hy, hy'⟩
    exact h.pair.ne (eq_of_le_normalizer_of_isWC hT ⟨x, hx⟩ hle)
  intro l hl
  by_cases hl1 : l = 1
  · rw [hl1]
    exact Subgroup.one_mem _
  have hlT : l ∈ T := (mem_normIn.1 hl).1
  have hcomm : ⁅y, l⁆ ∈ normIn T₁ T := h.sec3.cfg.symm.comm_mem_normIn hyT₁ hl
  have hmem : y * l * y⁻¹ ∈ sec4D₀ T T₁ T₂ := by
    refine ⟨conj_mem_classD ⟨1, l, hlT, hl1, by group⟩ y, ?_, fun hT' => ?_⟩
    · have e : y * l * y⁻¹ = ⁅y, l⁆ * l := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (sec4R T T₁ T₂).mul_mem (normIn_mid_le_sec4R hcomm) (left_le_sec4R hlT)
    · have h1 : ⁅y, l⁆ ∈ T := by
        have e : ⁅y, l⁆ = (y * l * y⁻¹) * l⁻¹ := by
          simp only [commutatorElement_def]
        rw [e]
        exact T.mul_mem hT' (T.inv_mem hlT)
      have h2 : ⁅y, l⁆ ∈ T ⊓ T₁ := ⟨h1, (mem_normIn.1 hcomm).1⟩
      rw [h.sec3.cfg.inf, Subgroup.mem_bot] at h2
      have h3 : y * l = l * y := by
        simpa using (commutatorElement_eq_one_iff_mul_comm.1 h2)
      exact hyN (hT.centralizer_le_normalizer hlT hl1
        (Subgroup.mem_centralizer_singleton_iff.2 h3))
  have e : l = ⁅y, l⁆⁻¹ * (y * l * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.closure _).mul_mem ((Subgroup.closure _).inv_mem
    (h.normIn_mid_le_closure hcomm)) (Subgroup.subset_closure hmem)

theorem Sec4Hyp.closure_sec4D₀_eq (h : Sec4Hyp T T₁ a T₂) :
    Subgroup.closure (sec4D₀ T T₁ T₂) = sec4N T T₁ T₂ :=
  le_antisymm ((Subgroup.closure_le _).2 h.sec4D₀_subset)
    (sup_le (sup_le h.normIn_left_le_closure h.normIn_mid_le_closure) h.normIn_right_le_closure)

theorem Sec4Hyp.mem_normalizer_sec4N (h : Sec4Hyp T T₁ a T₂) {x : G}
    (hxR : x ∈ Subgroup.normalizer (sec4R T T₁ T₂ : Set G))
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) :
    x ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) := by
  rw [← h.closure_sec4D₀_eq]
  refine mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le ?_)
  refine conjSubgroup_le_of_forall_mem fun z hz => ?_
  refine Subgroup.closure_induction (p := fun z _ => x * z * x⁻¹ ∈
    Subgroup.closure (sec4D₀ T T₁ T₂)) ?_ ?_ ?_ ?_ hz
  · rintro d ⟨hdD, hdR, hdT⟩
    refine Subgroup.subset_closure ⟨conj_mem_classD hdD x, ?_, fun hT' => hdT ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hxR d).1 hdR
    · have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hxT) _).1 hT'
      simpa [mul_assoc] using this
  · simp
  · intro u v _ _ hu hv
    have e : x * (u * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hu hv
  · intro u _ hu
    have e : x * u⁻¹ * x⁻¹ = (x * u * x⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hu

end Closure

end CFSG.CGT.Timmesfeld75
