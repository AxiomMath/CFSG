module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4NotConj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4_normalizer_closure_conj (z : G) {A : Subgroup G} {m : G}
    (hm : m ∈ normalizer (A : Set G)) {b : G}
    (hb : b ∈ Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G))) :
    m * b * m⁻¹ ∈ Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G)) := by
  refine Subgroup.closure_induction
    (p := fun g _ => m * g * m⁻¹ ∈ Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G)))
    ?_ ?_ ?_ ?_ hb
  · intro x hx
    obtain ⟨hxcl, hxA⟩ := hx
    obtain ⟨h, -, rfl⟩ := hxcl
    refine Subgroup.subset_closure ⟨⟨m * h, Subgroup.mem_top _, by group⟩, ?_⟩
    exact (Subgroup.mem_set_normalizer_iff.mp hm (h * z * h⁻¹)).mp hxA
  · simpa using (Subgroup.one_mem (Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G))))
  · intro x y _ _ ihx ihy
    rw [show m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) by group]
    exact mul_mem ihx ihy
  · intro x _ ih
    rw [show m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ by group]
    exact inv_mem ih

theorem asc82Lemma48a_of (h43 : Asc82Lemma43) (h47 : Asc82Lemma47) : Asc82Lemma48a := by
  intro G _ _ t L S z hctx
  have h47' : ∃ h : G, h⁻¹ * t * h = t * z := h47 G t L S z hctx
  have hzL : z ∈ L := hctx.pocket.mem
  ext w
  constructor
  · rintro ⟨hwG, hwC⟩
    obtain ⟨h, -, rfl⟩ := hwG
    rcases h43 G t L S z hctx h⁻¹ (by simpa using hwC) with h1 | h2
    · simpa using h1
    · exfalso
      have h2' : h * z * h⁻¹ ∈ conjClassIn L (t * z) := by simpa using h2
      obtain ⟨l, hl, hlw⟩ := h2'
      exact sec4_tz_not_conj_z h43 hctx h47' (h⁻¹ * l) (by
        calc (h⁻¹ * l)⁻¹ * z * (h⁻¹ * l)
            = l⁻¹ * (h * z * h⁻¹) * l := by group
          _ = l⁻¹ * (l * (t * z) * l⁻¹) * l := by rw [hlw]
          _ = t * z := by group)
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, Subgroup.mem_top _, rfl⟩,
      hctx.component.le (mul_mem (mul_mem hl hzL) (inv_mem hl))⟩

theorem asc82Lemma48b_of (h43 : Asc82Lemma43) (h46a : Asc82Lemma46a) (h47 : Asc82Lemma47) :
    Asc82Lemma48b := by
  intro G _ _ t L S z hctx A hA
  rcases h46a G t L S z hctx A hA with ⟨⟨g, hg⟩, _⟩ | ⟨_, hAL⟩
  · exact absurd hg (sec4_tz_not_conj_z h43 hctx (h47 G t L S z hctx) g)
  · refine ⟨hAL, ?_⟩
    intro m hm b hb
    rw [hAL] at hb ⊢
    exact sec4_normalizer_closure_conj z hm hb

end CFSG.OddStandard.SmallF3.Omega
