module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1SigmaRTypeD

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open scoped Pointwise

theorem exists_mem_conj_mem_of_not_dvd_relIndex {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P H : Subgroup G} (hP : IsPGroup p P) (hidx : ¬ p ∣ P.relIndex H) {h : G}
    (hh : ∀ t ∈ P, h * t * h⁻¹ ∈ H) : ∃ c ∈ H, ∀ t ∈ P, c * h * t * (c * h)⁻¹ ∈ P := by
  classical
  let P₁ : Sylow p H := (hP.comap_subtype (K := H)).toSylow hidx
  have hQ : IsPGroup p ((P.map (MulAut.conj h).toMonoidHom).subgroupOf H) :=
    (hP.map _).comap_subtype
  obtain ⟨P₂, hP₂⟩ := hQ.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H P₂ P₁
  refine ⟨c, c.2, fun t ht => ?_⟩
  have h1 : (⟨h * t * h⁻¹, hh t ht⟩ : H) ∈ P₂ :=
    hP₂ (Subgroup.mem_subgroupOf.mpr ⟨t, ht, rfl⟩)
  have h2 : MulAut.conj c • (⟨h * t * h⁻¹, hh t ht⟩ : H) ∈
      ((c • P₂ : Sylow p H) : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
  rw [hc] at h2
  simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using Subgroup.mem_subgroupOf.mp h2

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x m : G}

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G]
include hb

omit hb [Finite G] in
theorem conj_forty_of_mem_e1M0 {g : G ⧸ Z} (hg : g ∈ e1M0 Z (u * (x * u * x⁻¹))) :
    g * caseC3Word Z u m y x 40 * g⁻¹ = caseC3Word Z u m y x 40 := by
  rw [caseC3Word_forty, Subgroup.mem_centralizer_singleton_iff.mp (e1M0_le_centralizer hg),
    mul_inv_cancel_right]

theorem conj_eq_of_mem_e1M0_of_not_typeD (htype : ¬ ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s)
    (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) {h r : G ⧸ Z}
    (hh : h ∈ e1M0 Z (u * (x * u * x⁻¹))) (hr : r ∈ e1RBar Z u m y x)
    (hhr : h * r * h⁻¹ ∈ e1RBar Z u m y x) :
    h * r * h⁻¹ = r ∨ h * r * h⁻¹ = r * caseC3Word Z u m y x 40 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ζ := caseC3Word Z u m y x 40 with hζdef
  set M₀ := e1M0 Z (u * (x * u * x⁻¹)) with hM₀
  set s := h * r * h⁻¹ with hs
  have hζ := hb.forty_mul_self
  let C : Subgroup (G ⧸ Z) :=
    { carrier := {g | g ∈ M₀ ∧ (g * s * g⁻¹ = s ∨ g * s * g⁻¹ = s * ζ)}
      mul_mem' := fun {a b} ha hb' =>
        ⟨M₀.mul_mem ha.1 hb'.1, conj_mul_conj_mod hζ (conj_forty_of_mem_e1M0 ha.1) hb'.2 ha.2⟩
      one_mem' := ⟨M₀.one_mem, Or.inl (by group)⟩
      inv_mem' := fun {a} ha =>
        ⟨M₀.inv_mem ha.1, conj_inv_conj_mod hζ (conj_forty_of_mem_e1M0 ha.1) ha.2⟩ }
  have hRC : e1RBar Z u m y x ≤ C := fun t ht =>
    ⟨hb.e1RBar_le_e1M0 ht, hb.conj_of_mem_e1RBar ht hhr⟩
  have hCM : C ≤ M₀ := fun g hg => hg.1
  have hidx : ¬ 2 ∣ (e1RBar Z u m y x).relIndex C := fun h2 =>
    hb.not_two_dvd_relIndex S' hS' (by
      rw [← Subgroup.relIndex_mul_relIndex _ _ _ hRC hCM]
      exact dvd_mul_of_dvd_left h2 _)
  have hhC : ∀ t ∈ e1RBar Z u m y x, h * t * h⁻¹ ∈ C := by
    intro t ht
    have htM := hb.e1RBar_le_e1M0 ht
    refine ⟨M₀.mul_mem (M₀.mul_mem hh htM) (M₀.inv_mem hh), ?_⟩
    rw [hs, show h * t * h⁻¹ * (h * r * h⁻¹) * (h * t * h⁻¹)⁻¹ = h * (t * r * t⁻¹) * h⁻¹ by
      group]
    rcases hb.conj_of_mem_e1RBar ht hr with h1 | h1 <;> rw [h1]
    · exact Or.inl rfl
    · right
      rw [show h * (r * ζ) * h⁻¹ = h * r * h⁻¹ * (h * ζ * h⁻¹) by group,
        conj_forty_of_mem_e1M0 hh]
  obtain ⟨c, hcC, hc⟩ :=
    exists_mem_conj_mem_of_not_dvd_relIndex hb.isPGroup_e1RBar hidx hhC
  have hn : c * h ∈ e1NBar Z u m y x :=
    ⟨M₀.mul_mem (hCM hcC) hh, mem_normalizer_of_forall_conj_mem hc⟩
  have hnr := hb.conj_of_mem_e1NBar_of_not_typeD htype S' hS' hn hr
  rw [show c * h * r * (c * h)⁻¹ = c * s * c⁻¹ by rw [hs]; group] at hnr
  have hζζ : ∀ a : G ⧸ Z, a * ζ * ζ = a := fun a => by rw [mul_assoc, hζ, mul_one]
  rcases hcC.2 with h1 | h1 <;> rw [h1] at hnr
  · rcases hnr with h2 | h2
    · exact Or.inl h2
    · exact Or.inr h2
  · rcases hnr with h2 | h2
    · right
      rw [← hζζ s, h2]
    · left
      rw [← hζζ s, h2, hζζ]

theorem conj_eq_of_mem_centralizer_of_not_typeD (htype : ¬ ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s)
    (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) {h : G ⧸ Z}
    (hh : h ∈ Subgroup.centralizer {caseC3Word Z u m y x 40})
    (hhu : h * (u : G ⧸ Z) * h⁻¹ ∈ S.map (QuotientGroup.mk' Z)) :
    h * (u : G ⧸ Z) * h⁻¹ = u ∨ h * (u : G ⧸ Z) * h⁻¹ = ((x * u * x⁻¹ : G) : G ⧸ Z) := by
  set M₀ := e1M0 Z (u * (x * u * x⁻¹)) with hM₀
  rw [caseC3Word_forty] at hh
  obtain ⟨h', hh'M, hh'⟩ : ∃ h' ∈ M₀, h' * (u : G ⧸ Z) * h'⁻¹ = h * (u : G ⧸ Z) * h⁻¹ := by
    by_cases hhM : h ∈ M₀
    · exact ⟨h, hhM, rfl⟩
    refine ⟨h * caseC3Word Z u m y x 16, mul_mem_e1M0_of_not_mem hb.partC.center hb.mem_iff hh
      (hb.caseC3Word_mem_centralizer 16) hhM hb.sixteen_not_mem_e1M0, ?_⟩
    rw [show h * caseC3Word Z u m y x 16 * (u : G ⧸ Z) * (h * caseC3Word Z u m y x 16)⁻¹ =
        h * (caseC3Word Z u m y x 16 * (u : G ⧸ Z) * (caseC3Word Z u m y x 16)⁻¹) * h⁻¹ by
        group, ← caseC3Word_thirtytwo (Z := Z) (m := m) (y := y) (x := x), hb.caseC3Word_conj,
      show c3Conj 16 32 = 32 by decide]
  have hu : (u : G ⧸ Z) ∈ e1RBar Z u m y x := by
    rw [← caseC3Word_thirtytwo (Z := Z) (m := m) (y := y) (x := x)]
    exact hb.caseC3Word_mem_e1RBar_iff.mpr (by decide)
  have hsR : h' * (u : G ⧸ Z) * h'⁻¹ ∈ e1RBar Z u m y x := by
    rw [← hb.e1M0_inf_map_top]
    exact ⟨M₀.mul_mem (M₀.mul_mem hh'M (hb.e1RBar_le_e1M0 hu)) (M₀.inv_mem hh'M), hh' ▸ hhu⟩
  rw [← hh']
  rcases hb.conj_eq_of_mem_e1M0_of_not_typeD htype S' hS' hh'M hu hsR with h1 | h1
  · exact Or.inl h1
  · right
    rw [h1, ← caseC3Word_thirtytwo (Z := Z) (m := m) (y := y) (x := x), hb.caseC3Word_mul,
      show c3Mul 32 40 = 8 by decide, caseC3Word_eight]

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
