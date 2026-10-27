module

public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup
open scoped commutatorElement
open CFSG.Quasithin (perfectCore)

section Generic

variable {M : Type*} [Group M]

theorem commutatorElement_mul_left_of_mem_center {a b z : M} (hz : z ∈ center M) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hzb : z * b * z⁻¹ = b := by
    rw [← (mem_center_iff.1 hz b)]
    group
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hzb]

theorem commutatorElement_mul_right_of_mem_center {a b z : M} (hz : z ∈ center M) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_left_of_mem_center hz,
    commutatorElement_inv]

theorem eq_top_of_map_eq_top_of_perfect (hM : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = ⊤)
    {H : Subgroup M}
    (hH : H.map (QuotientGroup.mk' (center M)) = ⊤) : H = ⊤ := by
  have hdec : ∀ g : M, ∃ h ∈ H, ∃ z ∈ center M, g = h * z := by
    intro g
    have hg : QuotientGroup.mk' (center M) g ∈ H.map (QuotientGroup.mk' (center M)) :=
      hH ▸ mem_top _
    obtain ⟨h, hh, hhg⟩ := hg
    refine ⟨h, hh, h⁻¹ * g, ?_, by group⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hhg
    exact hhg
  rw [eq_top_iff, ← hM, commutator_le]
  intro a _ b _
  obtain ⟨h₁, hh₁, z₁, hz₁, rfl⟩ := hdec a
  obtain ⟨h₂, hh₂, z₂, hz₂, rfl⟩ := hdec b
  rw [commutatorElement_mul_left_of_mem_center hz₁, commutatorElement_mul_right_of_mem_center hz₂,
    commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)

theorem commutator_centralizer_map_le (T : Subgroup M) :
    ⁅centralizer ((T.map (QuotientGroup.mk' (center M)) : Subgroup (M ⧸ center M)) :
        Set (M ⧸ center M)),
      centralizer ((T.map (QuotientGroup.mk' (center M)) : Subgroup (M ⧸ center M)) :
        Set (M ⧸ center M))⁆ ≤
      (centralizer (T : Set M)).map (QuotientGroup.mk' (center M)) := by
  set π := QuotientGroup.mk' (center M) with hπ
  set A : Subgroup (M ⧸ center M) := centralizer ((T.map π : Subgroup (M ⧸ center M)) :
    Set (M ⧸ center M)) with hA
  set Ã : Subgroup M := A.comap π with hÃ
  have hÃT : ⁅Ã, T⁆ ≤ center M := by
    rw [commutator_le]
    intro a ha s hs
    have h1 : π ⁅a, s⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_centralizer_iff.1 ha (π s) ⟨s, hs, rfl⟩).symm
    rw [← QuotientGroup.ker_mk' (center M), MonoidHom.mem_ker]
    exact h1
  have hZÃ : ⁅center M, Ã⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [mem_centralizer_iff]
    intro y _
    exact (mem_center_iff.1 hz y)
  have h1 : ⁅⁅Ã, T⁆, Ã⁆ = ⊥ := eq_bot_iff.2 ((commutator_mono hÃT le_rfl).trans hZÃ.le)
  have h2 : ⁅⁅T, Ã⁆, Ã⁆ = ⊥ := by rw [commutator_comm T Ã]; exact h1
  have h3 : ⁅⁅Ã, Ã⁆, T⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  have hÃÃ : ⁅Ã, Ã⁆ ≤ centralizer (T : Set M) := by
    rw [← commutator_eq_bot_iff_le_centralizer]
    exact h3
  have hAÃ : Ã.map π = A := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) A
  rw [← hAÃ, ← map_commutator]
  exact map_mono hÃÃ

variable [Finite M]

theorem perfectCore_centralizer_map_le (T : Subgroup M) :
    perfectCore (centralizer ((T.map (QuotientGroup.mk' (center M)) :
        Subgroup (M ⧸ center M)) : Set (M ⧸ center M))) ≤
      (perfectCore (centralizer (T : Set M))).map (QuotientGroup.mk' (center M)) := by
  set A : Subgroup (M ⧸ center M) := centralizer ((T.map (QuotientGroup.mk' (center M)) :
    Subgroup (M ⧸ center M)) : Set (M ⧸ center M)) with hA
  have hP := CFSG.Quasithin.perfectCore_perfect A
  have hPA : perfectCore A ≤ ⁅A, A⁆ := by
    rw [← hP]
    exact commutator_mono (CFSG.Quasithin.perfectCore_le A) (CFSG.Quasithin.perfectCore_le A)
  have hle : perfectCore A ≤ (centralizer (T : Set M)).map (QuotientGroup.mk' (center M)) :=
    hPA.trans (commutator_centralizer_map_le T)
  rw [CFSG.Quasithin.map_perfectCore]
  exact CFSG.Quasithin.le_perfectCore_of_perfect hle hP

end Generic

end CFSG.SeitzReduction.E6Pilot
