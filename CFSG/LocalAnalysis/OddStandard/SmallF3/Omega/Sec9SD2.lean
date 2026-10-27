module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SD1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Layer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t z g : G} {L S B : Subgroup G}

theorem sec9d_B_inf_cent_conj (h82 : Asc82Lemma82) (hB8 : Asc82Sec8B)
    (h : Sec8Base G t L S z g B) : B ⊓ centralizer (CFSG.conjugate L g : Set G) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro b hb
  rw [Subgroup.mem_bot]
  obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.mp hb
  have hcyc : ∀ P : Subgroup G,
      IsSylow2Of P (centralizer (CFSG.conjugate L g : Set G)) → IsCyclic P :=
    h82 G (g⁻¹ * t * g) (CFSG.conjugate L g) (sec9d_setting_conj h) (sec9d_isOm6M_conj h).2
  rcases eq_one_or_eq_of_commute hcyc hbC (sec9d_tg_mem_cent h) (sec9d_B_sq h hbB)
      (sec9d_tg_order h) (sec9d_B_comm_tg hB8 h hbB) with h1 | hw
  · exact h1
  · exact absurd (hw ▸ hbB) (sec9d_tg_not_mem_B hB8 h)

omit [Finite G] in
theorem sec9d_layerCent_conj (L : Subgroup G) (u g : G) :
    layerCent (CFSG.conjugate L g) (g⁻¹ * u * g) = CFSG.conjugate (layerCent L u) g := by
  unfold layerCent
  rw [sec5b517_centralizer_conj u g, ← sec5b517_conjugate_inf L (centralizer ({u} : Set G)) g]
  exact sec5b517_inSubgroup_layer_conjugate (L ⊓ centralizer ({u} : Set G)) g

theorem sec9d_layerCent_conj_eq_bot (h37 : Asc82Lemma37) (hB8 : Asc82Sec8B)
    (h : Sec8Base G t L S z g B) :
    ∀ b ∈ B, orderOf b = 2 → layerCent (CFSG.conjugate L g) b = ⊥ := by
  intro b hbB hb2
  have hbne : b ≠ 1 := by
    intro hb1
    rw [hb1, orderOf_one] at hb2
    norm_num at hb2
  obtain ⟨l, hlL, hbconj⟩ := (hB8 G t L S z g B h).2 b hbB hbne
  set u : G := g * b * g⁻¹ with hu_def
  have hb_eq : b = g⁻¹ * u * g := by
    rw [hu_def]
    group
  have hc : (l⁻¹ * g⁻¹)⁻¹ * z * (l⁻¹ * g⁻¹) = u := by
    rw [hu_def, hbconj]
    group
  have huC : u ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := sec9d_B_comm_tg hB8 h hbB
    show u * t = t * u
    rw [hu_def]
    calc (g * b * g⁻¹) * t = g * (b * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * b) * g⁻¹ := by rw [hcomm]
      _ = t * (g * b * g⁻¹) := by group
  have hlayer : layerCent L u = ⊥ := by
    have h := h37 G t L h.toSec3SettingLB z (l⁻¹ * g⁻¹) h.pocket (by rw [hc]; exact huC)
    rw [hc] at h
    simpa [layerCent] using h
  rw [hb_eq]
  rw [sec9d_layerCent_conj L u g, hlayer]
  simp [CFSG.conjugate]

end CFSG.OddStandard.SmallF3.Omega
