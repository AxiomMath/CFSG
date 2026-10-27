module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43BComp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

variable {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {L₁ L₂ : Subgroup Y} {t : Y}

theorem sz32b_mem_map_conj {H : Subgroup Y} {g x : Y} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv]
  rfl

theorem sz32b_mem_normalizer_iff_map {H : Subgroup Y} {g : Y} :
    g ∈ Subgroup.normalizer (H : Set Y) ↔ H.map (MulAut.conj g).toMonoidHom = H := by
  constructor
  · intro hg
    ext x
    rw [sz32b_mem_map_conj]
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg)) x
    simpa using this.symm
  · intro hH
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := SetLike.ext_iff.1 hH (g * x * g⁻¹)
    rw [sz32b_mem_map_conj] at h1
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e] at h1
    exact h1

theorem sz32b_map_conj_mul (H : Subgroup Y) (g g' : Y) :
    H.map (MulAut.conj (g * g')).toMonoidHom =
      (H.map (MulAut.conj g').toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [sz32b_mem_map_conj, sz32b_mem_map_conj, sz32b_mem_map_conj]
  have e : g'⁻¹ * (g⁻¹ * x * g) * g' = (g * g')⁻¹ * x * (g * g') := by group
  rw [e]

theorem sz32b_map_conj_one (H : Subgroup Y) : H.map (MulAut.conj (1 : Y)).toMonoidHom = H := by
  ext x
  rw [sz32b_mem_map_conj]
  simp

theorem sz32b_map_conj_cancel (H : Subgroup Y) (g : Y) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [← sz32b_map_conj_mul, inv_mul_cancel, sz32b_map_conj_one]

theorem sz32b_map_conj_inj {H K : Subgroup Y} {g : Y}
    (hHK : H.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj g).toMonoidHom) : H = K :=
  Subgroup.map_injective (fun _ _ hab => (MulAut.conj g).injective hab) hHK

theorem sz32b_conj_L1 (h : Szh1Two Pb L₁ L₂ t) (g : Y) :
    L₁.map (MulAut.conj g).toMonoidHom = L₁ ∨ L₁.map (MulAut.conj g).toMonoidHom = L₂ :=
  h.all _ (A10B123.comp_conj h.comp₁ g)

theorem sz32b_conj_L2 (h : Szh1Two Pb L₁ L₂ t) (g : Y) :
    L₂.map (MulAut.conj g).toMonoidHom = L₁ ∨ L₂.map (MulAut.conj g).toMonoidHom = L₂ :=
  h.all _ (A10B123.comp_conj h.comp₂ g)

theorem sz32b_N1_mem_N2 (h : Szh1Two Pb L₁ L₂ t) {g : Y} (hg : g ∈ Subgroup.normalizer (L₁ : Set Y)) :
    g ∈ Subgroup.normalizer (L₂ : Set Y) := by
  rw [sz32b_mem_normalizer_iff_map] at hg ⊢
  rcases sz32b_conj_L2 h g with h2 | h2
  · exact absurd (sz32b_map_conj_inj (h2.trans hg.symm)).symm h.ne
  · exact h2

theorem sz32b_t_not_mem (h : Szh1Two Pb L₁ L₂ t) : t ∉ Subgroup.normalizer (L₁ : Set Y) := by
  intro ht
  rw [sz32b_mem_normalizer_iff_map] at ht
  exact h.ne (ht.symm.trans h.t₁)

theorem sz32b_N1_tt (h : Szh1Two Pb L₁ L₂ t) : t * t ∈ Subgroup.normalizer (L₁ : Set Y) := by
  rw [sz32b_mem_normalizer_iff_map, sz32b_map_conj_mul, h.t₁, h.t₂]

theorem sz32b_N1_split (h : Szh1Two Pb L₁ L₂ t) (g : Y) :
    g ∈ Subgroup.normalizer (L₁ : Set Y) ∨ t⁻¹ * g ∈ Subgroup.normalizer (L₁ : Set Y) := by
  rcases sz32b_conj_L1 h g with h1 | h1
  · exact Or.inl (sz32b_mem_normalizer_iff_map.2 h1)
  · refine Or.inr (sz32b_mem_normalizer_iff_map.2 ?_)
    rw [sz32b_map_conj_mul, h1, ← h.t₁, sz32b_map_conj_cancel]

theorem sz32b_N1_normal (h : Szh1Two Pb L₁ L₂ t) : (Subgroup.normalizer (L₁ : Set Y)).Normal := by
  have hidx : (Subgroup.normalizer (L₁ : Set Y)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨t, fun b => ?_⟩
    have h1 : b ∈ Subgroup.normalizer (L₁ : Set Y) ∨ b * t ∈ Subgroup.normalizer (L₁ : Set Y) := by
      rcases sz32b_N1_split h b⁻¹ with h2 | h2
      · exact Or.inl (inv_mem_iff.1 h2)
      · refine Or.inr ?_
        have := inv_mem h2
        simpa using this
    rcases h1 with h1 | h1
    · refine Or.inr ⟨h1, fun h3 => sz32b_t_not_mem h ?_⟩
      have h4 := Subgroup.mul_mem _ (inv_mem h1) h3
      simpa using h4
    · refine Or.inl ⟨h1, fun h3 => sz32b_t_not_mem h ?_⟩
      have h4 := Subgroup.mul_mem _ (inv_mem h3) h1
      simpa using h4
  exact Subgroup.normal_of_index_eq_two hidx

theorem sz32b_Pb_le_N1 (h : Szh1Two Pb L₁ L₂ t) : Pb ≤ Subgroup.normalizer (L₁ : Set Y) :=
  fun g hg => h.norm₁ g hg

theorem sz32b_sup_le_N1 (h : Szh1Two Pb L₁ L₂ t) : L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₁ : Set Y) :=
  sup_le (fun _ hv => A10B123.mem_normalizer_of_comp h.comp₁ h.comp₁ hv)
    (fun _ hv => A10B123.mem_normalizer_of_comp h.comp₂ h.comp₁ hv)

theorem sz32b_sup_normal (h : Szh1Two Pb L₁ L₂ t) : (L₁ ⊔ L₂ : Subgroup Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hle : (L₁ ⊔ L₂).map (MulAut.conj g).toMonoidHom ≤ L₁ ⊔ L₂ := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rcases sz32b_conj_L1 h g with h1 | h1 <;> rw [h1]
      · exact le_sup_left
      · exact le_sup_right
    · rcases sz32b_conj_L2 h g with h1 | h1 <;> rw [h1]
      · exact le_sup_left
      · exact le_sup_right
  exact hle (Subgroup.mem_map_of_mem _ hn)

theorem sz32b_comm (h : Szh1Two Pb L₁ L₂ t) : ∀ u ∈ L₁, ∀ v ∈ L₂, u * v = v * u :=
  A10B123.comp_commute h.comp₁ h.comp₂ h.ne

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
