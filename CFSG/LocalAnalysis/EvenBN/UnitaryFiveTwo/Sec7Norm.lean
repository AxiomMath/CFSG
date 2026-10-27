module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Def

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer

variable {G : Type} [Group G]

@[expose] def Data.Dsub (d : Data G) : Subgroup G :=
  ⨆ l ∈ d.L, d.K.map (MulAut.conj l).toMonoidHom

theorem mem_normalizer_of_map_conj_eq {D : Subgroup G} {x : G}
    (h : D.map (MulAut.conj x).toMonoidHom = D) : x ∈ normalizer (D : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      have : x * z * x⁻¹ = x * y * x⁻¹ := hzy
      simpa using this
    rwa [← this]

theorem mem_Dsub_of_mem_conj {d : Data G} {l : G} (hl : l ∈ d.L) {y : G}
    (hy : y ∈ d.K.map (MulAut.conj l).toMonoidHom) : y ∈ d.Dsub := by
  have := le_iSup₂ (f := fun (l : G) (_ : l ∈ d.L) => d.K.map (MulAut.conj l).toMonoidHom) l hl
  exact this hy

theorem Data.K_le_Dsub (d : Data G) : d.K ≤ d.Dsub := by
  intro y hy
  refine mem_Dsub_of_mem_conj (l := 1) d.L.one_mem ?_
  exact ⟨y, hy, by simp⟩

theorem map_conj_Dsub_le {d : Data G} {y : G} (hyL : y ∈ normalizer (d.L : Set G))
    (hyK : y ∈ normalizer (d.K : Set G)) : d.Dsub.map (MulAut.conj y).toMonoidHom ≤ d.Dsub := by
  rw [Data.Dsub, Subgroup.map_iSup]
  refine iSup_le fun l => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hl => ?_
  rintro a ⟨b, ⟨c, hc, rfl⟩, rfl⟩
  have hl' : y * l * y⁻¹ ∈ d.L := (mem_normalizer_iff.1 hyL l).1 hl
  have hyc : y * c * y⁻¹ ∈ d.K := (mem_normalizer_iff.1 hyK c).1 hc
  refine mem_Dsub_of_mem_conj (l := y * l * y⁻¹) hl' ⟨y * c * y⁻¹, hyc, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_Dsub_eq {d : Data G} {y : G} (hyL : y ∈ normalizer (d.L : Set G))
    (hyK : y ∈ normalizer (d.K : Set G)) : d.Dsub.map (MulAut.conj y).toMonoidHom = d.Dsub := by
  apply le_antisymm (map_conj_Dsub_le hyL hyK)
  intro z hz
  have h2 := map_conj_Dsub_le ((normalizer (d.L : Set G)).inv_mem hyL)
    ((normalizer (d.K : Set G)).inv_mem hyK) ⟨z, hz, rfl⟩
  refine ⟨y⁻¹ * z * y, ?_, ?_⟩
  · simpa [MulAut.conj_apply, mul_assoc] using h2
  · simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_Dsub_le_of_mem_L {d : Data G} {l₁ : G} (hl₁ : l₁ ∈ d.L) :
    d.Dsub.map (MulAut.conj l₁).toMonoidHom ≤ d.Dsub := by
  rw [Data.Dsub, Subgroup.map_iSup]
  refine iSup_le fun l => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hl => ?_
  rintro a ⟨b, ⟨c, hc, rfl⟩, rfl⟩
  refine mem_Dsub_of_mem_conj (l := l₁ * l) (d.L.mul_mem hl₁ hl) ⟨c, hc, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_Dsub_eq_of_mem_L {d : Data G} {l₁ : G} (hl₁ : l₁ ∈ d.L) :
    d.Dsub.map (MulAut.conj l₁).toMonoidHom = d.Dsub := by
  apply le_antisymm (map_conj_Dsub_le_of_mem_L hl₁)
  intro z hz
  have h2 := map_conj_Dsub_le_of_mem_L (d.L.inv_mem hl₁) ⟨z, hz, rfl⟩
  refine ⟨l₁⁻¹ * z * l₁, ?_, ?_⟩
  · simpa [MulAut.conj_apply, mul_assoc] using h2
  · simp [MulAut.conj_apply, mul_assoc]

namespace Data.Hyp

variable [Finite G] {d : Data G}

theorem centralizer_L_le_normalizer_K (h : d.Hyp) {c : G} (hc : c ∈ centralizer (d.L : Set G)) :
    c ∈ normalizer (d.K : Set G) := by
  refine d.mem_normalizer_K ?_
  have hce : c ∈ centralizer ({d.e₂} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hc d.e₂ (d.ι_mem _)).symm
  exact Subgroup.le_normalizer hce

theorem exists_mul_mem_normalizer_K (h : d.Hyp) {x : G} (hx : x ∈ d.H) :
    ∃ l ∈ d.L, ∃ n ∈ normalizer (d.K : Set G), x = l * n := by
  by_cases hσ : h.fieldFactor ⟨x, hx⟩ = 1
  · obtain ⟨l, hl, c, hc, hxlc⟩ := (h.fieldFactor_eq_one_iff ⟨x, hx⟩).1 hσ
    exact ⟨l, hl, c, h.centralizer_L_le_normalizer_K (Subgroup.mem_inf.1 hc).1, hxlc⟩
  · have hσ' : UnitaryFiveTwo.fieldFactor (h.act ⟨x, hx⟩) ≠ 1 := hσ
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fld hσ'
    have hl : d.ι s ∈ d.H := h.L_le_H (d.ι_mem s)
    have hb : (d.ι s)⁻¹ * x ∈ d.H := d.H.mul_mem (d.H.inv_mem hl) hx
    refine ⟨d.ι s, d.ι_mem s, (d.ι s)⁻¹ * x, ?_, by group⟩
    apply h.mem_normalizer_K_of_act_fld hb
    have h1 : h.act ⟨d.ι s, hl⟩ = MulAut.conj s := h.act_ι s
    have h2 : (⟨(d.ι s)⁻¹ * x, hb⟩ : d.H) = ⟨d.ι s, hl⟩⁻¹ * ⟨x, hx⟩ := rfl
    rw [h2, map_mul, map_inv, h1, hs, ← mul_assoc, ← map_inv, ← map_mul, inv_mul_cancel, map_one,
      one_mul]

theorem H_le_normalizer_Dsub (h : d.Hyp) : d.H ≤ normalizer (d.Dsub : Set G) := by
  intro x hx
  obtain ⟨l, hl, n, hn, hxn⟩ := h.exists_mul_mem_normalizer_K hx
  have hnH : n ∈ d.H := by
    have : n = l⁻¹ * x := by rw [hxn]; group
    rw [this]
    exact d.H.mul_mem (d.H.inv_mem (h.L_le_H hl)) hx
  have hcomp : (MulAut.conj x).toMonoidHom =
      (MulAut.conj l).toMonoidHom.comp (MulAut.conj n).toMonoidHom := by
    ext z
    simp [hxn, MulAut.conj_apply, mul_assoc]
  apply mem_normalizer_of_map_conj_eq
  rw [hcomp, ← Subgroup.map_map, map_conj_Dsub_eq (h.H_le_normalizer hnH) hn,
    map_conj_Dsub_eq_of_mem_L hl]

theorem map_conj_map_conj_comm {l t : G} (hlt : l * t = t * l) (M : Subgroup G) :
    (M.map (MulAut.conj l).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      (M.map (MulAut.conj t).toMonoidHom).map (MulAut.conj l).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext z
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc t * (l * z * l⁻¹) * t⁻¹ = (t * l) * z * (t * l)⁻¹ := by group
    _ = (l * t) * z * (l * t)⁻¹ := by rw [← hlt]
    _ = l * (t * z * t⁻¹) * l⁻¹ := by group

theorem Dsub_eq_nclL_sup (h : d.Hyp) {K₀ : Subgroup G} (hK : d.IsUnitaryFactor K₀) :
    d.Dsub = d.nclL K₀ ⊔ (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom := by
  have hlt : ∀ l ∈ d.L, l * d.t = d.t * l := fun l hl => mem_centralizer_iff.1 h.t_mem l hl
  apply le_antisymm
  · refine iSup₂_le fun l hl => ?_
    rw [hK.K_eq, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · exact le_sup_of_le_left (le_iSup₂_of_le l hl le_rfl)
    · rw [← map_conj_map_conj_comm (hlt l hl)]
      exact le_sup_of_le_right (Subgroup.map_mono (le_iSup₂_of_le l hl le_rfl))
  · refine sup_le ?_ ?_
    · refine iSup₂_le fun l hl => ?_
      refine le_trans ?_ (le_iSup₂_of_le l hl le_rfl)
      rw [hK.K_eq, Subgroup.map_sup]
      exact le_sup_left
    · rw [Data.nclL, Subgroup.map_iSup]
      refine iSup_le fun l => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hl => ?_
      rw [map_conj_map_conj_comm (hlt l hl)]
      refine le_trans ?_ (le_iSup₂_of_le l hl le_rfl)
      rw [hK.K_eq, Subgroup.map_sup]
      exact le_sup_right

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
