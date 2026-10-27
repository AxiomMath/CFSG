module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Config
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Dichotomy

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

namespace H2Cfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G}

theorem stable_aux_B [Finite G] (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    {L : Subgroup G} (hL : IsComponent L) {w u : G} (hw : w ∈ kleinV t v)
    (hu : u ∈ kleinV t v) (hwL : w ∉ normalizer (L : Set G))
    (huL : u ∉ normalizer (L : Set G)) (hwuL : w * u ∉ normalizer (L : Set G)) : False := by
  have hw1 : w ≠ 1 := by
    intro h
    apply hwL
    rw [h]
    exact Subgroup.one_mem _
  set Lw : Subgroup G := L.map (MulAut.conj w).toMonoidHom with hLwdef
  set Lu : Subgroup G := L.map (MulAut.conj u).toMonoidHom with hLudef
  set Luw : Subgroup G := L.map (MulAut.conj (u * w)).toMonoidHom with hLuwdef
  have hLw : IsComponent Lw := by rw [hLwdef]; exact isComponent_conj hL w
  have hLu : IsComponent Lu := by rw [hLudef]; exact isComponent_conj hL u
  have hLuw : IsComponent Luw := by rw [hLuwdef]; exact isComponent_conj hL (u * w)
  have hLwne : Lw ≠ L := by
    intro h
    apply hwL
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hLwdef.symm.trans h)
  have hLune : Lu ≠ L := by
    intro h
    apply huL
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hLudef.symm.trans h)
  have hLuwne : Luw ≠ L := by
    intro h
    apply hwuL
    have hmem : u * w ∈ normalizer (L : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hLuwdef.symm.trans h)
    rw [← cfg.comm_of_mem hu hw]
    exact hmem
  have hcom_w : ∀ a ∈ L, ∀ b ∈ Lw, a * b = b * a := component_commute hL hLw hLwne.symm
  have hcom_w' : ∀ a ∈ Lw, ∀ b ∈ L, a * b = b * a := component_commute hLw hL hLwne
  have hcom_u : ∀ a ∈ Lu, ∀ b ∈ L, a * b = b * a := component_commute hLu hL hLune
  have hcom_uw : ∀ a ∈ Luw, ∀ b ∈ L, a * b = b * a := component_commute hLuw hL hLuwne
  have hall : ∀ s ∈ L, s = 1 := by
    intro s hs
    set c : G := w * s * w⁻¹ with hc_def
    set d : G := s * c with hd_def
    have hc_mem : c ∈ Lw := by
      rw [hLwdef, hc_def]
      exact ⟨s, hs, rfl⟩
    have hd_comm : w * d = d * w := by
      rw [hd_def, hc_def]
      exact swap_fixed (hz := cfg.sq_eq_one_of_mem hw) hcom_w hLwdef hs
    have hdC : d ∈ centralizer ({t} : Set G) := by
      rw [← cfg.centralizer_eq_of_mem hw hw1]
      exact mem_centralizer_singleton_iff.mpr hd_comm.symm
    have hu_d : u * d = d * u := cfg.kleinV_central hdC hu
    set a : G := u * s * u⁻¹ with ha_def
    set b : G := u * c * u⁻¹ with hb_def
    have ha_mem : a ∈ Lu := by
      rw [hLudef, ha_def]
      exact ⟨s, hs, rfl⟩
    have hb_mem : b ∈ Luw := by
      rw [hLuwdef, hb_def, hc_def]
      refine ⟨s, hs, ?_⟩
      show (u * w) * s * (u * w)⁻¹ = u * (w * s * w⁻¹) * u⁻¹
      group
    have hab : a * b = s * c := by
      have h1 : a * b = u * d * u⁻¹ := by
        rw [ha_def, hb_def, hd_def, hc_def]
        group
      have h2 : u * d * u⁻¹ = d := by
        rw [hu_d]
        group
      exact h1.trans (h2.trans hd_def)
    have hs_eq : s = a * b * c⁻¹ := by
      rw [hab]
      group
    refine eq_one_of_commute_of_simple (component_isSimple hF hL) (component_nonab hF hL) hs ?_
    intro x hx
    have hax : Commute a x := hcom_u a ha_mem x hx
    have hbx : Commute b x := hcom_uw b hb_mem x hx
    have hcw : Commute c x := hcom_w' c hc_mem x hx
    have hcx : Commute c⁻¹ x := hcw.inv_left
    have hsx : s * x = x * s := by
      rw [hs_eq]
      exact ((hax.mul_left hbx).mul_left hcx).eq
    exact hsx.symm
  obtain ⟨a', ha', b', hb', hab'⟩ := component_nonab hF hL
  exact hab' (by simp [hall a' ha', hall b' hb'])

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
