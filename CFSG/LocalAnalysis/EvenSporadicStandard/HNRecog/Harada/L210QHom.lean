module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Inputs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)
  {φ : ↥(normalizer (Rgrp h : Set G)) →* A5WrTwo}

@[expose] noncomputable def psiq (hs : Lemma27Spec h φ) :
    ↥(normalizer (Aq h : Set (Xq z))) →* A5WrTwo :=
  (MonoidHom.liftOfSurjective (piN h) (piN_surjective h))
    ⟨φ, fun x hx => by
      rw [ker_piN h] at hx
      rw [hs.ker]
      exact Subgroup.mem_subgroupOf.2
        (Subgroup.zpowers_le.2 (z_mem_Rgrp h) (Subgroup.mem_subgroupOf.1 hx))⟩

theorem psiq_piN (hs : Lemma27Spec h φ) (n : ↥(normalizer (Rgrp h : Set G))) :
    psiq h hs (piN h n) = φ n := by
  rw [psiq]
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ n

theorem psiq_surjective (hs : Lemma27Spec h φ) : Function.Surjective (psiq h hs) := by
  intro y
  obtain ⟨n, hn⟩ := hs.surj y
  exact ⟨piN h n, by rw [psiq_piN h hs n, hn]⟩

theorem ker_psiq (hs : Lemma27Spec h φ) :
    (psiq h hs).ker = (Aq h).subgroupOf (normalizer (Aq h : Set (Xq z))) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := piN_surjective h x
    rw [MonoidHom.mem_ker, psiq_piN h hs n] at hx
    have hnR : (n : G) ∈ Rgrp h := by
      have hn : n ∈ (Rgrp h).subgroupOf (normalizer (Rgrp h : Set G)) := by
        rw [← hs.ker]
        exact MonoidHom.mem_ker.mpr hx
      exact Subgroup.mem_subgroupOf.mp hn
    rw [Subgroup.mem_subgroupOf, piN_val h n]
    exact (mem_Aq_iff h ⟨(n : G), normalizer_Rgrp_le_Mgrp h n.2⟩).2 hnR
  · intro hx
    obtain ⟨n, rfl⟩ := piN_surjective h x
    rw [Subgroup.mem_subgroupOf, piN_val h n] at hx
    have hnR : (n : G) ∈ Rgrp h :=
      (mem_Aq_iff h ⟨(n : G), normalizer_Rgrp_le_Mgrp h n.2⟩).1 hx
    rw [MonoidHom.mem_ker, psiq_piN h hs n]
    exact MonoidHom.mem_ker.mp (by
      rw [hs.ker]
      exact Subgroup.mem_subgroupOf.mpr hnR)

end CFSG.EvenSporadicStandard.HNRecog.Harada
