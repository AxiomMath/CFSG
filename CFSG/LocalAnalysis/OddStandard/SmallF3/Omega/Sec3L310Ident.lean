module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem le_conjugate_of_isComponentIn [Finite G] (h36 : Asc82Lemma36) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {g s : G} (hs : g⁻¹ * t * g = s) (hst : s * t = t * s)
    {J : Subgroup G} (hJ : IsComponentIn J (L ⊓ centralizer ({s} : Set G))) (hJF : InFStar J) :
    J ≤ CFSG.conjugate L g := by
  subst hs
  have hS' := hS.conjugate g
  have hnorm := conjugate_eq_self_of_lemma36 h36 hS
  have hJ1 : IsComponentIn J (centralizer ({t} : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G)) :=
    hJ.of_normal_inf_centralizer hS.component.le hnorm
  rw [← centralizer_pair_eq_inf] at hJ1
  have ht2 := hS.involution
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by rw [orderOf_conjugate_eq]; exact ht2
  obtain ⟨M, hM, hJM⟩ := hS.lBalance t (g⁻¹ * t * g) ht2 hs2 hst.symm J hJ1
  have hMF : InFStar M := hS.a2 t (g⁻¹ * t * g) ht2 hs2 hst.symm J M hJ1 hM hJM hJF
  have hML : M = CFSG.conjugate L g :=
    (h36 G (g⁻¹ * t * g) (CFSG.conjugate L g) hS' (g⁻¹ * t * g) (CFSG.conjugate L g) hs2
      hS'.component (Or.inl hS'.inF)).2 M hM hMF
  have htc : t ∈ centralizer ({g⁻¹ * t * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hst.symm
  have hLt := conjugate_eq_self_of_lemma36 h36 hS' t htc
  rw [hML, hLt, sup_idem] at hJM
  exact hJM

theorem layer_le_conjugate [Finite G] (h36 : Asc82Lemma36) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {g s : G} (hs : g⁻¹ * t * g = s) (hst : s * t = t * s)
    (hF : ∀ J : Subgroup G, IsComponentIn J (L ⊓ centralizer ({s} : Set G)) → InFStar J) :
    CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({s} : Set G)) ≤ CFSG.conjugate L g :=
  inSubgroup_layer_le fun J hJ => le_conjugate_of_isComponentIn h36 hS hs hst hJ (hF J hJ)

end CFSG.OddStandard.SmallF3.Omega
