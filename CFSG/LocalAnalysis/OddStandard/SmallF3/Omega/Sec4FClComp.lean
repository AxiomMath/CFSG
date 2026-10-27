module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem centralizer_pair_le_left' (x y : G) :
    centralizer ({x, y} : Set G) ≤ centralizer ({x} : Set G) :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (by simp))

private theorem centralizer_pair_le_right' (x y : G) :
    centralizer ({x, y} : Set G) ≤ centralizer ({y} : Set G) :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (by simp))

private theorem le_centralizer_pair' {K : Subgroup G} {x y : G}
    (hx : K ≤ centralizer ({x} : Set G)) (hy : K ≤ centralizer ({y} : Set G)) :
    K ≤ centralizer ({x, y} : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rcases hw with rfl | hw
  · exact Subgroup.mem_centralizer_iff.mp (hx hz) _ (Set.mem_singleton _)
  · rw [Set.mem_singleton_iff.mp hw]
    exact Subgroup.mem_centralizer_iff.mp (hy hz) _ (Set.mem_singleton _)

private theorem isSubnormal_subgroupOf_of_le {C K W : Subgroup G}
    (hK : (K.subgroupOf C).IsSubnormal) (hWC : W ≤ C) : (K.subgroupOf W).IsSubnormal := by
  have h := hK.comap (Subgroup.inclusion hWC)
  rwa [Subgroup.comap_inclusion_subgroupOf] at h

theorem sec4FCl_inFStar_of_l43 {X : Subgroup G} (hX : IsQuasisimple X)
    (h : LieModel (X ⧸ oddCore X) .PSL 4 3 1) : InFStar X := by
  refine Or.inl ⟨hX, Or.inl ?_⟩
  exact Or.inr (Or.inl h)

theorem sec4FCl_isComponentIn_pair [Finite G] {t s : G} {L X : Subgroup G}
    (hL : IsComponentIn L (centralizer ({t} : Set G)))
    (hX : IsComponentIn X (L ⊓ centralizer ({s} : Set G))) :
    IsComponentIn X (centralizer ({t, s} : Set G)) := by
  let W := centralizer ({t, s} : Set G)
  let M := L ⊓ centralizer ({s} : Set G)
  have hWCs : W ≤ centralizer ({s} : Set G) := centralizer_pair_le_right' t s
  have hMW : M ≤ W := le_centralizer_pair' (inf_le_left.trans hL.le) inf_le_right
  have hXW : X ≤ W := hX.le.trans hMW
  have hMW_eq : M.subgroupOf W = L.subgroupOf W := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hWCs x.2⟩⟩
  have hLsub : (L.subgroupOf W).IsSubnormal :=
    isSubnormal_subgroupOf_of_le hL.2.2 (centralizer_pair_le_left' t s)
  have hMsub : (M.subgroupOf W).IsSubnormal := by
    rw [hMW_eq]
    exact hLsub
  have hXsub : ((X.subgroupOf W).subgroupOf (M.subgroupOf W)).IsSubnormal := by
    have h := hX.2.2.comap (Subgroup.subgroupOfEquivOfLe hMW).toMonoidHom
    convert h using 1
    ext y
    simp [Subgroup.mem_subgroupOf]
  have hsub : (X.subgroupOf W).IsSubnormal :=
    Subgroup.IsSubnormal.trans (Subgroup.subgroupOf_mono W hX.le) hXsub hMsub
  exact isComponentIn_of_subnormal hXW hX.isQuasisimple hsub

theorem sec4FCl_component_le [Finite G] (h36 : Asc82Lemma36) {t s : G} {L L' X : Subgroup G}
    (hS : Sec3SettingLB G t L) (hS' : Sec3SettingLB G s L') (hts : t * s = s * t)
    (hX : IsComponentIn X (L ⊓ centralizer ({s} : Set G))) (hXF : InFStar X) : X ≤ L' := by
  have ht2 : orderOf t = 2 := hS.involution
  have hs2 : orderOf s = 2 := hS'.involution
  have hXp : IsComponentIn X (centralizer ({t, s} : Set G)) :=
    sec4FCl_isComponentIn_pair hS.component hX
  obtain ⟨K, hK, hXle⟩ := hS.lBalance t s ht2 hs2 hts X hXp
  have hKF : InFStar K := hS.a2 t s ht2 hs2 hts X K hXp hK hXle hXF
  have hKL' : K = L' :=
    (h36 G s L' hS' s L' hs2 hS'.component (Or.inl hS'.inF)).2 K hK hKF
  have htcs : t ∈ centralizer ({s} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hts
  have hconj : CFSG.conjugate L' t = L' := conjugate_eq_self_of_lemma36 h36 hS' t htcs
  calc X ≤ K ⊔ CFSG.conjugate K t := hXle
    _ = L' := by rw [hKL', hconj, sup_idem]

end CFSG.OddStandard.SmallF3.Omega
