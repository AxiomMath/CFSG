module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Transport
public import CFSG.GroupTheory.CentralizerMap

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem aux_card_comap_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (H : Subgroup Q') : Nat.card (H.comap e.toMonoidHom) = Nat.card H := by
  have h := Subgroup.card_map_of_injective (K := H.comap e.toMonoidHom)
    (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_comap_eq_self_of_surjective e.surjective H] at h
  exact h.symm

theorem centralizer_pair_eq_inf (x y : G) :
    centralizer ({x, y} : Set G) = centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) := by
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  · rintro ⟨hx, hy⟩ a (ha | ha)
    · exact hx a ha
    · exact hy a ha

theorem nonempty_quotient_oddCore_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    Nonempty (Q ⧸ oddCore Q ≃* Q' ⧸ oddCore Q') := by
  have hmap : (oddCore Q).map e.toMonoidHom = oddCore Q' := by
    unfold oddCore
    rw [(Subgroup.gc_map_comap e.toMonoidHom).l_sSup_eq_sSup_image]
    congr 1
    ext N'
    constructor
    · rintro ⟨N, ⟨hNnorm, hNodd⟩, rfl⟩
      exact ⟨hNnorm.map e.toMonoidHom e.surjective,
        by rw [Subgroup.card_map_of_injective e.injective]; exact hNodd⟩
    · intro hN'
      exact ⟨N'.comap e.toMonoidHom,
        ⟨hN'.1.comap e.toMonoidHom,
          by rw [aux_card_comap_mulEquiv e N']; exact hN'.2⟩,
        Subgroup.map_comap_eq_self_of_surjective e.surjective N'⟩
  exact ⟨QuotientGroup.congr (oddCore Q) (oddCore Q') e hmap⟩

theorem isFGroup_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : IsFGroup Q) : IsFGroup Q' := by
  unfold IsFGroup at h ⊢
  obtain ⟨hq, hquot⟩ := h
  obtain ⟨e'⟩ := nonempty_quotient_oddCore_mulEquiv e
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_⟩
  rcases hquot with h | h
  · exact Or.inl (smallF3OmegaQuotient_of_mulEquiv e' h)
  · exact Or.inr (isTwoU43_of_mulEquiv e' h)

theorem isFStarGroup_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : IsFStarGroup Q) : IsFStarGroup Q' := by
  unfold IsFStarGroup at h ⊢
  rcases h with h | ⟨hq, hstar⟩
  · exact Or.inl (isFGroup_of_mulEquiv e h)
  · obtain ⟨e'⟩ := nonempty_quotient_oddCore_mulEquiv e
    refine Or.inr ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_⟩
    rcases hstar with h | h | h | h
    · exact Or.inl (LieModel.of_mulEquiv e' h)
    · exact Or.inr (Or.inl (LieModel.of_mulEquiv e' h))
    · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e' h)))
    · exact Or.inr (Or.inr (Or.inr (LieModel.of_mulEquiv e' h)))

theorem isSL23Mod_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : IsSL23Mod Q) : IsSL23Mod Q' := by
  obtain ⟨f⟩ := h
  obtain ⟨e'⟩ := nonempty_quotient_oddCore_mulEquiv e
  exact ⟨e'.symm.trans f⟩

theorem InF.conjugate {L : Subgroup G} (h : InF L) (g : G) : InF (CFSG.conjugate L g) := by
  unfold InF at h ⊢
  unfold CFSG.conjugate
  exact isFGroup_of_mulEquiv
    (Subgroup.equivMapOfInjective L (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective) h

theorem InFStar.conjugate {L : Subgroup G} (h : InFStar L) (g : G) :
    InFStar (CFSG.conjugate L g) := by
  unfold InFStar at h ⊢
  unfold CFSG.conjugate
  exact isFStarGroup_of_mulEquiv
    (Subgroup.equivMapOfInjective L (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective) h

theorem conjugate_inv_eq_map_conj (K : Subgroup G) (g : G) :
    CFSG.conjugate K g⁻¹ = K.map (MulAut.conj g).toMonoidHom := by
  unfold CFSG.conjugate
  rw [inv_inv]

theorem conjugate_centralizer_singleton (x g : G) :
    CFSG.conjugate (centralizer ({x} : Set G)) g = centralizer ({g⁻¹ * x * g} : Set G) := by
  unfold CFSG.conjugate
  rw [CFSG.centralizer_singleton_map (MulAut.conj g⁻¹) x,
    show (MulAut.conj g⁻¹) x = g⁻¹ * x * g by simp [MulAut.conj_apply]]

theorem Sl23PocketIn.conjugate {X : Subgroup G} {y : G} {K : Subgroup G}
    (h : Sl23PocketIn X y K) (g : G) :
    Sl23PocketIn (CFSG.conjugate X g) (g⁻¹ * y * g) (CFSG.conjugate K g) := by
  let A : Subgroup G := X ⊓ centralizer ({y} : Set G)
  have hKA : K ≤ A := h.2.1
  have hKsub : (K.subgroupOf A).IsSubnormal := h.2.2.1
  let e : ↥A ≃* ↥(A.map (MulAut.conj g⁻¹).toMonoidHom) :=
    A.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hconjA : CFSG.conjugate A g =
      CFSG.conjugate X g ⊓ centralizer ({g⁻¹ * y * g} : Set G) := by
    unfold CFSG.conjugate
    change (X ⊓ centralizer ({y} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      X.map (MulAut.conj g⁻¹).toMonoidHom ⊓ centralizer ({g⁻¹ * y * g} : Set G)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      CFSG.centralizer_singleton_map (MulAut.conj g⁻¹) y,
      show (MulAut.conj g⁻¹) y = g⁻¹ * y * g by simp [MulAut.conj_apply]]
  have heq : (K.subgroupOf A).map e.toMonoidHom =
      (K.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf
        (A.map (MulAut.conj g⁻¹).toMonoidHom) := by
    apply Subgroup.map_injective
      (Subgroup.subtype_injective (A.map (MulAut.conj g⁻¹).toMonoidHom))
    rw [Subgroup.map_map]
    have hcomp : ((A.map (MulAut.conj g⁻¹).toMonoidHom).subtype).comp e.toMonoidHom =
        (MulAut.conj g⁻¹).toMonoidHom.comp A.subtype := by
      ext m
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hKA,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_mono hKA)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold CFSG.conjugate
    exact Subgroup.mem_map.mpr ⟨y, h.1, by simp [MulAut.conj_apply]⟩
  · rw [← hconjA]
    change K.map (MulAut.conj g⁻¹).toMonoidHom ≤ A.map (MulAut.conj g⁻¹).toMonoidHom
    exact Subgroup.map_mono h.2.1
  · have hsn : ((K.subgroupOf A).map e.toMonoidHom).IsSubnormal :=
      Subgroup.IsSubnormal.map (f := e.toMonoidHom) e.surjective hKsub
    rw [heq] at hsn
    rw [← hconjA]
    change ((K.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf
      (A.map (MulAut.conj g⁻¹).toMonoidHom)).IsSubnormal
    exact hsn
  · change IsSL23Mod ↥(K.map (MulAut.conj g⁻¹).toMonoidHom)
    exact isSL23Mod_of_mulEquiv
      (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective) h.2.2.2

private theorem aux_subnormal_inf_centralizer {L N : Subgroup G} {w : G} {J : Subgroup G}
    (hLN : L ≤ N) (hnorm : ∀ c ∈ N, CFSG.conjugate L c = L)
    (hJle : J ≤ L ⊓ centralizer ({w} : Set G))
    (hJ : (J.subgroupOf (L ⊓ centralizer ({w} : Set G))).IsSubnormal) :
    (J.subgroupOf (N ⊓ centralizer ({w} : Set G))).IsSubnormal := by
  have hAB : L ⊓ centralizer ({w} : Set G) ≤ N ⊓ centralizer ({w} : Set G) :=
    inf_le_inf hLN le_rfl
  have hAnorm : ((L ⊓ centralizer ({w} : Set G)).subgroupOf
      (N ⊓ centralizer ({w} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAB, Subgroup.le_normalizer_iff]
    intro b hb a ha
    rw [Subgroup.mem_inf] at hb ha ⊢
    obtain ⟨hbN, hbC⟩ := hb
    obtain ⟨haL, haC⟩ := ha
    refine ⟨?_, ?_⟩
    · have hconj := hnorm b⁻¹ (N.inv_mem hbN)
      rw [conjugate_inv_eq_map_conj] at hconj
      rw [← hconj]
      exact Subgroup.mem_map.mpr ⟨a, haL, by simp [MulAut.conj_apply]⟩
    · exact (centralizer ({w} : Set G)).mul_mem
        ((centralizer ({w} : Set G)).mul_mem hbC haC)
        ((centralizer ({w} : Set G)).inv_mem hbC)
  have hJleB : J.subgroupOf (N ⊓ centralizer ({w} : Set G)) ≤
      (L ⊓ centralizer ({w} : Set G)).subgroupOf (N ⊓ centralizer ({w} : Set G)) := by
    intro x hx
    exact hJle hx
  have hHsn : ((J.subgroupOf (N ⊓ centralizer ({w} : Set G))).subgroupOf
      ((L ⊓ centralizer ({w} : Set G)).subgroupOf
        (N ⊓ centralizer ({w} : Set G)))).IsSubnormal := by
    have h := hJ.comap
      ((L ⊓ centralizer ({w} : Set G)).subgroupOfEquivOfLe hAB).toMonoidHom
    convert h using 1
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rfl
  exact Subgroup.IsSubnormal.trans hJleB hHsn hAnorm.isSubnormal

theorem Sl23PocketIn.of_normal {L N : Subgroup G} {y : G} {K : Subgroup G}
    (h : Sl23PocketIn L y K) (hLN : L ≤ N) (hnorm : ∀ c ∈ N, CFSG.conjugate L c = L) :
    Sl23PocketIn N y K := by
  refine ⟨h.1, h.2.1.trans (inf_le_inf hLN le_rfl), ?_, h.2.2.2⟩
  exact aux_subnormal_inf_centralizer hLN hnorm h.2.1 h.2.2.1

theorem IsComponentIn.of_normal_inf_centralizer {L N : Subgroup G} {w : G} {J : Subgroup G}
    (hLN : L ≤ N) (hnorm : ∀ c ∈ N, CFSG.conjugate L c = L)
    (hJ : IsComponentIn J (L ⊓ centralizer ({w} : Set G))) :
    IsComponentIn J (N ⊓ centralizer ({w} : Set G)) := by
  exact isComponentIn_of_subnormal (hJ.1.trans (inf_le_inf hLN le_rfl)) hJ.isQuasisimple
    (aux_subnormal_inf_centralizer hLN hnorm hJ.1 hJ.2.2)

end CFSG.OddStandard.SmallF3.Omega
