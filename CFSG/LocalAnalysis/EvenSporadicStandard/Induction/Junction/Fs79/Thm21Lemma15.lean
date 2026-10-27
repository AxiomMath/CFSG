module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Layer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitCompAt

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

variable {G : Type} [Group G]

theorem isCompIn_of_isCompIn_of_subnormal {E U Y : Subgroup G} (hE : IsCompIn E U) (hUY : U ≤ Y)
    (hU : (U.subgroupOf Y).IsSubnormal) : IsCompIn E Y := by
  refine isCompIn_of_subnormal (hE.1.trans hUY) hE.isQuasisimple ?_
  have heq : (E.subgroupOf Y).subgroupOf (U.subgroupOf Y) =
      (E.subgroupOf U).comap (Subgroup.subgroupOfEquivOfLe hUY).toMonoidHom := by
    ext x
    rfl
  have h1 : ((E.subgroupOf Y).subgroupOf (U.subgroupOf Y)).IsSubnormal := by
    rw [heq]
    exact Subgroup.IsSubnormal.comap _ hE.2.2
  exact Subgroup.IsSubnormal.trans (Subgroup.subgroupOf_mono Y hE.1) h1 hU

theorem layerIn_le_of_subnormal {U Y : Subgroup G} (hUY : U ≤ Y)
    (hU : (U.subgroupOf Y).IsSubnormal) : layerIn U ≤ layerIn Y :=
  sSup_le fun _ hE => le_sSup (isCompIn_of_isCompIn_of_subnormal hE hUY hU)

variable [Finite G]

theorem layerIn_inf_le_of_lemma15At (h15 : FS79Lemma15At G)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hO : CFSG.oddCore G = ⊥)
    {S T : Subgroup G} (hS : IsPGroup 2 S) (hT : IsPGroup 2 T) (hST : ⁅S, T⁆ ≤ S ⊓ T)
    {K : Subgroup G} (hK : IsCompIn K (centralizer (S : Set G))) :
    layerIn (K ⊓ centralizer (T : Set G)) ≤ layerIn (centralizer (T : Set G)) := by
  have hP : IsPGroup 2 ↥(S ⊔ T) :=
    hS.to_sup_of_normal_right' hT (le_normalizer_of_commutator_le hST)
  have hY : centralizer ((S ⊔ T : Subgroup G) : Set G) =
      centralizer (S : Set G) ⊓ centralizer (T : Set G) := by
    ext x
    exact mem_centralizer_sup
  have hYS : centralizer (S : Set G) ⊓ centralizer (T : Set G) ≤ centralizer (S : Set G) :=
    inf_le_left
  have hUY : K ⊓ centralizer (T : Set G) ≤ centralizer (S : Set G) ⊓ centralizer (T : Set G) :=
    inf_le_inf hK.1 le_rfl
  have hsub : ((K ⊓ centralizer (T : Set G)).subgroupOf
      (centralizer (S : Set G) ⊓ centralizer (T : Set G))).IsSubnormal := by
    have heq : (K ⊓ centralizer (T : Set G)).subgroupOf
        (centralizer (S : Set G) ⊓ centralizer (T : Set G)) =
        (K.subgroupOf (centralizer (S : Set G))).comap (Subgroup.inclusion hYS) := by
      ext x
      exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
    rw [heq]
    exact Subgroup.IsSubnormal.comap _ hK.2.2
  have h1 := layerIn_le_of_subnormal hUY hsub
  have h2 := (h15 hkp (S ⊔ T) hP).1 T le_sup_right
  rw [(h15 hkp (S ⊔ T) hP).2 hO, (h15 hkp T hT).2 hO, hY] at h2
  exact h1.trans h2

theorem exists_isCompIn_of_lemma15At (h15 : FS79Lemma15At G)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hO : CFSG.oddCore G = ⊥)
    {S T : Subgroup G} (hS : IsPGroup 2 S) (hT : IsPGroup 2 T) (hST : ⁅S, T⁆ ≤ S ⊓ T)
    {K : Subgroup G} (hK : IsCompIn K (centralizer (S : Set G)))
    (hTK : T ≤ centralizer (K : Set G)) :
    ∃ M : Subgroup G, IsCompIn M (centralizer (T : Set G)) ∧
      IsCompIn K (centralizer (S : Set G) ⊓ conjClosure M S) := by
  have hKT : K ≤ centralizer (T : Set G) := fun k hk =>
    mem_centralizer_iff.2 fun t ht => (mem_centralizer_iff.1 (hTK ht) k hk).symm
  have hKK : IsCompIn K K :=
    isCompIn_of_normal le_rfl hK.isQuasisimple (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hKL : K ≤ layerIn (centralizer (T : Set G)) :=
    (le_layerIn_of_isCompIn (isCompIn_of_le hKK (le_inf le_rfl hKT) inf_le_left)).trans
      (layerIn_inf_le_of_lemma15At h15 hkp hO hS hT hST hK)
  have hKST : IsCompIn K (centralizer ((S ⊔ T : Subgroup G) : Set G)) :=
    isCompIn_of_le hK (le_centralizer_sup hK.1 hKT)
      (Subgroup.centralizer_le (by exact_mod_cast le_sup_left))
  obtain ⟨M, hM, hKM⟩ :=
    exists_isCompIn_le_conjClosure (le_normalizer_of_commutator_le hST) hKST hKL
  exact ⟨M, hM, isCompIn_of_le hK (le_inf hK.1 hKM) inf_le_left⟩

end CFSG.EvenSporadicStandard.Induction.Junction
