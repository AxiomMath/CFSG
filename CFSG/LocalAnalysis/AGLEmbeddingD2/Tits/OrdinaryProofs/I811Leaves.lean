module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.NormalizerChain

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

open CFSG.Open CFSG.QuasithinUnique

theorem le_of_odd_relindex {G : Type*} [Group G] [Finite G] {U Z K : Subgroup G}
    (hZ : IsPGroup 2 Z) (hUZ : U ≤ Z) (hZK : Z ≤ K) (hodd : ¬ 2 ∣ U.relIndex K) : Z ≤ U := by
  have hmul : U.relIndex Z * Z.relIndex K = U.relIndex K :=
    Subgroup.relIndex_mul_relIndex U Z K hUZ hZK
  have hdvd : U.relIndex Z ∣ U.relIndex K := ⟨Z.relIndex K, hmul.symm⟩
  have hodd' : ¬ 2 ∣ U.relIndex Z := fun h => hodd (h.trans hdvd)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
  have hdvdZ : U.relIndex Z ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_card (U.subgroupOf Z)
  have hcop : Nat.Coprime (U.relIndex Z) (2 ^ n) :=
    Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd').symm
  have h1 : U.relIndex Z = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvdZ
  exact Subgroup.relIndex_eq_one.mp h1

theorem isSylowTwoOf_of_normalizer {G : Type*} [Group G] [Finite G] {U I : Subgroup G}
    (hUI : U ≤ I) (hU : IsSylowTwoOf U (I ⊓ Subgroup.normalizer (U : Set G))) :
    IsSylowTwoOf U I := by
  classical
  obtain ⟨hUN, hU2, hodd⟩ := hU
  have hodd' : ¬ 2 ∣ U.relIndex (I ⊓ Subgroup.normalizer (U : Set G)) := hodd
  have hW2 : IsPGroup 2 (U.subgroupOf I) := IsPGroup.comap_subtype hU2 (K := I)
  obtain ⟨T, hWT⟩ := IsPGroup.exists_le_sylow (G := I) (p := 2) hW2
  set Z : Subgroup G := (T.toSubgroup : Subgroup I).map I.subtype with hZdef
  have hZI : Z ≤ I := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hUZ : U ≤ Z := by
    intro u hu
    have hmem : (⟨u, hUI hu⟩ : I) ∈ U.subgroupOf I := hu
    exact Subgroup.mem_map.mpr ⟨⟨u, hUI hu⟩, hWT hmem, rfl⟩
  have hZ2 : IsPGroup 2 Z := by
    exact T.isPGroup'.map I.subtype
  have hZsub : Z.subgroupOf I = T.toSubgroup := by
    rw [hZdef]
    exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  have hZidx : Z.relIndex I = T.toSubgroup.index := by
    show (Z.subgroupOf I).index = _
    rw [hZsub]
  have hZIodd : ¬ 2 ∣ Z.relIndex I := by
    rw [hZidx]
    exact Sylow.not_dvd_index T
  have hZU : Z ≤ U := by
    by_contra hne
    have hUZlt : U < Z := lt_of_le_of_ne hUZ (fun h => hne (le_of_eq h.symm))
    have hgrow : U < Subgroup.normalizer (U : Set G) ⊓ Z :=
      lt_normalizer_inf_of_isPGroup hZ2 hUZ hUZlt
    have hZ2N : Subgroup.normalizer (U : Set G) ⊓ Z ≤ I ⊓ Subgroup.normalizer (U : Set G) :=
      le_inf (inf_le_right.trans hZI) inf_le_left
    have hsub : Subgroup.normalizer (U : Set G) ⊓ Z ≤ U :=
      le_of_odd_relindex (IsPGroup.to_le hZ2 inf_le_right) hgrow.le hZ2N hodd'
    exact lt_irrefl _ (lt_of_lt_of_le hgrow hsub)
  have h1 : U.relIndex Z = 1 := Subgroup.relIndex_eq_one.mpr hZU
  have hmul : U.relIndex Z * Z.relIndex I = U.relIndex I :=
    Subgroup.relIndex_mul_relIndex U Z I hUZ hZI
  refine ⟨hUI, hU2, ?_⟩
  show ¬ 2 ∣ U.relIndex I
  rw [← hmul, h1, one_mul]
  exact hZIodd

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

end
