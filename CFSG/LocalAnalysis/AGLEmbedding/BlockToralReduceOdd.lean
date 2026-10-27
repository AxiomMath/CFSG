module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceOddQuot
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers

theorem isClassicalTwoOrG2_of_iso {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : IsClassicalTwoOrG2 X) : IsClassicalTwoOrG2 X' := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans f⟩⟩)

namespace ToralReduce

variable {Y : Type} [Group Y] {L : Subgroup Y}

theorem isPGroup_twoCenter : IsPGroup 2 (twoCenter L) := fun g => by
  obtain ⟨k, hk⟩ := g.2.2.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem twoCenter_subgroupOf_normal {A : Subgroup Y} (hAL : A ≤ L) :
    ((twoCenter L).subgroupOf A).Normal where
  conj_mem := by
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    change (g : Y) * n * (g : Y)⁻¹ ∈ twoCenter L
    rw [← mul_comm_of_mem_twoCenter hn (hAL g.2), mul_inv_cancel_right]
    exact hn

theorem twoCenter_le_of_isSylowTwoOf {T : Subgroup Y} (hT : IsSylowTwoOf T L) :
    twoCenter L ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 (T.subgroupOf L) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  let P : Sylow 2 ↥L := hT2.toSylow hT.2.2
  have : ((twoCenter L).subgroupOf L).Normal := twoCenter_subgroupOf_normal le_rfl
  have hZ2 : IsPGroup 2 ((twoCenter L).subgroupOf L) :=
    isPGroup_twoCenter.of_equiv (Subgroup.subgroupOfEquivOfLe twoCenter_le).symm
  have hle : (twoCenter L).subgroupOf L ≤ (P : Subgroup ↥L) := hZ2.le_sylow_of_normal P
  intro z hz
  exact hle (show (⟨z, twoCenter_le hz⟩ : ↥L) ∈ (twoCenter L).subgroupOf L from hz)

theorem mem_map_twoCenterHom_iff {A : Subgroup Y} (hZA : twoCenter L ≤ A) {a : ↥L} :
    twoCenterHom L a ∈ (A.subgroupOf L).map (twoCenterHom L) ↔ (a : Y) ∈ A := by
  refine ⟨fun ⟨b, hb, hba⟩ => ?_, fun ha => ⟨a, ha, rfl⟩⟩
  have hb' : (b : Y) ∈ A := hb
  have hz := hZA (twoCenterHom_eq_iff.mp hba)
  have := A.mul_mem hb' hz
  rwa [mul_inv_cancel_left] at this

theorem twoCenterMk_mem_normalizer {A : Subgroup Y} (hZA : twoCenter L ≤ A)
    {n : ↥(Subgroup.normalizer (L : Set Y))} (hn : (n : Y) ∈ Subgroup.normalizer (A : Set Y)) :
    twoCenterMk L n ∈
      Subgroup.normalizer (((A.subgroupOf L).map (twoCenterHom L) : Subgroup _) : Set _) := by
  have key : ∀ m : ↥(Subgroup.normalizer (L : Set Y)), (m : Y) ∈ Subgroup.normalizer (A : Set Y) →
      ∀ y ∈ (A.subgroupOf L).map (twoCenterHom L),
        twoCenterMk L m * y * (twoCenterMk L m)⁻¹ ∈ (A.subgroupOf L).map (twoCenterHom L) := by
    rintro m hm _ ⟨a, ha, rfl⟩
    rw [twoCenterMk_conj m a, mem_map_twoCenterHom_iff hZA]
    exact (Subgroup.mem_normalizer_iff.mp hm a).mp ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key n hn y, fun hy => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hy
  simpa [mul_assoc] using this

theorem twoCenterHom_mem_normalizer_iff {A : Subgroup Y} (hAL : A ≤ L) (hZA : twoCenter L ≤ A)
    (l : ↥L) : twoCenterHom L l ∈
      Subgroup.normalizer (((A.subgroupOf L).map (twoCenterHom L) : Subgroup _) : Set _) ↔
      (l : Y) ∈ Subgroup.normalizer (A : Set Y) := by
  refine ⟨fun hl => ?_, fun hl => twoCenterMk_mem_normalizer (n := ⟨l, Subgroup.le_normalizer l.2⟩)
    hZA hl⟩
  have key : ∀ m : ↥L, twoCenterHom L m ∈
      Subgroup.normalizer (((A.subgroupOf L).map (twoCenterHom L) : Subgroup _) : Set _) →
      ∀ h ∈ A, (m : Y) * h * (m : Y)⁻¹ ∈ A := by
    intro m hm h hh
    have h1 := (Subgroup.mem_normalizer_iff.mp hm (twoCenterHom L ⟨h, hAL hh⟩)).mp ⟨_, hh, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, mem_map_twoCenterHom_iff hZA] at h1
    exact h1
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key l hl h, fun hh => ?_⟩
  have := key l⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hl) _ hh
  simpa [mul_assoc] using this

theorem isSylowTwoOf_map_twoCenterHom [Finite Y] {T : Subgroup Y} (hT : IsSylowTwoOf T L) :
    IsSylowTwoOf ((T.subgroupOf L).map (twoCenterHom L)) (twoCenterHom L).range := by
  have hT2 : IsPGroup 2 (T.subgroupOf L) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  refine ⟨Subgroup.map_le_range _ _, hT2.map _, ?_⟩
  have h1 : ((T.subgroupOf L).map (twoCenterHom L)).subgroupOf (twoCenterHom L).range =
      (T.subgroupOf L).map (twoCenterHom L).rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  exact hT.2.2 (hd.trans (Subgroup.index_map_dvd _ (twoCenterHom L).rangeRestrict_surjective))

theorem isPGroup_of_map_mem {A : Subgroup Y} (hAL : A ≤ L) {X : Subgroup (TwoCenterQuot L)}
    (hX : IsPGroup 2 X) (h : ∀ a : ↥L, (a : Y) ∈ A → twoCenterHom L a ∈ X) : IsPGroup 2 A := by
  intro g
  obtain ⟨k, hk⟩ := hX ⟨_, h ⟨g, hAL g.2⟩ g.2⟩
  have h1 : twoCenterHom L (⟨g, hAL g.2⟩ ^ 2 ^ k) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ := (twoCenterHom_eq_one_iff.mp h1).2.2
  refine ⟨k + m, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, Subgroup.coe_one] at hm ⊢
  rw [pow_add, pow_mul, hm]

theorem isSylowTwoOf_comap_map [Finite Y] {T : Subgroup (TwoCenterQuot L)}
    (hT : IsSylowTwoOf T (twoCenterHom L).range) :
    IsSylowTwoOf ((T.comap (twoCenterHom L)).map L.subtype) L := by
  refine ⟨Subgroup.map_subtype_le _, isPGroup_of_map_mem (Subgroup.map_subtype_le _) hT.2.1
    fun a ha => ?_, ?_⟩
  · obtain ⟨b, hb, hba⟩ := ha
    rw [show a = b from Subtype.ext hba.symm]
    exact hb
  · have h1 : ((T.comap (twoCenterHom L)).map L.subtype).subgroupOf L =
        (T.subgroupOf (twoCenterHom L).range).comap (twoCenterHom L).rangeRestrict := by
      ext a
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_map,
        Subgroup.coe_subtype, MonoidHom.coe_rangeRestrict]
      exact ⟨fun ⟨b, hb, hba⟩ => by rwa [show a = b from Subtype.ext hba.symm],
        fun ha => ⟨a, ha, rfl⟩⟩
    rw [h1, Subgroup.index_comap_of_surjective _ (twoCenterHom L).rangeRestrict_surjective]
    exact hT.2.2

theorem map_comap_twoCenterHom {T : Subgroup (TwoCenterQuot L)}
    (hT : T ≤ (twoCenterHom L).range) :
    (((T.comap (twoCenterHom L)).map L.subtype).subgroupOf L).map (twoCenterHom L) = T := by
  ext y
  refine ⟨fun ⟨a, ha, hay⟩ => ?_, fun hy => ?_⟩
  · obtain ⟨b, hb, hba⟩ := ha
    rw [← hay, show a = b from Subtype.ext hba.symm]
    exact hb
  · obtain ⟨a, rfl⟩ := hT hy
    exact ⟨a, ⟨a, hy, rfl⟩, rfl⟩

theorem twoCenter_le_of_isParabolicTwo {J : Subgroup Y} (hP : IsParabolicTwo L J) :
    twoCenter L ≤ J := by
  obtain ⟨-, T, hT, hTJ⟩ := hP
  exact fun z hz =>
    hTJ ⟨twoCenter_le hz, Subgroup.le_normalizer (twoCenter_le_of_isSylowTwoOf hT hz)⟩

theorem isParabolicTwo_map [Finite Y] {J : Subgroup Y} (hP : IsParabolicTwo L J) :
    IsParabolicTwo (twoCenterHom L).range ((J.subgroupOf L).map (twoCenterHom L)) := by
  have hZJ := twoCenter_le_of_isParabolicTwo hP
  obtain ⟨hJL, T, hT, hTJ⟩ := hP
  refine ⟨Subgroup.map_le_range _ _, _, isSylowTwoOf_map_twoCenterHom hT, ?_⟩
  rintro _ ⟨⟨l, rfl⟩, hl⟩
  have hl' : twoCenterHom L l ∈ Subgroup.normalizer
      (((T.subgroupOf L).map (twoCenterHom L) : Subgroup _) : Set (TwoCenterQuot L)) := hl
  rw [twoCenterHom_mem_normalizer_iff hT.1 (twoCenter_le_of_isSylowTwoOf hT)] at hl'
  exact ⟨l, hTJ ⟨l.2, hl'⟩, rfl⟩

theorem map_ne_range {J : Subgroup Y} (hP : IsParabolicTwo L J) (hJL : J ≠ L) :
    (J.subgroupOf L).map (twoCenterHom L) ≠ (twoCenterHom L).range := by
  intro h
  apply hJL
  refine le_antisymm hP.1 fun l hl => ?_
  have : twoCenterHom L ⟨l, hl⟩ ∈ (J.subgroupOf L).map (twoCenterHom L) := h ▸ ⟨_, rfl⟩
  exact (mem_map_twoCenterHom_iff (twoCenter_le_of_isParabolicTwo hP)).mp this

theorem ne_borel_map [Finite Y] {J : Subgroup Y} (hP : IsParabolicTwo L J)
    (hJB : ∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) :
    ∀ T : Subgroup (TwoCenterQuot L), IsSylowTwoOf T (twoCenterHom L).range →
      (J.subgroupOf L).map (twoCenterHom L) ≠
        (twoCenterHom L).range ⊓ Subgroup.normalizer (T : Set (TwoCenterQuot L)) := by
  intro T hT heq
  have hZJ := twoCenter_le_of_isParabolicTwo hP
  obtain ⟨T₀, hT₀, hmap⟩ : ∃ T₀ : Subgroup Y, IsSylowTwoOf T₀ L ∧
      (T₀.subgroupOf L).map (twoCenterHom L) = T :=
    ⟨_, isSylowTwoOf_comap_map hT, map_comap_twoCenterHom hT.1⟩
  have hZT := twoCenter_le_of_isSylowTwoOf hT₀
  subst hmap
  apply hJB T₀ hT₀
  ext l
  constructor
  · intro hl
    have h1 : twoCenterHom L ⟨l, hP.1 hl⟩ ∈ (J.subgroupOf L).map (twoCenterHom L) := ⟨_, hl, rfl⟩
    rw [heq] at h1
    have h2 : twoCenterHom L ⟨l, hP.1 hl⟩ ∈ Subgroup.normalizer
        (((T₀.subgroupOf L).map (twoCenterHom L) : Subgroup _) : Set (TwoCenterQuot L)) := h1.2
    rw [twoCenterHom_mem_normalizer_iff hT₀.1 hZT] at h2
    exact ⟨hP.1 hl, h2⟩
  · rintro ⟨hlL, hlN⟩
    have h2 : twoCenterHom L ⟨l, hlL⟩ ∈ Subgroup.normalizer
        (((T₀.subgroupOf L).map (twoCenterHom L) : Subgroup _) : Set (TwoCenterQuot L)) := by
      rw [twoCenterHom_mem_normalizer_iff hT₀.1 hZT]
      exact hlN
    have h1 : twoCenterHom L ⟨l, hlL⟩ ∈ (twoCenterHom L).range ⊓ Subgroup.normalizer
        (((T₀.subgroupOf L).map (twoCenterHom L) : Subgroup _) : Set (TwoCenterQuot L)) :=
      ⟨⟨_, rfl⟩, h2⟩
    rw [← heq, mem_map_twoCenterHom_iff hZJ] at h1
    exact h1

end ToralReduce

end CFSG.AGLEmbedding
