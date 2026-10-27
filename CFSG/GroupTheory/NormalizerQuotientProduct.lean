module

public import TauCeti.GroupTheory.PGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport

public section

namespace CFSG.GroupTheory

open TauCeti.Subgroup (normalizerQuotient normalizerQuotientMk
  normalizerQuotientMk_surjective normalizerQuotientMk_eq_one_iff)

theorem normalizerQuotient_prodMulEquiv {A B : Type*} [Group A] [Group B]
    (S : Subgroup A) (T : Subgroup B) :
    Nonempty (normalizerQuotient (S.prod T) ≃*
      normalizerQuotient S × normalizerQuotient T) := by
  classical
  let N : Subgroup (A × B) :=
    Subgroup.normalizer ((S.prod T : Subgroup (A × B)) : Set (A × B))
  have hfst : ∀ g ∈ N, g.1 ∈ Subgroup.normalizer (S : Set A) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro x
    constructor
    · intro hx
      exact (Subgroup.mem_prod.mp ((hg (x, 1)).mp
        (Subgroup.mem_prod.mpr ⟨hx, T.one_mem⟩))).1
    · intro hx
      exact (Subgroup.mem_prod.mp ((hg (x, 1)).mpr
        (Subgroup.mem_prod.mpr ⟨hx, by simpa using T.one_mem⟩))).1
  have hsnd : ∀ g ∈ N, g.2 ∈ Subgroup.normalizer (T : Set B) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro y
    constructor
    · intro hy
      exact (Subgroup.mem_prod.mp ((hg (1, y)).mp
        (Subgroup.mem_prod.mpr ⟨S.one_mem, hy⟩))).2
    · intro hy
      exact (Subgroup.mem_prod.mp ((hg (1, y)).mpr
        (Subgroup.mem_prod.mpr ⟨by simpa using S.one_mem, hy⟩))).2
  let f : N →* normalizerQuotient S × normalizerQuotient T :=
    { toFun := fun g =>
        (normalizerQuotientMk S ⟨g.1.1, hfst g g.2⟩,
          normalizerQuotientMk T ⟨g.1.2, hsnd g g.2⟩)
      map_one' := by
        apply Prod.ext
        · change normalizerQuotientMk S ⟨(1 : N).1.1, hfst 1 (1 : N).2⟩ = 1
          exact (normalizerQuotientMk_eq_one_iff S _).mpr (by simp)
        · change normalizerQuotientMk T ⟨(1 : N).1.2, hsnd 1 (1 : N).2⟩ = 1
          exact (normalizerQuotientMk_eq_one_iff T _).mpr (by simp)
      map_mul' := by
        intro g h
        apply Prod.ext
        · change normalizerQuotientMk S ⟨(g * h).1.1, hfst (g * h) (g * h).2⟩ =
            normalizerQuotientMk S ⟨g.1.1, hfst g g.2⟩ *
              normalizerQuotientMk S ⟨h.1.1, hfst h h.2⟩
          rw [← map_mul]
          exact congrArg (normalizerQuotientMk S) (Subtype.ext rfl)
        · change normalizerQuotientMk T ⟨(g * h).1.2, hsnd (g * h) (g * h).2⟩ =
            normalizerQuotientMk T ⟨g.1.2, hsnd g g.2⟩ *
              normalizerQuotientMk T ⟨h.1.2, hsnd h h.2⟩
          rw [← map_mul]
          exact congrArg (normalizerQuotientMk T) (Subtype.ext rfl) }
  have hker : f.ker = (S.prod T).subgroupOf N := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      have hg' : (normalizerQuotientMk S ⟨g.1.1, hfst g g.2⟩,
          normalizerQuotientMk T ⟨g.1.2, hsnd g g.2⟩) = 1 := hg
      have h1 : normalizerQuotientMk S ⟨g.1.1, hfst g g.2⟩ = 1 := by
        simpa using congrArg Prod.fst hg'
      have h2 : normalizerQuotientMk T ⟨g.1.2, hsnd g g.2⟩ = 1 := by
        simpa using congrArg Prod.snd hg'
      exact Subgroup.mem_prod.mpr
        ⟨(normalizerQuotientMk_eq_one_iff S _).mp h1,
          (normalizerQuotientMk_eq_one_iff T _).mp h2⟩
    · intro hg
      obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp hg
      have e1 : normalizerQuotientMk S ⟨g.1.1, hfst g g.2⟩ = 1 :=
        (normalizerQuotientMk_eq_one_iff S _).mpr h1
      have e2 : normalizerQuotientMk T ⟨g.1.2, hsnd g g.2⟩ = 1 :=
        (normalizerQuotientMk_eq_one_iff T _).mpr h2
      change (normalizerQuotientMk S ⟨g.1.1, hfst g g.2⟩,
        normalizerQuotientMk T ⟨g.1.2, hsnd g g.2⟩) = 1
      rw [e1, e2]
      rfl
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, ha⟩ := normalizerQuotientMk_surjective S y.1
    obtain ⟨b, hb⟩ := normalizerQuotientMk_surjective T y.2
    have hmem : ((a : A), (b : B)) ∈ N := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.mp hx
        exact Subgroup.mem_prod.mpr
          ⟨(Subgroup.mem_normalizer_iff.mp a.2 x.1).mp hx1,
            (Subgroup.mem_normalizer_iff.mp b.2 x.2).mp hx2⟩
      · intro hx
        obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.mp hx
        exact Subgroup.mem_prod.mpr
          ⟨(Subgroup.mem_normalizer_iff.mp a.2 x.1).mpr hx1,
            (Subgroup.mem_normalizer_iff.mp b.2 x.2).mpr hx2⟩
    refine ⟨⟨((a : A), (b : B)), hmem⟩, ?_⟩
    change (normalizerQuotientMk S ⟨(a : A), hfst _ hmem⟩,
      normalizerQuotientMk T ⟨(b : B), hsnd _ hmem⟩) = y
    apply Prod.ext
    · have hsub : (⟨(a : A), hfst _ hmem⟩ :
          Subgroup.normalizer (S : Set A)) = a := Subtype.ext rfl
      rw [hsub, ha]
    · have hsub : (⟨(b : B), hsnd _ hmem⟩ :
          Subgroup.normalizer (T : Set B)) = b := Subtype.ext rfl
      rw [hsub, hb]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

theorem isSylowTwoOf_prod {A B : Type*} [Group A] [Group B]
    {S : Subgroup A} {T : Subgroup B}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤)
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S.prod T) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · have hprod : IsPGroup 2 (S × T) := IsPGroup.prod hS.2.1 hT.2.1
    exact IsPGroup.of_equiv hprod (Subgroup.prodEquiv S T).symm
  · have hSidx : ¬ 2 ∣ S.index := by
      rw [← Subgroup.relIndex_top_right (H := S)]
      exact hS.2.2
    have hTidx : ¬ 2 ∣ T.index := by
      rw [← Subgroup.relIndex_top_right (H := T)]
      exact hT.2.2
    show ¬ 2 ∣ (S.prod T).relIndex ⊤
    rw [Subgroup.relIndex_top_right, Subgroup.index_prod]
    exact fun h => (Nat.Prime.dvd_mul Nat.prime_two).mp h |>.elim hSidx hTidx

theorem exists_isElemAbelian_nine_prod_of_orderOf_three {A B : Type*} [Group A] [Group B]
    {a : A} {b : B} (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ E : Subgroup (A × B), CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  refine ⟨(Subgroup.zpowers a).prod (Subgroup.zpowers b), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
        (Subgroup.prodEquiv (Subgroup.zpowers a) (Subgroup.zpowers b)).symm
        (inferInstance : IsMulCommutative (Subgroup.zpowers a × Subgroup.zpowers b))
    · intro x hx
      obtain ⟨hu, hv⟩ := Subgroup.mem_prod.mp hx
      obtain ⟨u, v⟩ := x
      have hu3 : u ^ 3 = 1 := by
        have hdvd : orderOf u ∣ 3 := by
          have := orderOf_dvd_of_mem_zpowers hu
          rwa [ha] at this
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      have hv3 : v ^ 3 = 1 := by
        have hdvd : orderOf v ∣ 3 := by
          have := orderOf_dvd_of_mem_zpowers hv
          rwa [hb] at this
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      ext <;> simp [Prod.pow_mk, hu3, hv3]
  · have hcarda : Nat.card (Subgroup.zpowers a) = 3 := by
      rw [Nat.card_zpowers, ha]
    have hcardb : Nat.card (Subgroup.zpowers b) = 3 := by
      rw [Nat.card_zpowers, hb]
    calc Nat.card ((Subgroup.zpowers a).prod (Subgroup.zpowers b))
        = Nat.card (Subgroup.zpowers a) * Nat.card (Subgroup.zpowers b) :=
          (Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv).trans (Nat.card_prod _ _)
      _ = 3 * 3 := by rw [hcarda, hcardb]
      _ = 9 := by norm_num

end CFSG.GroupTheory
