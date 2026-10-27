module

public import CFSG.CGT.PushingUpLit.C2L.SylowGraph

public section

namespace CFSG.CGT.PushingUpLit.C2L.Tame

open CFSG.Open CFSG.ABGLocalTools CFSG.CGT.PushingUpLit.T2KSW

variable {G : Type} [Group G]

theorem isSylowOf_top_of_sylow [Finite G] (S : Sylow 2 G) : IsSylowOf 2 (S : Subgroup G) ⊤ := by
  rw [isSylowOf_iff, Subgroup.relIndex_top_right]
  exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩

theorem lt_inf_normalizer_of_lt [Finite G] {P H : Subgroup G} (hP : IsPGroup 2 P) (hHP : H < P) :
    H < P ⊓ Subgroup.normalizer (H : Set G) := by
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hlt' : H.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun h => hHP.ne (le_antisymm hHP.le h)
  have hn := Group.normalizerCondition_of_isNilpotent (H.subgroupOf P) hlt'
  rw [← Subgroup.subgroupOf_normalizer_eq hHP.le] at hn
  obtain ⟨s, hs1, hs2⟩ := IsConcreteLE.exists_of_lt hn
  refine lt_of_le_of_ne (le_inf hHP.le Subgroup.le_normalizer) fun h => hs2 ?_
  have hmem : (s : G) ∈ P ⊓ Subgroup.normalizer (H : Set G) := ⟨s.2, hs1⟩
  rw [← h] at hmem
  exact hmem

theorem exists_sylow_inf_eq [Finite G] {N A : Subgroup G} (hA : IsSylowOf 2 A N) :
    ∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ S ⊓ N = A := by
  obtain ⟨S, hAS⟩ := hA.isPGroup.exists_le_sylow
  refine ⟨S, isSylowOf_top_of_sylow S, ?_⟩
  exact hA.eq_of_le (le_inf hAS hA.le) inf_le_right S.isPGroup'.to_inf_left

def NAdj (H A B : Subgroup G) : Prop :=
  IsSylowOf 2 A (Subgroup.normalizer (H : Set G)) ∧
    IsSylowOf 2 B (Subgroup.normalizer (H : Set G)) ∧ A ≠ B ∧ H < A ⊓ B

theorem sylowOf_normalizer_conn [Finite G] {H : Subgroup G} (hH : IsPGroup 2 H)
    (hne : ¬ ∃ K : Subgroup (↥(Subgroup.normalizer (H : Set G)) ⧸
      H.subgroupOf (Subgroup.normalizer (H : Set G))), fusionStronglyEmbedded K)
    {A B : Subgroup G} (hA : IsSylowOf 2 A (Subgroup.normalizer (H : Set G)))
    (hB : IsSylowOf 2 B (Subgroup.normalizer (H : Set G))) :
    Relation.ReflTransGen (NAdj H) A B := by
  set N : Subgroup G := Subgroup.normalizer (H : Set G) with hN
  have hHN : H ≤ N := Subgroup.le_normalizer
  set π : ↥N →* ↥N ⧸ H.subgroupOf N := QuotientGroup.mk' (H.subgroupOf N) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = H.subgroupOf N := QuotientGroup.ker_mk' _
  have hH'p : IsPGroup 2 (H.subgroupOf N) := hH.comap_subtype
  have hH'le : ∀ Q : Sylow 2 ↥N, H.subgroupOf N ≤ (Q : Subgroup ↥N) :=
    fun Q => hH'p.le_sylow_of_normal Q
  let φ : Sylow 2 ↥N → Sylow 2 (↥N ⧸ H.subgroupOf N) := fun Q => Q.mapSurjective hπ
  have hφ : ∀ Q : Sylow 2 ↥N, (φ Q : Subgroup (↥N ⧸ H.subgroupOf N)) = (Q : Subgroup ↥N).map π :=
    fun Q => Sylow.coe_mapSurjective hπ Q
  have hφinj : Function.Injective φ := by
    intro Q Q' h
    have h1 : (Q : Subgroup ↥N).map π = (Q' : Subgroup ↥N).map π := by
      rw [← hφ, ← hφ, h]
    have h2 : ((Q : Subgroup ↥N).map π).comap π = ((Q' : Subgroup ↥N).map π).comap π := by
      rw [h1]
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, hker, sup_eq_left.2 (hH'le Q),
      sup_eq_left.2 (hH'le Q')] at h2
    exact Sylow.ext h2
  have hadj : ∀ Q Q' : Sylow 2 ↥N, SylowAdj (φ Q) (φ Q') →
      NAdj H ((Q : Subgroup ↥N).map N.subtype) ((Q' : Subgroup ↥N).map N.subtype) := by
    rintro Q Q' ⟨hne', x, hx1, hxQ, hxQ'⟩
    have hH : (H.subgroupOf N).map N.subtype = H := Subgroup.map_subgroupOf_eq_of_le hHN
    refine ⟨⟨Q, rfl⟩, ⟨Q', rfl⟩, ?_, ?_⟩
    · intro h
      exact hne' (congrArg φ (Sylow.ext (Subgroup.map_injective N.subtype_injective h)))
    · have hxQ₁ : x ∈ (φ Q : Subgroup (↥N ⧸ H.subgroupOf N)) := hxQ
      have hxQ₂ : x ∈ (φ Q' : Subgroup (↥N ⧸ H.subgroupOf N)) := hxQ'
      rw [hφ] at hxQ₁ hxQ₂
      obtain ⟨a, haQ, rfl⟩ := hxQ₁
      obtain ⟨a', ha'Q', haa'⟩ := hxQ₂
      have h0 : (QuotientGroup.mk a : ↥N ⧸ H.subgroupOf N) = QuotientGroup.mk a' := haa'.symm
      have h1 : a⁻¹ * a' ∈ H.subgroupOf N := QuotientGroup.eq.1 h0
      have haQ' : a ∈ (Q' : Subgroup ↥N) := by
        have h2 : a' * (a⁻¹ * a')⁻¹ ∈ (Q' : Subgroup ↥N) :=
          Q'.mul_mem ha'Q' (Q'.inv_mem (hH'le Q' h1))
        simpa using h2
      have haH : a ∉ H.subgroupOf N := fun h => hx1 ((QuotientGroup.eq_one_iff a).2 h)
      have hle : H ≤ (Q : Subgroup ↥N).map N.subtype ⊓ (Q' : Subgroup ↥N).map N.subtype := by
        rw [← hH]
        exact le_inf (Subgroup.map_mono (hH'le Q)) (Subgroup.map_mono (hH'le Q'))
      refine lt_of_le_of_ne hle fun h => ?_
      have hmem : (a : G) ∈ (Q : Subgroup ↥N).map N.subtype ⊓
          (Q' : Subgroup ↥N).map N.subtype :=
        ⟨⟨a, haQ, rfl⟩, ⟨a, haQ', rfl⟩⟩
      rw [← h] at hmem
      exact haH hmem
  obtain ⟨QA, hQA⟩ := hA
  obtain ⟨QB, hQB⟩ := hB
  have hconn : SylowConn (φ QA) (φ QB) := sylowConn_of_no_stronglyEmbedded hne _ _
  have key : ∀ Y : Sylow 2 (↥N ⧸ H.subgroupOf N), SylowConn (φ QA) Y →
      ∀ Q : Sylow 2 ↥N, φ Q = Y →
        Relation.ReflTransGen (NAdj H) A ((Q : Subgroup ↥N).map N.subtype) := by
    intro Y hY
    induction hY with
    | refl =>
      intro Q hQ
      rw [hφinj hQ, hQA]
    | @tail Y' Y'' _ hstep ih =>
      intro Q'' hQ''
      obtain ⟨Q', hQ'⟩ := Sylow.mapSurjective_surjective hπ 2 Y'
      have h1 := ih Q' hQ'
      have h2 : SylowAdj (φ Q') (φ Q'') := by
        have : φ Q' = Y' := hQ'
        rw [this, hQ'']
        exact hstep
      exact h1.tail (hadj Q' Q'' h2)
  have := key (φ QB) hconn QB rfl
  rwa [hQB] at this

theorem lift_conn [Finite G] {H : Subgroup G} (Lk : Subgroup G → Subgroup G → Prop)
    (IH : ∀ S S' : Subgroup G, IsSylowOf 2 S ⊤ → IsSylowOf 2 S' ⊤ → H < S ⊓ S' →
      Relation.ReflTransGen Lk S S')
    {A B : Subgroup G} (hAB : Relation.ReflTransGen (NAdj H) A B) (hHA : H < A)
    {R : Subgroup G} (hR : IsSylowOf 2 R ⊤) (hRA : R ⊓ Subgroup.normalizer (H : Set G) = A) :
    ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → S ⊓ Subgroup.normalizer (H : Set G) = B →
      Relation.ReflTransGen Lk R S := by
  induction hAB with
  | refl =>
    intro S hS hSA
    refine IH R S hR hS (lt_of_lt_of_le hHA (le_inf ?_ ?_))
    · rw [← hRA]
      exact inf_le_left
    · rw [← hSA]
      exact inf_le_left
  | @tail B' B'' _ hstep ih =>
    intro S hS hSB
    obtain ⟨S', hS', hS'B⟩ := exists_sylow_inf_eq hstep.1
    have h1 := ih S' hS' hS'B
    have h2 : H < S' ⊓ S := by
      refine lt_of_lt_of_le hstep.2.2.2 (le_inf ?_ ?_)
      · exact (inf_le_left : B' ⊓ B'' ≤ B').trans (by rw [← hS'B]; exact inf_le_left)
      · exact (inf_le_right : B' ⊓ B'' ≤ B'').trans (by rw [← hSB]; exact inf_le_left)
    exact h1.trans (IH S' S hS' hS h2)

end CFSG.CGT.PushingUpLit.C2L.Tame
