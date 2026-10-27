module

public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneFStar
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open Subgroup

theorem isPGroup_three_range_of_index {H L : Type} [Group H] [Group L] (f : H →* L)
    (hidx : f.ker.index = 3) : IsPGroup 3 f.range := by
  have hcard : Nat.card (H ⧸ f.ker) = 3 ^ 1 := by
    rw [pow_one]
    exact hidx
  exact (IsPGroup.of_card hcard).of_equiv (QuotientGroup.quotientKerEquivRange f)

theorem le_of_isSubnormal_image_three {L : Type} [Group L] [Finite L] (N : Subgroup L) [N.Normal]
    {B : Subgroup L} (hB : B.IsSubnormal) (hO3 : CFSG.pCore 3 (L ⧸ N) = ⊥)
    (h3 : IsPGroup 3 (B.map (QuotientGroup.mk' N))) : B ≤ N := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hsub : (B.map (QuotientGroup.mk' N)).IsSubnormal :=
    hB.map (QuotientGroup.mk'_surjective N)
  have hle := CFSG.CGT.PushingUpLit.ThmOne.le_pCore_of_isSubnormal_of_isPGroup hsub h3
  rw [hO3] at hle
  intro x hx
  have hmem := hle (Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hx)
  rw [Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff x).mp hmem

theorem le_of_isPGroup_normal_of_isSylowTwoOf {G : Type} [Group G] [Finite G] {Y S A : Subgroup G}
    (hSY : CFSG.QuasithinUnique.IsSylowTwoOf S Y) (hAY : A ≤ Y)
    (hnorm : ∀ h ∈ Y, ∀ a ∈ A, h * a * h⁻¹ ∈ A) (hA : IsPGroup 2 A) : A ≤ S := by
  have hP1 : IsPGroup 2 (S.subgroupOf Y) := hSY.2.1.comap_subtype
  have hP2 : ¬ 2 ∣ (S.subgroupOf Y).index := hSY.2.2
  let syl : Sylow 2 ↥Y := hP1.toSylow hP2
  have : (A.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAY]
    intro h k hh hk
    exact hnorm k hk h hh
  have hA' : IsPGroup 2 (A.subgroupOf Y) := hA.comap_subtype
  have hle : A.subgroupOf Y ≤ syl := hA'.le_sylow_of_normal syl
  intro a ha
  have hmem : (⟨a, hAY ha⟩ : ↥Y) ∈ syl := hle (Subgroup.mem_subgroupOf.mpr ha)
  exact (IsPGroup.mem_toSylow hP1 hP2).mp hmem

theorem le_of_index_three_block {G : Type} [Group G] [Finite G] {Y Q B : Subgroup G}
    [(Q.subgroupOf Y).Normal] (hBY : B ≤ Y)
    (hB : (B.subgroupOf Y).IsSubnormal)
    (hO3 : CFSG.pCore 3 (↥Y ⧸ Q.subgroupOf Y) = ⊥)
    (hidx : ((Q.subgroupOf Y).subgroupOf (B.subgroupOf Y)).index = 3) : B ≤ Q := by
  let f : ↥(B.subgroupOf Y) →* ↥Y ⧸ Q.subgroupOf Y :=
    (QuotientGroup.mk' (Q.subgroupOf Y)).comp (B.subgroupOf Y).subtype
  have hk : f.ker = (Q.subgroupOf Y).subgroupOf (B.subgroupOf Y) := by
    ext x
    simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have h3 : IsPGroup 3 ((B.subgroupOf Y).map (QuotientGroup.mk' (Q.subgroupOf Y))) := by
    have hr := isPGroup_three_range_of_index f (by rw [hk]; exact hidx)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at hr
  have hle := le_of_isSubnormal_image_three (Q.subgroupOf Y) hB hO3 h3
  intro b hb
  have hmem : (⟨b, hBY hb⟩ : ↥Y) ∈ B.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hb
  have := hle hmem
  exact Subgroup.mem_subgroupOf.mp this

theorem pCore_three_quot_eq_bot_of_R_form {G : Type} [Group G] [Finite G] {Y Q : Subgroup G}
    (hQY : Q ≤ Y) [(Q.subgroupOf Y).Normal]
    (hR : ∀ R : Subgroup G, Q ≤ R → R ≤ Y → (∀ y ∈ Y, ∀ r ∈ R, y * r * y⁻¹ ∈ R) →
      (∃ k : ℕ, Q.relIndex R = 3 ^ k) → R = Q) :
    CFSG.pCore 3 (↥Y ⧸ Q.subgroupOf Y) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hM3 : IsPGroup 3 (CFSG.pCore 3 (↥Y ⧸ Q.subgroupOf Y)) := CFSG.pCore_isPGroup
  let T : Subgroup ↥Y := (CFSG.pCore 3 (↥Y ⧸ Q.subgroupOf Y)).comap (QuotientGroup.mk' (Q.subgroupOf Y))
  let R : Subgroup G := T.map Y.subtype
  have hQR : Q ≤ R := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hQY hx⟩, ?_, rfl⟩
    have h1 : QuotientGroup.mk' (Q.subgroupOf Y) (⟨x, hQY hx⟩ : ↥Y) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx)
    rw [Subgroup.mem_comap, h1]
    exact one_mem _
  have hRY : R ≤ Y := Subgroup.map_subtype_le T
  have hRn : ∀ y ∈ Y, ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
    intro y hy r hr
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hr
    exact Subgroup.mem_map.mpr ⟨(⟨y, hy⟩ : ↥Y) * t * (⟨y, hy⟩ : ↥Y)⁻¹,
      Normal.conj_mem inferInstance t ht ⟨y, hy⟩, by simp⟩
  have hrel : Q.relIndex R = (Q.subgroupOf Y).relIndex T := by
    have e1 : (Q.subgroupOf Y).map Y.subtype = Q := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQY]
    have h := Subgroup.relIndex_map_map_of_injective (f := Y.subtype) (Q.subgroupOf Y) T
      Subtype.val_injective
    rw [e1] at h
    exact h
  have hkind : ∃ k : ℕ, Q.relIndex R = 3 ^ k := by
    let f : ↥T →* (↥Y ⧸ Q.subgroupOf Y) := (QuotientGroup.mk' (Q.subgroupOf Y)).comp T.subtype
    have hker : f.ker = (Q.subgroupOf Y).subgroupOf T := by
      ext x
      simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hrange_le : f.range ≤ CFSG.pCore 3 (↥Y ⧸ Q.subgroupOf Y) := by
      rintro _ ⟨t, rfl⟩
      exact t.2
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (IsPGroup.to_le hM3 hrange_le)
    refine ⟨n, ?_⟩
    have hidx : ((Q.subgroupOf Y).subgroupOf T).index = Nat.card (↥T ⧸ f.ker) := by
      rw [hker]
      rfl
    rw [hrel, Subgroup.relIndex, hidx, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
      hn]
  have hRQ : R = Q := hR R hQR hRY hRn hkind
  rw [Subgroup.eq_bot_iff_forall]
  intro m hm
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf Y) m
  have hyT : y ∈ T := Subgroup.mem_comap.mpr hm
  have hyR : (y : G) ∈ R := Subgroup.mem_map.mpr ⟨y, hyT, rfl⟩
  rw [hRQ] at hyR
  exact (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr hyR)

theorem isSubnormal_subgroupOf_of_open {X : Type} [Group X] {A B : Subgroup X}
    (h : CFSG.Open.IsSubnormal A B) : (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

theorem pCoreOf_eq_map {G : Type} [Group G] (X : Subgroup G) :
    CFSG.Open.pCoreOf 2 X = (CFSG.pCore 2 ↥X).map X.subtype := CFSG.openPCoreOf_eq_map_pCore 2 X

theorem isPGroup_two_pCoreOf {G : Type} [Group G] (X : Subgroup G) :
    IsPGroup 2 (CFSG.Open.pCoreOf 2 X) := by
  rw [pCoreOf_eq_map]
  exact IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) X.subtype

theorem pCoreOf_subgroupOf_normal {G : Type} [Group G] {X Y : Subgroup G} (hYX : Y ≤ X)
    (hQY : CFSG.Open.pCoreOf 2 X ≤ Y) : ((CFSG.Open.pCoreOf 2 X).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hQY]
  intro h k hh hk
  rw [pCoreOf_eq_map] at hh ⊢
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hh
  exact Subgroup.mem_map.mpr ⟨(⟨k, hYX hk⟩ : ↥X) * r * (⟨k, hYX hk⟩ : ↥X)⁻¹,
    Normal.conj_mem inferInstance r hr _, by simp⟩

theorem pCoreOf_le_of_isSylowTwoOf {G : Type} [Group G] [Finite G] {X Y S : Subgroup G}
    (hYX : Y ≤ X) (hQY : CFSG.Open.pCoreOf 2 X ≤ Y)
    (hSY : CFSG.QuasithinUnique.IsSylowTwoOf S Y) : CFSG.Open.pCoreOf 2 X ≤ S := by
  have hN := pCoreOf_subgroupOf_normal hYX hQY
  refine le_of_isPGroup_normal_of_isSylowTwoOf hSY hQY ?_ (isPGroup_two_pCoreOf X)
  intro h hh a ha
  exact (Subgroup.normal_subgroupOf_iff hQY).mp hN a h ha hh

end CFSG.HardMathSupport.Cooperstein.Proving

end
