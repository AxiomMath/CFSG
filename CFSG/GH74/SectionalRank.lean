module

public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.GH74

theorem SectionalTwoRankLE.mono {X : Type*} [Group X] {r r' : ℕ} (h : r ≤ r') :
    SectionalTwoRankLE X r → SectionalTwoRankLE X r' := fun hX P hP => by
  obtain ⟨s, hs, hsP⟩ := hX P hP
  exact ⟨s, hs.trans h, hsP⟩

theorem SectionalTwoRankLE.of_injective {H X : Type*} [Group H] [Group X] (f : H →* X)
    (hf : Function.Injective f) {r : ℕ} : SectionalTwoRankLE X r → SectionalTwoRankLE H r := by
  classical
  intro hX P hP
  obtain ⟨s, hs, hsP⟩ := hX (P.map f) (hP.map f)
  have hsub : (s : Set X) ⊆ f '' (P : Set H) := fun x hx => by
    have hx' : x ∈ P.map f := hsP ▸ Subgroup.subset_closure hx
    simpa using hx'
  obtain ⟨t, -, hts⟩ := Finset.subset_set_image_iff.mp hsub
  refine ⟨t, ?_, ?_⟩
  · rw [← Finset.card_image_of_injective t hf, hts]
    exact hs
  · apply Subgroup.map_injective hf
    rw [MonoidHom.map_closure, ← Finset.coe_image, hts, hsP]

theorem SectionalTwoRankLE.subgroup {X : Type*} [Group X] {r : ℕ} (K : Subgroup X) :
    SectionalTwoRankLE X r → SectionalTwoRankLE K r :=
  SectionalTwoRankLE.of_injective K.subtype K.subtype_injective

theorem SectionalTwoRankLE.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {r : ℕ} :
    SectionalTwoRankLE X r → SectionalTwoRankLE Y r :=
  SectionalTwoRankLE.of_injective e.symm.toMonoidHom e.symm.injective

theorem SectionalTwoRankLE.of_surjective {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (hf : Function.Surjective f) {r : ℕ} :
    SectionalTwoRankLE X r → SectionalTwoRankLE Y r := by
  classical
  intro hX Q hQ
  let H : Subgroup X := Q.comap f
  let g : H →* Q := (f.comp H.subtype).codRestrict Q fun h => h.2
  have hg : Function.Surjective g := fun q => by
    obtain ⟨x, hx⟩ := hf q
    exact ⟨⟨x, by simp [H, hx]⟩, Subtype.ext hx⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 H) := inferInstance
  have hTQ : (T : Subgroup H).map g = ⊤ := by
    have h2 : (⊤ : Subgroup Q) = (T.mapSurjective hg : Subgroup Q) :=
      (T.mapSurjective hg).is_maximal' (hQ.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h2
    exact h2.symm
  have hmap : ((T : Subgroup H).map H.subtype).map f = Q := by
    have hcomp : Q.subtype.comp g = f.comp H.subtype := MonoidHom.ext fun _ => rfl
    calc ((T : Subgroup H).map H.subtype).map f
        = (T : Subgroup H).map (f.comp H.subtype) := Subgroup.map_map _ _ _
      _ = (T : Subgroup H).map (Q.subtype.comp g) := by rw [hcomp]
      _ = ((T : Subgroup H).map g).map Q.subtype := (Subgroup.map_map _ _ _).symm
      _ = Q := by rw [hTQ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨s, hs, hsT⟩ := hX ((T : Subgroup H).map H.subtype) (T.2.map H.subtype)
  refine ⟨s.image f, Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsT, hmap]

theorem SectionalTwoRankLE.quotient {X : Type*} [Group X] [Finite X] {r : ℕ} (N : Subgroup X)
    [N.Normal] : SectionalTwoRankLE X r → SectionalTwoRankLE (X ⧸ N) r :=
  SectionalTwoRankLE.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem sectionalTwoRankLE_card {X : Type*} [Group X] [Finite X] :
    SectionalTwoRankLE X (Nat.card X) := by
  intro P _
  refine ⟨(Set.toFinite (P : Set X)).toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card (P : Set X) (Set.toFinite _), ← Nat.card_coe_set_eq]
    exact Subgroup.card_le_card_group P
  · rw [Set.Finite.coe_toFinset, Subgroup.closure_eq]

theorem sectionalTwoRank_le_iff {X : Type*} [Group X] [Finite X] {r : ℕ} :
    sectionalTwoRank X ≤ r ↔ SectionalTwoRankLE X r := by
  constructor
  · intro h
    have hne : {r | SectionalTwoRankLE X r}.Nonempty := ⟨Nat.card X, sectionalTwoRankLE_card⟩
    exact (Nat.sInf_mem hne : SectionalTwoRankLE X (sectionalTwoRank X)).mono h
  · exact fun h => Nat.sInf_le (s := {r | SectionalTwoRankLE X r}) h

theorem sectionalTwoRankLE_sectionalTwoRank {X : Type*} [Group X] [Finite X] :
    SectionalTwoRankLE X (sectionalTwoRank X) :=
  sectionalTwoRank_le_iff.mp le_rfl

theorem gen4_iff_sectionalTwoRank_le {X : Type*} [Group X] [Finite X] :
    Gen4 X ↔ sectionalTwoRank X ≤ 4 :=
  sectionalTwoRank_le_iff.symm

theorem sectionalTwoRank_le_of_injective {H X : Type*} [Group H] [Group X] [Finite X]
    (f : H →* X) (hf : Function.Injective f) : sectionalTwoRank H ≤ sectionalTwoRank X := by
  have : Finite H := Finite.of_injective f hf
  exact sectionalTwoRank_le_iff.mpr
    (SectionalTwoRankLE.of_injective f hf sectionalTwoRankLE_sectionalTwoRank)

theorem sectionalTwoRank_subgroup_le {X : Type*} [Group X] [Finite X] (K : Subgroup X) :
    sectionalTwoRank K ≤ sectionalTwoRank X :=
  sectionalTwoRank_le_of_injective K.subtype K.subtype_injective

theorem sectionalTwoRank_le_of_surjective {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (hf : Function.Surjective f) : sectionalTwoRank Y ≤ sectionalTwoRank X := by
  have : Finite Y := Finite.of_surjective f hf
  exact sectionalTwoRank_le_iff.mpr
    (SectionalTwoRankLE.of_surjective f hf sectionalTwoRankLE_sectionalTwoRank)

theorem sectionalTwoRank_quotient_le {X : Type*} [Group X] [Finite X] (N : Subgroup X)
    [N.Normal] : sectionalTwoRank (X ⧸ N) ≤ sectionalTwoRank X :=
  sectionalTwoRank_le_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem sectionalTwoRank_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) : sectionalTwoRank X = sectionalTwoRank Y := by
  have : Finite Y := Finite.of_equiv X e.toEquiv
  exact le_antisymm (sectionalTwoRank_le_of_injective e.toMonoidHom e.injective)
    (sectionalTwoRank_le_of_injective e.symm.toMonoidHom e.symm.injective)

open scoped IsMulCommutative in
theorem SectionalTwoRankLE.card_le_of_elementary {X : Type*} [Group X] {r : ℕ}
    (h : SectionalTwoRankLE X r) (E : Subgroup X) (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ 2 ^ r := by
  have hP : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨s, hs, hsE⟩ := h E hP
  subst hsE
  obtain ⟨hcomm, hpow⟩ := hE
  have hdvd : Nat.card (Subgroup.closure (s : Set X)) ∣
      2 ^ Group.rank (Subgroup.closure (s : Set X)) :=
    card_dvd_exponent_pow_rank' (Subgroup.closure (s : Set X))
      fun g => Subtype.ext (by simpa using hpow g g.2)
  calc Nat.card (Subgroup.closure (s : Set X))
      ≤ 2 ^ Group.rank (Subgroup.closure (s : Set X)) := Nat.le_of_dvd (by positivity) hdvd
    _ ≤ 2 ^ s.card := Nat.pow_le_pow_right (by norm_num) (Subgroup.rank_closure_finset_le_card s)
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hs

theorem SectionalTwoRankLE.twoRank_le {X : Type*} [Group X] [Finite X] {r : ℕ}
    (h : SectionalTwoRankLE X r) : CFSG.Open.twoRank X ≤ r :=
  CFSG.SectionRank.pRank_le Nat.one_lt_two fun E _ hE => h.card_le_of_elementary E hE

theorem SectionalTwoRankLE.pRank_two_le {X : Type*} [Group X] {r : ℕ}
    (h : SectionalTwoRankLE X r) : CFSG.pRank 2 X ≤ r := by
  refine csSup_le' ?_
  rintro k ⟨A, hA, hk⟩
  have hcard := h.card_le_of_elementary A
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).mp hA)
  rw [hk] at hcard
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hcard

theorem Gen4.of_injective {H X : Type*} [Group H] [Group X] (f : H →* X)
    (hf : Function.Injective f) : Gen4 X → Gen4 H :=
  SectionalTwoRankLE.of_injective f hf

theorem Gen4.subgroup {X : Type*} [Group X] (K : Subgroup X) : Gen4 X → Gen4 K :=
  SectionalTwoRankLE.subgroup K

theorem Gen4.of_surjective {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    (hf : Function.Surjective f) : Gen4 X → Gen4 Y :=
  SectionalTwoRankLE.of_surjective f hf

theorem Gen4.quotient {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal] :
    Gen4 X → Gen4 (X ⧸ N) :=
  SectionalTwoRankLE.quotient N

theorem Gen4.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) : Gen4 X → Gen4 Y :=
  SectionalTwoRankLE.of_mulEquiv e

theorem Gen4.twoRank_le {X : Type*} [Group X] [Finite X] (h : Gen4 X) :
    CFSG.Open.twoRank X ≤ 4 :=
  SectionalTwoRankLE.twoRank_le h

theorem Gen4.pRank_two_le {X : Type*} [Group X] (h : Gen4 X) : CFSG.pRank 2 X ≤ 4 :=
  SectionalTwoRankLE.pRank_two_le h

end CFSG.GH74
