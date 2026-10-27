module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7End1
public import CFSG.GH74.SectionalRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec65_quasisimple {X : Subgroup G} (hXF : InFStar X) : IsQuasisimple ↥X := by
  unfold InFStar IsFStarGroup IsFGroup at hXF
  rcases hXF with ⟨hq, _⟩ | ⟨hq, _⟩
  · exact hq
  · exact hq

theorem sec65_shape [Finite G] (hsh : Asc82Shapes) {t : G} {L X : Subgroup G}
    (hS : Sec3SettingLB G t L) (hXC : InC X) (hXF : InFStar X) :
    IsL29 X ∨ IsL281 X ∨ IsL3Eps3 X ∨ IsOmega5 X ∨ IsOmega6Plus X ∨ IsOmega6Minus X := by
  unfold InFStar IsFStarGroup at hXF
  rcases hXF with hF | ⟨-, hQ⟩
  · obtain ⟨x, hx, hXx⟩ := hXC
    have h : Sec3SettingLB G x X := sec3SettingLB_of_component hS hx hXx hF
    rcases hsh G x X h with h5 | h6p | h6m
    · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6p))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6m))))
  · unfold SmallF3StarQuotient at hQ
    rcases hQ with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr h)))

theorem sec65_pRank_le_of_sylow [Finite G] {C T H : Subgroup G} (hT : IsSylow2Of T C)
    (hHC : H ≤ C) (hH : IsPGroup 2 H) {m : ℕ} (hm : CFSG.Open.pRank 2 T ≤ m) :
    CFSG.Open.pRank 2 H ≤ m := by
  obtain ⟨c, _hcC, hc⟩ := exists_conj_le_of_isSylow2Of hT hH hHC
  let f : G →* G := (MulAut.conj c).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj c).injective
  have hmap : H.map f ≤ T := by
    rintro _ ⟨k, hk, rfl⟩
    simpa [f, MulAut.conj_apply] using hc k hk
  calc CFSG.Open.pRank 2 H ≤ CFSG.Open.pRank 2 (H.map f) :=
        CFSG.SectionRank.pRank_le_map (by norm_num) f hf H
    _ ≤ CFSG.Open.pRank 2 T := CFSG.SectionRank.pRank_mono (by norm_num) hmap
    _ ≤ m := hm

theorem sec65_pRank_cyclic [Finite G] {T : Subgroup G} (hT : IsCyclic ↥T) :
    CFSG.Open.pRank 2 T ≤ 1 := by
  refine CFSG.SectionRank.pRank_le (k := 1) (by norm_num) ?_
  intro E hET hE
  calc Nat.card E ≤ 2 := sec7End_card_le hET hT (by norm_num : 0 < 2) hE.2
    _ = 2 ^ 1 := by norm_num

theorem sec65_pRank_sectional [Finite G] {T : Subgroup G}
    (hT : CFSG.GH74.sectionalTwoRank ↥T ≤ 3) : CFSG.Open.pRank 2 T ≤ 3 := by
  have h3 : CFSG.GH74.SectionalTwoRankLE ↥T 3 := fun P hP => by
    obtain ⟨s, hs, hsP⟩ := CFSG.GH74.sectionalTwoRankLE_sectionalTwoRank (X := ↥T) P hP
    exact ⟨s, hs.trans hT, hsP⟩
  refine CFSG.SectionRank.pRank_le (k := 3) (by norm_num) ?_
  intro E hET hE
  let E' : Subgroup ↥T := E.subgroupOf T
  have hE' : CFSG.Open.IsElemAbelian 2 E' := by
    obtain ⟨hcomm, hpow⟩ := hE
    haveI : IsMulCommutative ↥E := hcomm
    refine ⟨IsMulCommutative.of_comm (fun a b => ?_), fun x hx => ?_⟩
    · apply (Subgroup.subgroupOfEquivOfLe hET).injective
      rw [map_mul, map_mul]
      exact mul_comm' _ _
    · apply Subtype.ext
      simpa using hpow ((x : ↥T) : G) (Subgroup.mem_subgroupOf.mp hx)
  calc Nat.card E = Nat.card E' :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv).symm
    _ ≤ 2 ^ 3 := CFSG.GH74.SectionalTwoRankLE.card_le_of_elementary h3 E' hE'

theorem sec65_core [Finite G] (hsh : Asc82Shapes) (hF : Asc82AutFacts) (h64 : Asc82Lemma64)
    {t : G} {L X E : Subgroup G} (hS : Sec3SettingLB G t L) (hHyp : Asc82Hyp62 G)
    (hXC : InC X) (hXF : InFStar X) (hEN : E ≤ normalizer (X : Set G))
    (hE : CFSG.Open.IsElemAbelian 2 E) : CFSG.Open.pRank 2 E ≤ 6 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, IsSylow2Of T (centralizer (X : Set G)) :=
    ⟨_, isSylow2Of_map_sylow (Classical.arbitrary (Sylow 2 ↥(centralizer (X : Set G))))⟩
  have hq : IsQuasisimple ↥X := sec65_quasisimple hXF
  have hra := hF.rank_aut G X E hq hEN hE
  have hE2 : IsPGroup 2 ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 (g : G) g.2)⟩
  have hE2' : IsPGroup 2 ↥(E ⊓ centralizer (X : Set G)) := hE2.to_le inf_le_left
  have hrank : ∀ m : ℕ, CFSG.Open.pRank 2 T ≤ m →
      CFSG.Open.pRank 2 (E ⊓ centralizer (X : Set G)) ≤ m :=
    fun m hm => sec65_pRank_le_of_sylow hT inf_le_right hE2' hm
  rcases h64 G t L hS hHyp X hXC hXF T hT with hcyc | ⟨hshape, hr2⟩ | ⟨hshape, hs3⟩
  · have h1 : CFSG.Open.pRank 2 (E ⊓ centralizer (X : Set G)) ≤ 1 :=
      hrank 1 (sec65_pRank_cyclic hcyc)
    rcases sec65_shape hsh hS hXC hXF with h | h | h | h | h | h
    · have hb := hra.1 (Or.inl h); omega
    · have hb := hra.1 (Or.inr (Or.inl h)); omega
    · have hb := hra.1 (Or.inr (Or.inr h)); omega
    · have hb := hra.2.1 h; omega
    · have hb := hra.2.2 (Or.inl h); omega
    · have hb := hra.2.2 (Or.inr h); omega
  · have h2 : CFSG.Open.pRank 2 (E ⊓ centralizer (X : Set G)) ≤ 2 := hrank 2 hr2.le
    rcases hshape with h | h | h
    · have hb := hra.1 (Or.inr (Or.inr h)); omega
    · have hb := hra.1 (Or.inl h); omega
    · have hb := hra.2.1 h; omega
  · have h3 : CFSG.Open.pRank 2 (E ⊓ centralizer (X : Set G)) ≤ 3 :=
      hrank 3 (sec65_pRank_sectional hs3)
    rcases hshape with h | h
    · have h3e : IsL3Eps3 X := Or.inr h
      have hb := hra.1 (Or.inr (Or.inr h3e)); omega
    · have hb := hra.1 (Or.inl h); omega

theorem asc82Lemma65_of (hsh : Asc82Shapes) (hF : Asc82AutFacts) (h64 : Asc82Lemma64) :
    Asc82Lemma65 := by
  intro G _ _ t L hS hHyp X hXC hXF
  obtain ⟨E, hEN, hE, hcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) (normalizer (X : Set G))
  have h1 : CFSG.Open.pRank 2 (normalizer (X : Set G)) ≤ CFSG.Open.pRank 2 E :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE hcard
  have h2 : CFSG.Open.pRank 2 E ≤ 6 := sec65_core hsh hF h64 hS hHyp hXC hXF hEN hE
  omega

end CFSG.OddStandard.SmallF3.Omega
