module

public import CFSG.ClassicalInvolution.Asc77.AscT7EC24
public import CFSG.ClassicalInvolution.Asc77.AscT7DExit24

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7E

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_orderOf_four_mem_dGrp24 [IsSimpleGroup G] {K K' : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u g : G} (hyp : Hyp24 p f Ω K K' W S R R' z u)
    (hg : g⁻¹ * z * g = u) (h8R : 8 < Nat.card ↥R) :
    ∃ d ∈ dGrp24 K S R R' g, orderOf d = 4 := by
  obtain ⟨y, hyD, hy4⟩ := exists_mem_dGrp24_of_gt hyp hg h8R
  have hyS : y ∈ (S : Subgroup G) := hyD.1.2
  have hD2 : IsPGroup 2 ↥(Subgroup.zpowers y) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hyS)
  have hcard : 4 ≤ Nat.card ↥(Subgroup.zpowers y) := by rwa [Nat.card_zpowers]
  obtain ⟨d, hd, hd4⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic hD2 inferInstance hcard
  exact ⟨d, Subgroup.zpowers_le.mpr hyD hd, hd4⟩

theorem c24_10_of_g (h8 : C24_8 p f) (h9 : C24_9 p f) (hchain : C24_chain p f) {G : Type}
    [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
    {S : Sylow 2 G} {R R' : Subgroup G} {z u : G} (hyp : Hyp24 p f Ω K K' W S R R' z u) {g : G}
    (hg : g⁻¹ * z * g = u) : ConcOrTF4 G := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hdata : Hyp24Data Ω K K' W S R R' z u := hyp.data
  obtain ⟨d, hd, hd4⟩ := exists_orderOf_four_mem_dGrp24 hyp hg (h9 G Ω K K' W S R R' z u hyp)
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  obtain ⟨x, hxW, hx4⟩ := T7C.exists_orderOf_four_mem_inf hp hq hΩ hyp.hW hyp.hWS hK' hR'syl
    hyp.hR'.2.2 hz'
  have hxR' : x ∈ R' := by
    have : K' ⊓ (S : Subgroup G) = R' :=
      hR'syl.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hyp.hR'.2.1 hyp.hR'.2.2)
    rw [← this]
    exact ⟨hxW.1, hyp.hWS hxW.2⟩
  obtain ⟨hsec, hgen⟩ := h8 G Ω K K' W S R R' z u hyp g hg d x hd hd4 ⟨hxR', hxW.2⟩ hx4
  obtain ⟨hlin, hphan⟩ := hchain G Ω K K' W S R R' z u hs hdata
    (h9 G Ω K K' W S R R' z u hyp) g hg d x hd hd4 ⟨hxR', hxW.2⟩ hx4 hsec hgen
  have hnab : ∃ a b : G, a * b ≠ b * a := T7C.exists_not_commute_of_stand hst
  refine Or.inl (Or.inl ?_)
  cases hπ : piSign p f
  · obtain ⟨U, hU⟩ := hphan hπ
    exact oddLieType_of_phanChain3 hp hq hnab hU
  · obtain ⟨U, hU⟩ := hlin hπ
    exact oddLieType_of_linearChain3 hp hq hnab hU

end T7E

variable {p f : ℕ} [Fact p.Prime]

theorem c24_1_of_inputs'' (h8 : C24_8 p f) (h9 : C24_9 p f) (hchain : C24_chain p f) :
    C24_1 p f := by
  intro G _ _ _ Ω K K' z hs W hW hzW hS4 hZ
  obtain ⟨S, R, R', b, b', hb, hb', ob, ob', hyp⟩ := c24_setupU p f G Ω K K' z hs W hW hzW hS4 hZ
  obtain ⟨g, -, hg⟩ := T7D.c24_2_of_frame hs.setting hyp.data hb hb' ob ob' rfl
  exact T7E.c24_10_of_g h8 h9 hchain hyp hg

end CFSG.ClassicalInvolution.Asc77
