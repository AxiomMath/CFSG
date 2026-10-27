module

public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit24

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C24_setupU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 p f Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoS4 Ω W →
      W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥ →
        ∃ (S : Sylow 2 G) (R R' : Subgroup G) (b b' : G), b ∈ K ⊓ W ∧ b' ∈ K' ⊓ W ∧
          orderOf b = 4 ∧ orderOf b' = 4 ∧ Hyp24 p f Ω K K' W S R R' z (b * b')

theorem c24_setupU : C24_setupU p f := by
  intro G _ _ _ Ω K K' z hs W hW hzW hS4 hZ
  have hst : AscStand p f Ω K := hs.1.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.1.hK'.1
  have hKK' : K' ≠ K := hs.1.hne
  have hz : IsUniqueInvolution K z := hs.1.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.1.hK'
  have hW2 : IsPGroup 2 W := Thompson.isPGroup_of_mem_WSet hW
  have hWab := Thompson.commutes_of_mem_WSet hp hq hΩ hW
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw z hzW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  have hR : IsSylow2In (T ⊓ K) K :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (T7A.isSubnormal_centralizer hΩ hK hz)
  have hR' : IsSylow2In (T ⊓ K') K' :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (T7A.isSubnormal_centralizer hΩ hK' hz')
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  have hWS : W ≤ (S : Subgroup G) := hWT.trans hTS
  have hRS : T ⊓ K ≤ (S : Subgroup G) := inf_le_left.trans hTS
  have hR'S : T ⊓ K' ≤ (S : Subgroup G) := inf_le_left.trans hTS
  obtain ⟨x₁, hx₁, o₁⟩ := T7C.exists_orderOf_four_mem_inf hp hq hΩ hW hWS hK hR hRS hz
  obtain ⟨x₂, hx₂, o₂⟩ := T7C.exists_orderOf_four_mem_inf hp hq hΩ hW hWS hK' hR' hR'S hz'
  have s₁ : x₁ * x₁ = z := T7A.sq_eq_of_orderOf_four hz hx₁.1 o₁
  have s₂ : x₂ * x₂ = z := T7A.sq_eq_of_orderOf_four hz' hx₂.1 o₂
  have hc : x₁ * x₂ = x₂ * x₁ := hWab x₁ hx₁.2 x₂ hx₂.2
  have hx₁₂ : x₁ ∈ K ⊓ W := ⟨hx₁.1, hx₁.2⟩
  have hx₂₂ : x₂ ∈ K' ⊓ W := ⟨hx₂.1, hx₂.2⟩
  refine ⟨S, T ⊓ K, T ⊓ K', x₁, x₂, hx₁₂, hx₂₂, o₁, o₂, hs, hW, hzW, hS4, hZ, hWS,
    ⟨mem_RSet_of_isSylow2In hK hR, inf_le_right, hRS⟩,
    ⟨mem_RSet_of_isSylow2In hK' hR', inf_le_right, hR'S⟩,
    Subgroup.mul_mem_sup hx₁.1 hx₂.1, W.mul_mem hx₁.2 hx₂.2, ?_, ?_, ?_⟩
  · calc x₁ * x₂ * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
      _ = x₁ * (x₁ * x₂) * x₂ := by rw [← hc]
      _ = (x₁ * x₁) * (x₂ * x₂) := by group
      _ = 1 := by rw [s₁, s₂, hz.sq]
  · intro he
    refine T7A.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' o₂ ?_ hx₂.1
    have : x₂ = x₁⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K.inv_mem hx₁.1
  · intro he
    refine T7A.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' o₂ ?_ hx₂.1
    have : x₂ = x₁⁻¹ * z := by rw [← he]; group
    rw [this]
    exact K.mul_mem (K.inv_mem hx₁.1) hz.mem

variable {p f}

namespace T7D

theorem c24_10_of_g (h4 : C24_4 p f) (h7 : C24_7 p f) (h8 : C24_8 p f) (h9 : C24_9 p f)
    (hchain : C24_chain p f) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
    (hyp : Hyp24 p f Ω K K' W S R R' z u) {g : G} (hg : g⁻¹ * z * g = u) : ConcOrTF4 G := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hdata : Hyp24Data Ω K K' W S R R' z u := hyp.data
  obtain ⟨d, hd, hd4⟩ := T7C.exists_orderOf_four_mem_dGrp24 hs hdata hg
    (h4 G Ω K K' W S R R' z u hyp g hg) (h7 G Ω K K' W S R R' z u hyp g hg)
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

end T7D

theorem c24_1_of_inputs' (h4 : C24_4 p f) (h7 : C24_7 p f) (h8 : C24_8 p f) (h9 : C24_9 p f)
    (hchain : C24_chain p f) : C24_1 p f := by
  intro G _ _ _ Ω K K' z hs W hW hzW hS4 hZ
  obtain ⟨S, R, R', b, b', hb, hb', ob, ob', hyp⟩ := c24_setupU p f G Ω K K' z hs W hW hzW hS4 hZ
  obtain ⟨g, -, hg⟩ := T7D.c24_2_of_frame hs.setting hyp.data hb hb' ob ob' rfl
  exact T7D.c24_10_of_g h4 h7 h8 h9 hchain hyp hg

end CFSG.ClassicalInvolution.Asc77
