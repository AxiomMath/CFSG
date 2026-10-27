module

public import CFSG.GH74.Generic.S45.Phase1
public import CFSG.GH74.Generic.S45.PartA
public import CFSG.GH74.Generic.JMaxThin

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools CFSG.Blueprint Subgroup

structure S45Conf {G : Type} [Group G] (x : G) (K : Subgroup (CentralizerBar x)) (T : Subgroup G) :
    Prop where
  sylow : IsSylowOf 2 T (centralizer ({x} : Set G))
  comm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a
  sq : ∀ a ∈ T, a * a = 1
  card : Nat.card ↥T = 16
  x_mem : x ∈ T
  R_card : Nat.card ↥(T ⊓ Pre x K) = 8
  fusion : ∀ t ∈ T, (∃ g : G, g * x * g⁻¹ = t) ↔ t ∉ Pre x K
  not_sylow : ¬ IsSylowOf 2 T ⊤
  aut_card : Nat.card ↥T.normalizerMonoidHom.range = 168
  rank : 3 ≤ pRank 2 G
  nonabSylow : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)
  jmax : IsJMax x K
  nothin : ¬ GLS.HasTwoThinConfiguration G

@[expose] def B_S45_pumpup : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → Gen4 G → KGH G →
    ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K → IsJ1OrRee ↥K →
      xbar x ∉ K → ∀ T : Subgroup G, S45Conf x K T → False

section Main

variable {G : Type} [Group G] [Finite G]

theorem s45_false (hK : B_S45_KFacts) (hP : B_S45_pumpup)
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hr : 3 ≤ Open.twoRank G)
    (hnab : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) (hgen : Gen4 G) (hKGH : KGH G)
    {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K)
    (hj : IsJ1OrRee ↥K) (hnot : xbar x ∉ K) (hmax : IsJMax x K)
    (hthin : ¬ GLS.HasTwoThinConfiguration G) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : KData (CentralizerBar x) K (xbar x) :=
    { gen4 := gen4_centralizerBar hgen x
      oddcore := pPrimeCore_quotient_pPrimeCore_eq_bot _ 2
      central := fun g => xbar_comm x g
      sq := xbar_mul_self hx
      ne := xbar_ne_one hx
      comp := hKc
      notin := hnot
      facts := hK ↥K hj }
  obtain ⟨R₀, T, hR₀K, hc⟩ := hd.exists_conf2 (card_D_eq_two hs hn hx hd)
  have hcard : Nat.card ↥T = 16 := hc.lift.card_eq.trans hc.S_card
  have h315' : ∀ A' : Subgroup (MulAut ↥T), Nat.card ↥A' ≠ 315 :=
    fun A' => no_subgroup_card_315 ↥T hcard A'
  refine hP G hs hn hgen hKGH x hx K hKc hj hnot T ?_
  refine ⟨hc.lift.sylow, fun a ha b hb => hc.lift.comm hc.S_comm ha hb,
    fun a ha => hc.lift.sq_eq_one hc.S_sq ha, hcard, hc.lift.x_mem hx, ?_, ?_,
    hc.not_isSylowOf_top hs hn hx h315', (fusion_step hs hn hx hc h315').2.2.1,
    by rw [CFSG.SectionRank.pRank_eq_open_pRank_top]; exact hr, hnab, hmax, hthin⟩
  · rw [← hd.Rg_eq hR₀K hc]
    exact hc.card_Rg
  · intro t ht
    rw [hc.fusion_iff hs hn hx h315' t ht, hd.Rg_eq hR₀K hc]
    simp [ht]

end Main

theorem s_shapeCase_S4_of_leaves (hK : B_S45_KFacts) (hP : B_S45_pumpup) :
    S_shapeCaseMaxNT @ShapeS4 := by
  intro G _ _ hs hn hr hgen hKGH hnab _ x hx K hKc _ hP'
  obtain ⟨hthin, hmax, hsh⟩ := hP'
  exfalso
  obtain ⟨⟨f, hf⟩, hnot⟩ := hsh
  exact s45_false hK hP hs hn hr hnab hgen hKGH hx hKc (Or.inr ⟨f, hf⟩) hnot hmax hthin

theorem s_shapeCase_S5_of_leaves (hK : B_S45_KFacts) (hP : B_S45_pumpup) :
    S_shapeCaseMaxNT @ShapeS5 := by
  intro G _ _ hs hn hr hgen hKGH hnab _ x hx K hKc _ hP'
  obtain ⟨hthin, hmax, hsh⟩ := hP'
  exfalso
  obtain ⟨hJ, hnot⟩ := hsh
  exact s45_false hK hP hs hn hr hnab hgen hKGH hx hKc (Or.inl hJ) hnot hmax hthin

end CFSG.GH74.Generic.S45
