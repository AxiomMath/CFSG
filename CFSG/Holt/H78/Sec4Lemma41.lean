module

public import CFSG.Holt.H78.Sec4Bender
public import CFSG.Holt.H78.Sec4Defs
public import CFSG.Holt.Bender
public import CFSG.Timmesfeld.Bridge.SchurNarrow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open CFSG.Timmesfeld.Connectivity

section NoPolar

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Finite Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem holtPrimitiveConclusion_of_noPolar (hG : IsStarGroup G Ω) [IsPreprimitive G Ω]
    (hgen : jHull G Ω = ⊤) (hO : CFSG.pPrimeCore 2 G = ⊥)
    (hN : ∀ t ∈ longInv G Ω, ∀ u ∈ longInv G Ω, Commute t u → t ≠ u → t * u ∈ longInv G Ω) :
    ∃ q e : ℕ, IsBenderNormal Ω (⊤ : Subgroup G) q e := by
  have := hG.isPretransitive
  have hJn : IsNormalSet (longInv G Ω) := fun g x hx => conj_mem_longInv hx g
  have hJ2 : CFSG.Timmesfeld.Bridge.IsInvolutionSet (longInv G Ω) := fun d hd => hd.1
  have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by have := hG.three_le_card; omega)
  obtain ⟨α, β, hαβ⟩ := exists_pair_ne Ω
  obtain ⟨x, hx⟩ := hG.longInvAt_nonempty α
  obtain ⟨y, hy⟩ := hG.longInvAt_nonempty β
  have hdisc : Disconnected (longInv G Ω) := by
    have key : ∀ z, Reach (longInv G Ω) x z → z ∈ longInvAt G Ω α := fun z hz => by
      induction hz with
      | refl => exact hx
      | tail _ hbc ih => exact mem_longInvAt_of_commute ih hbc.2.1 hbc.2.2
    exact ⟨x, hx.1, y, hy.1, fun hreach => hαβ (eq_of_mem_longInvAt (key y hreach) hy)⟩
  have hSE := (CFSG.Timmesfeld.Bridge.fusionStronglyEmbedded_iff _).mpr
    (CFSG.Timmesfeld.Bridge.asc73For_of CFSG.ShultStronglyClosedTI.theoremTwo
      CFSG.Timmesfeld.Bridge.schurNarrowInput G (longInv G Ω) hJn hJ2 hgen hN hdisc x hx.1)
  have hinv : ∀ g : G, orderOf g = 2 → ∃! ω : Ω, g • ω = ω := fun g hg =>
    (mem_longInv_of_mem_of_fusionStronglyEmbedded hG hO (L := ⊤) inferInstance
      ⟨_, hSE.map_mulEquiv Subgroup.topEquiv.symm⟩ (Subgroup.mem_top g) hg).2
  obtain ⟨t, ht, u, hu, htu, hc⟩ := exists_commute_ne_of_pPrimeCore_eq_bot hG hO
  have hne1 : ∀ {s : G}, s ∈ longInv G Ω → s ≠ 1 := fun hs h1 => by
    have h2 := hs.1
    rw [h1, orderOf_one] at h2
    omega
  obtain ⟨V, hV4, hV2⟩ := CFSG.Timmesfeld.Bridge.twoRankAtLeastTwo_of_commute
    (mul_self_eq_one_of_mem_longInv ht) (mul_self_eq_one_of_mem_longInv hu) hc (hne1 ht)
    (hne1 hu) htu
  obtain ⟨N, q, i, hB⟩ := exists_isBenderNormal hinv hV4 fun w hw =>
    congrArg Subtype.val (hV2 ⟨w, hw⟩)
  have : N.Normal := hB.normal
  have hJN : jHull G Ω ≤ N := jHull_le_iff.mpr fun s hs =>
    le_of_isPGroup_of_odd_index hB.odd_index (isPGroup_zpowers_of_orderOf_eq_two hs.1)
      (Subgroup.mem_zpowers s)
  rw [hgen, top_le_iff] at hJN
  subst hJN
  exact ⟨q, i, hB⟩

end NoPolar

section Lemma41

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Hyp.exists_isTypeL (hS : Sec4Hyp G Ω) : ∃ (α : Ω) (v : G), IsTypeL G Ω α v := by
  by_contra h
  push Not at h
  have := hS.preprimitive
  refine hS.not_conclusion (Or.inr (holtPrimitiveConclusion_of_noPolar hS.star hS.jHull_eq_top
    hS.pPrimeCore_eq_bot fun t ht u hu htu hne => ?_))
  obtain ⟨α, htα⟩ := exists_mem_longInvAt ht
  by_contra hmem
  exact h α (t * u) ⟨t, htα, u, mem_longInvAt_of_commute htα hu htu, hne, htu, rfl, hmem⟩

end Lemma41

end CFSG.Holt.H78
