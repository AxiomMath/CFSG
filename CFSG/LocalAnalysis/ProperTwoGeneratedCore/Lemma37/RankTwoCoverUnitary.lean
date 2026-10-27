module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverUnitaryForm
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverAssembly
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Recognition.StrongEmbedding
public import CFSG.Milestones.SE_simple_strong_embedding_models
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelHold
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.BenderCoverStatement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCoverCentral

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ProperTwoGeneratedCore.TheoremC CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover

theorem mem_center_of_inCenterOf {G : Type*} [Group G] {S : Subgroup G} {ω : G}
    (h : InCenterOf S ω) : (⟨ω, h.1⟩ : S) ∈ Subgroup.center S :=
  Subgroup.mem_center_iff.mpr fun g => Subtype.ext (h.2 g g.2).eq

theorem inCenterOf_of_mem_center {G : Type*} [Group G] {S : Subgroup G} {z : S}
    (h : z ∈ Subgroup.center S) : InCenterOf S (z : G) :=
  ⟨z.2, fun q hq => congrArg Subtype.val (Subgroup.mem_center_iff.mp h ⟨q, hq⟩)⟩

theorem card_inCenterOf {G : Type*} [Group G] (S : Subgroup G) :
    Nat.card {ω : G // InCenterOf S ω} = Nat.card (Subgroup.center S) :=
  Nat.card_congr
    { toFun := fun ω => ⟨⟨ω.1, ω.2.1⟩, mem_center_of_inCenterOf ω.2⟩
      invFun := fun z => ⟨(z : S), inCenterOf_of_mem_center z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem rankTwoCoverUnitaryExcluded :
    RankTwoCoverUnitaryExcluded := by
  intro J _ _ hperf hZ hZne hcyc hsimple S hU
  obtain ⟨H, _, U, hT, hSU⟩ := hU
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective
    (QuotientGroup.mk'_surjective (Subgroup.center J)) 2 S
  have hnonab := exists_mul_ne_of_perfect (commutator_quotient_center_eq_top hperf)
  have hemb := (CFSG.LyonsUnitaryFour.lyons_unitary_four_sylow_strong_embedding hnonab hT
    (centralSylow Q) U hSU).2
  have hB := CFSG.Milestones.bender_suzuki _ hemb
  have hBF : BenderBorelFacts (J ⧸ Subgroup.center J) (centralImage (Q : Subgroup J)) :=
    benderBorelFactsHold (J ⧸ Subgroup.center J) hB (centralSylow Q)
  obtain ⟨-, hZcomm, hsq_iff, -, hZcard⟩ :=
    CFSG.LyonsUnitaryFour.unitary_four_sylow_structure hT (centralSylow Q) U hSU
  obtain ⟨u, huZ, hu2⟩ := exists_orderOf_eq_two_of_isPGroup hZ hZne
  have hu : ∀ s ∈ Subgroup.center J, s * s = 1 → s = 1 ∨ s = u := by
    intro s hs hs2
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    · exact Or.inr (eq_of_orderOf_eq_two_of_isCyclic hcyc hs huZ
        (orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1) hu2)
  have hZQ : Subgroup.center J ≤ (Q : Subgroup J) := hZ.le_sylow_of_normal Q
  have hW2 : ∀ ω, InCenterOf (centralImage (Q : Subgroup J)) ω → ω * ω = 1 := by
    intro ω hω
    have := (hsq_iff ⟨ω, hω.1⟩).mpr (mem_center_of_inCenterOf hω)
    rw [pow_two] at this
    exact congrArg Subtype.val this
  have hcard : Nat.card {ω : J ⧸ Subgroup.center J //
      InCenterOf (centralImage (Q : Subgroup J)) ω} = 4 := by
    rw [card_inCenterOf]
    exact hZcard
  have hab : ∀ x y : J, x ∈ (Q : Subgroup J) → y ∈ (Q : Subgroup J) →
      InCenterOf (centralImage (Q : Subgroup J)) (x : J ⧸ Subgroup.center J) →
      InCenterOf (centralImage (Q : Subgroup J)) (y : J ⧸ Subgroup.center J) →
      x * y = y * x := by
    intro x y hx hy hxc hyc
    have hker : ∀ c, centralSylowMap Q c = 1 ↔ (c : J) ∈ Subgroup.center J := fun c => by
      rw [show centralSylowMap Q c = coverHom Q (MulEquiv.refl _) c from rfl,
        coverHom_eq_one_iff]
    have key := commute_of_map_mem_center (centralSylowMap Q)
      (fun c hc g => Subtype.ext (Subgroup.mem_center_iff.mp ((hker c).mp hc) g))
      (centralSylowMap_surjective Q)
      (fun z z' hz hz' hz2 hz'2 hz1 hz'1 => by
        have h1 := (hu z ((hker z).mp hz) (congrArg Subtype.val hz2)).resolve_left
          (fun h => hz1 (Subtype.ext h))
        have h2 := (hu z' ((hker z').mp hz') (congrArg Subtype.val hz'2)).resolve_left
          (fun h => hz'1 (Subtype.ext h))
        exact Subtype.ext (h1.trans h2.symm))
      (hZcomm ▸ le_refl _)
      (fun r hr => by
        have := (hsq_iff r).mpr hr
        rwa [pow_two] at this)
      (w₁ := ⟨x, hx⟩) (w₂ := ⟨y, hy⟩) (mem_center_of_inCenterOf hxc)
      (mem_center_of_inCenterOf hyc)
    exact congrArg Subtype.val key
  obtain ⟨w₀, hw₀Q, hw₀c, hw₀Z⟩ := exists_central_lift_of_borelFacts hZQ hu hBF hab hW2 hcard
  exact hZne (center_eq_bot_of_borelFacts hperf hZ hu Q hBF hw₀Q hw₀c hw₀Z)

theorem eq_of_orderOf_eq_two_of_rankTwo_cover
    {J : Type} [Group J] [Finite J]
    (hperf : commutator J = ⊤) (hZ : IsPGroup 2 (Subgroup.center J))
    (hZne : Subgroup.center J ≠ ⊥) (hcyc : IsCyclic (Subgroup.center J))
    (hsimple : IsSimpleGroup (J ⧸ Subgroup.center J))
    (hrank : CFSG.Assembly.twoRank (J ⧸ Subgroup.center J) = 2) {x y : J}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y :=
  eq_of_orderOf_eq_two_of_rankTwo_cover_of_unitaryExcluded rankTwoCoverUnitaryExcluded hperf hZ
    hZne hcyc hsimple hrank hx hy

theorem rankTwoCoverStatement
    : RankTwoCoverStatement :=
  fun _ _ _ hperf hZ hZne hcyc hsimple hrank _ _ hx hy =>
    eq_of_orderOf_eq_two_of_rankTwo_cover hperf hZ hZne hcyc hsimple hrank hx hy

end CFSG.ProperTwoGeneratedCore.Lemma37
