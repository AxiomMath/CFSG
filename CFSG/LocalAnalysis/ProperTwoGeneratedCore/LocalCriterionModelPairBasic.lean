module

public import CFSG.StronglyEmbedded.BenderBorelTransport
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u v

theorem card_nonidentity (G : Type u) [Group G] [Finite G] :
    Nat.card {x : G // x ≠ 1} = Nat.card G - 1 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : G => x = 1)]
  simp

theorem rank_two_of_square_one_subgroup
    {G : Type u} [Group G] [Finite G] (Z : Subgroup G)
    (hcard : 4 ≤ Nat.card Z) (hsquare : ∀ z : Z, z ^ 2 = 1) :
    TwoRankAtLeastTwo G := by
  have hp : IsPGroup 2 Z := isPGroup_iff_pow_pow_eq_one.mpr fun z =>
    ⟨1, by simpa only [pow_one] using hsquare z⟩
  obtain ⟨E, hEcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    (G := Z) (n := 2) (p := 2) Nat.prime_two hp (by simpa using hcard)
  have hrank : TwoRankAtLeastTwo Z := by
    refine ⟨E, by simpa using hEcard, ?_⟩
    intro z
    apply Subtype.ext
    exact hsquare (z : Z)
  exact twoRankAtLeastTwo_of_injective Z.subtype Z.subtype_injective hrank

theorem rank_two_of_sylow_center
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (hcard : 4 ≤ Nat.card (Subgroup.center (S : Subgroup G)))
    (hsquare : ∀ z ∈ Subgroup.center (S : Subgroup G), z ^ 2 = 1) :
    TwoRankAtLeastTwo G := by
  have hrank : TwoRankAtLeastTwo (S : Subgroup G) :=
    rank_two_of_square_one_subgroup (Subgroup.center (S : Subgroup G)) hcard
      (fun z => Subtype.ext (hsquare z z.property))
  exact twoRankAtLeastTwo_of_injective (S : Subgroup G).subtype
    (S : Subgroup G).subtype_injective hrank

theorem point_involution_card_of_sylow_center
    {G : Type u} {Omega : Type v} [Group G] [Finite G] [MulAction G Omega]
    (S : Sylow 2 G) (b : Omega)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) = MulAction.stabilizer G b)
    (hcentral : ∀ x : (S : Subgroup G), IsInvolution x →
      x ∈ Subgroup.center (S : Subgroup G))
    (hsquare : ∀ z ∈ Subgroup.center (S : Subgroup G), z ^ 2 = 1) :
    Nat.card {x : G // x ∈ MulAction.stabilizer G b ∧ IsInvolution x} =
      Nat.card (Subgroup.center (S : Subgroup G)) - 1 := by
  let Z := Subgroup.center (S : Subgroup G)
  let f : {x : G // x ∈ MulAction.stabilizer G b ∧ IsInvolution x} →
      {z : Z // z ≠ 1} := fun x => by
    have hxS : (x : G) ∈ (S : Subgroup G) :=
      involution_mem_sylow_of_normalizer_eq_stabilizer S b hN x.property.1 x.property.2
    let s : (S : Subgroup G) := ⟨x, hxS⟩
    have hsI : IsInvolution s := IsInvolution.subtype x.property.2 hxS
    exact ⟨⟨s, hcentral s hsI⟩, fun h =>
      x.property.2.ne_one (congrArg (fun z : Z => ((z : (S : Subgroup G)) : G)) h)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact congrArg (fun z : {z : Z // z ≠ 1} => (((z : Z) : (S : Subgroup G)) : G)) h
    · intro z
      let s : (S : Subgroup G) := (z : Z)
      have hsB : (s : G) ∈ MulAction.stabilizer G b := by
        rw [← hN]
        exact Subgroup.le_normalizer s.property
      have hsI : IsInvolution (s : G) := by
        constructor
        · intro h
          exact z.property (Subtype.ext (Subtype.ext h))
        · exact congrArg (fun x : (S : Subgroup G) => (x : G))
            (hsquare s (z : Z).property)
      refine ⟨⟨s, hsB, hsI⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rfl
  calc
    Nat.card {x : G // x ∈ MulAction.stabilizer G b ∧ IsInvolution x} =
        Nat.card {z : Z // z ≠ 1} := Nat.card_congr (Equiv.ofBijective f hf)
    _ = Nat.card Z - 1 := card_nonidentity Z

end CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
