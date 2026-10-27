module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.HardMathSupport.Lang.AlphaThree.UnitaryFourPairs
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.HardMathSupport.Lang.AlphaThree

open CFSG.AGLEmbedding CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

theorem liftableNormalizerGen_of_fourPairs {G L : Type*} [Group G] [Group L] (π : G →* L)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G) (h w : Fin 4 → G)
    (hcomm : ∀ i j, Commute (h i) (h j)) (hpow : ∀ i, h i ^ 3 = 1) (hne : ∀ i, h i ≠ 1)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j)
    (hgen : Subgroup.closure {x : G | ∃ j k, j ≠ k ∧ Commute x (h j) ∧ Commute x (h k)} = ⊤) :
    LiftableNormalizerGen L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : ∀ i, orderOf (π (h i)) = 3 := by
    intro i
    refine orderOf_eq_prime (by rw [← map_pow, hpow, map_one]) fun h1 => ?_
    have hmem : h i ∈ Subgroup.center G := hker (MonoidHom.mem_ker.2 h1)
    have hc : w i * h i = h i * w i := Subgroup.mem_center_iff.1 hmem (w i)
    have h2 : (h i)⁻¹ = h i := by
      rw [← hinv i, hc, mul_assoc, mul_inv_cancel, mul_one]
    have h3 : h i * h i = 1 := by
      calc h i * h i = h i * (h i)⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel _
    apply hne i
    calc h i = h i ^ 3 := by
          rw [pow_succ, pow_two, h3, one_mul]
      _ = 1 := hpow i
  refine liftableNormalizerGen_of_inverters (fun i => π (h i)) (fun i => π (w i))
    (fun i j => (hcomm i j).map π) hord
    (fun i => by simp only [← map_inv, ← map_mul, hinv i])
    (fun i j hij => by simp only [← map_inv, ← map_mul, hfix i j hij]) ?_
  rw [eq_top_iff]
  have htop : (⊤ : Subgroup L) = (Subgroup.closure {x : G | ∃ j k, j ≠ k ∧ Commute x (h j) ∧
      Commute x (h k)}).map π := by
    rw [hgen, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 hπ]
  rw [htop, MonoidHom.map_closure]
  refine Subgroup.closure_mono (Set.subset_union_of_subset_left ?_ _)
  rintro _ ⟨x, ⟨j, k, hjk, hxj, hxk⟩, rfl⟩
  exact ⟨j, k, hjk, hxj.map π, hxk.map π⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem liftableNormalizerGen_statedProj_two (hK : Nat.card K = (2 ^ 1) ^ 2) {n : ℕ}
    (hn : 9 ≤ n) : LiftableNormalizerGen (StatedProj (StatedSU n (2 ^ 1) K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) hK
  set e := equivStatedSU (p := 2) (f := 1) hK n with he
  set π : SU (unitaryInvolution K 2 1) n →* StatedProj (StatedSU n (2 ^ 1) K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ 1) K))).comp
      e.toMonoidHom with hπ
  have hsurj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp e.surjective
  have hker : π.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 1) n) := by
    intro x hx
    have h1 : e x ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ 1) K) := by
      rw [← QuotientGroup.eq_one_iff]
      exact hx
    have h2 : e x ∈ Subgroup.center (StatedSU n (2 ^ 1) K) :=
      statedScalars_subgroupOf_le_center n (2 ^ 1) h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro y
    apply e.injective
    simp only [map_mul]
    exact h2 (e y)
  exact liftableNormalizerGen_of_fourPairs π hsurj hker (hEl (unitaryInvolution K 2 1) hn)
    (sEl (unitaryInvolution K 2 1) hn) (commute_hEl_hEl hn) (hEl_pow_three hn) (hEl_ne_one hn)
    (sEl_hEl_inv hn) (fun i j hij => sEl_hEl_fix hn hij) (closure_pairCentralizing_eq_top hσ hn)

theorem liftableNormalizerGen_twistedA_two (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hr : 8 ≤ r) (hp : q.p = 2)
    (he : q.exponent = 1) :
    LiftableNormalizerGen (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) := by
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : f = 1 := he
  have hcard : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 (2 * 1) (by norm_num)]
    norm_num
  exact LiftableNormalizerGen.of_mulEquiv
    (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r _ hv).symm
    (liftableNormalizerGen_statedProj_two (K := GaloisField 2 (2 * 1)) hcard (n := r + 1) (by omega))

end CFSG.HardMathSupport.Lang.AlphaThree
