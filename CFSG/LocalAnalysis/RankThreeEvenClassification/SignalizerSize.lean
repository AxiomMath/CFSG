module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeFunctor

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem signalizerSpectrum_finite {G : Type u} [Group G] [Finite G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) :
    (signalizerSpectrum actor signalizer).Finite := by
  apply (Set.finite_Iic (Nat.card G)).subset
  rintro prime ⟨_, element, _, _, hdiv⟩
  exact Nat.le_of_dvd Nat.card_pos (hdiv.trans (Subgroup.card_subgroup_dvd_card (signalizer element)))

theorem subgroup_card_map_of_injOn {G : Type u} {H : Type v} [Group G] [Group H]
    (subgroup : Subgroup G) (homomorphism : G →* H)
    (hinjective : Set.InjOn homomorphism (subgroup : Set G)) :
    Nat.card (subgroup.map homomorphism) = Nat.card subgroup := by
  let restricted : subgroup → subgroup.map homomorphism :=
    fun element => ⟨homomorphism element, Subgroup.mem_map_of_mem homomorphism element.property⟩
  have hbijective : Function.Bijective restricted := by
    constructor
    · intro first second heq
      apply Subtype.ext
      exact hinjective first.property second.property (congrArg Subtype.val heq)
    · intro element
      obtain ⟨preimage, hpreimage, heq⟩ := Subgroup.mem_map.mp element.property
      exact ⟨⟨preimage, hpreimage⟩, Subtype.ext heq⟩
  exact (Nat.card_congr (Equiv.ofBijective restricted hbijective)).symm

theorem subgroup_map_commutative {G : Type u} {H : Type v} [Group G] [Group H]
    (subgroup : Subgroup G) (homomorphism : G →* H) (hcomm : IsMulCommutative subgroup) :
    IsMulCommutative (subgroup.map homomorphism) := by
  apply isMulCommutative_iff.mpr
  intro first second
  obtain ⟨firstPreimage, hfirstPreimage, hfirstEq⟩ := Subgroup.mem_map.mp first.property
  obtain ⟨secondPreimage, hsecondPreimage, hsecondEq⟩ := Subgroup.mem_map.mp second.property
  apply Subtype.ext
  change (first : H) * second = (second : H) * first
  rw [← hfirstEq, ← hsecondEq, ← map_mul, ← map_mul]
  apply congrArg homomorphism
  exact congrArg (fun element : subgroup => (element : G))
    (isMulCommutative_iff.mp hcomm ⟨firstPreimage, hfirstPreimage⟩ ⟨secondPreimage, hsecondPreimage⟩)

theorem subgroup_map_prime_power {G : Type u} {H : Type v} [Group G] [Group H]
    (subgroup : Subgroup G) (homomorphism : G →* H) (prime : ℕ)
    (hpower : ∀ member : subgroup, member ^ prime = 1) :
    ∀ member : subgroup.map homomorphism, member ^ prime = 1 := by
  intro member
  obtain ⟨preimage, hpreimage, heq⟩ := Subgroup.mem_map.mp member.property
  apply Subtype.ext
  change (member : H) ^ prime = 1
  rw [← heq, ← map_pow]
  have hone : preimage ^ prime = 1 := congrArg (fun element : subgroup => (element : G))
    (hpower ⟨preimage, hpreimage⟩)
  rw [hone, map_one]

theorem prime_deleted_signalizerSpectrum_ncard_lt {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (deleted : ℕ) (hdeleted : deleted ∈ signalizerSpectrum actor signalizer) :
    (signalizerSpectrum actor
      (primeSetSignalizer (signalizerSpectrum actor signalizer \ {deleted}) actor signalizer)).ncard <
      (signalizerSpectrum actor signalizer).ncard := by
  apply Set.ncard_lt_ncard _ (signalizerSpectrum_finite actor signalizer)
  apply Set.ssubset_iff_subset_ne.mpr
  have hsubset := signalizerSpectrum_primeSetSignalizer_subset prime hprime
    (signalizerSpectrum actor signalizer \ {deleted}) actor signalizer hpgroup hsignalizer
  refine ⟨hsubset.trans Set.inter_subset_right, ?_⟩
  intro heq
  have hmem := heq.symm ▸ hdeleted
  exact (hsubset hmem).1.2 rfl

end CFSG.RankThreeEvenClassification.Helpers
