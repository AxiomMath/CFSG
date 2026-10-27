module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Quot
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Cyc

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG Subgroup

theorem eq_of_center_involution_of_alternating {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) {n : ℕ} (hn : 5 ≤ n) (e : Q ⧸ center Q ≃* alternatingGroup (Fin n))
    {u v : Q} (hu : u ∈ center Q) (hv : v ∈ center Q) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) : u = v := by
  by_contra huv
  obtain ⟨N, _, -, -, hQN, h2, ⟨e'⟩, u', hu', v', hv', -, -, hu1', hv1', huv'⟩ :=
    exists_twoCover_quotient hQ hu hv hu2 hv2 hu1 hv1 huv
  have : Group.IsPerfect (Q ⧸ N) := hQN.1
  let η : Q ⧸ N →* alternatingGroup (Fin n) :=
    (e'.trans e).toMonoidHom.comp (QuotientGroup.mk' (center (Q ⧸ N)))
  have hη : Function.Surjective η :=
    (e'.trans e).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center (Q ⧸ N) := by
    ext x
    rw [MonoidHom.mem_ker]
    change (e'.trans e) (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff _ (e'.trans e).injective, QuotientGroup.eq_one_iff]
  have h := LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
    hn η hη hker.le (by rw [hker]; exact h2)
  rw [hker] at h
  have := three_le_card_of_ne hu' hv' hu1' hv1' huv'
  omega

theorem eq_of_center_involution_of_sporadic (hB : EvenSporadicStandard.CentralTwoBound)
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hS : Blueprint.NativeSporadic.SporadicRep (Q ⧸ center Q)) {u v : Q} (hu : u ∈ center Q)
    (hv : v ∈ center Q) (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    u = v := by
  by_contra huv
  obtain ⟨N, _, -, -, hQN, h2, ⟨e'⟩, u', hu', v', hv', hu2', hv2', hu1', hv1', huv'⟩ :=
    exists_twoCover_quotient hQ hu hv hu2 hv2 hu1 hv1 huv
  obtain ⟨s, ⟨e⟩⟩ := hS
  have hQN' := ((Foundations.SteinbergCA.quasisimple_iff (Q ⧸ N)).2.2.1).mp hQN
  obtain ⟨hdvd, hM22⟩ := hB (Q ⧸ N) hQN' h2 s ⟨e'.trans e⟩
  by_cases hs : s = .M22
  · have : IsCyclic (center (Q ⧸ N)) := hM22 hs
    apply huv'
    have := eq_of_involution_of_isCyclic (C := center (Q ⧸ N)) (x := ⟨u', hu'⟩)
      (y := ⟨v', hv'⟩) (Subtype.ext hu2') (Subtype.ext hv2')
      (fun h => hu1' (congrArg Subtype.val h)) (fun h => hv1' (congrArg Subtype.val h))
    exact congrArg Subtype.val this
  · have hle : EvenSporadicStandard.twoPartBound s ≤ 2 := by
      cases s <;> simp_all [EvenSporadicStandard.twoPartBound]
    have := Nat.le_of_dvd (by cases s <;> simp_all [EvenSporadicStandard.twoPartBound]) hdvd
    have := three_le_card_of_ne hu' hv' hu1' hv1' huv'
    omega

end CFSG.ComponentClassification.Sol76T13.Hq4
