module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddFull
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint
open CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

theorem ambLQ_of_classical {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Type} [Group H] [Finite H]
    (S : Subgroup H) [S.Normal] {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (ht : t ∈ classicalTags) (hcl : CFSG.Open.StatedClassicalModel ↥S t n p f)
    (hC : Subgroup.centralizer (S : Set H) = ⊥)
    {Q : Subgroup H} (hQS : Q ≤ S) (hQ : Q ≠ ⊥) (hQp : IsPGroup p ↥Q) :
    ∀ h ∈ Subgroup.normalizer (Q : Set H),
      (∀ r ∈ pCoreOf p (Subgroup.normalizer (Q : Set H)), h * r = r * h) →
      h ∈ pCoreOf p (Subgroup.normalizer (Q : Set H)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hH : CFSG.LieType.BorelTits.Holds ↥S p :=
    CFSG.LieType.BorelTits.holds_of_statedClassicalModel hcl
  exact lieQ_of_radRigid S hH.holdsTits
    (radRigid_classical_odd hp hp2 ht hcl hH) hC hQS hQ hQp

theorem ambiguousChev_prime_of_mem {r : ℕ} {i : TauCeti.CFSGIndex} (h : ambiguousChev r i) :
    r = 2 ∨ r = 3 ∨ r = 5 := by
  cases i with
  | cyclic p hp => simp [ambiguousChev] at h
  | alternating n hn =>
    simp only [ambiguousChev] at h
    omega
  | lie d =>
    obtain ⟨lt, hv⟩ := d
    cases lt <;> simp only [ambiguousChev] at h <;> split at h <;> tauto
  | sporadic s => simp [ambiguousChev] at h

end CFSG.LocalAnalysis.GLTheoremA
