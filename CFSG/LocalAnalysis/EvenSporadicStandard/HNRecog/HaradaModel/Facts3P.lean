module

public import Certificates.Certificate441603
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquivAux
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixPrimes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongrK

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup

structure Cent3Facts : Prop where
  three_conj : ∀ x y : ↥P1408, orderOf x = 3 → orderOf y = 3 → IsConj x y
  card_C3 : ∀ x : ↥P1408, orderOf x = 3 → Nat.card (centralizer ({x} : Set ↥P1408)) = 1440
  odd_normal : ∀ x : ↥P1408, orderOf x = 3 → ∀ N : Subgroup ↥P1408,
    N ≤ centralizer ({x} : Set ↥P1408) →
    (∀ c ∈ centralizer ({x} : Set ↥P1408), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → Odd (Nat.card N) →
    N ≤ zpowers x
  card_tT : ∀ x : ↥P1408, orderOf x = 3 →
    Set.ncard {y : ↥P1408 | y ∈ centralizer ({x} : Set ↥P1408) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧
      tTH pA pZ pZ₁ y} = 46
  perfect60 : ∀ x : ↥P1408, orderOf x = 3 → ∃ M : Subgroup ↥P1408,
    M ≤ centralizer ({x} : Set ↥P1408) ∧ ⁅M, M⁆ = M ∧ Nat.card M = 60 ∧ M ⊓ zpowers x = ⊥
  W_comm : ∀ x : ↥P1408, orderOf x = 3 → ∃ s : ↥P1408, s ∈ centralizer ({x} : Set ↥P1408) ∧
    s ^ 2 = 1 ∧ s ≠ 1 ∧ tTH pA pZ pZ₁ s ∧ s ∈ ⁅WsubH pA pZ pZ₁ x, WsubH pA pZ pZ₁ x⁆

section Cert



theorem cent3Facts_P (hP : Nat.card ↥P1408 = 177408000) : Cent3Facts := by
  have hpf := primeFacts3 hP
  obtain ⟨hodd, hperf, hcard, hw⟩ :=
    Certificates.certificate441603 hpf (not_isConj_inv hP)
  have key : ∀ x : ↥P1408, orderOf x = 3 → IsConj (repP fix3) x := fun x hx => by
    obtain ⟨d, hd, hc⟩ := hpf.2 x hx
    obtain rfl : d = fix3 := by simpa using hd
    exact hc
  exact
    { three_conj := fun x y hx hy => (key x hx).symm.trans (key y hy)
      card_C3 := fun x hx => by
        obtain ⟨c, rfl⟩ := isConj_iff.1 (key x hx)
        have e : ↥(centralizer ({repP fix3} : Set ↥P1408)) ≃*
            ↥(centralizer ({c * repP fix3 * c⁻¹} : Set ↥P1408)) :=
          TwoHSData.centralizerMulEquiv (MulAut.conj c) (repP fix3)
        rw [← Nat.card_congr e.toEquiv,
          Nat.card_congr (centralizerSubtypeEquiv P1408 (repP fix3)).toEquiv]
        exact (hpf.1 fix3 (by simp)).1
      odd_normal := fun x hx => (hodd.of_isConj (key x hx))
      card_tT := fun x hx => hcard.of_isConj (key x hx)
      perfect60 := fun x hx => hperf.of_isConj (key x hx)
      W_comm := fun x hx => hw.of_isConj (key x hx) }

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
