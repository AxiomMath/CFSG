module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.LocalAnalysis.GLTheoremB.BaseCase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P51

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_not_le_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hchar : IsCharTwoType G) {S H D : Subgroup G} (hS : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hHN : H ≤ Subgroup.normalizer (S : Set G)) (hDN : D ≤ Subgroup.normalizer (S : Set G))
    (hD : IsElemAbelian p D) (hDnc : ¬ IsCyclic D)
    (hHD : H ≤ Subgroup.centralizer (D : Set G)) (hH2 : ¬ IsPGroup 2 H) :
    ∃ a' ∈ D, a' ≠ 1 ∧ ¬ H ≤ Subgroup.centralizer
      ((pCoreOf 2 (Subgroup.normalizer (S : Set G)) ⊓
        Subgroup.centralizer ({a'} : Set G) : Subgroup G) : Set G) := by
  by_contra hcon
  have hall : ∀ a ∈ D, a ≠ 1 → H ≤ Subgroup.centralizer
      ((pCoreOf 2 (Subgroup.normalizer (S : Set G)) ⊓
        Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
    intro a ha ha1
    by_contra hnot
    exact hcon ⟨a, ha, ha1, hnot⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hrank : p ^ 2 ≤ Nat.card D := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (isPGroup_of_isElemAbelian hD)
    by_contra hlt
    push Not at hlt
    apply hDnc
    rcases n with _ | _ | n
    · have h1 : Nat.card D = 1 := by simpa using hn
      haveI : Subsingleton D := (Nat.card_eq_one_iff_unique.mp h1).1
      infer_instance
    · have h1 : Nat.card D = p := by simpa using hn
      exact isCyclic_of_prime_card h1
    · have h2 : p ^ 2 ≤ p ^ (n + 1 + 1) := Nat.pow_le_pow_right hp.pos (by omega)
      rw [← hn] at h2
      exact absurd hlt (not_lt.mpr h2)
  have hX2 : IsPGroup 2 (pCoreOf 2 (Subgroup.normalizer (S : Set G))) := by
    unfold pCoreOf
    exact CFSG.pCore_isPGroup.map _
  have hXcop : Nat.Coprime p (Nat.card (pCoreOf 2 (Subgroup.normalizer (S : Set G)))) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hX2
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hAX : D ≤ Subgroup.normalizer
      ((pCoreOf 2 (Subgroup.normalizer (S : Set G)) : Subgroup G) : Set G) :=
    hDN.trans (le_normalizer_pCoreOf 2 (Subgroup.normalizer (S : Set G)))
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity hp hD hrank
    hAX hXcop
  have hHX : H ≤ Subgroup.centralizer
      ((pCoreOf 2 (Subgroup.normalizer (S : Set G)) : Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    have key : (⨆ (a : G) (_ : a ∈ D) (_ : a ≠ 1),
        pCoreOf 2 (Subgroup.normalizer (S : Set G)) ⊓ Subgroup.centralizer ({a} : Set G))
        ≤ Subgroup.centralizer (H : Set G) := by
      refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
      exact Subgroup.le_centralizer_iff.mp (hall a ha ha1)
    rwa [hgen] at key
  have hHX' : H ≤ pCoreOf 2 (Subgroup.normalizer (S : Set G)) :=
    (le_inf hHN hHX).trans (hchar (Subgroup.normalizer (S : Set G)) ⟨S, hS, hS2, rfl⟩)
  exact hH2 (IsPGroup.to_le hX2 hHX')

end CFSG.LocalAnalysis.GLTheoremA.P51
