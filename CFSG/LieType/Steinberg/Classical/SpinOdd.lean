module

public import CFSG.LieType.Steinberg.Classical.SpinOdd.Commutator
public import CFSG.LieType.Steinberg.Classical.SpinOdd.Weyl
public import CFSG.LieType.Steinberg.Classical.SpinOdd.RankOne
public import CFSG.LieType.Steinberg.Classical.SpinOdd.Unipotent
public import CFSG.LieType.Steinberg.Classical.SpinOdd.RankTwo
public import CFSG.LieType.CurtisTits.Spin

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinOdd

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem

variable {n : ℕ} {K : Type} [Field K]

theorem chevalleyExtras (hn : 2 ≤ n) (O : CommOrder (Φ n K))
    (C : (Fin n → ℤ) → (Fin n → ℤ) → ℕ × ℕ → ℤ) (hC : CommutatorFormula (x n K) O C) :
    ChevalleyExtras (oddDatum n K) K (x n K) C O where
  param := isParametrization
  comm := hC
  weyl i _ hβ := weyl i hβ
  rankOne i := rankOne i
  prodInjective f L hL hpos hsort := prodInjective f L hL hpos hsort
  rankTwo i := rankTwo hn hC i

theorem isCTGroupDatum (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    IsCTGroupDatum (coxeterMatrix (oddDatum n K).isFiniteType).toCoxeterSystem
      (weylAction (oddDatum n K).isFiniteType) (oddDatum n K).roots (oddDatum n K).rootGroup
      (weylB K) (fun k => (torusB K k).range) :=
  oddDatum_isCTGroupDatum n K (oddDatum_iSup_eq_top n K h2 hn)

theorem presentationB [Finite K] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    PresentationB (Φ := Φ n K) (x n K) :=
  presentationB_of rfl
    (fun O => ⟨commC, commC_natAbs_mem (K := K), commutatorFormula O⟩)
    (fun O C hC => chevalleyExtras (by omega) O C hC)
    (bijective_stPi_of (isCTGroupDatum h2 hn) (oddDatum_steinbergExtras h2)).2

theorem redundantR2 [Finite K] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    RedundantR2 (Φ n K) (oddDatum n K).rootGroup :=
  redundantR2_of rfl (fun O => ⟨commC, commutatorFormula O⟩)
    (fun O C hC => chevalleyExtras (by omega) O C hC)
    (bijective_stPi_of (isCTGroupDatum h2 hn) (oddDatum_steinbergExtras h2)).2

theorem conclusionB [Finite K] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    ConclusionB (oddDatum n K) K (x n K) :=
  conclusionB_of rfl (isCTGroupDatum h2 hn) (oddDatum_steinbergExtras h2) isParametrization
    (fun O => ⟨commC, commC_natAbs_mem (K := K), commutatorFormula O⟩)
    (fun O C hC => chevalleyExtras (by omega) O C hC)

end CFSG.LieType.Steinberg.SpinOdd
