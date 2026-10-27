module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Data
public import CFSG.Sporadic.J4.QTMask
public import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Data
public meta import CFSG.Sporadic.J4.QTMask
public meta import CFSG.Sporadic.Mathieu.M24
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4CheckInputs
public import Certificates.Certificate4092

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs

open CFSG.Sporadic.J4.QT CFSG.Sporadic.Mathieu

set_option synthInstance.maxSize 1024 in
theorem star_facts :
    (∀ c ∈ duadMasks, 0 < c ∧ c < 2 ^ 11) ∧ starMasks.length = 24 ∧
    (∀ s ∈ starMasks, s.length = 23 ∧ ∀ c ∈ s, c ∈ duadMasks) ∧
    (∀ i < 24, ∃ c₁ ∈ starMasks.getD i [], ∃ c₂ ∈ starMasks.getD i [], c₁ ≠ c₂) ∧
    (∀ i < 24, ∀ j < 24, i ≠ j → ∀ c ∈ starMasks.getD i [], c ∈ starMasks.getD j [] →
      ∀ c' ∈ starMasks.getD i [], c' ∈ starMasks.getD j [] → c = c') ∧
    (∀ d ∈ duadMasks, ∃ i < 24, ∃ j < 24, i ≠ j ∧ d ∈ starMasks.getD i [] ∧
      d ∈ starMasks.getD j []) ∧
    (∀ j < 11, 2 ^ j ∈ duadMasks) :=
  Certificates.certificate4092.1

theorem star_perm_facts :
    ∀ k < 3, (starPermOf k).length = 24 ∧ (∀ i < 24, (starPermOf k).getD i 0 < 24) ∧
      ∀ i < 24, ∀ c ∈ starMasks.getD i [],
        act ((k : ℤ) + 1) c ∈ starMasks.getD ((starPermOf k).getD i 0) [] :=
  Certificates.certificate4092.2.1

theorem tau_facts :
    ∀ k < 3, (∀ i : Fin 24, ((tauOf k) i : ℕ) = (starPermOf k).getD i 0) ∧
    ((wordOf k).map genM24).prod = tauOf k :=
  Certificates.certificate4092.2.2

end CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
