
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModelBase
import all CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModelBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAut
public import Certificates.Certificate22219

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem t1_lt {k l : ℕ} (hk : k < 64) (hl : l < 64) :
    (t1Entry k l).1 < 64 :=
  (Certificates.certificate22219.1 k hk l hl).1

theorem alpha_lt {i k : ℕ} (hi : i < 36) (hk : k < 64) :
    (alphaEntry i k).1 < 64 :=
  ((Certificates.certificate22219.2.1 i hi).2.2.1 k hk).1.1

theorem t1_spec {k l : ℕ}
    (hk : k < 64) (hl : l < 64) :
    cv (tw k) * cv (tw l) = cv (tw (t1Entry k l).1) * cv (zOf (t1Entry k l)) :=
  (Certificates.certificate22219.1 k hk l hl).2.2.2.2

theorem abPerm_uA {i : ℕ}
    (hi : i < 36) : abPerm (uA i) = repPerm i * aS * (repPerm i)⁻¹ :=
  (Certificates.certificate22219.2.1 i hi).1

theorem abPerm_uB {i : ℕ}
    (hi : i < 36) : abPerm (uB i) = repPerm i * bS * (repPerm i)⁻¹ :=
  (Certificates.certificate22219.2.1 i hi).2.1

theorem conj_tg {i k : ℕ} (hi : i < 36) (hk : k < 64) :
    repPerm i * wordPerm (tg k) * (repPerm i)⁻¹ = wordPerm (tg (alphaEntry i k).1) :=
  ((Certificates.certificate22219.2.1 i hi).2.2.1 k hk).2.1

theorem exists_alpha
    {i : ℕ} (hi : i < 36) :
    ∃ α : Cover →* Cover, (∀ w, α (cv w) = cv (substWord (aut i) w)) ∧
      ∀ c, sigma (α c) = repPerm i * sigma c * (repPerm i)⁻¹ :=
  exists_autLift (repPerm i) (abPerm_uA hi) (abPerm_uB hi)

theorem alpha_spec
    {i k : ℕ} (hi : i < 36) (hk : k < 64) :
    cv (substWord (aut i) (tw k)) = cv (tw (alphaEntry i k).1) * cv (zOf (alphaEntry i k)) :=
  ((Certificates.certificate22219.2.1 i hi).2.2.1 k hk).2.2

theorem alphaZ_spec
    {i j : ℕ} (hi : i < 36) (hj : j < 2) :
    cv (substWord (aut i) (zGen j)) = cv (zOf (alphaEntry i (64 + j))) :=
  ((Certificates.certificate22219.2.1 i hi).2.2.2 j hj).2.2

theorem exists_decomp
    {y : Equiv.Perm (Fin 42)}
    (hy : y ∈ R) (hN : ∀ t ∈ T0, y * t * y⁻¹ ∈ T0) :
    ∃ i < 36, ∃ t < 64, y = wordPerm (tg t) * repPerm i :=
  Certificates.certificate22219.2.2 y hy hN

end CFSG.ComponentClassification.GrSLit.L34Facts.Real
