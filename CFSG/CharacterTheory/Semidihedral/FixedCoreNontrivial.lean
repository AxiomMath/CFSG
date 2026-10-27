module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialAssembly
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialParameterSum
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameter
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierGaps

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem fixedCoreNontrivial
    : SimpleLayerFrontier.FixedCoreNontrivialStatement := by
  intro G _ _ _ hGnonab hrecognition n hn S fS t ht _ hnonab hcentral hnc p f hp hpodd hf hq
    hmodel hcov hY
  exact fixed_core_nontrivial_of_cases G hGnonab hrecognition n hn S fS t ht hnonab hcentral hnc
    p f hp hpodd hf hq hmodel hcov hY
    (fun hq9 hA₀ hN d F' _ _ φ hcl => trivial_fixed_core_torus_parameter_sum G hGnonab
      hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq9 hmodel hcov hY hA₀ hN
      d F' φ hcl)
    (fun hq9 hA₀ hN d F' _ _ φ hcl => trivial_fixed_core_torus_parameter_ne G hGnonab
      hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq9 hmodel hcov hY hA₀ hN
      d F' φ hcl)

end CFSG.Semidihedral.FixedCoreNontrivial
