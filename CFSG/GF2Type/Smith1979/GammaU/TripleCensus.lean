module

public import Certificates.Certificate16969
public import CFSG.GF2Type.Smith1979.GammaU.Transport

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

theorem triple_census
    {i : ℕ} (hi : i = 0 ∨ i = 1) {r : Array ℕ}
    (hr : r ∈ unitaryElts i) (hrH : r ∉ ResPair.hyp10 i) {n : ℕ} (hn : n ∈ colPts r)
    {De : Submodule (ZMod 2) V12} {Le : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (H : Hyp (vecOf n) De Le)
    (hs : ∃ l ∈ Le, ∀ y, l y = linOfRows r y) (ha : vecOf a0 ∈ De)
    (hc : Nat.card (candGrp i Le) = 1152) :
    Viol.Violation (ResPair.n2 i ⊔ candGrp i Le) (compOf i) (compOf i) := by
  obtain ⟨r0, T, m, te, hB, hP⟩ := Certificates.certificate16969 i hi
  obtain ⟨h, hh, hrr, hcfg⟩ := hP r hr hrH
  obtain ⟨G, hG, hR⟩ := census_conj_cfg Certificates.certificate16963
    Certificates.certificate16964 (by omega) hB hh hrr hcfg hn H hs ha hc
  rw [hR]
  exact hG

end CFSG.GF2Type.Smith1979.GammaU.StepA
