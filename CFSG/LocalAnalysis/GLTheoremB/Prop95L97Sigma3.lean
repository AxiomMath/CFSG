module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Sigma3Dec
public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Sigma3Core

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3

variable {𝔄 : Type*} [Group 𝔄] [Finite 𝔄]

theorem IsSigma3Family.main {I : Finset (Subgroup 𝔄)} (hI : IsSigma3Family I) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {δ h : 𝔄}
    (hδJ : δ ∈ Subgroup.normalizer ((⨆ L ∈ I, L : Subgroup 𝔄) : Set 𝔄))
    (hhJ : h ∈ Subgroup.normalizer ((⨆ L ∈ I, L : Subgroup 𝔄) : Set 𝔄))
    (hδp : δ ^ p = 1) {m : ℕ} (hhm : h ^ (2 ^ m) = 1) (hδh : δ * h = h * δ)
    (key : ∀ y ∈ (⨆ L ∈ I, L : Subgroup 𝔄), δ * y * δ⁻¹ = y →
      ∃ k : ℕ, (h * y * h⁻¹ * y⁻¹) ^ (2 ^ k) = 1) :
    ∀ e ∈ (⨆ L ∈ I, L : Subgroup 𝔄), e ^ 3 = 1 → h * e * h⁻¹ = e :=
  hI.conj_eq_of_components fun _ hL _ ha ha3 =>
    hI.core hp hp2 (fun _ hL' => hI.conjBy_mem hδJ hL') (fun _ hL' => hI.conjBy_mem hhJ hL')
      hδp hhm hδh key hL ha ha3

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3
