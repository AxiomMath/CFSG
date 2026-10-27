module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutZ
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HASpec
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HASpec2

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaHAut

open CFSG.Fischer Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaSec3


variable {G : Type} [Group G] {L : Subgroup G} {t : G} {e : L ≃* T46}
  {Θ : centralizer ({t} : Set G) →* Equiv.Perm (Fin 693)}

theorem CH_A₁_mod' (hΘ : ThetaSpec t e Θ) :
    ∀ n ∈ (sec3DData e t).H, n ∈ normalizer ((sec3DData e t).A₁ : Set G) →
      (∀ a ∈ (sec3DData e t).A₁, n * a * n⁻¹ * a⁻¹ ∈ zpowers (sec3DData e t).z) →
      n ∈ (sec3DData e t).withT (sec3DData e t).A₁ :=
  CH_A₁_mod_of hΘ fun hk hi hj h => c10_spec hk hi hj h

theorem CH_A₁' (hΘ : ThetaSpec t e Θ) :
    centralizer ((sec3DData e t).A₁ : Set G) ⊓ (sec3DData e t).H ≤ (sec3DData e t).ZR :=
  CH_A₁_of hΘ fun hk hi hj h => c10_spec hk hi hj h

theorem oTwo_CHz' (hΘ : ThetaSpec t e Θ) :
    ∀ P : Subgroup G, P ≤ centralizer ({(sec3DData e t).z} : Set G) ⊓ (sec3DData e t).H →
      centralizer ({(sec3DData e t).z} : Set G) ⊓ (sec3DData e t).H ≤ normalizer (P : Set G) →
      IsPGroup 2 P → P ≤ (sec3DData e t).withT (sec3DData e t).A₁ :=
  oTwo_CHz_of hΘ (fun hk hi hj hij h => c8_spec hk hi hj hij h) fun hs h =>
    i5_spec hs h

end CFSG.EvenSmallLie.UnitarySix.YamadaHAut
