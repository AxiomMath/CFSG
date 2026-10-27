module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW

namespace ThmE

section Config


variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.of_sylow (c : MinCex r Ω K S R W H) {S' : Sylow 2 G} {W' : Subgroup G}
    (hRS' : R ≤ (S' : Subgroup G)) {K' R' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S' : R' ≤ (S' : Subgroup G))
    (hW' : W' ∈ WSet Ω) (hW'S' : W' ≤ (S' : Subgroup G))
    (hW'n : ∀ s ∈ (S' : Subgroup G), conjSub s W' = W') (hCW' : CentPairs Ω (S' : Subgroup G) W' H) :
    MinCex r Ω K S' R W' H where
  stand :=
    { hyp := c.stand.hyp
      cls := c.stand.cls
      quat := c.stand.quat
      two := c.stand.two
      ih := c.stand.ih
      mem := c.stand.mem
      aEmpty := c.stand.aEmpty
      twin := ⟨K', hK', hne, R', hR', hR'K', hR'S'⟩
      hR := ⟨c.stand.hR.1, c.stand.hR.2.1, hRS'⟩
      hW := ⟨hW', hW'S', hW'n⟩ }
  hyp := ⟨c.hyp.trans, hCW'⟩
  proper := c.proper
  minimal := c.minimal

theorem MinCex.exists_config_sylow (c : MinCex r Ω K S R W H)
    {K' R' X : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hR' : R' ∈ RSet Ω)
    (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) (hRX : R ⊔ R' ≤ X) :
    ∃ (S' : Sylow 2 G) (W' : Subgroup G), MinCex r Ω K S' R W' H ∧ R ⊔ R' ≤ (S' : Subgroup G) ∧
      IsSylow2In ((S' : Subgroup G) ⊓ X) X := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hRR' : IsPGroup 2 ↥(R ⊔ R') := S.isPGroup'.to_le (sup_le hRS hR'S)
  obtain ⟨P, hP, hRRP⟩ := IsSylow2In.exists_ge hRR' hRX
  obtain ⟨S', hPS'⟩ := IsPGroup.exists_le_sylow hP.2.1
  have hSyl : IsSylow2In ((S' : Subgroup G) ⊓ X) X := by
    have hle : P ≤ (S' : Subgroup G) ⊓ X := le_inf hPS' hP.1
    have hp2 : IsPGroup 2 ↥((S' : Subgroup G) ⊓ X) := S'.isPGroup'.to_le inf_le_left
    have heq := hP.eq_of_le hp2 inf_le_right hle
    rw [heq]
    exact hP
  have hRS' : R ≤ (S' : Subgroup G) := le_sup_left.trans (hRRP.trans hPS')
  have hR'S' : R' ≤ (S' : Subgroup G) := le_sup_right.trans (hRRP.trans hPS')
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ c.stand.mem
  obtain ⟨x, -, -, hW', hW'S', hW'n, hCW'⟩ := exists_W_of_sylow hΩ c.stand.mem c.hyp.trans hz
    (c.centralizer_le hz) hRR hRK hRS c.stand.hW.1 c.stand.hW.2.1 c.stand.hW.2.2 c.hyp.cent hRR
    hRK hRS'
  exact ⟨S', conjSub x W, c.of_sylow hRS' hK' hne hR' hR'K' hR'S' hW' hW'S' hW'n hCW',
    sup_le hRS' hR'S', hSyl⟩

theorem MinCex.exists_config_sylow_centralizer (c : MinCex r Ω K S R W H) {z : G}
    (hz : IsUniqueInvolution K z) :
    ∃ (S' : Sylow 2 G) (W' : Subgroup G), MinCex r Ω K S' R W' H ∧
      IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
        (Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨-, hRK, -⟩ := c.stand.hR
  have hz' : IsUniqueInvolution K' z := by
    obtain ⟨-, z', hz'K, hz'K'⟩ := hK'tw
    have := hz.eq hz'K
    rwa [← this] at hz'K'
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hz.commute_of_mem hx).symm
  have hK'C : K' ≤ Subgroup.centralizer ({z} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hz'.commute_of_mem hx).symm
  obtain ⟨S', W', c', -, hSyl⟩ := c.exists_config_sylow hK'tw hne hR' hR'K' hR'S
    (X := Subgroup.centralizer ({z} : Set G)) (sup_le (hRK.trans hKC) (hR'K'.trans hK'C))
  exact ⟨S', W', c', hSyl⟩

theorem configSylowCentralizer : ConfigSylowCentralizer r :=
  fun _ _ _ _ _ _ _ _ _ c z hz => c.exists_config_sylow_centralizer hz

end Config

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
