module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf12Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinOddCent
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOdd
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEQuotOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

namespace ThmE

section O2


variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem exactO2 (c : MinCex r Ω K S R W H) {z : G} (hz : IsUniqueInvolution K z)
    {Q : Subgroup G} (hQn : Q.Normal) (hQ2 : IsPGroup 2 ↥Q) (hzQ : z ∈ Q) :
    ∀ J ∈ Ω, IsPGroup 2 ↥J := by
  intro J hJ
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  obtain ⟨g, rfl⟩ := e18_3 G Ω K S R W H c J hJ
  have hzJ := hz.conj g
  have hzQ' : g * z * g⁻¹ ∈ Q := hQn.conj_mem z hzQ g
  have hodd := TwinExitPf12.oddCoreIn_centralizer_eq_bot_of_mem_normal c.oddCore_eq_bot hQn hQ2 hzQ'
  exact isPGroup_of_oddCent hΩ (hΩ.conjInvariant g K c.stand.mem) hzJ hodd
    (c.stand.two _ (hΩ.conjInvariant g K c.stand.mem))

@[expose] def E18_6NotO2 (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z → ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q → z ∉ Q

theorem e18_6NotO2_of_four_le (hr : 4 ≤ r) : E18_6NotO2 r := by
  intro G _ _ Ω K S R W H c z hz Q hQn hQ2 hzQ
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hex := exactO2 c hz hQn hQ2 hzQ
  have htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3 G Ω K S R W H c
  have hA : ∀ J ∈ Ω, AEmpty Ω J :=
    aEmpty_forall_of_transitive hΩ.conjInvariant htrans c.stand.aEmpty
  have h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r := by
    intro J hJ
    obtain ⟨P, hP, ⟨e⟩⟩ := c.stand.quat J hJ
    have hPJ : J = P := hP.eq_of_le (hex J hJ) le_rfl hP.1
    subst hPJ
    rw [Nat.card_congr e.toEquiv]
    exact card_quaternion_pow (by omega)
  have hinO2 : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
      ∃ Q' : Subgroup G, Q'.Normal ∧ IsPGroup 2 Q' ∧ u ∈ Q' := by
    intro L hL u hu
    obtain ⟨g, rfl⟩ := htrans L hL
    refine ⟨Q, hQn, hQ2, ?_⟩
    have hgu : g * z * g⁻¹ = u := (hz.conj g).eq hu
    rw [← hgu]
    exact hQn.conj_mem z hzQ g
  obtain ⟨W', hW'⟩ := wSet_eq_singleton_of_four_le hr hΩ hex h8 hA c.oddCore_eq_bot hinO2
  have hWW : W = W' := by
    have := c.stand.hW.1
    rw [hW'] at this
    exact this
  refine c.proper (eq_top_iff.mpr fun g _ => ?_)
  refine c.mem_of_conjSub_eq_W (TwinThmEW.etaAbelian_of_gen hΩ) (n := g) ?_
  have hmem := WSet.conj hΩ.conjInvariant c.stand.hW.1 g
  rw [hW'] at hmem
  exact (Set.mem_singleton_iff.mp hmem).trans hWW.symm

theorem e18_6O2_of (h5 : E18_5 r) (hN : E18_6NotO2 r) : E18_6O2 r := by
  intro G _ _ Ω K S R W H c Q hQn hQ2
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3 G Ω K S R W H c
  have hgen : (⨆ J ∈ Ω, J) = ⊤ := h5 G Ω K S R W H c
  obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 K c.stand.mem
  have hmiss : ∀ J ∈ Ω, J ⊓ Q = ⊥ := by
    intro J hJ
    have hzQ : z ∉ Q := hN G Ω K S R W H c z hz Q hQn hQ2
    obtain ⟨g, hg⟩ := htrans J hJ
    by_contra hne
    have hzJ : IsUniqueInvolution J (g * z * g⁻¹) := by
      rw [← hg]
      exact hz.conj g
    have hA2 : IsPGroup 2 ↥(J ⊓ Q) := hQ2.to_inf_right
    have hcard : 2 ≤ Nat.card ↥(J ⊓ Q) := by
      have := (Subgroup.one_lt_card_iff_ne_bot (J ⊓ Q)).mpr hne
      omega
    have hmem : g * z * g⁻¹ ∈ J ⊓ Q :=
      AscL62.mem_of_uniqueInvolution_of_pGroup hzJ inf_le_left hA2 hcard
    apply hzQ
    have := hQn.conj_mem _ hmem.2 g⁻¹
    simpa [mul_assoc] using this
  refine ⟨?_, hmiss⟩
  have hJc : ∀ J ∈ Ω, J ≤ Subgroup.centralizer (Q : Set G) := fun J hJ =>
    TwinThmE.normal_two_central_Q8 hΩ c.stand.cls c.stand.two hQ2 hJ (hmiss J hJ)
  have hle : (⨆ J ∈ Ω, J) ≤ Subgroup.centralizer (Q : Set G) := iSup₂_le hJc
  intro q hq'
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ ⨆ J ∈ Ω, J := by rw [hgen]; exact Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp (hle hg) q hq').symm

end O2

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
