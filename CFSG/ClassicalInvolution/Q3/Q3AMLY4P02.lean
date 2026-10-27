module

public import CFSG.ClassicalInvolution.Q3.Q3AMLYBase

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
open scoped commutatorElement

section Core


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem layerCentralizer_conjSub_eq (hs : Std8 Ω K J S R T W z t) {M : Subgroup G} {a : G}
    (hM : M ∈ Ω) (ha : IsUniqueInvolution M a) :
    ∀ g ∈ Subgroup.centralizer ({a} : Set G), conjSub g M = M := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  exact fun g hg => mem_normalizer_iff_conjSub_eq.mp
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM (hnt M hM) ha hg)

theorem centralizer_le_normalizer_nbrLayer_of_std8 (hs : Std8 Ω K J S R T W z t)
    {M : Subgroup G} {a : G} (hM : M ∈ Ω) (ha : IsUniqueInvolution M a) :
    Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer ((nbrLayer Ω M a : Subgroup G) : Set G) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hCM := layerCentralizer_conjSub_eq hs hM ha
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_nbrLayer hΩ hCM hg hy, fun hy => ?_⟩
  have := conj_mem_nbrLayer hΩ hCM (Subgroup.inv_mem _ hg) hy
  simpa [mul_assoc] using this

theorem layerT_le_centralizer (hs : Std8 Ω K J S R T W z t) :
    T ≤ Subgroup.centralizer ({z} : Set G) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.stand.mem hRΩ hRK
  have h8R := hΩ.eight_le_of_mem_RSet hRΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have hcomm : Commutes T R :=
    l6_7_proved G Ω hΩ S T hTΩ R hRΩ hTS hRS (Ne.symm (T8R.R_ne_T hs))
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hcomm x hx z hzR

theorem layerT_le_exactCore (hs : Std8 Ω K J S R T W z t) : T ≤ exactCore3 z J :=
  le_inf hs.hT.2.1 (layerT_le_centralizer hs)

theorem mem_centralizer_of_conjSub_eq {K : Subgroup G} {z b : G} (hz : IsUniqueInvolution K z)
    (hb : conjSub b K = K) : b ∈ Subgroup.centralizer ({z} : Set G) := by
  have hy : b * z * b⁻¹ ∈ K := mem_of_conjSub_eq hb hz.mem
  have hy2 : (b * z * b⁻¹) * (b * z * b⁻¹) = 1 := by
    calc (b * z * b⁻¹) * (b * z * b⁻¹) = b * (z * z) * b⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hz.unique _ hy hy2 with h | h
  · exfalso
    apply hz.ne_one
    have : z = b⁻¹ * (b * z * b⁻¹) * b := by group
    rw [h] at this
    simpa using this
  · calc b * z = (b * z * b⁻¹) * b := by group
      _ = z * b := by rw [h]

theorem exactCore3_mem_layerFam {N : Subgroup G} {M : Subgroup G} {a : G}
    (hN : N ∈ omegaNbr Ω M) :
    modOddIn (nbrLayer Ω M a) (exactCore3 a N) ∈ layerFam Ω M a :=
  ⟨(exactCore3 a N).subgroupOf (nbrLayer Ω M a),
    ⟨exactCore3 a N, ⟨⟨N, hN, rfl⟩, exactCore3_le_centralizer a N⟩, exactCore3_le_nbrLayer hN,
      rfl⟩, rfl⟩

end Core

end CFSG.ClassicalInvolution.Q3.Q3AM
