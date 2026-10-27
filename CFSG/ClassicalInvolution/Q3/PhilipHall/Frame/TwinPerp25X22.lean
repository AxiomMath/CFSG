module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X21

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Asc77.CX (TwinGroup DiagTriv DiagRel TwinIso centTG fixSubgroup)
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan AEIdent)
open scoped MatrixGroups


section Cases

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

@[expose] def FixTwoAt (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {b : G} (hb2 : b * b = 1)
    (hbA : b ∈ cA S R R') : Prop :=
  ∀ (x : G) (hx : x ∈ cA S R R') (hxb : x ∈ Subgroup.centralizer ({b} : Set G)),
    actOf hyp hb2 ⟨x, hxb⟩ = 1 ∨ actOf hyp hb2 ⟨x, hxb⟩ = MulAut.conj (zBar hyp hb2 hbA)

theorem fixTwo_of_sec (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {b : G} (hb2 : b * b = 1)
    (hbA : b ∈ cA S R R')
    (h : ∀ β ∈ actImg hyp hb2, β = 1 ∨ β = MulAut.conj (zSec hyp hb2 hbA)) :
    FixTwoAt hyp hb2 hbA := by
  intro x hx hxb
  have hmem : TwinDisc.secAct hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hb2) ⟨x, hxb⟩ ∈
      actImg hyp hb2 := ⟨⟨x, hxb⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rw [actOf_eq_congr hyp hb2]
  rcases h _ hmem with h1 | h1
  · left
    rw [h1, map_one]
  · right
    rw [h1, congr_conj]
    rfl

theorem layer_cases (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {b : G} (hbA : b ∈ cA S R R')
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hT : LayerTypedL Ω b) :
    FixTwoAt hyp hb2 hbA ∨ (SecNoExitAt Ω b ∧ LayerLie Ω b 6) := by
  classical
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers b) := isPGroup_zpowers_of_sq_eq_one hb2
  have hS := layer_q8Section hyp hb2
  have hconj : ∀ J ∈ liftFam (TwinDisc.secFam Ω b), ∀ y : SecQ Ω b,
      conjSub y J ∈ liftFam (TwinDisc.secFam Ω b) :=
    fun J hJ y => conjInvariant_liftFam hS.hyp.conjInvariant y J hJ
  rcases hT with ⟨hno, hL⟩ | hae
  · rcases hL with ⟨D, hD1, i, hi⟩ | h6
    · left
      obtain ⟨htC, htY, hu₁C, hu₁Y, hu₂C, hu₂Y, A, A', htw, hAK, hAK'⟩ :=
        EndL.layer_twinData hyp hb2 hb1 hbA hno
      have hLT := CFSG.ClassicalInvolution.Q3.Q3T7P25.layerTwinFactsFive3_proved D hD1 ⟨i, hi⟩ htw
      obtain ⟨eA⟩ := nonempty_equiv_of_mem_liftFam htw.hA hLT.2.1
      obtain ⟨eA'⟩ := nonempty_equiv_of_mem_liftFam htw.hA' hLT.2.2.1
      have hPfix : ∀ β ∈ actImg hyp hb2, (∀ y ∈ A, β y = y) ∧ ∀ y ∈ A', β y = y := by
        rintro _ ⟨⟨x, hxb⟩, hx, rfl⟩
        exact secAct_fix_lifts hyp hb2 hb1 hbA hno hAK hAK' htw.hA htw.hA' eA eA'
          (Subgroup.mem_subgroupOf.mp hx) hxb
      exact fixTwo_of_sec hyp hb2 hbA (secFacts_five D hD1 ⟨i, hi⟩ htw hconj hPfix).2
    · exact Or.inr ⟨hno, h6⟩
  · left
    obtain ⟨I, hker⟩ := hae
    obtain ⟨hKtq, hK'tq, hz, hz', -, -⟩ := layer_twins_tq hyp hbA
    obtain ⟨htC, htY, hzbar⟩ := isUniqueInvolution_secImg hΩ hc2 hKtq hz
    obtain ⟨htC', htY', hzbar'⟩ := isUniqueInvolution_secImg hΩ hc2 hK'tq hz'
    have hne : TwinDisc.secImg Ω b K ≠ TwinDisc.secImg Ω b K' :=
      TwinPerpV3.secImg_ne_of_twin hΩ hc2 hKtq hK'tq hyp.std.1.hne.symm hz hz'
    have F := TwinDisc.AE5.q8Fam_of_aeIdent_n (le_refl 5) hS I
    have h2' := F.two
    have hperm : ∀ β ∈ actImg hyp hb2, ∀ L ∈ TwinDisc.secFam Ω b, ∃ L' ∈ TwinDisc.secFam Ω b,
        L.map β.toMonoidHom = L' := by
      rintro _ ⟨⟨x, hxb⟩, hx, rfl⟩ L hL
      obtain ⟨J₁, hJ₁, rfl⟩ := TwinDisc.exists_of_mem_secFam hL
      exact ⟨_, TwinDisc.secImg_mem_secFam (conjSub_mem_tqMembers3 hΩ.conjInvariant hxb hJ₁),
        TwinDisc.secAct_map_secImg hΩ hc2 ⟨x, hxb⟩⟩
    have hfixK : ∀ β ∈ actImg hyp hb2, ∀ y ∈ TwinDisc.secImg Ω b K, β y = y := by
      rintro _ ⟨⟨x, hxb⟩, hx, rfl⟩
      exact TwinDisc.secAct_fix_secImg hΩ hc2 (h2' _ (TwinDisc.secImg_mem_secFam hKtq)) hxb
        (mem_trivialOnQuot_of_mem_A hyp (Subgroup.mem_subgroupOf.mp hx)).1
    have hfixK' : ∀ β ∈ actImg hyp hb2, ∀ y ∈ TwinDisc.secImg Ω b K', β y = y := by
      rintro _ ⟨⟨x, hxb⟩, hx, rfl⟩
      exact TwinDisc.secAct_fix_secImg hΩ hc2 (h2' _ (TwinDisc.secImg_mem_secFam hK'tq)) hxb
        (mem_trivialOnQuot_of_mem_A hyp (Subgroup.mem_subgroupOf.mp hx)).2
    exact fixTwo_of_sec hyp hb2 hbA
      (secFacts_ae5 hS I hker (TwinDisc.secImg_mem_secFam hKtq) (TwinDisc.secImg_mem_secFam hK'tq)
        hne hzbar hzbar' hperm hfixK hfixK').2

end Cases

section Edge

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem reflection_of_bad (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w x y : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') (hLF : LayerFacts hyp hw2) (hxA : x ∈ cA S R R') (hyA : y ∈ cA S R R')
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hy : y ∈ Subgroup.centralizer ({w} : Set G))
    (hyx : y = x * w * z) (hbx : z ∉ zStarOf (Subgroup.centralizer ({w, x} : Set G)))
    (hby : z ∉ zStarOf (Subgroup.centralizer ({w, y} : Set G))) :
    actOf hyp hw2 ⟨y, hy⟩ = actOf hyp hw2 ⟨x, hx⟩ * MulAut.conj (zBar hyp hw2 hwA) ∧
      actOf hyp hw2 ⟨x, hx⟩ ≠ 1 ∧ actOf hyp hw2 ⟨x, hx⟩ ≠ MulAut.conj (zBar hyp hw2 hwA) := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_sq_eq_one hw2
  have hz : z ∈ Subgroup.centralizer ({w} : Set G) := z_centralizes hyp hwA
  have hwC : w ∈ Subgroup.centralizer ({w} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hyeq : actOf hyp hw2 ⟨y, hy⟩ = actOf hyp hw2 ⟨x, hx⟩ * MulAut.conj (zBar hyp hw2 hwA) := by
    have e : (⟨y, hy⟩ : ↥(Subgroup.centralizer ({w} : Set G))) = ⟨x, hx⟩ * ⟨w, hwC⟩ * ⟨z, hz⟩ :=
      Subtype.ext hyx
    have h1 : actOf hyp hw2 ⟨w, hwC⟩ = 1 := actW_self hΩ hc2
    have h2 : actOf hyp hw2 ⟨z, hz⟩ = MulAut.conj (zBar hyp hw2 hwA) :=
      actW_eq_conj hΩ hc2 hz (z_mem_core hyp hw2 hwA)
    rw [e, map_mul, map_mul, h1, mul_one, h2]
  have hβz : actOf hyp hw2 ⟨x, hx⟩ ≠ MulAut.conj (zBar hyp hw2 hwA) := fun h =>
    hbx ((good_iff_actW hLF hwA hxA hx).mpr h)
  have hβ1 : actOf hyp hw2 ⟨x, hx⟩ ≠ 1 := by
    intro h
    apply hby
    refine (good_iff_actW hLF hwA hyA hy).mpr ?_
    rw [hyeq, h, one_mul]
    rfl
  exact ⟨hyeq, hβ1, hβz⟩

end Edge

section EdgeOm

variable {Y : Type} [Group Y] [Finite Y] {E E' : Type} {e : E → Y} {e' : E' → Y} {zb : Y}
  {P : Subgroup (MulAut Y)}

theorem refl_edge_om (T : TwinLift e e' zb P) {β₁ β₂ : MulAut Y}
    (h₂ : β₂ = β₁ * MulAut.conj T.z') (hf : ∀ y ∈ T.A, β₁ y = y) (hf' : ∀ y ∈ T.A', β₁ y = y)
    (hsq : β₁ * β₁ = 1) (h1 : β₁ ≠ 1) (hz : β₁ ≠ MulAut.conj T.z') :
    ∃ (hA : T.A ≤ Goldschmidt75.perfRes (fixSubgroup β₁))
      (hA' : T.A' ≤ Goldschmidt75.perfRes (fixSubgroup β₁))
      (hB : T.A ≤ Goldschmidt75.perfRes (fixSubgroup β₂))
      (hB' : T.A' ≤ Goldschmidt75.perfRes (fixSubgroup β₂)),
      CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 (centTG T.A T.A' β₁ hA hA') ∧
        CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5 (centTG T.A T.A' β₂ hB hB') ∧
          ¬ DiagRel 3 (centTG T.A T.A' β₁ hA hA') (centTG T.A T.A' β₂ hB hB') := by
  subst h₂
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.om6ReflDiag_proved Y T.Φ T.A T.A' T.z' T.a₀ T.b₀
    T.om6 β₁ hf hf' hsq h1 hz

end EdgeOm

section RestrCoe

variable {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y'] {A₁ A₁' : Subgroup Y}
  {A₂ A₂' : Subgroup Y'} {β : MulAut Y} {β' : MulAut Y'}

theorem restrTo_coe (hA : A₁ ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hA' : A₁' ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hB : A₂ ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (hB' : A₂' ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (ψ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) ≃* ↥(Goldschmidt75.perfRes (fixSubgroup β')))
    (hAm : (centTG A₁ A₁' β hA hA').A.map (ψ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) →*
      ↥(Goldschmidt75.perfRes (fixSubgroup β'))) = (centTG A₂ A₂' β' hB hB').A) (k : ↥A₁) :
    ((restrTo (centTG A₁ A₁' β hA hA') (centTG A₂ A₂' β' hB hB') ψ hAm k : ↥A₂) : Y') =
      ((ψ ⟨(k : Y), hA k.2⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β'))) : Y') := by
  have h := restrTo_apply (centTG A₁ A₁' β hA hA') (centTG A₂ A₂' β' hB hB') ψ hAm k
  exact congrArg (fun m : ↥(Goldschmidt75.perfRes (fixSubgroup β')) => (m : Y')) h

theorem restrTo'_coe (hA : A₁ ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hA' : A₁' ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hB : A₂ ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (hB' : A₂' ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (ψ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) ≃* ↥(Goldschmidt75.perfRes (fixSubgroup β')))
    (hAm : (centTG A₁ A₁' β hA hA').A'.map (ψ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) →*
      ↥(Goldschmidt75.perfRes (fixSubgroup β'))) = (centTG A₂ A₂' β' hB hB').A') (k : ↥A₁') :
    ((restrTo' (centTG A₁ A₁' β hA hA') (centTG A₂ A₂' β' hB hB') ψ hAm k : ↥A₂') : Y') =
      ((ψ ⟨(k : Y), hA' k.2⟩ : ↥(Goldschmidt75.perfRes (fixSubgroup β'))) : Y') := by
  have h := restrTo'_apply (centTG A₁ A₁' β hA hA') (centTG A₂ A₂' β' hB hB') ψ hAm k
  exact congrArg (fun m : ↥(Goldschmidt75.perfRes (fixSubgroup β')) => (m : Y')) h

end RestrCoe

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
