module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FSW2

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)

section AEmpty


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ : Y}

theorem mem_normalizer_core_of_isFAut (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂) {b : Y} (hbS : b ∈ (S₁ : Subgroup Y)) (hF₁ : IsFAut R₁ b) :
    b ∈ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) := by
  have hs := hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hzK : IsUniqueInvolution (tightCore R) t := hs.hz
  have hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := hs.hK'
  have hne : K' ≠ tightCore R := hs.hne
  have hKtw : tightCore R ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
    mem_twinSet_self hK hzK
  have hbC : b ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS b hbS)
  have hconj := hP.conj_mem_twinSet hKtw hbC
  rw [twinSet_eq hP hyp] at hconj
  rcases hconj with h | h
  · exact mem_normalizer_iff_conjSub_eq.mpr h
  · exfalso
    have hR1 : conjSub b R₁ = R₁ := mem_normalizer_iff_conjSub_eq.mp hF₁.1
    have hle : R₁ ≤ tightCore R ⊓ K' := by
      refine le_inf hyp.hR.2.1 ?_
      have := conjSub_mono (n := b) hyp.hR.2.1
      rwa [hR1, h] at this
    have h1 := (hΩ.omega4 (tightCore R) hK K' hK'.1 hne.symm).1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdvd : 2 ^ r ∣ Nat.card ↥(tightCore R ⊓ K') := by
      rw [← card_R₁ hr hP hyp]
      exact Subgroup.card_dvd_of_le hle
    have h2 := (padicValNat_dvd_iff_le Nat.card_pos.ne').mp hdvd
    omega

theorem fBase_of_isFAut (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂) {b : Y} (hbS : b ∈ (S₁ : Subgroup Y)) (hF₁ : IsFAut R₁ b) :
    FBase (CoreAssembly.conjClass (tightCore R)) b (tightCore R) t := by
  have hs := hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hR₁ : IsSylow2In R₁ (tightCore R) :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have h2 : IsPGroup 2 (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R)) :=
    TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hP.core.datum.twoGroup
  obtain ⟨Q, hQ, hqQ, -⟩ := isSylow2In_coreAt_of_isFAut hR₁ h2
    (mem_normalizer_core_of_isFAut hr hP hyp hbS hF₁) hF₁
  exact ⟨hΩ, hK, hs.hz, (hyp.hzS b hbS).symm, ⟨Q, hQ, hqQ⟩⟩

theorem false_of_normalizes_fcore (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂)
    (h11 : (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) =
      Subgroup.zpowers t) {b : Y} (hbS : b ∈ (S₁ : Subgroup Y)) (hb2 : b * b = 1)
    (hF₁ : IsFAut R₁ b) {s : Y} (hsb : s ∈ Subgroup.centralizer ({b} : Set Y)) (hs2 : s * s = 1)
    (hst : s ≠ t) (hconj : ∃ y : Y, y * t * y⁻¹ = s)
    (hsN : s ∈ Subgroup.normalizer ((coreAt b (tightCore R) : Subgroup Y) : Set Y)) : False := by
  have hbase := fBase_of_isFAut hr hP hyp hbS hF₁
  have hst' : s * t = t * s := by
    have h1 : conjSub s (coreAt b (tightCore R)) = coreAt b (tightCore R) :=
      mem_normalizer_iff_conjSub_eq.mp hsN
    have h2 := hbase.inv_core.conj s
    rw [h1] at h2
    have h3 : s * t * s⁻¹ = t := (hbase.inv_core.eq h2).symm
    calc s * t = (s * t * s⁻¹) * s := by group
      _ = t * s := by rw [h3]
  have hsb' : s * b = b * s := Subgroup.mem_centralizer_singleton_iff.mp hsb
  have hsw := swap_of_conj hr hP hyp h11 hbS hb2 hF₁ hst' hsb' hs2 hst hconj
  have e1 : conjSub s (coreAt b (tightCore R)) = coreAt b K' := by
    rw [TwinADescent.conjSub_coreAt hsb, hsw]
  have e2 : conjSub s (coreAt b (tightCore R)) = coreAt b (tightCore R) :=
    mem_normalizer_iff_conjSub_eq.mp hsN
  have e3 : coreAt b (tightCore R) = coreAt b K' := e2.symm.trans e1
  obtain ⟨Q, hQ, hqQ⟩ := hbase.syl
  have hQK : Q ≤ tightCore R := hQ.1.trans (TwinADescent.coreAt_le_left b _)
  have hQK' : Q ≤ K' := by
    have := hQ.1.trans e3.le
    exact this.trans (TwinADescent.coreAt_le_left b K')
  have hs := hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hK'Ω : K' ∈ CoreAssembly.conjClass (tightCore R) := hs.hK'.1
  have hne : K' ≠ tightCore R := hs.hne
  have h1 := (hΩ.omega4 (tightCore R) hK K' hK'Ω hne.symm).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : Nat.card ↥Q ∣ Nat.card ↥(tightCore R ⊓ K') :=
    Subgroup.card_dvd_of_le (le_inf hQK hQK')
  obtain ⟨k, hk⟩ := hQ.2.1.exists_card_eq
  have h8 := hqQ.eight_le
  rw [hk] at hdvd h8
  have h2 := (padicValNat_dvd_iff_le Nat.card_pos.ne').mp hdvd
  have h3 : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end AEmpty

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
