module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigPi

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Arith

theorem card_psl2_of_two_pow {r : ℕ} (hr : 2 ≤ r) {F : Type} [Field F] [Finite F]
    (h : Nat.card F % 2 ^ (r + 1) = 2 ^ r + 1) :
    ∃ m : ℕ, Odd m ∧ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 2 ^ r * m := by
  rw [OrderReductions.LinearOrders.card_projectiveSpecialLinear F 2 (by norm_num)]
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  have hk : 2 ^ (k + 2 + 1) = 2 ^ (k + 3) := rfl
  rw [hk] at h
  obtain ⟨a, ha⟩ : ∃ a, Nat.card F = 2 ^ (k + 3) * a + (2 ^ (k + 2) + 1) := by
    refine ⟨Nat.card F / 2 ^ (k + 3), ?_⟩
    have hdm := Nat.div_add_mod (Nat.card F) (2 ^ (k + 3))
    rw [h] at hdm
    exact hdm.symm
  have h3 : 2 ^ (k + 3) = 2 ^ (k + 2) * 2 := by
    rw [show k + 3 = (k + 2) + 1 by omega, pow_succ]
  have h2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ']
  have hq1' : Nat.card F = 2 ^ (k + 2) * (2 * a + 1) + 1 := by
    rw [ha, h3]; ring
  have hq1 : Nat.card F - 1 = 2 ^ (k + 2) * (2 * a + 1) := by omega
  have hq2 : Nat.card F + 1 = 2 * (2 ^ (k + 1) * (2 * a + 1) + 1) := by
    rw [ha, h3, h2]; ring
  have hD : 2 ^ (k + 3) = 4 * 2 ^ (k + 1) := by
    rw [show k + 3 = (k + 1) + 2 by omega, pow_add]; ring
  have hE : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ']
  have hsq' : Nat.card F ^ 2 =
      2 ^ (k + 3) * ((2 * a + 1) * (2 ^ (k + 1) * (2 * a + 1) + 1)) + 1 := by
    rw [ha, hD, hE]; ring
  have hsq : Nat.card F ^ 2 - 1 =
      2 ^ (k + 3) * ((2 * a + 1) * (2 ^ (k + 1) * (2 * a + 1) + 1)) := by omega
  have hgcd : Nat.gcd 2 (Nat.card F - 1) = 2 := by
    rw [hq1]
    exact Nat.gcd_eq_left (by
      rw [show 2 ^ (k + 2) = 2 * 2 ^ (k + 1) by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ'], mul_assoc]
      exact dvd_mul_right 2 _)
  have hprod : ∏ index ∈ Finset.Icc 2 2, (Nat.card F ^ index - 1) = Nat.card F ^ 2 - 1 := by
    simp
  refine ⟨Nat.card F * ((2 * a + 1) * (2 ^ (k + 1) * (2 * a + 1) + 1)), ?_, ?_⟩
  · refine Odd.mul ?_ (Odd.mul ⟨a, by ring⟩ ?_)
    · refine ⟨2 ^ (k + 1) * (2 * a + 1), ?_⟩
      rw [hq1']
      rw [show 2 ^ (k + 2) = 2 * 2 ^ (k + 1) by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ']]
      ring
    · refine ⟨2 ^ k * (2 * a + 1), ?_⟩
      rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ']]
      ring
  · rw [hprod, hgcd, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one, hsq]
    rw [show Nat.card F *
          (2 ^ (k + 3) * ((2 * a + 1) * (2 ^ (k + 1) * (2 * a + 1) + 1))) =
        2 * (2 ^ (k + 2) *
          (Nat.card F * ((2 * a + 1) * (2 ^ (k + 1) * (2 * a + 1) + 1)))) by
      rw [show 2 ^ (k + 3) = 2 * 2 ^ (k + 2) by
        rw [show k + 3 = (k + 2) + 1 by omega, pow_succ']]
      ring,
      Nat.mul_div_cancel_left _ (by norm_num)]

theorem Z2BigLinkModel.fstar_card {r : ℕ} (hr : 2 ≤ r) {X : Type} [Group X] [Finite X]
    {p f : ℕ} (hm : Z2BigLinkModel r X p f) :
    (∃ m : ℕ, Odd m ∧ Nat.card ↥(genFittingFStar X) = 2 ^ r * m) ∧
      Subgroup.center ↥(genFittingFStar X) = ⊥ := by
  haveI := hm.simple
  obtain ⟨-, -, F, _, _, hFc, ⟨e⟩⟩ := MF163.psl2_of_lieModel hm.model
  obtain ⟨m, hm_odd, hcardF⟩ :=
    card_psl2_of_two_pow hr (F := F) (by rw [hFc]; exact hm.arith)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center ↥(genFittingFStar X))
  have h2 : Nat.card (↥(genFittingFStar X) ⧸
      Subgroup.center ↥(genFittingFStar X)) = 2 ^ r * m :=
    (Nat.card_congr e.toEquiv).trans hcardF
  rw [h2] at h1
  have hZ : Subgroup.center ↥(genFittingFStar X) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(genFittingFStar X)) with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at h1
      have hpos : 0 < Nat.card ↥(genFittingFStar X) := Nat.card_pos
      have hm1 : 1 ≤ m := hm_odd.pos
      have h2r : 1 < 2 ^ r := Nat.one_lt_pow (by omega) (by norm_num)
      have hlt1 : 1 < 2 ^ r * m := by
        have hle : 2 ^ r ≤ 2 ^ r * m := by
          simpa using Nat.mul_le_mul_left (2 ^ r) hm1
        exact lt_of_lt_of_le h2r hle
      have hlt : Nat.card ↥(genFittingFStar X) <
          2 ^ r * m * Nat.card ↥(genFittingFStar X) := by
        calc Nat.card ↥(genFittingFStar X) = 1 * Nat.card ↥(genFittingFStar X) :=
              (one_mul _).symm
          _ < (2 ^ r * m) * Nat.card ↥(genFittingFStar X) :=
              Nat.mul_lt_mul_of_pos_right hlt1 hpos
      exact absurd h1 hlt.ne
  rw [hZ, Subgroup.card_bot, mul_one] at h1
  exact ⟨⟨m, hm_odd, h1⟩, hZ⟩

theorem Z2BigLinkModel.card_le {r : ℕ} (hr : 2 ≤ r) {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hm : Z2BigLinkModel r X p f) {D : Subgroup X} (hD : IsPGroup 2 ↥D) :
    Nat.card ↥D ≤ 2 ^ (r + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨m, hm_odd, hcard⟩, -⟩ := hm.fstar_card hr
  set N := genFittingFStar X with hN
  haveI : N.Normal := CFSG.ClassicalInvolution.genFittingFStar_normal X
  have h1 := Subgroup.relIndex_mul_card N D
  have h2 : N.relIndex D ≤ 2 := by
    have h3 := Subgroup.relIndex_dvd_index_of_normal N D
    have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd hpos h3).trans hm.index
  have h3 : Nat.card ↥(N ⊓ D) ≤ 2 ^ r := by
    have hp2 : IsPGroup 2 ↥(N ⊓ D) := hD.to_le inf_le_right
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp2
    have hdvd : Nat.card ↥(N ⊓ D) ∣ 2 ^ r * m := hcard ▸ Subgroup.card_dvd_of_le inf_le_left
    rw [hk] at hdvd ⊢
    have hcop : Nat.Coprime (2 ^ k) m :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm_odd)
    exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)
  calc Nat.card ↥D = N.relIndex D * Nat.card ↥(N ⊓ D) := h1.symm
    _ ≤ 2 * 2 ^ r := Nat.mul_le_mul h2 h3
    _ = 2 ^ (r + 1) := by rw [pow_succ]; ring

theorem Z2BigLinkModel.conj_injective {r : ℕ} (hr : 2 ≤ r) {X : Type} [Group X] [Finite X]
    {p f : ℕ} (hm : Z2BigLinkModel r X p f) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  haveI := hm.simple
  obtain ⟨⟨m, hm_odd, hcard⟩, hZ⟩ := hm.fstar_card hr
  have hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center ↥(genFittingFStar X) = ⊤ :=
      eq_top_iff.mpr fun a _ => Subgroup.mem_center_iff.mpr fun b => h b a
    rw [htop] at hZ
    have h1 := congrArg (fun H : Subgroup ↥(genFittingFStar X) => Nat.card ↥H) hZ
    simp only [Subgroup.card_top, Subgroup.card_bot] at h1
    have hm1 : 1 ≤ m := hm_odd.pos
    have h2r : 1 < 2 ^ r := Nat.one_lt_pow (by omega) (by norm_num)
    nlinarith
  have hC := CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot hnab
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxC : x ∈ Subgroup.centralizer
      ((genFittingFStar X : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    have h1 := congrArg (fun α : MulAut X => α y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  rw [hC] at hxC
  exact hxC

theorem conj_injective_of_mulEquiv {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    (h : Function.Injective (MulAut.conj : B →* MulAut B)) :
    Function.Injective (MulAut.conj : A →* MulAut A) := by
  intro a a' haa
  apply φ.injective
  apply h
  rw [← mulAut_congr_conj φ a, ← mulAut_congr_conj φ a', haa]

end Arith

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.conj_injective_quot (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hArith : Z2BigModelArith r) :
    Function.Injective (MulAut.conj : (↥(linkLayer R t) ⧸
        classicalInvolutionOddCore ↥(linkLayer R t)) →*
      MulAut (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t))) := by
  obtain ⟨p, f, hm⟩ := hs.exists_linkModel hr hArith
  exact conj_injective_of_mulEquiv (linkLayerEquiv hs.large) (hm.conj_injective (by omega))

theorem Z2SetR.card_le_quot (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hArith : Z2BigModelArith r)
    {D : Subgroup (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t))}
    (hD : IsPGroup 2 ↥D) : Nat.card ↥D ≤ 2 ^ (r + 1) := by
  obtain ⟨p, f, hm⟩ := hs.exists_linkModel hr hArith
  have hD' : IsPGroup 2 ↥(D.map (linkLayerEquiv hs.large).toMonoidHom) :=
    IsPGroup.map hD (linkLayerEquiv hs.large).toMonoidHom
  have hcard : Nat.card ↥(D.map (linkLayerEquiv hs.large).toMonoidHom) = Nat.card ↥D :=
    Subgroup.card_map_of_injective (linkLayerEquiv hs.large).injective
  calc Nat.card ↥D = Nat.card ↥(D.map (linkLayerEquiv hs.large).toMonoidHom) := hcard.symm
    _ ≤ 2 ^ (r + 1) := hm.card_le (by omega) hD'

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
