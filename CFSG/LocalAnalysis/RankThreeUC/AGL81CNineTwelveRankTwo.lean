module

import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.Walter.Cited.HuppertBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup CFSG.LocalAnalysis.RankThreeUC.S15
open scoped MatrixGroups
open scoped commutatorElement

private theorem card_GL_dvd_card_GL_two {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≤ 2) :
    Nat.card (GL (Fin k) (ZMod p)) ∣ Nat.card (GL (Fin 2) (ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  interval_cases k
  · rw [CFSG.SectionRank.Ccomm.card_GL_zmod 0, CFSG.SectionRank.Ccomm.card_GL_zmod 2]
    simp
  · rw [CFSG.SectionRank.Ccomm.card_GL_zmod 1, CFSG.SectionRank.Ccomm.card_GL_zmod 2]
    have h1 : (∏ i : Fin 1, (p ^ 1 - p ^ (i : ℕ))) = p - 1 := by simp [Fin.prod_univ_one]
    have h2 : (∏ i : Fin 2, (p ^ 2 - p ^ (i : ℕ))) = (p ^ 2 - 1) * (p ^ 2 - p) := by
      simp [Fin.prod_univ_two]
    rw [h1, h2]
    refine dvd_mul_of_dvd_left ?_ _
    rw [show p ^ 2 - 1 = (p + 1) * (p - 1) by simpa using Nat.sq_sub_sq p 1]
    exact dvd_mul_left (p - 1) (p + 1)
  · rfl

theorem card_dvd_card_GL_two_of_coprime {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hC : centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X)
    (hrk : CFSG.Open.pRank p (CFSG.pCore p X) ≤ 2) {S : Subgroup X}
    (hS : Nat.Coprime (Nat.card S) p) : Nat.card S ∣ Nat.card (GL (Fin 2) (ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Subgroup X := CFSG.pCore p X
  haveI hPnorm : P.Normal := CFSG.pCore_normal
  have hPp : IsPGroup p ↥P := CFSG.pCore_isPGroup
  let σ : ↥S →* MulAut ↥P := (MulAut.conjNormal (H := P)).comp S.subtype
  have hσdvd : ∀ s : ↥S, orderOf (σ s) ∣ Nat.card S := fun s =>
    (orderOf_map_dvd σ s).trans (orderOf_dvd_natCard s)
  have hσcop : ∀ s : ↥S, Nat.Coprime (orderOf (σ s)) p := fun s =>
    Nat.Coprime.of_dvd_left (hσdvd s) hS
  obtain ⟨C, hCcrit, hCne, hCfaith, hDset, hDchar, hDne, hDcomm, hDexp, hDfixP, hDdet⟩ :=
    CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical_omega (P := ↥P) (p := p)
      hp2 hPp
  let D : Subgroup ↥P := CFSG.RankThree.PartTwo.Sec13.CritProof.omegaOneIn p C
  haveI : D.Characteristic := hDchar
  have hDp : IsPGroup p ↥D := hPp.to_subgroup D
  have hDexp' : ∀ x : ↥D, x ^ p = 1 := fun x => by
    apply Subtype.ext
    simpa using hDexp (x : ↥P) x.2
  have hDrank : CFSG.pRank p ↥D ≤ 2 := by
    have h1 : CFSG.Open.pRank p D ≤ CFSG.Open.pRank p (D.map P.subtype) :=
      CFSG.SectionRank.pRank_le_map (p := p) hp.one_lt P.subtype P.subtype_injective D
    have h2 : CFSG.Open.pRank p (D.map P.subtype) ≤ CFSG.Open.pRank p (CFSG.pCore p X) :=
      CFSG.SectionRank.pRank_mono (p := p) hp.one_lt (Subgroup.map_subtype_le D)
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact h1.trans (h2.trans hrk)
  have hclass : commutator ↥D ≤ Subgroup.center ↥D := by
    change ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆ ≤ Subgroup.center ↥D
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hmem : ⁅(x : ↥P), (y : ↥P)⁆ ∈ ⁅D, (⊤ : Subgroup ↥P)⁆ :=
      Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top (y : ↥P))
    have hcen : (z : ↥P) * ⁅(x : ↥P), (y : ↥P)⁆ =
        ⁅(x : ↥P), (y : ↥P)⁆ * (z : ↥P) :=
      Subgroup.mem_centralizer_iff.mp (hDcomm hmem).2 (z : ↥P) z.2
    have hcoe : ((⁅x, y⁆ : ↥D) : ↥P) = ⁅(x : ↥P), (y : ↥P)⁆ :=
      map_commutatorElement (f := D.subtype) x y
    simpa only [Subgroup.coe_mul, hcoe] using hcen
  have hfratt : frattini ↥D = commutator ↥D :=
    CFSG.RankThree.PartTwo.frattini_eq_commutator hDp hDexp'
  have hWp : IsPGroup p (↥D ⧸ frattini ↥D) := hDp.to_quotient (frattini ↥D)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hWp
  have hWc_card : Nat.card (↥D ⧸ commutator ↥D) = p ^ k := by
    rw [← hfratt]
    exact hk
  have hqr :=
    CFSG.RankThree.PartTwo.quotient_commutator_rank (p := p) hp hDexp' hWc_card
  have hk_le : k ≤ 2 := by
    rw [← hqr.2]
    exact (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds (p := p) hDp hDexp'
      hclass).1 hDrank
  let β : ↥S →* MulAut ↥D := (MulAut.characteristic D).comp σ
  let Ψ : ↥S →* MulAut (↥D ⧸ frattini ↥D) :=
    (CFSG.Walter.Huppert.frattiniAut ↥D).comp β
  have hΨ_inj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro s hs1
    have hγ : CFSG.Walter.Huppert.frattiniAut ↥D (β s) = 1 := by
      simpa only [Ψ, MonoidHom.comp_apply] using hs1
    have hcopβ : Nat.Coprime p (orderOf (β s)) := by
      have h1 : orderOf (β s) ∣ orderOf (σ s) :=
        orderOf_map_dvd (MulAut.characteristic D) (σ s)
      exact (Nat.Coprime.of_dvd_left h1 (hσcop s)).symm
    have hβs1 : β s = 1 :=
      CFSG.Walter.Huppert.eq_one_of_frattiniAut_eq_one (p := p) hDp hcopβ hγ
    have hσs1 : σ s = 1 := by
      refine hDdet (σ s) (hσcop s) ?_
      intro x hx
      have h1 : (β s) ⟨x, hx⟩ = ⟨x, hx⟩ := by
        rw [hβs1, MulAut.one_apply]
      have h2 := congrArg (fun y : ↥D => (y : ↥P)) h1
      change (σ s) x = x at h2
      exact h2
    have hsP : (s : X) ∈ P := by
      apply hC
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hconj : MulAut.conjNormal (H := P) (s : X) = 1 := hσs1
      have hfix : (MulAut.conjNormal (H := P) (s : X)) ⟨y, hy⟩ = ⟨y, hy⟩ := by
        rw [hconj, MulAut.one_apply]
      have h2 := congrArg (fun z : ↥P => (z : X)) hfix
      rw [MulAut.conjNormal_apply] at h2
      have h3 := congrArg (fun z : X => z * (s : X)) h2
      have hcomm : (s : X) * y = y * (s : X) := by simpa [mul_assoc] using h3
      exact hcomm.symm
    obtain ⟨m, hm⟩ := hPp ⟨(s : X), hsP⟩
    have hsdvd : orderOf s ∣ p ^ m := by
      refine orderOf_dvd_of_pow_eq_one ?_
      apply S.subtype_injective
      rw [map_pow, map_one]
      simpa using congrArg (fun z : ↥P => (z : X)) hm
    have hcop_s : Nat.Coprime (orderOf s) p :=
      Nat.Coprime.of_dvd_left (orderOf_dvd_natCard s) hS
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hcop_s.pow_right m) dvd_rfl hsdvd)
  haveI : IsMulCommutative (↥D ⧸ frattini ↥D) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := frattini ↥D)).mpr (by
      rw [hfratt])
  have hWcomm : ∀ a b : ↥D ⧸ frattini ↥D, a * b = b * a := fun a b => mul_comm' a b
  have hWpow : ∀ a : ↥D ⧸ frattini ↥D, a ^ p = 1 :=
    CFSG.RankThree.PartTwo.quotient_pow_eq_one (p := p) hDexp' (frattini ↥D)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := p) hWcomm hWpow hk
  have hcard : Nat.card (MulAut (↥D ⧸ frattini ↥D)) = Nat.card (GL (Fin k) (ZMod p)) :=
    CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e
  have hSdvd : Nat.card S ∣ Nat.card (MulAut (↥D ⧸ frattini ↥D)) :=
    Subgroup.card_dvd_of_injective Ψ hΨ_inj
  rw [hcard] at hSdvd
  exact hSdvd.trans (card_GL_dvd_card_GL_two hp hk_le)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
