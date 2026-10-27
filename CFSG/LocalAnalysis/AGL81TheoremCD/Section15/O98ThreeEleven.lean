module

public import CFSG.Foundations.Basic
public import CFSG.Open.RankThreeDefs

import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input223
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1311

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB (gLBConj_gLBConj)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1311
open CFSG.HardMathSupport.Solomon.Coordinator (i183_glaPLayer_le)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

private theorem le_sSup_centralizer_of_not_le_normalizer
    (hp : p.Prime) {L E : Subgroup X} (hL : CFSG.IsComponent L) (hpL : p ∣ Nat.card L)
    (hE : CFSG.Open.IsElemAbelian p E) (hE2 : 2 ≤ CFSG.Open.pRank p E)
    (hEN : ¬ E ≤ Subgroup.normalizer (L : Set X)) :
    L ≤ sSup {C : Subgroup X | ∃ e ∈ E, e ≠ 1 ∧ C = Subgroup.centralizer ({e} : Set X)} := by
  classical
  have hLopen : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  have hLmem : L ∈ orbitSet1311 E L := mem_orbitSet1311_self E L E.one_mem
  have hle : L ≤ orbitProd1311 E L := le_orbitProd1311 hLmem
  have hsup : orbitProd1311 E L = sSup (orbitSet1311 E L) := sSup_eq_iSup.symm
  have hdvd : p ∣ Nat.card (orbitProd1311 E L) :=
    hpL.trans (Subgroup.card_dvd_of_le hle)
  have hcomp : ∀ K ∈ orbitSet1311 E L, IsComponentOf K (orbitProd1311 E L) :=
    fun K hK => isComponentOf_orbitProd1311 hLopen hK
  have hcomm : ∀ K ∈ orbitSet1311 E L, ∀ K' ∈ orbitSet1311 E L, K ≠ K' →
      ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := by
    intro K hK K' hK' hne x hx y hy
    have hc := (Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (orbit_commute1311 hLopen K hK K' hK' hne)) hx
    exact (Subgroup.mem_centralizer_iff.1 hc y hy).symm
  have htrans : ∀ K ∈ orbitSet1311 E L, ∀ K' ∈ orbitSet1311 E L,
      ∃ b ∈ E, GLBConj b K = K' := by
    rintro K ⟨b₀, hb₀, rfl⟩ K' ⟨b₁, hb₁, rfl⟩
    refine ⟨b₀⁻¹ * b₁, E.mul_mem (E.inv_mem hb₀) hb₁, ?_⟩
    rw [gLBConj_gLBConj, mul_inv_cancel_left]
  rw [SetLike.le_def] at hEN
  push Not at hEN
  obtain ⟨b, hbE, hbN⟩ := hEN
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbN (Subgroup.one_mem _)
  have hJ : ∃ b ∈ E, b ≠ 1 ∧
      (b ∈ Subgroup.centralizer (orbitProd1311 E L : Set X) ∨
        b ∉ Subgroup.normalizer (L : Set X)) :=
    ⟨b, hbE, hb1, Or.inr hbN⟩
  have hmain := CFSG.LocalAnalysis.GLTheoremB.MovingAround.input22_3_2_holds X p hp
    E (orbitProd1311 E L) L (orbitSet1311 E L) hE le_normalizer_orbitProd1311 hLmem
    hE2 hdvd hsup hcomp hcomm htrans hJ
  refine hle.trans ?_
  rw [hmain]
  refine sSup_le ?_
  rintro Z ⟨e, he, he1, _, rfl⟩
  exact (i183_glaPLayer_le p (orbitProd1311 E L ⊓ Subgroup.centralizer ({e} : Set X))).trans
    (inf_le_right.trans (le_sSup ⟨e, he, he1, rfl⟩))

theorem le_sSup_centralizer_or_le_normalizer
    (hp : p.Prime) {L E : Subgroup X} (hL : CFSG.IsComponent L) (hpL : p ∣ Nat.card L)
    (hE : CFSG.Open.IsElemAbelian p E) (hE2 : 2 ≤ CFSG.Open.pRank p E) :
    L ≤ sSup {C : Subgroup X | ∃ e ∈ E, e ≠ 1 ∧ C = Subgroup.centralizer ({e} : Set X)} ∨
      E ≤ Subgroup.normalizer (L : Set X) := by
  by_cases hEN : E ≤ Subgroup.normalizer (L : Set X)
  · exact Or.inr hEN
  · exact Or.inl (le_sSup_centralizer_of_not_le_normalizer hp hL hpL hE hE2 hEN)

theorem le_gamma_or_le_normalizer
    (hp : p.Prime) {L E : Subgroup X} (hL : CFSG.IsComponent L) (hpL : p ∣ Nat.card L)
    (hE : CFSG.Open.IsElemAbelian p E) (hE2 : 2 ≤ CFSG.Open.pRank p E) :
    L ≤ CFSG.Open.rankThreeGamma 1 p E ∨
      E ≤ Subgroup.normalizer (L : Set X) := by
  rcases le_sSup_centralizer_or_le_normalizer (X := X) hp hL hpL hE hE2 with h | h
  · left
    refine h.trans (sSup_le ?_)
    rintro C ⟨e, he, he1, rfl⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hQ : Subgroup.zpowers e ≤ E := Subgroup.zpowers_le.2 he
    have hcard : Nat.card (Subgroup.zpowers e) = p ^ 1 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hE.2 e he) he1, pow_one]
    have hrank : 1 ≤ CFSG.Open.pRank p (Subgroup.zpowers e) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl (isElemAbelian_zpowers (hE.2 e he)) hcard
    have hN : Subgroup.normalizer (Subgroup.zpowers e : Set X) ≤
        CFSG.Open.rankThreeGamma 1 p E := by
      change _ ≤ CFSG.Open.GLBCore p 1 E
      exact le_sSup ⟨Subgroup.zpowers e, hQ, hrank, rfl⟩
    have hC : Subgroup.centralizer ({e} : Set X) ≤
        Subgroup.normalizer (Subgroup.zpowers e : Set X) := by
      rw [Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure]
      exact Subgroup.centralizer_le_normalizer _
    exact hC.trans hN
  · exact Or.inr h

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
