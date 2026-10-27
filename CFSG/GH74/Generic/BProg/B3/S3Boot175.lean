module

public import CFSG.GH74.Generic.BProg.B3.S3Boot152
public import CFSG.GH74.Generic.BProg.B2.T1Comp
public import CFSG.GH74.Generic.BProg.B1.PilotS3
public import CFSG.GH74.GLS.C3.Layer1.Th2P86
public import CFSG.GH74.GLS.C3.Layer1.Th2Main
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21i
public import CFSG.GH74.GLS.C3.Layer1.EvenAltConfig
public import CFSG.GH74.GLS.C3.Layer1.EvenStd
public import CFSG.GH74.GLS.C3.Layer1.Th2L83Gen
public import CFSG.GH74.GLS.C3.Layer1.Th2L83GenCore
public import CFSG.GH74.GLS.C3.Layer1.Th2L84
public import CFSG.GH74.GLS.C3.Layer1.Th2P73
public import CFSG.GH74.GLS.C3.Layer1.Th2P812
public import CFSG.GH74.GLS.C3.Layer1.Th2P812Rows
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic6
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic7
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic8
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic9

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.GH74.GLS.Th2.Bal CFSG.Assembly.Dichotomy
open scoped commutatorElement

section SD13

variable {G : Type} [Group G] [Finite G]

theorem exists_E_of_source {x : G} {K A : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hsrc : IsSource2 x K A)
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∃ E : Subgroup G, E ≤ K ∧ A = E ⊔ zpowers x ∧ CFSG.IsElementaryAbelian 2 ↥E ∧
      Nat.card ↥E = 4 := by
  obtain ⟨-, -, -, hcase⟩ := hsrc
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK h3
  rcases hcase with ⟨-, h1⟩ | ⟨E, hEK, hAE, -, hEel, hE4, -⟩
  · exact (B1.PilotS3.not_qShape1_of_center_trivial h1 hZ).elim
  · exact ⟨E, hEK, hAE, hEel, hE4⟩

theorem lemma175_p2 (hKG : BootKG G) (hB2 : B_B2_g4) {x : G} {K A B M : Subgroup G}
    (hyp : Hyp2 G) (ht : IsTwoTerminal x K) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    (hsrc : IsSource2 x K A) (hext : IsExtSource2 x K A B) (hB4 : pRank 2 ↥B = 4) (hM : M ≠ ⊤)
    (hKM : K ≤ M) (hΓ : gammaK 2 B 3 ≤ M) :
    thetaHalf 1 (A.subgroupOf M) ≤ pPrimeCore 2 ↥M ∧
      thetaHalfPrime (A.subgroupOf M) ≤ pPrimeCore 2 ↥M := by
  have hILo : IsILo 2 x K := ht.1
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hext.2.2.2.1
  have hBM : B ≤ M := (S3Boot152.le_gammaK_self hBel (by rw [hB4]; norm_num)).trans hΓ
  have hxB : x ∈ B := hext.2.1
  have hxM : x ∈ M := hBM hxB
  have hAB : A ≤ B := hext.1
  have hAM : A ≤ M := hAB.trans hBM
  obtain ⟨E, hEK, hAE, hEel, hE4⟩ := exists_E_of_source hILo.2.2 hsrc h3
  have hxA : x ∈ A := by
    rw [hAE]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hEA : E ≤ A := by
    rw [hAE]
    exact le_sup_left
  have hAcard : Nat.card ↥A = 8 := hsrc.2.2.1
  obtain ⟨H, hH⟩ := Th2.exists_minSubnormal hKM
  have hcK : barIn M H = barIn M K := by
    by_contra hne
    have hB0 := hKG.h175 x K A B M H hyp ht h3 hsrc hext hB4 hM hKM hΓ hH hne
    have hBA : B ≤ A := by
      rw [hext.2.2.2.2.2.2]
      exact sup_le le_rfl (hB0.trans ((Subgroup.zpowers_le).mpr hxA))
    have hAeqB : A = B := le_antisymm hAB hBA
    have h2 : Nat.card ↥B = 2 ^ pRank 2 ↥B := C3.Layer1.Back.card_eq_two_pow_pRank hBel
    rw [hB4, ← hAeqB, hAcard] at h2
    norm_num at h2
  have hKc := B2.barIn_K_isCompIn_gen hB2 hyp hM hILo hKM hxM
  have hKq : IsQuasisimple ↥(barIn M K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKc.1) hKc.2.1
  have hKsub : (barIn M K).IsSubnormal := by
    rw [← hcK]
    exact Th2.P85.isSubnormal_imgM hH.2.1
  have hKcomp : IsComponent (barIn M K) := ⟨hKq, hKsub⟩
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := (isE3_of_isSource2 hsrc).2.1
  have hAel' : CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf M) := by
    have := hAel
    exact CFSG.IsElementaryAbelian.subgroupOf hAM
  have hAcard' : Nat.card ↥(A.subgroupOf M) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, hAcard]
  have hA3 : IsE 3 ⊤ (A.subgroupOf M) :=
    ⟨le_top, hAel', (CFSG.pRank_eq_of_card_eq_pow one_lt_two (by rw [hAcard']; norm_num)).ge⟩
  have hEM : E ≤ M := hEA.trans hAM
  have hEcard : Nat.card ↥(E.subgroupOf M) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hE4]
  have hloc : ∀ Jb : Subgroup (↥M ⧸ pPrimeCore 2 ↥M), IsComponent Jb →
      (∃ F : Subgroup ↥M, F ≤ A.subgroupOf M ∧ 2 * Nat.card ↥F ≥ Nat.card ↥(A.subgroupOf M) ∧
        F.map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤
          centralizer (Jb : Set (↥M ⧸ pPrimeCore 2 ↥M))) ∨
      ∃ _hN : (A.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤
          normalizer (Jb : Set (↥M ⧸ pPrimeCore 2 ↥M)),
        IsLocBal32 (↥Jb ⧸ center ↥Jb)
          ((((A.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M))).subgroupOf
            (normalizer (Jb : Set (↥M ⧸ pPrimeCore 2 ↥M)))).map (rhoL Jb)) := by
    intro Jb hJb
    by_cases hJK : Jb = barIn M K
    · subst hJK
      exact Or.inr (hKG.loc28 x K A B M hyp ht h3 hsrc hext hB4 hM hKM hΓ)
    · refine Or.inl ⟨E.subgroupOf M, fun f hf => hEA hf, ?_, ?_⟩
      · rw [hEcard, hAcard']
      · rintro _ ⟨f, hf, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        have hfK : QuotientGroup.mk' (pPrimeCore 2 ↥M) f ∈ barIn M K :=
          ⟨f, Subgroup.mem_subgroupOf.mpr (hEK (Subgroup.mem_subgroupOf.mp hf)), rfl⟩
        rcases distinct_components_commute hKcomp hJb with h | h
        · exact absurd h.symm hJK
        · have h1 := Subgroup.commutator_mem_commutator hfK hj
          rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
          exact h1.symm
  exact ⟨iii2_3_15 hA3 hloc, iii2_3_15_prime hA3 hloc⟩

end SD13

end CFSG.GH74.Generic.BProg.B3
