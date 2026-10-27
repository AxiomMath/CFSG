module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxClaim

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

namespace L62

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem partC (hp : p.Prime) (hp2 : p ≠ 2) (h183 : Input18_3_4) (h145 : I145UsedAt G p)
    {A D J J₀ S : Subgroup G} {b : G}
    (hX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (A : Set G)))
    (hCb : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({b} : Set G)))
    (hAD : A ≤ D) (hDel : IsElemAbelian p D) (hbA : b ∈ A)
    (hJC : GLAPComponent p (Subgroup.centralizer (D : Set G)) J) (hJ₀J : J₀ ≤ J)
    (hSJ₀ : S ≤ ⁅S, J₀⁆) (hSK : S ≤ GLAPPrimeCoreOf p (layerClosure p A J)) :
    S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨hKL, hKsub, hJK⟩ := layerClosure_facts hp h183 hX hAD hDel hJC
  have hS1 : S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) :=
    hSK.trans (glaPPrimeCoreOf_le_of_isSubnormal hp hKsub)
  have hAel : IsElemAbelian p A := isElemAbelian_mono hDel hAD
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := isElemAbelian_le_centralizer hAel hbA
  have hI := h145 hp hp2 _ A hCb hAb (isPGroup_of_isElemAbelian hAel)
  have hCbA : Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (A : Set G) =
      Subgroup.centralizer (A : Set G) :=
    inf_eq_right.2 (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbA))
  rw [hCbA] at hI
  calc S ≤ ⁅S, J₀⁆ := hSJ₀
    _ ≤ ⁅GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)),
          GLAPLayer p (Subgroup.centralizer (A : Set G))⁆ :=
        Subgroup.commutator_mono hS1 ((hJ₀J.trans hJK).trans hKL)
    _ = ⁅GLAPLayer p (Subgroup.centralizer (A : Set G)),
          GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G))⁆ := Subgroup.commutator_comm _ _
    _ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) := hI

theorem partD (hc : S6Ctx G p) (h183 : Input18_3_4) (hLB : LBalanceAt G p)
    {B : Subgroup G} {x : G} {L D J J₀ S : Subgroup G} {b : G}
    (hT : InT p B x L) (hD : InD p B x L D J) (hbD : b ∈ D) (hb1 : b ≠ 1)
    (hJ₀J : J₀ ≤ J) (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥) (hSJ₀ : S ≤ ⁅S, J₀⁆)
    (hSb : S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))) : False := by
  have hp := hc.prime
  have hp2 := hc.odd
  have hBmax : GLAIsBmax p B := hT.1
  have hDB : D ≤ B := hD.1.1
  have hbB : b ∈ B := hDB hbD
  have hBel : IsElemAbelian p B := hBmax.1
  have hDel : IsElemAbelian p D := isElemAbelian_mono hBel hDB
  have hJC : GLAPComponent p (Subgroup.centralizer (D : Set G)) J := J_comp_centralizer hp hT hD
  have hCb : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({b} : Set G)) := kGroup_centralizer hc hb1
  have hDCb : D ≤ Subgroup.centralizer ({b} : Set G) := isElemAbelian_le_centralizer hDel hbD
  have hCbD : Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer (D : Set G) :=
    inf_eq_right.2 (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbD))
  have hJ' : GLAPComponent p (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (D : Set G)) J := by
    rw [hCbD]
    exact hJC
  obtain ⟨𝒞, hcomp, hsup, -, htr, hJle, hne⟩ := exists_family_gen hp h183 hCb hDCb hDel hJ'
  obtain ⟨K₁, hK₁⟩ := hne
  have hK₁comp : GLAPComponent p (Subgroup.centralizer ({b} : Set G)) K₁ := hcomp K₁ hK₁
  have hJM : J ≤ closureIn K₁ B := by
    refine hJle.trans (hsup ▸ iSup₂_le fun C hC => ?_)
    obtain ⟨e, he, rfl⟩ := htr K₁ hK₁ C hC
    rw [closureIn_eq_iSup_gLBConj]
    exact le_biSup (fun g => GLBConj g K₁) (hDB he)
  have hMJC : GLAPComponent p (closureIn K₁ B ⊓ Subgroup.centralizer (D : Set G)) J :=
    glaPComponent_of_le hp hJC (le_inf hJM hJC.1) inf_le_right
  have hJne : J ≠ ⊥ := glaPComponent_ne_bot' hJC
  have hGstar : IsGStar p B K₁ := by
    by_cases hD2 : Nat.card D = p ^ 2
    · obtain ⟨E, hEB, hEel, hEcard, hDE, hlayer⟩ := hD.2.2 hD2
      refine ⟨E, hEB, hEel, hEcard, fun hbot => hlayer ?_⟩
      have hCE : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer (D : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hDE)
      have hsn := isSubnormal_inf hMJC.2.1 (Subgroup.centralizer (E : Set G))
      have e : closureIn K₁ B ⊓ Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (E : Set G) =
          closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G) := by
        rw [inf_assoc, inf_eq_right.2 hCE]
      rw [e] at hsn
      have := glaPLayer_le_of_isSubnormal hp hsn
      rw [hbot] at this
      exact le_bot_iff.1 this
    · have hDp : IsPGroup p D := isPGroup_of_isElemAbelian hDel
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hDp
      have h2k : p ^ 2 ≤ p ^ k := hk ▸ hD.1.2.1
      have hk3 : 3 ≤ k := by
        have h2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 h2k
        have h3 : k ≠ 2 := fun h => hD2 (by rw [hk, h])
        omega
      obtain ⟨E, hED, hEcard⟩ := S3.exists_card_pow_le hp hDel (r := 3)
        (by rw [hk]; exact Nat.pow_dvd_pow p hk3)
      have hEel : IsElemAbelian p E := isElemAbelian_mono hDel hED
      refine ⟨E, hED.trans hDB, hEel, hEcard, fun hbot => hJne ?_⟩
      have hCE : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer (E : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hED)
      have hMC : closureIn K₁ B ≤ Subgroup.centralizer ({b} : Set G) := by
        rw [closureIn_eq_iSup_gLBConj]
        refine iSup₂_le fun g hg => ?_
        have hgC : g ∈ Subgroup.centralizer ({b} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact isElemAbelian_commute hBel hg hbB
        have h1 := gLBConj_mono (g := g) hK₁comp.1
        rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hgC)] at h1
      have hDN : D ≤ Subgroup.normalizer ((closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
        intro d hd
        refine i183_mem_normalizer_inf (le_normalizer_closureIn K₁ B (hDB hd)) (Subgroup.le_normalizer ?_)
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        exact isElemAbelian_commute hDel (hED he) hd
      have hKG : CFSG.Open.IsKGroup ↥(closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G) ⊔ D) :=
        CFSG.Open.IsKGroup.of_le hCb (sup_le (inf_le_left.trans hMC) hDCb)
      have hbal := glaPLayer_inf_centralizer_le hp hLB hKG hDp hDN
      have e : closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G) ⊓ Subgroup.centralizer (D : Set G) =
          closureIn K₁ B ⊓ Subgroup.centralizer (D : Set G) := by
        rw [inf_assoc, inf_eq_right.2 hCE]
      rw [e] at hbal
      have hJlay0 : J ≤ GLAPLayer p (closureIn K₁ B ⊓ Subgroup.centralizer (D : Set G)) :=
        le_sSup hMJC
      have hJlay : J ≤ GLAPLayer p (closureIn K₁ B ⊓ Subgroup.centralizer (E : Set G)) :=
        hJlay0.trans hbal
      rw [hbot] at hJlay
      exact le_bot_iff.1 hJlay
  have h413 := hc.stage4.2.1 B b K₁ hBmax hbB hb1 hK₁comp hGstar
  have hSM : S ≤ ⁅closureIn K₁ B, GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))⁆ := by
    calc S ≤ ⁅S, J₀⁆ := hSJ₀
      _ ≤ ⁅GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)), closureIn K₁ B⁆ :=
          Subgroup.commutator_mono hSb (hJ₀J.trans hJM)
      _ = ⁅closureIn K₁ B, GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))⁆ :=
          Subgroup.commutator_comm _ _
  have hS_even : 2 ∣ Nat.card S := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hSne (Subgroup.eq_bot_of_card_eq S (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  exact (Nat.not_even_iff_odd.2 h413)
    (even_iff_two_dvd.2 (hS_even.trans (Subgroup.card_dvd_of_le hSM)))

end L62

structure Lemma62Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  lBalance : LBalanceAt G p
  input18_3_4 : Input18_3_4
  input14_5 : Input14_5Print
  i1416 : I1416At G p
  chevClosure : ChevClosureQAt G p
  diag : I183DiagAt G p
  i2019 : I2019At G p

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem lemma62_holds (hc : S6Ctx G p) (hin : Lemma62Inputs G p) : Lemma62At G p := by
  intro q hq hq2 hqp B x L hT D J hD0
  obtain ⟨hD, N, hN, hDN, hcov⟩ := hD0
  have hp := hc.prime
  have hp2 := hc.odd
  obtain ⟨A, J₀, S, hAD, hidx, hJ₀J, hJ₀cov, hS2, hSne, hSA, hJ₀S, hSJ₀⟩ :=
    L62.partA hc hT.1 hD hN hDN hcov
  have h145 : I145UsedAt G p := i145UsedAt_of hin.input14_5 p
  have hSK := L62.partB hc hin.input18_3_4 hin.diag hin.chevClosure hin.i1416 hin.i2019 h145 hq hq2
    hqp hT hD hAD hidx hJ₀J hJ₀cov hS2 hSA hJ₀S hSJ₀
  obtain ⟨b, hbA, hb1⟩ := L62.exists_ne_one_mem hp hD.1.2.1 hAD hidx
  have hDel : IsElemAbelian p D := isElemAbelian_mono hT.1.1.1 hD.1.1
  have hJC := L62.J_comp_centralizer hp hT.1 hD
  have hX := L62.centralizer_isKGroup hc hbA hb1
  have hCb : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({b} : Set G)) := kGroup_centralizer hc hb1
  have hSb := L62.partC hp hp2 hin.input18_3_4 h145 hX hCb hAD hDel hbA hJC hJ₀J hSJ₀ hSK
  exact L62.partD hc hin.input18_3_4 hin.lBalance hT.1 hD (hAD hbA) hb1 hJ₀J hS2 hSne hSJ₀ hSb

end CFSG.LocalAnalysis.GLTheoremA
