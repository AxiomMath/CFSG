module

public import CFSG.GH74.Generic.BProg.B2.T1Pre
public import CFSG.GH74.Generic.BProg.B2.ListedG5
import CFSG.GH74.Generic.BProg.B2.T1ThetaBar
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyBasic
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC1
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC2
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyG4
import CFSG.ClassicalInvolution.Balance.LocalBalance.Fixed
import CFSG.Assembly.OddCoreSpan
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.BProg.B2

namespace T1One

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

section Abstract

variable {Y : Type} [Group Y] [Finite Y]

theorem pPrimeCoreOf_le_centralizer_pCore {e : Y} (he : orderOf e = 2) :
    pPrimeCoreOf 2 (centralizer ({e} : Set Y)) ≤ centralizer ((CFSG.pCore 2 Y : Subgroup Y) : Set Y) := by
  intro d hd
  have hd' : d ∈ CFSG.Assembly.Dichotomy.involutionOddCore e := by
    show d ∈ (CFSG.Assembly.oddCore ↥(centralizer ({e} : Set Y))).map (centralizer ({e} : Set Y)).subtype
    rw [CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]
    exact hd
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h := ClassicalInvolution.Balance.LocalBalance.commute_pCore_of_mem_involutionOddCore he hd' q hq
  calc q * d = (d * q * d⁻¹) * d := by rw [h]
    _ = d * q := by group

theorem pPrimeCoreOf_le_centralizer_of_isComponent (hO : CFSG.pPrimeCore 2 Y = ⊥) {e : Y}
    {L : Subgroup Y} (hL : IsComponent L) (hLe : L ≤ centralizer ({e} : Set Y)) :
    pPrimeCoreOf 2 (centralizer ({e} : Set Y)) ≤ centralizer (L : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup Y := centralizer ({e} : Set Y) with hC
  have hL' : IsComponent (L.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLe).symm hL.1,
      hL.2.subgroupOf⟩
  rcases CFSG.LocalCores.component_normal_subgroup hL' (CFSG.pPrimeCore_normal (p := 2) (G := ↥C))
    with hle | hcomm
  · exfalso
    have hcard : Nat.card ↥(L.subgroupOf C) = Nat.card ↥L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLe).toEquiv
    have hdvd : Nat.card ↥(L.subgroupOf C) ∣ Nat.card ↥(CFSG.pPrimeCore 2 ↥C) :=
      Subgroup.card_dvd_of_le hle
    have hcop : Nat.Coprime 2 (Nat.card ↥L) := by
      rw [← hcard]
      exact Nat.Coprime.coprime_dvd_right hdvd CFSG.pPrimeCore_coprime_card
    have hLO := le_pPrimeCore_of_subnormal 2 hL.2 hcop
    rw [hO, le_bot_iff] at hLO
    have := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    rw [hLO] at this
    exact not_nontrivial_iff_subsingleton.2 (inferInstance : Subsingleton (⊥ : Subgroup Y)) this
  · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := Subgroup.mem_centralizer_iff.1 (hle (show (⟨l, hLe hl⟩ : ↥C) ∈ L.subgroupOf C from hl)) d hd
    exact (congrArg Subtype.val h1).symm

end Abstract

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

theorem orderOf_eq_two_of_mem_barIn (hs : Stage2Setup G x K A M P Q) {e : Mbar M}
    (he : e ∈ barIn M (A ⊓ K)) (he1 : e ≠ 1) : orderOf e = 2 := by
  obtain ⟨-, hAel, -, -⟩ := hs.src
  obtain ⟨a, ha, rfl⟩ := he
  have haA : (a : G) ∈ A := (Subgroup.mem_subgroupOf.1 ha).1
  have haa : (a : G) * a = 1 :=
    (C3.Layer1.Back.forall_of_isElementaryAbelian hAel).2 _ haA
  have h2 : (QuotientGroup.mk' (pPrimeCore 2 ↥M) a) ^ 2 = 1 := by
    rw [← map_pow, sq]
    have : a * a = 1 := Subtype.ext haa
    rw [this, map_one]
  exact orderOf_eq_prime h2 he1

theorem barIn_A_le_normalizer_barIn_K (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M) :
    barIn M A ≤ normalizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)) := by
  have hKx : K ≤ centralizer ({x} : Set G) := hs.pair.1.1.1.2.2.1
  have hxC : x ∈ centralizer (K : Set G) := Subgroup.mem_centralizer_iff.2 fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (hKx hk)
  have hxN : x ∈ normalizer (K : Set G) := Subgroup.centralizer_le_normalizer _ hxC
  have hAN : A ≤ normalizer (K : Set G) := by
    obtain ⟨-, -, -, hcase⟩ := hs.src
    rcases hcase with ⟨hAK, -⟩ | ⟨E, hEK, hA, -⟩
    · exact hAK.trans Subgroup.le_normalizer
    · rw [hA]
      exact sup_le (hEK.trans Subgroup.le_normalizer) ((Subgroup.zpowers_le).2 hxN)
  have hsub : A.subgroupOf M ≤ normalizer ((K.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hKM]
    intro a ha
    exact Subgroup.mem_subgroupOf.2 (hAN (Subgroup.mem_subgroupOf.1 ha))
  exact (Subgroup.map_mono hsub).trans (Subgroup.le_normalizer_map _)

theorem O_ne_of_barIn_theta_eq_bot (hs : Stage2Setup G x K A M P Q)
    (h : barIn M (thetaHalf 1 A) = ⊥) : pPrimeCoreOf 2 M ≠ ⊥ := by
  have hΘM : thetaHalf 1 A ≤ M := thetaHalf_le_M hs
  have hle : thetaHalf 1 A ≤ pPrimeCoreOf 2 M := by
    intro θ hθ
    have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥M) (⟨θ, hΘM hθ⟩ : ↥M) ∈ barIn M (thetaHalf 1 A) :=
      ⟨⟨θ, hΘM hθ⟩, Subgroup.mem_subgroupOf.2 hθ, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact ⟨⟨θ, hΘM hθ⟩, (QuotientGroup.eq_one_iff _).1 hmem, rfl⟩
  intro hbot
  rw [hbot, le_bot_iff] at hle
  exact hs.reg.2.1 hle

theorem O_ne_of_pre (hFam : ListedWeakSigMinFamG5) (hL4m : TA7.RefinePuL4) (hG2r : TA7.RefinePuG2)
    (hB : B_B2_g4) (hPump : PumpupTableU) (hs : Stage2Setup G x K A M P Q) {H : Subgroup G}
    (h1 : Stage2Concl1Pre x K M Q H) : pPrimeCoreOf 2 M ≠ ⊥ := by
  apply O_ne_of_barIn_theta_eq_bot hs
  obtain ⟨hDel, hDrank, hWodd, hDW, hCW⟩ := thetaBar_data hs
  have hO : CFSG.pPrimeCore 2 (Mbar M) = ⊥ := GLS.pPrimeCore_quotient_eq_bot ↥M
  have hY4 := sectionalTwoRankLE_Mbar hs
  have hcore := thetaBar_le_iSup_core hs
  have hrk : pRank 2 ↥(barIn M A) = 2 ∨ pRank 2 ↥(barIn M A) = 3 := Or.inr hDrank
  refine ClassicalInvolution.Balance.LocalBalance.eq_bot_of_centralizes_pCore_of_centralizes_components
    hO hWodd ?_ ?_
  · refine hcore.trans (iSup₂_le fun e he => ?_)
    exact pPrimeCoreOf_le_centralizer_pCore (orderOf_eq_two_of_mem_barIn hs he.1 he.2)
  · intro L hL
    rcases h1.H_tri with hc1 | ⟨hF, hsimple⟩ |
        ⟨hF, hx, L₁, L₂, hL₁, hL₂, hne, hs₁, hs₂, hsup, hconj, hall⟩
    ·
      obtain ⟨hKc, hother⟩ := components_c1_pre hs h1 hc1
      by_cases hLK : L = barIn M K
      · rw [hLK]
        have hsh := Thm2AssemblyC1.qShapeNS_barIn_K hs h1.K_le hKc
        have hWS : WeakSig2NormG4 ↥(barIn M K) := by
          rcases hsh with h | h | h | h
          · exact hFam.s1 _ hKc.1 h
          · exact hFam.s3 _ hKc.1 h
          · exact hFam.s4 _ hKc.1 h
          · exact hFam.s5 _ hKc.1 h
        exact hWS (Mbar M) hO hY4 (barIn M K) hKc ⟨MulEquiv.refl _⟩ (barIn M A)
          (barIn M (thetaHalf 1 A)) hDel hrk hWodd hDW hCW
          (barIn_A_le_normalizer_barIn_K hs h1.K_le)
      · have hLc := hother L hL hLK
        refine hcore.trans (iSup₂_le fun e he => ?_)
        refine pPrimeCoreOf_le_centralizer_of_isComponent hO hL ?_
        intro l hl
        have heK : e ∈ barIn M K := by
          obtain ⟨a, ha, rfl⟩ := he.1
          exact ⟨a, Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 ha).2, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 (hLc hl) e heK).symm
    ·
      have hLH := Thm2AssemblyBasic.components_c2 hF hsimple L hL
      have hHt := puTargetG4_of_c2_pre hL4m hG2r hB hPump hs h1 hF hsimple
      rw [hLH] at hL ⊢
      have hWS : WeakSig2NormG4 ↥(barIn M H) := by
        rcases hHt with h | h | h | h
        · exact hFam.l5 _ hL.1 h
        · exact hFam.l4 _ hL.1 h
        · exact hFam.l3sq _ hL.1 h
        · exact hFam.g2 _ hL.1 h
      have hHn : (barIn M H).Normal := by
        rw [hF]; exact (CFSG.LocalCores.generalized_fitting_characteristic).2
      exact hWS (Mbar M) hO hY4 (barIn M H) hL ⟨MulEquiv.refl _⟩ (barIn M A)
        (barIn M (thetaHalf 1 A)) hDel hrk hWodd hDW hCW
        (fun d _ => Subgroup.le_normalizer_of_normal (H := barIn M H) (K := ⊤) (Subgroup.mem_top d))
    ·
      obtain ⟨hP₁, hP₂⟩ := listedPair_of_c3_pre hB hs h1 hx hL₁ hL₂ hne hs₁ hs₂ hsup hconj
      have hTwo : ∀ J : Subgroup (Mbar M), ListedPair ↥J → IsComponent J → WeakSig2TwoG4 ↥J := by
        intro J hJ hJc
        obtain ⟨hJs, h3 | h4 | h5⟩ := hJ
        · exact hFam.p3 _ hJc.1 hJs h3
        · exact hFam.p4 _ hJc.1 hJs h4
        · exact hFam.p5 _ hJc.1 hJs h5
      rcases hall L hL with rfl | rfl
      · exact hTwo L hP₁ hL (Mbar M) hO hY4 L hL ⟨MulEquiv.refl _⟩ (barIn M A)
          (barIn M (thetaHalf 1 A)) hDel hrk hWodd hDW hCW ⟨L₂, fun d _ => by
            rcases hall _ (Thm2AssemblyBasic.isComponent_conjugate hL d) with h | h
            · exact Or.inl h
            · exact Or.inr h⟩
      · exact hTwo L hP₂ hL (Mbar M) hO hY4 L hL ⟨MulEquiv.refl _⟩ (barIn M A)
          (barIn M (thetaHalf 1 A)) hDel hrk hWodd hDW hCW ⟨L₁, fun d _ => by
            rcases hall _ (Thm2AssemblyBasic.isComponent_conjugate hL d) with h | h
            · exact Or.inr h
            · exact Or.inl h⟩

end T1One

end CFSG.GH74.Generic.BProg.B2
