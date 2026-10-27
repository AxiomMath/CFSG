module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_5SMain
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.Proving.CoreCentralQuotient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Proving (GLAPPrimeCoreOf_conj_mem coprime_card_GLAPPrimeCoreOf
  le_GLAPPrimeCoreOf_of_normal)
open scoped commutatorElement

theorem input14_5Second_of_central_quot (h : Lemma27Ns.Input14_5)
    (h18 : Lemma514CoverNs.Input18_1) (hSP : I145SCentralQuot) : Input14_5Second := by
  intro Y _ _ hK hcore Q hQ0 hQ
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set N : Subgroup Y := Subgroup.normalizer (Q : Set Y) with hN
  set C : Subgroup Y := Subgroup.centralizer (Q : Set Y) with hC
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hQN : Q ≤ N := Subgroup.le_normalizer
  have hC0 := i145s_main h h18 hSP (Nat.card Y) Y le_rfl hK hcore Q hQ
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 N)) :=
    coprime_card_GLAPPrimeCoreOf hp3 N
  have hdisj : Disjoint (GLAPPrimeCoreOf 3 N) Q := by
    obtain ⟨a, ha⟩ := hQ.exists_card_eq
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [ha]
    exact Nat.Coprime.pow_right a hcop.symm
  have hcomm : ∀ g ∈ N, ∀ q ∈ Q, ⁅g, q⁆ ∈ GLAPPrimeCoreOf 3 N → g * q = q * g := by
    intro g hg q hq hgq
    have hQ' : ⁅g, q⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem ((Subgroup.mem_normalizer_iff.1 hg q).1 hq) (Q.inv_mem hq)
    have h1 : ⁅g, q⁆ ∈ GLAPPrimeCoreOf 3 N ⊓ Q := ⟨hgq, hQ'⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hLC : GLAPLayer 3 N ≤ C := by
    intro g hg
    refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
    have hgN : g ∈ N := i145s_layer_le N hg
    have hmem : ⁅g, q⁆ ∈ GLAPPrimeCoreOf 3 N := by
      have h2 : q ∈ LocalBalance.oPrimePOf 3 N := by
        refine Lemma27Ns.g2_crit hQN ((Subgroup.normal_subgroupOf_iff_le_normalizer hQN).2 le_rfl)
          ?_ hq
        intro g' hg'
        obtain ⟨k, hk⟩ := hQ ⟨g', hg'⟩
        exact ⟨k, by
          have : g' ^ (3 ^ k) = 1 := congrArg Subtype.val hk
          rw [this]
          exact Subgroup.one_mem _⟩
      exact Lemma27Ns.layer_comm_oPrimeP N (Subgroup.commutator_mem_commutator hg h2)
    exact (hcomm g hgN q hq hmem).symm
  have hL : GLAPLayer 3 N ≤ GLAPLayer 3 C := by
    refine sSup_le fun J hJ => le_sSup ?_
    exact glaPComponent_of_le hp3 hJ ((le_sSup hJ).trans hLC) hCN
  have hOC : GLAPPrimeCoreOf 3 N ≤ C := by
    intro w hw
    refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
    have hwN : w ∈ N := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le N hw
    have hmem : ⁅w, q⁆ ∈ GLAPPrimeCoreOf 3 N := by
      rw [commutatorElement_def]
      have h1 : q * w⁻¹ * q⁻¹ ∈ GLAPPrimeCoreOf 3 N :=
        GLAPPrimeCoreOf_conj_mem q (hQN hq) _ ((GLAPPrimeCoreOf 3 N).inv_mem hw)
      have : w * q * w⁻¹ * q⁻¹ = w * (q * w⁻¹ * q⁻¹) := by group
      rw [this]
      exact (GLAPPrimeCoreOf 3 N).mul_mem hw h1
    exact (hcomm w hwN q hq hmem).symm
  have hO : GLAPPrimeCoreOf 3 N ≤ GLAPPrimeCoreOf 3 C :=
    le_GLAPPrimeCoreOf_of_normal hOC
      (fun g hg x hx => GLAPPrimeCoreOf_conj_mem g (hCN hg) x hx) hcop
  exact le_bot_iff.1 (hC0 ▸ Subgroup.commutator_mono hL hO)

theorem input14_5Second_of_lemma27 (h : Lemma27Ns.Input14_5) (h18 : Lemma514CoverNs.Input18_1) :
    Input14_5Second :=
  input14_5Second_of_central_quot h h18 fun _ _ _ hcore _ _ hZ hZp =>
    CFSG.HardMathSupport.Solomon.Proving.glaPPrimeCore_quotient_eq_bot_of_le_center
      Nat.prime_three hcore hZ hZp

end CFSG.HardMathSupport.Solomon.Coordinator
