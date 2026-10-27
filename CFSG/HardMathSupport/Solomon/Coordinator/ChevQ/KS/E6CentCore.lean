module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PlaneKill
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MLocal
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.GLTheoremB.S7Decide

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Dickson.I271
open scoped commutatorElement

theorem glaPPrimeCore_eq_bot_of_subnormal_family {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q]
    [Finite Q] {ι : Type*} {C : Subgroup Q} (L : ι → Subgroup Q)
    (hsub : ∀ i, CFSG.Open.IsSubnormal (L i) C) (hq : ∀ i, CFSG.Open.IsQuasisimple ↥(L i))
    (hpL : ∀ i, p ∣ Nat.card ↥(L i))
    (hcent : IsPGroup p ↥(C ⊓ Subgroup.centralizer ((⨆ i, L i : Subgroup Q) : Set Q))) :
    GLAPPrimeCore p ↥C = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup ↥C := GLAPPrimeCore p ↥C with hN
  have hcop : Nat.Coprime p (Nat.card N) := CFSG.pPrimeCore_coprime_card (p := p) (G := ↥C)
  have key : ∀ {M : Subgroup Q}, CFSG.Open.IsSubnormal M C → CFSG.Open.IsQuasisimple ↥M →
      p ∣ Nat.card ↥M → ⁅M.subgroupOf C, N⁆ = ⊥ := by
    intro M hM hqM hpM
    have hMC : M ≤ C := hM.le
    have e1 : ↥(M.subgroupOf C) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMC
    have hq1 : CFSG.Open.IsQuasisimple ↥(M.subgroupOf C) :=
      CFSG.Open.IsQuasisimple.of_mulEquiv e1 hqM
    have hq' : CFSG.IsQuasisimple ↥(M.subgroupOf C) :=
      ⟨⟨hq1.1⟩, hq1.2,
        CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq1⟩
    have hK : CFSG.IsComponent (M.subgroupOf C) := ⟨hq', hM.subgroupOf⟩
    rcases CFSG.LocalCores.component_normal_subgroup hK (inferInstance : N.Normal) with h | h
    · exfalso
      have h1 : Nat.card (M.subgroupOf C) ∣ Nat.card N := Subgroup.card_dvd_of_le h
      have h2 : p ∣ Nat.card (M.subgroupOf C) := by
        rw [Nat.card_congr e1.toEquiv]
        exact hpM
      exact hp.ne_one (hcop.eq_one_of_dvd (h2.trans h1))
    · exact h
  have cent : ∀ {M : Subgroup Q}, M ≤ C → ⁅M.subgroupOf C, N⁆ = ⊥ →
      ∀ n ∈ N, (n : Q) ∈ Subgroup.centralizer (M : Set Q) := by
    intro M hMC hc n hn
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro l hl
    have hl' : (⟨l, hMC hl⟩ : ↥C) ∈ M.subgroupOf C := hl
    have hc' : ⁅(⟨l, hMC hl⟩ : ↥C), n⁆ ∈ ⁅M.subgroupOf C, N⁆ :=
      Subgroup.commutator_mem_commutator hl' hn
    rw [hc, Subgroup.mem_bot] at hc'
    have := congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.1 hc')
    exact this
  have hle : N.map C.subtype ≤
      C ⊓ Subgroup.centralizer ((⨆ i, L i : Subgroup Q) : Set Q) := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n.2, ?_⟩
    have hjoin : (⨆ i, L i) ≤ Subgroup.centralizer ({(n : Q)} : Set Q) := by
      refine iSup_le fun i x hx => ?_
      have h := Subgroup.mem_centralizer_iff.1
        (cent (hsub i).le (key (hsub i) (hq i) (hpL i)) n hn) x hx
      exact Subgroup.mem_centralizer_singleton_iff.2 h
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    exact Subgroup.mem_centralizer_singleton_iff.1 (hjoin hh)
  have hNp : IsPGroup p N :=
    (hcent.to_le hle).of_equiv (N.equivMapOfInjective C.subtype C.subtype_injective).symm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hNp
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hcop
    exact hp.ne_one (hcop.eq_one_of_dvd (dvd_pow_self p hk0))
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq N hk

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
