module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPCase2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLayer
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPSylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.LocalCores Subgroup

@[expose] def RankPCase1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → f.Prime → 5 ≤ f → f < p →
    CFSG.Open.IsKGroup X →
    (∀ C : CFSG.LocalCores.ComponentIndex (X ⧸ CFSG.pPrimeCore p X),
      IsSimpleGroup ↥C.1 ∧ f ∣ Nat.card C.1) →
    p ≤ Nat.card (CFSG.LocalCores.ComponentIndex (X ⧸ CFSG.pPrimeCore p X)) →
    ∀ E : Subgroup X, IsPGroup f E → E ≤ CFSG.pLayer X p ⊓ CFSG.pPrimeCore p X →
      (∀ Q : Subgroup X, Q ≤ CFSG.pLayer X p ⊓ CFSG.pPrimeCore p X → IsPGroup f Q → E ≤ Q →
        Q = E) →
      CFSG.layer (X ⧸ CFSG.pPrimeCore p X) ≤
        (CFSG.pLayer X p ⊓ centralizer (E : Set X)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore p X)) →
      ∀ y : X, orderOf y = f → y ∈ normalizer (E : Set X) →
        3 ≤ CFSG.Open.pRank f (centralizer ({y} : Set X))

theorem kFact613rankP_of_case1 (hcase1 : RankPCase1) : KFact613rankP := by
  intro X _ _ p f hp hf hf5 hfp hK hC hcard htrans P hPnc h3 y hy
  haveI := Fact.mk hp
  haveI := Fact.mk hf
  haveI hLc : (CFSG.pLayer X p).Characteristic :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic (G := X) (p := p)
  haveI hLn : (CFSG.pLayer X p).Normal := inferInstance
  haveI : (CFSG.pLayer X p ⊓ CFSG.pPrimeCore p X).Normal := inferInstance
  have hOp : ¬ p ∣ Nat.card (CFSG.pLayer X p ⊓ CFSG.pPrimeCore p X : Subgroup X) := by
    intro hdvd
    have hcop : Nat.Coprime p (Nat.card (CFSG.pPrimeCore p X)) := CFSG.pPrimeCore_coprime_card
    have hle : Nat.card (CFSG.pLayer X p ⊓ CFSG.pPrimeCore p X : Subgroup X) ∣
        Nat.card (CFSG.pPrimeCore p X) := Subgroup.card_dvd_of_le inf_le_right
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop (hdvd.trans hle))
  obtain ⟨E, hEO, hEp, hEmax, hEy, hfrat⟩ :=
    RankP.exists_sylow_normalized (CFSG.pLayer X p ⊓ CFSG.pPrimeCore p X)
      (by have := pow_orderOf_eq_one y; rwa [hy] at this)
  have hfrat' : ∀ g : X, ∃ n ∈ normalizer (E : Set X), ∃ o ∈ CFSG.pPrimeCore p X, g = n * o := by
    intro g
    obtain ⟨n, hn, o, ho, rfl⟩ := hfrat g
    exact ⟨n, hn, o, ho.2, rfl⟩
  have htrans' : ∀ C D : CFSG.LocalCores.ComponentIndex (X ⧸ CFSG.pPrimeCore p X),
      ∃ g : X ⧸ CFSG.pPrimeCore p X, C.1.map (MulAut.conj g).toMonoidHom = D.1 := by
    intro C D
    obtain ⟨g, hg⟩ := htrans C D
    exact ⟨QuotientGroup.mk' (CFSG.pPrimeCore p X) g, hg⟩
  rcases RankP.dichotomy p E hfrat' (fun C => (hC C).1) htrans' with hbot | hcover
  ·
    have hH : ∀ h ∈ CFSG.pLayer X p, (∀ e ∈ E, h * e = e * h) →
        h ∈ CFSG.pLayer X p ⊓ CFSG.pPrimeCore p X := by
      intro h hL hc
      refine ⟨hL, ?_⟩
      have hmem : (QuotientGroup.mk' (CFSG.pPrimeCore p X)) h ∈
          (CFSG.pLayer X p ⊓ centralizer (E : Set X)).map
            (QuotientGroup.mk' (CFSG.pPrimeCore p X)) :=
        ⟨h, ⟨hL, Subgroup.mem_centralizer_iff.mpr fun e he => (hc e he).symm⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff h).mp hmem
    exact RankP.three_le_pRank_of_case2 hf hp (by omega) hfp hOp hEp hfrat hH P hPnc h3 hy hEy
  · exact hcase1 X p f hp hf hf5 hfp hK hC hcard E hEp hEO hEmax hcover y hy hEy

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
