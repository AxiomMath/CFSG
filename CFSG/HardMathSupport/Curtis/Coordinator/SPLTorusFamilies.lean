module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusCyclic
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAlt
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusSmall
public import CFSG.HardMathSupport.Curtis.Proving.ToralCaseSplit

public section

open CFSG.AGLEmbedding
open CFSG.Assembly.LowTwoRank

namespace CFSG.HardMathSupport.Curtis.Coordinator

@[expose] def KFactSPLBlockTorusCaseBLie : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (p r : ℕ), CFSG.IsComponent L →
    p.Prime → p ≠ 2 → r.Prime → r ∣ p ^ 2 + 1 → ¬ r ∣ p ^ 2 - 1 →
    (∃ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2Index d.1 ∧
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    (¬ ∃ n : ℕ, Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin n))) →
    (¬ ∃ P : Sylow p (↥L ⧸ Subgroup.center ↥L), IsCyclic ↥(P : Subgroup (↥L ⧸ Subgroup.center ↥L))) →
    ∀ (u c : Y) (T X : Subgroup Y),
      u ∈ Subgroup.normalizer (L : Set Y) → u ^ p = 1 →
      u ∉ Subgroup.centralizer (L : Set Y) →
      Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({u} : Set Y)) →
      T ≤ Subgroup.normalizer (L : Set Y) → T ≤ Subgroup.centralizer ({u} : Set Y) → X ≤ T →
      T ⊓ Subgroup.centralizer (L : Set Y) = X →
      (∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ X) → (∀ a ∈ T, a ^ p ∈ X) →
      X.relIndex T = p ^ 4 →
      c ∈ Subgroup.normalizer (L : Set Y) → c ∈ Subgroup.centralizer ({u} : Set Y) →
      (∃ k : ℕ, c ^ r ^ k = 1) → (∀ t ∈ T, c * t * c⁻¹ ∈ T) →
      (∃ t ∈ T, c * t * c⁻¹ * t⁻¹ ∉ X) → False

open CFSG.HardMathSupport.Curtis.Proving in
theorem caseB_of_lie_rest (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hRest : KFactSPLBlockTorusCaseBLie) : KFactSPLBlockTorusCaseB := by
  intro Y _ _ L p r hL hp hp2 hr hdvd hndvd hSPL hCat u c T X hu hup hunC hsolv hTN hTC hXT hTX
    hcomm hpow hidx hcN hcC hcr hcT hnt
  have : Group.IsPerfect L := hL.1.1
  obtain ⟨E, ζ, γ, hdata⟩ := exists_splAutData L p r hp hp2 hr hdvd hndvd u c T X hu hup hsolv hTN
    hTC hTX hcomm hpow hidx hcN hcC hcr hcT hnt
  have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  have hnab := hL.1.2.2
  by_cases halt : ∃ n : ℕ, Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin n))
  · obtain ⟨n, ⟨e⟩⟩ := halt
    exact false_of_alternating hs hnab e hdata
  by_cases hcyc : ∃ P : Sylow p (↥L ⧸ Subgroup.center ↥L), IsCyclic ↥(P : Subgroup (↥L ⧸ Subgroup.center ↥L))
  · obtain ⟨P, hP⟩ := hcyc
    exact false_of_cyclic_sylow hOut hs hnab hCat P hP hdata
  rcases splTypeBar_of_blockType hp hSPL with hcl | h2 | h3
  · rcases hcl with ⟨d, hd, hSd⟩ | ⟨n, -, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
    · exact hRest Y L p r hL hp hp2 hr hdvd hndvd ⟨d, hd, hSd⟩ halt hcyc u c T X hu hup hunC hsolv
        hTN hTC hXT hTX hcomm hpow hidx hcN hcC hcr hcT hnt
    · exact absurd ⟨n, ⟨e⟩⟩ halt
    · obtain ⟨idx, hv⟩ := d
      rcases hd with ⟨q, hq7, hd1⟩ | ⟨q, hq3, hd1⟩
      · obtain rfl : idx = .A 1 q := hd1
        have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
        have hpe : q.p = 7 ∧ q.exponent = 1 := by
          have h7 : q.p ^ q.exponent = 7 := by rw [← TauCeti.PrimePower.card_def]; exact hq7
          exact (Nat.Prime.pow_eq_iff (by norm_num)).1 h7
        rw [hpe.1, hpe.2] at h
        exact false_of_psl_seven_family hnab h hdata
      · obtain rfl : idx = .twistedA 2 q := hd1
        have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
        have hpe : q.p = 3 ∧ q.exponent = 1 := by
          have h3 : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq3
          exact (Nat.Prime.pow_eq_iff (by norm_num)).1 h3
        rw [hpe.1, hpe.2] at h
        exact false_of_psu_three_three_family hnab h hdata
  · exact absurd h2 halt
  · exact absurd h3 hcyc

end CFSG.HardMathSupport.Curtis.Coordinator
