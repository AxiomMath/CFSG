module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.Adapters.LinearCatalog
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

theorem heisFamA_model {X : Type} [Group X] (d : TauCeti.ValidLieTypeIndex) (hd : IdxA d.1)
    (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ n f : ℕ, 2 ≤ n ∧ 1 ≤ f ∧ CFSG.Blueprint.LieModel X .PSL n 2 f ∧
      Nonempty (X ≃* StatedProj (StatedSL n (GaloisField 2 f))) := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    change q.p = 2 at hd
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    obtain ⟨p, k, hp, hk⟩ := q
    change p = 2 at hd
    subst hd
    have : Fact (Nat.Prime 2) := ⟨hp⟩
    have hr' : 1 ≤ r ∧ (r = 1 → 4 ≤ 2 ^ k) := by
      simpa only [TauCeti.PrimePower.card_def] using hr
    have h2k : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    let eX : X ≃* StatedProj (StatedSL (r + 1) (GaloisField 2 k)) :=
      (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r ⟨2, k, hp, hk⟩ hv)).trans
        (projectiveSpecialLinearGroupEquivStatedProj (r + 1) _)
    have hadm : StatedLieAdmissible .PSL (r + 1) 2 k := by
      refine ⟨Nat.prime_two, hk, by omega, ?_, ?_⟩
      · intro h
        simp only [Prod.mk.injEq] at h
        have := hr'.2 (by omega)
        omega
      · intro h
        simp only [Prod.mk.injEq] at h
        have := hr'.2 (by omega)
        omega
    refine ⟨r + 1, k, by omega, hk, Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
      hadm, GaloisField 2 k, inferInstance, inferInstance, GaloisField.card 2 k (by omega),
      ⟨eX⟩⟩, ⟨eX⟩⟩
  | _ => exact hd.elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
