module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnType
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116e

public section

namespace CFSG.LieType.SeitzGeneration.CubeCoverE6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116e
  CFSG.HardMathSupport.Dickson.Sec6

theorem exists_lieIndex_char_of_chevSimple_odd {r : ℕ} (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    {S : Type} [Group S] (h : IsChevSimple r S) :
    (∃ d : TauCeti.ValidLieTypeIndex,
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) ∧ d.1.characteristic = r ∧
          3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1) ∨
      NoPlane3 S := by
  rcases h with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      have hd : d.1.characteristic = r := hi
      refine Or.inl ⟨d, ⟨e⟩, hd, by omega, ?_⟩
      intro hexc
      rcases hexc with ⟨-, h2⟩ | ⟨h35, -⟩
      · rcases h2 with ⟨q, hq, -, hdq⟩ | ⟨q, hq, -, hdq⟩ | ⟨q, hq, -, hdq⟩ |
          ⟨q, hq, -, hdq | hdq⟩ | hdt
        · rw [hdq] at hd; simp at hd; omega
        · rw [hdq] at hd; simp at hd; omega
        · rw [hdq] at hd; simp at hd; omega
        · rw [hdq] at hd; simp at hd; omega
        · rw [hdq] at hd; simp at hd; omega
        · rw [hdt] at hd; simp at hd; omega
      · omega
    | alternating n hn => exact hi.elim
    | cyclic p hp => exact hi.elim
    | sporadic s => exact hi.elim
  · cases i with
    | alternating n hn =>
      rcases hi with ⟨h5, h25⟩ | ⟨h6, h23⟩ | ⟨h8, h2⟩
      · subst h5
        refine Or.inr ?_
        intro D hD hcard
        let φ : MulAut S ≃* MulAut (alternatingGroup (Fin 5)) := MulAut.congr e
        have hD' : CFSG.Open.IsElemAbelian 3 (D.map φ.toMonoidHom) :=
          CFSG.SectionRank.isElemAbelian_map hD φ.toMonoidHom
        have hcard' : Nat.card (D.map φ.toMonoidHom) = 3 ^ 2 := by
          rw [Subgroup.card_map_of_injective φ.injective, hcard]
        exact noPlane3_alternatingGroup_five _ hD' hcard'
      · omega
      · omega
    | lie d =>
      exfalso
      obtain ⟨d, hdv⟩ := d
      cases d with
      | A rank q =>
        rcases rank with _ | _ | rank
        · simp [ambiguousChev] at hi
        · simp [ambiguousChev] at hi; omega
        · simp [ambiguousChev] at hi
      | twistedA rank q =>
        rcases rank with _ | _ | _ | _ | rank
        · simp [ambiguousChev] at hi
        · simp [ambiguousChev] at hi
        · simp [ambiguousChev] at hi; omega
        · simp [ambiguousChev] at hi; omega
        · simp [ambiguousChev] at hi
      | _ => simp [ambiguousChev] at hi
    | cyclic p hp => exact hi.elim
    | sporadic s => exact hi.elim

section TwE6ComponentCoverShape


theorem twE6ComponentCoverShape_of_odd (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hK2 : ringChar K ≠ 2) (hσ : ∀ c, σ c = c ^ q)
    (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q) {f : MulAut (twistedE6RootGroup K σ)}
    (hf3 : f ^ 3 = 1) {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))) :
    (∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group),
        3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
          ¬ ExcIndex 3 d.1 ∧ ¬ IsLThreeFour (J ⧸ Subgroup.center J)) ∨
      NoPlane3 (J ⧸ Subgroup.center J) ∨ ¬ 3 ∣ Nat.card J := by
  by_cases h3 : 3 ∣ Nat.card (J ⧸ Subgroup.center J)
  · have hchev := KSNotAll24.component_isChevSimple K σ q hK3 hσ hKq hq2 hf3 hJ h3
    rcases exists_lieIndex_char_of_chevSimple_odd hK2 hK3 hchev with
      ⟨d, ⟨e⟩, hchar, h3char, hD2⟩ | hno
    · refine Or.inl ⟨d, e, h3char, hD2, ?_, ?_⟩
      · intro hexc
        exact hK2 (hchar ▸ characteristic_eq_two_of_excIndex_three hexc)
      · intro hL
        exact not_isChevSimple_of_isLThreeFour hK2 hL hchev
    · exact Or.inr (Or.inl hno)
  · exact Or.inr (Or.inr (KSNotAll24.not_three_dvd_card_of_perfect hJ.2.2.1 h3))

end TwE6ComponentCoverShape

end CFSG.LieType.SeitzGeneration.CubeCoverE6
