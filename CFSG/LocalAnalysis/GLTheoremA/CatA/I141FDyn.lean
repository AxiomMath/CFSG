module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

abbrev isLie2NoTits : TauCeti.CFSGIndex → Prop :=
  onLie fun d => d.characteristic = 2 ∧ d ≠ TauCeti.LieTypeIndex.tits

abbrev isRankSmall : TauCeti.CFSGIndex → Prop :=
  fun i => S10.isG2Quot i ∨ ambiguousChev 2 i ∨ onLie (fun d => d = TauCeti.LieTypeIndex.tits) i

@[expose] def I141DynkinLie : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Γ : Type) [Group Γ] [Finite Γ] (L K A : Subgroup Γ) (y : Γ),
    catalogIs (PSimple p L) isLie2NoTits → IsElemAbelian p A → A ≤ Subgroup.normalizer (L : Set Γ) →
    S10.InnDiagOn p A L → y ∈ A → ¬ CentMod p L y →
    GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set Γ)) K →
    catalogIs (PSimple p K) isG2der → catalogIs (PSimple p L) S10.isG2Quot

@[expose] def I141RankSmall : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Γ : Type) [Group Γ] [Finite Γ] (L A : Subgroup Γ),
    catalogIs (PSimple p L) isRankSmall → IsElemAbelian p A → S10.InnDiagOn p A L →
    p ^ 3 * Nat.card ↥(A ⊓ centModSubgroup p L) ≤ Nat.card A → False

theorem catalogIs_rankSmall_of_char2 {S : Type} [Group S]
    (h : catalogIs S (onLie fun d => d.characteristic = 2))
    (ht : ¬ catalogIs S isLie2NoTits) : catalogIs S isRankSmall := by
  obtain ⟨i, hi, e⟩ := h
  cases i with
  | lie d =>
    by_cases htits : d.1 = TauCeti.LieTypeIndex.tits
    · exact ⟨TauCeti.CFSGIndex.lie d, Or.inr (Or.inr htits), e⟩
    · exact absurd ⟨TauCeti.CFSGIndex.lie d, ⟨hi, htits⟩, e⟩ ht
  | _ => exact absurd hi (by simp [onLie])

theorem i141DynkinAt_of_facts (hA : I141DynkinLie) (hB : I141RankSmall) (G : Type) [Group G]
    [Finite G] : CFSG.LocalAnalysis.GLTheoremA.I141DynkinAt G := by
  intro p X L K A y hp hp2 _hLX hchev hAel hAN hInn hrank hyA hycent hK hG2
  have hsmall : catalogIs (PSimple p L) isRankSmall := by
    rcases hchev with h | h
    · by_cases ht : catalogIs (PSimple p L) isLie2NoTits
      · exact S10.catalogIs_imp (fun i hi => Or.inl hi)
          (hA p hp hp2 G L K A y ht hAel hAN hInn hyA hycent hK hG2)
      · exact catalogIs_rankSmall_of_char2 h ht
    · exact S10.catalogIs_imp (fun i hi => Or.inr (Or.inl hi)) h
  exact hB p hp hp2 G L A hsmall hAel hInn hrank

end CFSG.LocalAnalysis.GLTheoremA.I141F
