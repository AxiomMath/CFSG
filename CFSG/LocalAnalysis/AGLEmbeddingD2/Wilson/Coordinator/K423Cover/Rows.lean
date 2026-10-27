module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofMcL
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Cover423.Defs
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofK
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesA7
public import CFSG.RankThree.PartTwo.KFacts.KP4

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4

theorem alphaNine_alt6 :
    Census.Karpilovsky.Coordinator.Cover423.AlphaNine (alternatingGroup (Fin 6)) :=
  fun _ _ hD9 => Res423Two.alphaVanishes_alt6 (MulEquiv.refl _) hD9

theorem alphaNine_McL :
    Census.Karpilovsky.Coordinator.Cover423.AlphaNine
      (Blueprint.NativeSporadic.Carrier .McL) := by
  intro D hD hD9
  have eM : Blueprint.NativeSporadic.Carrier .McL ≃* CFSG.Sporadic.Schreier.mclP :=
    CFSG.Sporadic.Schreier.mclPermEquiv
  have : Finite (Blueprint.NativeSporadic.Carrier .McL) := Finite.of_equiv _ eM.symm.toEquiv
  refine Res423Two.alphaVanishes_of_mulEquiv eM ?_
  refine Res423Three.alphaVanishes_mclP ?_ (Res423Two.isElemAbelian_map' _ hD).2
  intro h
  have h9 : Nat.card (D.map eM.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective eM.injective, hD9]
  rw [h, Subgroup.card_bot] at h9
  norm_num at h9

theorem centralizer_le_of_map {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y) {P : Subgroup X}
    (h : Subgroup.centralizer ((P.map ψ.toMonoidHom : Subgroup Y) : Set Y) ≤ P.map ψ.toMonoidHom) :
    Subgroup.centralizer (P : Set X) ≤ P := by
  intro x hx
  have hx' : ψ x ∈ (Subgroup.centralizer (P : Set X)).map ψ.toMonoidHom := ⟨x, hx, rfl⟩
  rw [CFSG.RankThree.Asc83Table.map_equiv_centralizer_eq] at hx'
  obtain ⟨y, hy, hyx⟩ := h hx'
  rw [← ψ.injective hyx]
  exact hy

theorem rowFacts_alt7 {S : Type} [Group S] [Finite S] (e : S ≃* alternatingGroup (Fin 7)) :
    ¬ 27 ∣ Nat.card S ∧
      (∀ P : Subgroup S, Nat.card P = 9 → ∃ g : S, ∀ x ∈ P, g * x * g⁻¹ = x⁻¹) ∧
      ∀ P : Subgroup S, Nat.card P = 9 → Subgroup.centralizer (P : Set S) ≤ P := by
  refine ⟨?_, fun P hP => ?_, fun P hP => ?_⟩
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · obtain ⟨g, -, hg⟩ := Sec17.Proof1721.ks1721Invert_alt7 ⟨e⟩ hP
    exact ⟨g, hg⟩
  · have hfac : (Nat.card (alternatingGroup (Fin 7))).factorization 3 = 2 :=
      Res423Two.factorization_card_alternatingGroup (n := 7) (m := 280) (by norm_num)
        (by decide) (by decide)
    have hP' : Nat.card (P.map e.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective e.injective, hP]
    obtain ⟨g, hg⟩ := Res423Two.exists_map_conj_eq_of_card_nine hfac hP'
      Sec14.Res5TypesA7.card_P7
    set ψ : S ≃* alternatingGroup (Fin 7) := e.trans (MulAut.conj g) with hψ
    have hPψ : P.map ψ.toMonoidHom = Sec14.Res5TypesA7.P7 := by
      rw [← hg, Subgroup.map_map]
      rfl
    refine centralizer_le_of_map ψ ?_
    rw [hPψ]
    exact Sec14.Res5TypesA7.centralizer_P7_le

theorem rowFacts_m22
    {S : Type} [Group S] [Finite S]
    (e : S ≃* Blueprint.NativeSporadic.M22) :
    ¬ 27 ∣ Nat.card S ∧
      (∀ P : Subgroup S, Nat.card P = 9 → ∃ g : S, ∀ x ∈ P, g * x * g⁻¹ = x⁻¹) ∧
      ∀ P : Subgroup S, Nat.card P = 9 → Subgroup.centralizer (P : Set S) ≤ P := by
  refine ⟨?_, fun P hP => ?_, fun P hP => ?_⟩
  · rw [Nat.card_congr e.toEquiv, Census.card_m22_eq]
    decide
  · obtain ⟨g, -, hg⟩ := Sec17.Proof1721.ks1721Invert_m22 ⟨e⟩ hP
    exact ⟨g, hg⟩
  · exact (KFacts.KP4.m22_centralizer_eq ⟨e⟩ hP).le

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover
