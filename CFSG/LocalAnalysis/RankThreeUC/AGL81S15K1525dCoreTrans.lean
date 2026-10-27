module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K1525dRed
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bTrans
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenYLevel

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.McLaughlin
open KFactsSmall

namespace K1525dCoreProof

section Transport

variable {L K : Type} [Group L] [Group K] [Finite L] [Finite K]

theorem map_map_symm (e : L ≃* K) (A : Subgroup L) :
    (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
  rw [Subgroup.map_map]
  ext x
  simp

theorem map_symm_map (e : L ≃* K) (A : Subgroup K) :
    (A.map e.symm.toMonoidHom).map e.toMonoidHom = A := by
  rw [Subgroup.map_map]
  ext x
  simp

theorem pElementSubgroup_map_equiv_aux (e : L ≃* K) (A : Subgroup L) :
    (pElementSubgroup 2 A).map e.toMonoidHom = pElementSubgroup 2 (A.map e.toMonoidHom) := by
  rw [pElementSubgroup, pElementSubgroup, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxA, k, hk⟩, rfl⟩
    exact ⟨⟨x, hxA, rfl⟩, k, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hk]⟩
  · rintro ⟨⟨x, hxA, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hxA, k, ?_⟩, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hk

theorem sylowTwo_map (e : L ≃* K) {S₀ : Subgroup L}
    (h : CFSG.QuasithinUnique.IsSylowTwoOf S₀ ⊤) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S₀.map e.toMonoidHom) ⊤ :=
  K1525d_of_core_aux_sylow_map e.toMonoidHom e.surjective h

theorem pRank_map_equiv (e : L ≃* K) (p : ℕ) (A : Subgroup L) :
    CFSG.Open.pRank p (A.map e.toMonoidHom) = CFSG.Open.pRank p A := by
  have key : ∀ {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
      (B : Subgroup X) (k : ℕ),
      (∃ E : Subgroup X, E ≤ B ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k) →
        ∃ E : Subgroup Y, E ≤ B.map e.toMonoidHom ∧ CFSG.Open.IsElemAbelian p E ∧
          Nat.card E = p ^ k := by
    rintro X Y _ _ _ _ e B k ⟨E, hEB, hE, hc⟩
    exact ⟨E.map e.toMonoidHom, Subgroup.map_mono hEB,
      K21bTransProof.isElemAbelian_map_inj e.injective hE,
      by rw [Subgroup.card_map_of_injective e.injective, hc]⟩
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  · intro h
    have h' := key e.symm (A.map e.toMonoidHom) k h
    rwa [map_map_symm] at h'
  · exact key e A k

theorem cover_map (e : L ≃* K) {S₀ A₁ A₂ : Subgroup L}
    (h : ∀ P : Subgroup L, IsMinOverBorel ⊤ S₀ P →
      pElementSubgroup 2 P ≤ A₁ ∨ pElementSubgroup 2 P ≤ A₂) :
    ∀ P : Subgroup K, IsMinOverBorel ⊤ (S₀.map e.toMonoidHom) P →
      pElementSubgroup 2 P ≤ A₁.map e.toMonoidHom ∨
        pElementSubgroup 2 P ≤ A₂.map e.toMonoidHom := by
  intro P hP
  have hP' := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.isMinOverBorel_top_map
    e.symm hP
  rw [map_map_symm] at hP'
  have hmap : ∀ A : Subgroup L, pElementSubgroup 2 (P.map e.symm.toMonoidHom) ≤ A →
      pElementSubgroup 2 P ≤ A.map e.toMonoidHom := by
    intro A hA
    have h1 := Subgroup.map_mono (f := e.toMonoidHom) hA
    rwa [pElementSubgroup_map_equiv_aux, map_symm_map] at h1
  rcases h _ hP' with h1 | h1
  · exact Or.inl (hmap _ h1)
  · exact Or.inr (hmap _ h1)

theorem isL3TwoModO2_of_map (e : L ≃* K) {A : Subgroup L}
    (h : IsL3TwoModO2 (A.map e.toMonoidHom)) : IsL3TwoModO2 A := by
  let f : ↥A ≃* ↥(A.map e.toMonoidHom) := Subgroup.equivMapOfInjective A e.toMonoidHom e.injective
  exact IsLThreeTwo.of_mulEquiv
    (QuotientGroup.congr (CFSG.pCore 2 ↥A) (CFSG.pCore 2 ↥(A.map e.toMonoidHom)) f
      (CFSG.pCore_map_iso 2 f)).symm h

end Transport

end K1525dCoreProof

end CFSG.LocalAnalysis.RankThreeUC.S15
