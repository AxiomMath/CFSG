module

public import CFSG.GH74.GLS.Stage12.McLEndgame
public import CFSG.GH74.GLS.Stage12.McLNative

public section

namespace CFSG.GH74.GLS.Stage12.McLRec

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Sporadic.Schreier

@[expose] def JWContains : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    OneClassDoubleCover G 8 →
      ∃ H : Subgroup G, Nonempty (↥H ≃* Blueprint.NativeSporadic.McL)

theorem card_centralizer_involution_of_oneClass {G : Type} [Group G] [Finite G]
    (hG : OneClassDoubleCover G 8) {u : G} (hu : orderOf u = 2) :
    Nat.card (centralizer ({u} : Set G)) = 40320 :=
  card_centralizer_involution_of_coverFacts coverFacts_eight hG hu

theorem exists_mulEquiv_of_subgroup
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hG : OneClassDoubleCover G 8) (H : Subgroup G)
    (e : ↥H ≃* Blueprint.NativeSporadic.McL) : Nonempty (G ≃* Blueprint.NativeSporadic.McL) := by
  let e2 : ↥H ≃* mclP := e.trans mclEquivP
  have hcardH : Nat.card H = 898128000 := card_of_equiv_mclP e2
  have hev : Even (Nat.card H) := by rw [hcardH]; decide
  have hone : ∀ u v : H, orderOf u = 2 → orderOf v = 2 → IsConj u v :=
    fun u v hu hv => isConj_of_equiv_mclP e2 hu hv
  have hH : H = ⊤ :=
    eq_top_of_oneClass_centralizers hs coverFacts_eight hG H hev hone
      (fun u hu => card_centralizer_of_equiv_mclP e2 hu)
  exact ⟨((Subgroup.topEquiv (G := G)).symm.trans (MulEquiv.subgroupCongr hH.symm)).trans e⟩

theorem S_McL_leaf_of_JWContains
    (h : JWContains) : S_McL_leaf := by
  intro G _ _ hs hnab hG
  obtain ⟨H, ⟨e⟩⟩ := h G hs hnab hG
  obtain ⟨f⟩ := exists_mulEquiv_of_subgroup hs hG H e
  exact ⟨f⟩

end CFSG.GH74.GLS.Stage12.McLRec
