module

public import CFSG.RankThree.Asc83Table.J3

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint
open CFSG.Sporadic.J3 CFSG.SectionRank.LocalWitness Subgroup MulAction
open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.J3

theorem j3_exists_conj_le_basis
    {A : Subgroup (J D)} (hA : IsElementaryAbelian 3 A) :
    ∃ g : J D, A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure (Set.range x) :=
  exists_conj_le_basis x_pow x_comm x_inj h_conj card_normalizer omega_basis factorization_card hA

theorem j3_exists_conj_eq_basis
    {A : Subgroup (J D)} (hA : IsElementaryAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ g : J D, A.map (MulAut.conj g).toMonoidHom = Subgroup.closure (Set.range x) := by
  obtain ⟨g, hg⟩ := j3_exists_conj_le_basis hA
  refine ⟨g, eq_of_le_of_card_ge hg ?_⟩
  rw [card_map_conj, h27, card_closure_basis x_pow x_comm x_inj]
  norm_num

theorem conj_transport {G L : Type*} [Group G] [Group L] (ψ : L ≃* G) (B : Subgroup G)
    (h : ∀ C : Subgroup G, IsElementaryAbelian 3 C → Nat.card C = 27 →
      ∃ g : G, C.map (MulAut.conj g).toMonoidHom = B)
    {A A' : Subgroup L} (hA : IsElementaryAbelian 3 A) (hA' : IsElementaryAbelian 3 A')
    (h27 : Nat.card A = 27) (h27' : Nat.card A' = 27) :
    ∃ g : L, A.map (MulAut.conj g).toMonoidHom = A' := by
  have key : ∀ C : Subgroup L, IsElementaryAbelian 3 C → Nat.card C = 27 →
      ∃ g : L, (C.map (MulAut.conj g).toMonoidHom).map ψ.toMonoidHom = B := by
    intro C hC hc
    obtain ⟨g, hg⟩ := h (C.map ψ.toMonoidHom) (IsElementaryAbelian.map_hom _ hC)
      (by rw [card_map_of_injective ψ.injective, hc])
    refine ⟨ψ.symm g, ?_⟩
    rw [Subgroup.map_map, ← hg, Subgroup.map_map]
    congr 1
    ext c
    simp [MulAut.conj_apply]
  obtain ⟨g1, h1⟩ := key A hA h27
  obtain ⟨g2, h2⟩ := key A' hA' h27'
  have e : (A.map (MulAut.conj g1).toMonoidHom).map ψ.toMonoidHom =
      (A'.map (MulAut.conj g2).toMonoidHom).map ψ.toMonoidHom := h1.trans h2.symm
  have e' : A.map (MulAut.conj g1).toMonoidHom = A'.map (MulAut.conj g2).toMonoidHom :=
    Subgroup.map_injective ψ.injective e
  refine ⟨g2⁻¹ * g1, ?_⟩
  have e3 : A.map (MulAut.conj (g2⁻¹ * g1)).toMonoidHom =
      (A.map (MulAut.conj g1).toMonoidHom).map (MulAut.conj g2⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext c
    simp [MulAut.conj_apply, mul_assoc]
  rw [e3, e', Subgroup.map_map]
  have : (MulAut.conj g2⁻¹).toMonoidHom.comp (MulAut.conj g2).toMonoidHom = MonoidHom.id L := by
    ext c; simp [MulAut.conj_apply, mul_assoc]
  rw [this, Subgroup.map_id]

theorem j3_e27_conj
    {L : Type*} [Group L] (e : L ≃* NativeSporadic.J3) {A A' : Subgroup L}
    (hA : IsElementaryAbelian 3 A) (hA' : IsElementaryAbelian 3 A') (h27 : Nat.card A = 27)
    (h27' : Nat.card A' = 27) : ∃ g : L, A.map (MulAut.conj g).toMonoidHom = A' := by
  have hB : ∀ C : Subgroup (J D), IsElementaryAbelian 3 C → Nat.card C = 27 →
      ∃ g : J D, C.map (MulAut.conj g).toMonoidHom = Subgroup.closure (Set.range x) :=
    fun C hC h => j3_exists_conj_eq_basis hC h
  have ψ : L ≃* J D := e.trans φ
  exact @conj_transport (J D) L (inferInstance : Group (J D)) (inferInstance : Group L) ψ
    (Subgroup.closure (Set.range x)) hB A A' hA hA' h27 h27'

theorem card_normalizer_map {G N : Type*} [Group G] [Group N] (f : G ≃* N) (H : Subgroup G) :
    Nat.card (normalizer ((H.map f.toMonoidHom : Subgroup N) : Set N)) =
      Nat.card (normalizer (H : Set G)) := by
  rw [← Subgroup.map_equiv_normalizer_eq H f]
  exact Subgroup.card_map_of_injective f.injective

theorem card_normalizer_le_transport {G L : Type*} [Group G] [Group L] (ψ : L ≃* G)
    (B : Subgroup G)
    (h : ∀ C : Subgroup G, IsElementaryAbelian 3 C → Nat.card C = 27 →
      ∃ g : G, C.map (MulAut.conj g).toMonoidHom = B)
    {n : ℕ} (hN : Nat.card (normalizer (B : Set G)) ≤ n)
    {A : Subgroup L} (hA : IsElementaryAbelian 3 A) (h27 : Nat.card A = 27) :
    Nat.card (normalizer (A : Set L)) ≤ n := by
  have hC : IsElementaryAbelian 3 (A.map ψ.toMonoidHom) := IsElementaryAbelian.map_hom _ hA
  have hC27 : Nat.card (A.map ψ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective ψ.injective, h27]
  obtain ⟨g, hg⟩ := h _ hC hC27
  have h1 := card_normalizer_map ψ A
  have h2 := card_normalizer_map (MulAut.conj g) (A.map ψ.toMonoidHom)
  rw [hg] at h2
  rw [← h1, ← h2]
  exact hN

theorem j3_e27_card_normalizer
    {L : Type*} [Group L] (e : L ≃* NativeSporadic.J3) {A : Subgroup L}
    (hA : IsElementaryAbelian 3 A) (h27 : Nat.card A = 27) :
    Nat.card (normalizer (A : Set L)) ≤ 1944 := by
  have hB : ∀ C : Subgroup (J D), IsElementaryAbelian 3 C → Nat.card C = 27 →
      ∃ g : J D, C.map (MulAut.conj g).toMonoidHom = Subgroup.closure (Set.range x) :=
    fun C hC h => j3_exists_conj_eq_basis hC h
  have ψ : L ≃* J D := e.trans φ
  exact @card_normalizer_le_transport (J D) L (inferInstance : Group (J D)) (inferInstance : Group L)
    ψ (Subgroup.closure (Set.range x)) hB 1944 card_normalizer A hA h27

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
