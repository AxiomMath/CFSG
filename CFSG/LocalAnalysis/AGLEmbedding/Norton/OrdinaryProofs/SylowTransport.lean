module

public import CFSG.Open.GLBDefs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.Open
open scoped Pointwise

section Basic

theorem isMulCommutative_of_mulEquiv {M N : Type*} [Mul M] [Mul N] [IsMulCommutative M]
    (e : M ≃* N) : IsMulCommutative N := by
  have hc : ∀ a b : M, a * b = b * a := fun a b => (IsMulCommutative.is_comm (M := M)).comm a b
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  show e x * e y = e y * e x
  rw [← map_mul, ← map_mul, hc x y]

theorem isElemAbelian_map {p : ℕ} {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {E : Subgroup G} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map e.toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem map_map_symm_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (H : Subgroup G) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  ext x
  simp

theorem map_symm_map_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (H : Subgroup G') :
    (H.map e.symm.toMonoidHom).map e.toMonoidHom = H := by
  rw [Subgroup.map_map]
  ext x
  simp

theorem rankSet_subset {p : ℕ} {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) :
    {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} ⊆
      {k | ∃ E : Subgroup G', E ≤ H.map e.toMonoidHom ∧ IsElemAbelian p E ∧
        Nat.card E = p ^ k} := by
  rintro k ⟨E, hEH, hE, hcard⟩
  refine ⟨E.map e.toMonoidHom, Subgroup.map_mono hEH, isElemAbelian_map e hE, ?_⟩
  rw [Subgroup.card_map_of_injective e.injective]
  exact hcard

theorem pRank_map_equiv {p : ℕ} {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (e : G ≃* G') (H : Subgroup G) : pRank p (H.map e.toMonoidHom) = pRank p H := by
  unfold pRank
  congr 1
  have h := rankSet_subset (p := p) e.symm (H.map e.toMonoidHom)
  rw [map_map_symm_equiv] at h
  exact Set.Subset.antisymm h (rankSet_subset e H)

theorem centralizer_image_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (S : Set G) :
    Subgroup.centralizer (e.toMonoidHom '' S) = (Subgroup.centralizer S).map e.toMonoidHom := by
  ext x'
  constructor
  · intro hx
    refine Subgroup.mem_map.2 ⟨e.symm x', ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    apply e.injective
    have := Subgroup.mem_centralizer_iff.1 hx (e.toMonoidHom h) ⟨h, hh, rfl⟩
    simpa [map_mul] using this
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hx h hh
    show e.toMonoidHom h * e.toMonoidHom x = e.toMonoidHom x * e.toMonoidHom h
    rw [← map_mul, ← map_mul, this]

theorem centralizer_map_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (Q : Subgroup G) :
    Subgroup.centralizer ((Q.map e.toMonoidHom : Subgroup G') : Set G') =
      (Subgroup.centralizer (Q : Set G)).map e.toMonoidHom := by
  rw [Subgroup.coe_map]
  exact centralizer_image_equiv e (Q : Set G)

theorem normalizer_map_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (Q : Subgroup G) :
    Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup G') : Set G') =
      (Subgroup.normalizer (Q : Set G)).map e.toMonoidHom :=
  (Subgroup.map_normalizer_eq_of_bijective Q e.bijective).symm

theorem weakJoin_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (P Q : Subgroup G) :
    Q.map e.toMonoidHom ⊔ (P.map e.toMonoidHom ⊓
        Subgroup.centralizer ((Q.map e.toMonoidHom : Subgroup G') : Set G')) =
      (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G))).map e.toMonoidHom := by
  rw [centralizer_map_equiv e Q,
    ← Subgroup.map_inf_eq P (Subgroup.centralizer (Q : Set G)) e.toMonoidHom e.injective,
    ← Subgroup.map_sup]

end Basic

section Cores

variable {p k : ℕ}

theorem GLBCore_map_equiv {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (e : G ≃* G') (P : Subgroup G) :
    GLBCore p k (P.map e.toMonoidHom) = (GLBCore p k P).map e.toMonoidHom := by
  have hset : {N : Subgroup G' | ∃ Q : Subgroup G', Q ≤ P.map e.toMonoidHom ∧
      k ≤ pRank p Q ∧ N = Subgroup.normalizer (Q : Set G')} =
      Subgroup.map e.toMonoidHom '' {N : Subgroup G | ∃ Q : Subgroup G, Q ≤ P ∧
        k ≤ pRank p Q ∧ N = Subgroup.normalizer (Q : Set G)} := by
    ext N'
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨Q', hQ'P, hk, rfl⟩
      have hQ'eq : (Q'.comap e.toMonoidHom).map e.toMonoidHom = Q' :=
        Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Q'
      have hQP : Q'.comap e.toMonoidHom ≤ P := by
        rw [← Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective, hQ'eq]
        exact hQ'P
      refine ⟨Subgroup.normalizer ((Q'.comap e.toMonoidHom : Subgroup G) : Set G),
        ⟨Q'.comap e.toMonoidHom, hQP, ?_, rfl⟩, ?_⟩
      · rw [← pRank_map_equiv e, hQ'eq]
        exact hk
      · rw [Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom) _ e.bijective, hQ'eq]
    · rintro ⟨N, ⟨Q, hQP, hk, rfl⟩, rfl⟩
      refine ⟨Q.map e.toMonoidHom, Subgroup.map_mono hQP, ?_, ?_⟩
      · rw [pRank_map_equiv e]
        exact hk
      · exact Subgroup.map_normalizer_eq_of_bijective Q e.bijective
  unfold GLBCore
  rw [hset, (Subgroup.gc_map_comap e.toMonoidHom).l_sSup_eq_sSup_image]

theorem GLBWeakCore_map_equiv {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (e : G ≃* G') (P : Subgroup G) :
    GLBWeakCore p (P.map e.toMonoidHom) = (GLBWeakCore p P).map e.toMonoidHom := by
  have hset : {N : Subgroup G' | ∃ Q : Subgroup G', Q ≤ P.map e.toMonoidHom ∧
      2 ≤ pRank p Q ∧ 3 ≤ pRank p (Q ⊔ (P.map e.toMonoidHom ⊓
        Subgroup.centralizer (Q : Set G'))) ∧ N = Subgroup.normalizer (Q : Set G')} =
      Subgroup.map e.toMonoidHom '' {N : Subgroup G | ∃ Q : Subgroup G, Q ≤ P ∧
        2 ≤ pRank p Q ∧ 3 ≤ pRank p (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G))) ∧
        N = Subgroup.normalizer (Q : Set G)} := by
    ext N'
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨Q', hQ'P, h2, h3, rfl⟩
      have hQ'eq : (Q'.comap e.toMonoidHom).map e.toMonoidHom = Q' :=
        Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Q'
      have hQP : Q'.comap e.toMonoidHom ≤ P := by
        rw [← Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective, hQ'eq]
        exact hQ'P
      refine ⟨Subgroup.normalizer ((Q'.comap e.toMonoidHom : Subgroup G) : Set G),
        ⟨Q'.comap e.toMonoidHom, hQP, ?_, ?_, rfl⟩, ?_⟩
      · rw [← pRank_map_equiv e, hQ'eq]
        exact h2
      · have h3' : 3 ≤ pRank p ((Q'.comap e.toMonoidHom).map e.toMonoidHom ⊔
            (P.map e.toMonoidHom ⊓ Subgroup.centralizer
              (((Q'.comap e.toMonoidHom).map e.toMonoidHom : Subgroup G') : Set G'))) := by
          rw [hQ'eq]
          exact h3
        rw [weakJoin_map e, pRank_map_equiv e] at h3'
        exact h3'
      · rw [Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom) _ e.bijective, hQ'eq]
    · rintro ⟨N, ⟨Q, hQP, h2, h3, rfl⟩, rfl⟩
      refine ⟨Q.map e.toMonoidHom, Subgroup.map_mono hQP, ?_, ?_, ?_⟩
      · rw [pRank_map_equiv e]
        exact h2
      · rw [weakJoin_map e, pRank_map_equiv e]
        exact h3
      · exact Subgroup.map_normalizer_eq_of_bijective Q e.bijective
  unfold GLBWeakCore CFSG.Open.rankThreeAschCore
  rw [hset, (Subgroup.gc_map_comap e.toMonoidHom).l_sSup_eq_sSup_image]

theorem GLBCore_map_conj {G : Type*} [Group G] [Finite G] (g : G) (P : Subgroup G) :
    GLBCore p k (P.map (MulAut.conj g : G ≃* G).toMonoidHom) =
      (GLBCore p k P).map (MulAut.conj g : G ≃* G).toMonoidHom :=
  GLBCore_map_equiv (MulAut.conj g : G ≃* G) P

end Cores

section Sylow

variable {p k : ℕ}

theorem sylow_eq_map_conj {G : Type*} [Group G] [Finite G] [Fact p.Prime] (P0 P : Sylow p G) :
    ∃ g : G, (P : Subgroup G) = (P0 : Subgroup G).map (MulAut.conj g : G ≃* G).toMonoidHom := by
  have : MulAction.IsPretransitive G (Sylow p G) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P0 P
  refine ⟨g, ?_⟩
  have hc : ((g • P0 : Sylow p G) : Subgroup G) = MulAut.conj g • (P0 : Subgroup G) :=
    Sylow.coe_subgroup_smul
  rw [Subgroup.pointwise_smul_def] at hc
  rw [← hg, hc]
  rfl

theorem GLBCore_top_of_one_sylow {G : Type*} [Group G] [Finite G] [Fact p.Prime]
    (P0 : Sylow p G) (h0 : GLBCore p k (P0 : Subgroup G) = ⊤) (P : Sylow p G) :
    GLBCore p k (P : Subgroup G) = ⊤ := by
  obtain ⟨g, hg⟩ := sylow_eq_map_conj P0 P
  rw [hg, GLBCore_map_conj, h0]
  exact Subgroup.map_top_of_surjective (MulAut.conj g : G ≃* G).toMonoidHom
    (MulAut.conj g : G ≃* G).surjective

theorem GLBCore_top_forall_sylow_map {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    [Fact p.Prime] (e : G ≃* G') (h : ∀ P : Sylow p G, GLBCore p k (P : Subgroup G) = ⊤)
    (P' : Sylow p G') : GLBCore p k (P' : Subgroup G') = ⊤ := by
  have hG := h (Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective P')
  have hcoe : ((Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective P' : Sylow p G) :
      Subgroup G) = (P' : Subgroup G').map e.symm.toMonoidHom := rfl
  rw [hcoe] at hG
  have h1 := GLBCore_map_equiv (p := p) (k := k) e ((P' : Subgroup G').map e.symm.toMonoidHom)
  rw [hG, map_symm_map_equiv e] at h1
  rw [h1]
  exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective

end Sylow

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
