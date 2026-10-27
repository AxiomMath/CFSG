module

public import CFSG.LocalAnalysis.AGLEmbedding.CoverModule
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbedding

theorem le_pRank_of_pow_le_card {G : Type*} [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    {E H : Subgroup G} (hEH : E ≤ H) (hE : Open.IsElemAbelian p E)
    (hcard : p ^ k ≤ Nat.card E) : k ≤ Open.pRank p H := by
  have := Fact.mk hp
  have hEp : IsPGroup p E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩
  obtain ⟨m, hm⟩ := hEp.exists_card_eq
  exact ((Nat.pow_le_pow_iff_right hp.one_lt).mp (hm ▸ hcard)).trans
    (SectionRank.le_pRank hp.one_lt hEH hE hm)

section Cover

variable {K X : Type} [Group K] [Group X] {p : ℕ} (D : ModuleSpec X p) (π : K →* X)

theorem ModuleSpec.pow_le_card_omegaOf [Finite K] (hp : p.Prime) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K)
    (hcomm : ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, x * y = y * x) :
    p ^ D.n ≤ Nat.card (omegaOf (D.span.comap π) hcomm p) := by
  let ψ : D.span.comap π →* K :=
    { toFun := fun x => (x : K) ^ p
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul]
        exact (show Commute (x : K) y from hcomm _ x.2 _ y.2).mul_pow p }
  have hkerψ : ψ.ker = (omegaOf (D.span.comap π) hcomm p).subgroupOf (D.span.comap π) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_omegaOf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hrange : Nat.card ψ.range ≤ Nat.card (Subgroup.center K) := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨x, rfl⟩
    exact D.pow_mem_center π hker x.2
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hkerψ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe omegaOf_le).toEquiv,
    D.card_comap π hp hπ hker] at h1
  refine Nat.le_of_mul_le_mul_right (c := Nat.card (Subgroup.center K)) ?_ Nat.card_pos
  rw [mul_comm, ← h1]
  exact Nat.mul_le_mul_left _ hrange

theorem ModuleSpec.g_mem_normalizer [Finite X] (j : Fin D.m) :
    D.g j ∈ Subgroup.normalizer (D.span : Set X) := by
  let f := (MulAut.conj (D.g j)).toMonoidHom
  have hle : D.span.map f ≤ D.span := Subgroup.map_le_iff_le_comap.mpr <|
    (Subgroup.closure_le _).mpr <| by
      rintro _ ⟨i, rfl⟩
      show MulAut.conj (D.g j) (D.a i) ∈ D.span
      rw [MulAut.conj_apply, ← D.elt_col]
      exact D.elt_mem _
  have heq : D.span.map f = D.span := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj (D.g j)).injective).ge
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hle (Subgroup.mem_map_of_mem f hx), fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [← (MulAut.conj (D.g j)).injective hyx]

end Cover

theorem coverRankLiftLemma : CoverRankLiftLemma := by
  intro K _ _ X _ _ π hπ hker p hp hp2 hZ1 hZp hZc hdat T
  obtain ⟨r, D, P, hP, hDP, hD, hgen⟩ := hdat
  have := Fact.mk hp
  have : Finite X := Finite.of_surjective π hπ
  have hπZ : ∀ z ∈ Subgroup.center K, π z = 1 := fun z hz =>
    MonoidHom.mem_ker.mp (hker.symm ▸ hz)
  obtain ⟨i₀⟩ : Nonempty (Fin r) := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Set.iUnion_of_empty, Subgroup.closure_empty] at hgen
    exact bot_ne_top hgen
  have hcomm : ∀ i, ∀ x ∈ (D i).span.comap π, ∀ y ∈ (D i).span.comap π, x * y = y * x := by
    intro i
    have hA : (D i).NoAlt := by
      rcases hD i with h | h
      exacts [h.2, h.2.1]
    exact (D i).commute_of_noAlt π hp hp2 hπ hker hZp hZc hA
  have hrank : ∀ i, 3 ≤ Open.pRank p ((D i).span.comap π) := by
    intro i
    refine le_pRank_of_pow_le_card (E := omegaOf _ (hcomm i) p) hp omegaOf_le
      isElemAbelian_omegaOf ?_
    rcases hD i with ⟨hn, -⟩ | ⟨hn, -, hF⟩
    · exact (Nat.pow_le_pow_right hp.pos hn).trans
        ((D i).pow_le_card_omegaOf π hp hπ hker (hcomm i))
    · exact (Nat.pow_le_pow_right hp.pos (by omega)).trans
        ((D i).pow_succ_le_card_omegaOf π hp hp2 hπ hker hZ1 hZp hZc (hcomm i) hF)
  obtain ⟨T₀, hT₀⟩ := (hP.comap_of_ker_isPGroup π (hker ▸ hZp)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K T₀ T
  let c := (MulAut.conj k).toMonoidHom
  have hT : (T : Subgroup K) = (T₀ : Subgroup K).map c := by
    rw [← hk, Sylow.coe_subgroup_smul]
    rfl
  have hcore : ∀ i, ∀ x ∈ Subgroup.normalizer (((D i).span.comap π : Subgroup K) : Set K),
      c x ∈ Open.GLBCore p 3 (T : Subgroup K) := by
    intro i x hx
    have hQ : ((D i).span.comap π).map c ≤ T := by
      rw [hT]
      exact Subgroup.map_mono ((Subgroup.comap_mono (hDP i)).trans hT₀)
    have hQr : 3 ≤ Open.pRank p (((D i).span.comap π).map c) :=
      (hrank i).trans (SectionRank.pRank_le_map hp.one_lt c (MulAut.conj k).injective _)
    exact (le_sSup ⟨_, hQ, hQr, rfl⟩ : Subgroup.normalizer _ ≤ Open.GLBCore p 3 (T : Subgroup K))
      (Subgroup.le_normalizer_map c (Subgroup.mem_map_of_mem c hx))
  let S : Set K := (Subgroup.center K : Set K) ∪
    ⋃ i, Set.range fun j => Function.surjInv hπ ((D i).g j)
  have hS : Subgroup.closure S = ⊤ := by
    have hmap : (Subgroup.closure S).map π = ⊤ := by
      rw [eq_top_iff, ← hgen, Subgroup.closure_le]
      intro u hu
      obtain ⟨i, j, rfl⟩ := Set.mem_iUnion.mp hu
      rw [← Function.surjInv_eq hπ ((D i).g j)]
      exact Subgroup.mem_map_of_mem π
        (Subgroup.subset_closure (Or.inr (Set.mem_iUnion.mpr ⟨i, j, rfl⟩)))
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : π x ∈ (Subgroup.closure S).map π := hmap ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    have hz : y⁻¹ * x ∈ Subgroup.center K := hker ▸ π.eq_iff.mp hyx.symm
    exact mul_inv_cancel_left y x ▸ mul_mem hy (Subgroup.subset_closure (Or.inl hz))
  have hSle : S ⊆ (Open.GLBCore p 3 (T : Subgroup K)).comap c := by
    rintro x (hx | hx)
    · refine hcore i₀ x (Subgroup.le_normalizer_comap π ?_)
      rw [Subgroup.mem_comap, hπZ x hx]
      exact one_mem _
    · obtain ⟨i, j, rfl⟩ := Set.mem_iUnion.mp hx
      refine hcore i _ (Subgroup.le_normalizer_comap π ?_)
      show π (Function.surjInv hπ ((D i).g j)) ∈ Subgroup.normalizer ((D i).span : Set X)
      rw [Function.surjInv_eq hπ]
      exact (D i).g_mem_normalizer j
  refine ⟨eq_top_iff.mpr fun y _ => ?_,
    (hrank i₀).trans (SectionRank.pRank_mono hp.one_lt le_top)⟩
  have hle := (Subgroup.closure_le _).mpr hSle
  rw [hS] at hle
  obtain ⟨z, rfl⟩ := (MulAut.conj k).surjective y
  exact hle (Subgroup.mem_top z)

end CFSG.AGLEmbedding
