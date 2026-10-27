module

public import CFSG.LieType.Chevalley.FixedRootCentralizerGeneration
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Fixed

variable {t : TwistTag} {k : Type} [Field k]

theorem exists_radicals_of_graphFixedParabolicLevi
    [Finite k] {r : ℕ} [Fact r.Prime] [CharP k r] (σ : k ≃+* k)
    [IsSimpleGroup (graphFixedRootGroup t k σ.toRingHom)] {J : Set (Fin t.foldedTag.rank)}
    (hJ : J ≠ Set.univ) :
    ∃ Q Q' : Subgroup (ModGL t.tag k), IsPGroup r Q ∧ IsPGroup r Q' ∧
      Q ≤ graphFixedRootGroup t k σ.toRingHom ∧ Q' ≤ graphFixedRootGroup t k σ.toRingHom ∧
      graphFixedParabolicLevi t k σ.toRingHom J ≤
        Subgroup.normalizer (Q : Set (ModGL t.tag k)) ∧
      graphFixedParabolicLevi t k σ.toRingHom J ≤
        Subgroup.normalizer (Q' : Set (ModGL t.tag k)) ∧
      graphFixedRootGroup t k σ.toRingHom ≤ Q ⊔ Q' := by
  have := finite_modGL (τ := t.tag) (K := k)
  obtain ⟨w₀, δ, hmax, hδδ, hδ, hcomm⟩ := exists_longest_fixed_data t
  obtain ⟨-, hR, hH⟩ := canonical_weyl_root_transport t.tag k
  set C := graphFixedRootGroup t k σ.toRingHom
  have hnC : canonicalRep (coxeterSystem t.tag) k w₀ ∈ C :=
    canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hmax)
  set n := canonicalRep (coxeterSystem t.tag) k w₀
  have hpos : ∀ i, (rootSubgroup t.tag k (Pi.single i 1)).map (MulAut.conj n).toMonoidHom =
      rootSubgroup t.tag k (-Pi.single (δ i) 1) := fun i => by
    rw [hR w₀ _ (isRoot_single t.tag i), hδ]
  have hneg : ∀ i, (rootSubgroup t.tag k (-Pi.single i 1)).map (MulAut.conj n).toMonoidHom =
      rootSubgroup t.tag k (Pi.single (δ i) 1) := fun i => by
    rw [hR w₀ _ (isRoot_neg_single t.tag i), smul_neg, hδ, neg_neg]
  have hpos' : ∀ i, (rootSubgroup t.tag k (Pi.single i 1)).map (MulAut.conj n⁻¹).toMonoidHom =
      rootSubgroup t.tag k (-Pi.single (δ i) 1) := fun i => by
    rw [← map_conj_inv_map_conj (rootSubgroup t.tag k (-Pi.single (δ i) 1)) n, hneg, hδδ]
  have hneg' : ∀ i, (rootSubgroup t.tag k (-Pi.single i 1)).map (MulAut.conj n⁻¹).toMonoidHom =
      rootSubgroup t.tag k (Pi.single (δ i) 1) := fun i => by
    rw [← map_conj_inv_map_conj (rootSubgroup t.tag k (Pi.single (δ i) 1)) n, hpos, hδδ]
  set J' := (fun i => t.orbitIndex (δ i)) '' t.orbitUnion J
  have hJJ' : δ '' t.orbitUnion J = t.orbitUnion J' := image_orbitUnion_eq hcomm J
  have hJ'J : δ '' t.orbitUnion J' = t.orbitUnion J := by
    rw [← hJJ', image_image_of_involutive hδδ]
  have hLn : (graphFixedParabolicLevi t k σ.toRingHom J').map (MulAut.conj n).toMonoidHom ≤
      graphFixedParabolicLevi t k σ.toRingHom J :=
    map_conj_graphFixedParabolicLevi_le hnC (by
      rw [← hJ'J]
      exact map_conj_parabolicLevi_le_of_rootSubgroup (hH w₀) hpos hneg _)
  have hLn' : (graphFixedParabolicLevi t k σ.toRingHom J).map (MulAut.conj n⁻¹).toMonoidHom ≤
      graphFixedParabolicLevi t k σ.toRingHom J' :=
    map_conj_graphFixedParabolicLevi_le (inv_mem hnC) (by
      rw [← hJJ']
      exact map_conj_parabolicLevi_le_of_rootSubgroup (inv_mem (hH w₀)) hpos' hneg' _)
  set Q := graphFixedParabolicRadical t k σ.toRingHom J
  set Q' := (graphFixedParabolicRadical t k σ.toRingHom J').map (MulAut.conj n).toMonoidHom
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hLP, -, -, -, -, -, hfin, hne⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t k σ J
  obtain ⟨-, -, -, -, -, -, -, -, hQP', hQnorm', hLP', -, -, -, -, -, hfin', -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t k σ J'
  have hQp : IsPGroup r Q := hfin r
  have hQ'p : IsPGroup r Q' := (hfin' r).map _
  have hQ1 : Q ≠ ⊥ := hne hJ
  have hQC : Q ≤ C := hQP.trans (graphFixedParabolic_le t k σ.toRingHom J)
  have hQ'C : Q' ≤ C := by
    rintro _ ⟨q, hq, rfl⟩
    exact mul_mem (mul_mem hnC ((hQP'.trans (graphFixedParabolic_le t k σ.toRingHom J')) hq))
      (inv_mem hnC)
  have hPQ : graphFixedParabolic t k σ.toRingHom J ≤
      Subgroup.normalizer (Q : Set (ModGL t.tag k)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm
  have hPQ' : graphFixedParabolic t k σ.toRingHom J' ≤
      Subgroup.normalizer (graphFixedParabolicRadical t k σ.toRingHom J' : Set (ModGL t.tag k)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP').1 hQnorm'
  have hLQ : graphFixedParabolicLevi t k σ.toRingHom J ≤
      Subgroup.normalizer (Q : Set (ModGL t.tag k)) := hLP.trans hPQ
  have hLQ' : graphFixedParabolicLevi t k σ.toRingHom J ≤
      Subgroup.normalizer (Q' : Set (ModGL t.tag k)) := fun m hm => by
    have h := mem_normalizer_map_conj_inv (n := n⁻¹) (m := m)
      (H := graphFixedParabolicRadical t k σ.toRingHom J')
      (hPQ' (hLP' (hLn' (Subgroup.mem_map_of_mem _ hm))))
    rwa [inv_inv] at h
  have hgen : C ≤ Q ⊔ Q' ⊔ graphFixedParabolicLevi t k σ.toRingHom J := by
    refine sup_le ((graphFixedPosUnipotent_le_sup σ J).trans
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)) ?_
    rw [← map_conj_graphFixedPosUnipotent hmax]
    refine (Subgroup.map_mono (graphFixedPosUnipotent_le_sup σ J')).trans ?_
    rw [Subgroup.map_sup]
    exact sup_le (le_sup_right.trans le_sup_left) (hLn.trans le_sup_right)
  have hXC : Q ⊔ Q' ≤ C := sup_le hQC hQ'C
  have hCX : C ≤ Q ⊔ Q' := by
    have hN : C ≤ Subgroup.normalizer ((Q ⊔ Q' : Subgroup (ModGL t.tag k)) : Set (ModGL t.tag k)) :=
      hgen.trans (sup_le Subgroup.le_normalizer fun m hm =>
        mem_normalizer_sup_of_mem (hLQ hm) (hLQ' hm))
    have : ((Q ⊔ Q').subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).2 hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q ⊔ Q').subgroupOf C) with h | h
    · exfalso
      apply hQ1
      have hdis := Subgroup.subgroupOf_eq_bot.1 h
      exact eq_bot_iff.2 fun q hq => (Subgroup.disjoint_def.1 hdis)
        (Subgroup.mem_sup_left hq) (hQC hq) ▸ Subgroup.mem_bot.2 rfl
    · exact Subgroup.subgroupOf_eq_top.1 h
  exact ⟨Q, Q', hQp, hQ'p, hQC, hQ'C, hLQ, hLQ', hCX⟩

end Fixed

theorem fixed_root_invariant_prime_subgroup_hyperplane_generation
    (t : TwistTag) (k : Type)
    [Field k] [Finite k] (r p : ℕ) [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    (σ : k ≃+* k) (hσ : σ ^ t.order = 1) [IsSimpleGroup (graphFixedRootGroup t k σ.toRingHom)]
    (A : Subgroup (ModGL t.tag k)) (hAC : A ≤ graphFixedRootGroup t k σ.toRingHom)
    [IsElementaryAbelian p A] (hA1 : A ≠ ⊥) (R : Subgroup (ModGL t.tag k))
    (hRC : R ≤ graphFixedRootGroup t k σ.toRingHom) (hRr : IsPGroup r R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL t.tag k))) :
    (⨆ (B : Subgroup (ModGL t.tag k)) (_ : B ≤ A) (_ : B.relIndex A = p),
      graphFixedRootGroup t k σ.toRingHom ⊓ Subgroup.centralizer (B : Set (ModGL t.tag k))) =
      graphFixedRootGroup t k σ.toRingHom := by
  have := finite_modGL (τ := t.tag) (K := k)
  refine le_antisymm (iSup₂_le fun B _ => iSup_le fun _ => inf_le_left) ?_
  obtain ⟨M, -, -, -, F, -, -, ⟨g, hg, l, hl, hl1, hgl⟩, hdom, -⟩ :=
    (RootWeightDatum.fixed t σ hσ : RootWeightDatum k).root_p_subgroup_optimal_parabolic_containment
      r R hRC hRr hR
  obtain ⟨hJ, -, hN, hset, -⟩ := hdom g hg l hl hl1 hgl
  obtain ⟨g', rfl⟩ : ∃ g' : ModGL t.tag k, g' = g := ⟨g, rfl⟩
  have hgC : g' ∈ graphFixedRootGroup t k σ.toRingHom := hg
  have hJ' : ((RootWeightDatum.fixed t σ hσ : RootWeightDatum k).face l :
      Set (Fin t.foldedTag.rank)) ≠ Set.univ := hJ
  set J : Set (Fin t.foldedTag.rank) := (RootWeightDatum.fixed t σ hσ : RootWeightDatum k).face l
  change {x : ModGL t.tag k | x ∈ graphFixedRootGroup t k σ.toRingHom ∧
      ∀ c : ℝ, (F c).map (x : Module.End k (RootModule t.tag k)) = F c} =
    ((graphFixedParabolic t k σ.toRingHom J).map (MulAut.conj g').toMonoidHom :
      Set (ModGL t.tag k)) at hset
  have hA1' : A.map (MulAut.conj g'⁻¹).toMonoidHom ≤ graphFixedParabolic t k σ.toRingHom J := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem := (Set.ext_iff.1 hset a).1
      (And.intro (hAC ha) (hN a (Subgroup.mem_inf.2 ⟨hAC ha, hAR ha⟩)))
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hmem
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hmem
  have hindex : ¬ p ∣ ((graphFixedParabolicLevi t k σ.toRingHom J).subgroupOf
      (graphFixedParabolic t k σ.toRingHom J)).index := by
    rw [graphFixedParabolicLevi_index_eq]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfin, -⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors t k σ J
    exact not_dvd_card_of_isPGroup hrp (hfin r)
  have hA1p : IsPGroup p (A.map (MulAut.conj g'⁻¹).toMonoidHom) :=
    (IsElementaryAbelian.isPGroup p A).map _
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_not_dvd_index hA1' hA1p hindex
  have hyC : y ∈ graphFixedRootGroup t k σ.toRingHom := graphFixedParabolic_le t k σ.toRingHom J hy
  have hxC : y * g'⁻¹ ∈ graphFixedRootGroup t k σ.toRingHom := mul_mem hyC (inv_mem hgC)
  have hmap : A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom =
      (A.map (MulAut.conj g'⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map, map_mul]
    rfl
  set A' := A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom
  have hAx : A' ≤ graphFixedParabolicLevi t k σ.toRingHom J := hmap ▸ hyA
  have : IsElementaryAbelian p A' := IsElementaryAbelian.map _
  have : Nontrivial A' := (Subgroup.nontrivial_iff_ne_bot A').2 fun h =>
    hA1 ((Subgroup.map_eq_bot_iff_of_injective A (MulAut.conj (y * g'⁻¹)).injective).1 h)
  obtain ⟨Q, Q', hQp, hQ'p, hQC, hQ'C, hLQ, hLQ', hCX⟩ :=
    exists_radicals_of_graphFixedParabolicLevi (r := r) σ hJ'
  refine le_iSup_hyper_of_map_conj hxC (hCX.trans (sup_le ?_ ?_))
  · exact le_iSup_hyper_of_coprime (not_dvd_card_of_isPGroup hrp hQp) (hAx.trans hLQ) hQC
  · exact le_iSup_hyper_of_coprime (not_dvd_card_of_isPGroup hrp hQ'p) (hAx.trans hLQ') hQ'C

end CFSG.LieType.Chevalley
