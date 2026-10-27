module

public import CFSG.LieType.Chevalley.FixedRootHyperplaneGeneration

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section General

variable {G : Type*} [Group G]

@[expose] def hyperRSet (C A : Subgroup G) (r p : ℕ) : Set G :=
  {x | x ∈ C ∧ (∃ n : ℕ, x ^ r ^ n = 1) ∧
    ∃ B : Subgroup G, B ≤ A ∧ B.relIndex A = p ∧ x ∈ Subgroup.centralizer (B : Set G)}

theorem le_closure_hyperRSet_of_coprime {r p : ℕ} [Fact p.Prime] {A H C : Subgroup G}
    [Finite A] [Finite H] [IsElementaryAbelian p A] [Nontrivial A] (hHr : IsPGroup r H)
    (hp : ¬ p ∣ Nat.card H) (hAH : A ≤ Subgroup.normalizer (H : Set G)) (hHC : H ≤ C) :
    H ≤ Subgroup.closure (hyperRSet C A r p) := by
  let : MulDistribMulAction A H := MulDistribMulAction.compHom H (Subgroup.inclusion hAH)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := A) (H := H) hp
  have hle : (⨆ (B : Subgroup A) (_ : B.index = p), CFSG.fixedPointSubgroup B H) ≤
      (Subgroup.closure (hyperRSet C A r p)).comap H.subtype := by
    refine iSup₂_le fun B hB => fun x hx => ?_
    have hBA : B.map A.subtype ≤ A := Subgroup.map_subtype_le B
    have hBi : (B.map A.subtype).relIndex A = p := by
      have h := Subgroup.relIndex_map_map_of_injective B ⊤ A.subtype_injective
      rw [Subgroup.relIndex_top_right, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
      rw [h, hB]
    obtain ⟨n, hn⟩ := hHr x
    show (x : G) ∈ Subgroup.closure (hyperRSet C A r p)
    refine Subgroup.subset_closure ⟨hHC x.2, ⟨n, ?_⟩, B.map A.subtype, hBA, hBi, ?_⟩
    · have h1 := congrArg Subtype.val hn
      simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using h1
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have hc : (b : G) * x * (b : G)⁻¹ = x := congrArg Subtype.val (hx ⟨b, hb⟩)
      calc (A.subtype b : G) * x = (b : G) * x * (b : G)⁻¹ * b := by
            rw [inv_mul_cancel_right]; rfl
        _ = x * A.subtype b := by rw [hc]; rfl
  intro h hh
  have hmem : (⟨h, hh⟩ : H) ∈
      ⨆ (B : Subgroup A) (_ : B.index = p), CFSG.fixedPointSubgroup B H := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle hmem

theorem le_closure_hyperRSet_of_map_conj {r p : ℕ} {C A : Subgroup G} {x : G} (hx : x ∈ C)
    (h : C ≤ Subgroup.closure (hyperRSet C (A.map (MulAut.conj x).toMonoidHom) r p)) :
    C ≤ Subgroup.closure (hyperRSet C A r p) := by
  set f : G →* G := (MulAut.conj x⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj x⁻¹).injective
  have hAA : (A.map (MulAut.conj x).toMonoidHom).map f = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext y
    simp only [f, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  have hS : f '' hyperRSet C (A.map (MulAut.conj x).toMonoidHom) r p ⊆ hyperRSet C A r p := by
    rintro _ ⟨y, ⟨hyC, ⟨n, hn⟩, B, hB, hBi, hyc⟩, rfl⟩
    refine ⟨?_, ⟨n, ?_⟩, B.map f, hAA ▸ Subgroup.map_mono hB, ?_, ?_⟩
    · change x⁻¹ * y * x⁻¹⁻¹ ∈ C
      exact mul_mem (mul_mem (inv_mem hx) hyC) (by rw [inv_inv]; exact hx)
    · rw [← map_pow, hn, map_one]
    · rw [← hAA, Subgroup.relIndex_map_map_of_injective _ _ hf, hBi]
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hyc b hb]
  have hle : Subgroup.closure (hyperRSet C (A.map (MulAut.conj x).toMonoidHom) r p) ≤
      (Subgroup.closure (hyperRSet C A r p)).comap f := by
    rw [← Subgroup.map_le_iff_le_comap, MonoidHom.map_closure]
    exact Subgroup.closure_mono hS
  intro c hc
  have hmem := hle (h (mul_mem (mul_mem hx hc) (inv_mem hx)))
  rw [Subgroup.mem_comap] at hmem
  have e : f (x * c * x⁻¹) = c := by
    change x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c
    group
  rwa [e] at hmem

end General

theorem ordinary_root_invariant_prime_subgroup_hyperplane_generation_r (τ : Tag) (k : Type)
    [Field k] [Finite k] (r p : ℕ) [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    [IsSimpleGroup (adjointGroup τ k)] (A : Subgroup (ModGL τ k)) (hAC : A ≤ adjointGroup τ k)
    [IsElementaryAbelian p A] (hA1 : A ≠ ⊥) (R : Subgroup (ModGL τ k))
    (hRC : R ≤ adjointGroup τ k) (hRr : IsPGroup r R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL τ k))) :
    adjointGroup τ k ≤ Subgroup.closure (hyperRSet (adjointGroup τ k) A r p) := by
  have := finite_modGL (τ := τ) (K := k)
  obtain ⟨M, -, -, -, F, -, -, ⟨g, hg, l, hl, hl1, hgl⟩, hdom, -⟩ :=
    (RootWeightDatum.ordinary τ : RootWeightDatum k).root_p_subgroup_optimal_parabolic_containment
      r R hRC hRr hR
  obtain ⟨hJ, -, hN, hset, -⟩ := hdom g hg l hl hl1 hgl
  obtain ⟨g', rfl⟩ : ∃ g' : ModGL τ k, g' = g := ⟨g, rfl⟩
  have hgC : g' ∈ adjointGroup τ k := hg
  have hJ' : ((RootWeightDatum.ordinary τ : RootWeightDatum k).face l : Set (Fin τ.rank)) ≠
      Set.univ := hJ
  set J : Set (Fin τ.rank) := (RootWeightDatum.ordinary τ : RootWeightDatum k).face l
  change {x : ModGL τ k | x ∈ adjointGroup τ k ∧
      ∀ c : ℝ, (F c).map (x : Module.End k (RootModule τ k)) = F c} =
    ((parabolicSubgroup τ k J).map (MulAut.conj g').toMonoidHom : Set (ModGL τ k)) at hset
  have hA1' : A.map (MulAut.conj g'⁻¹).toMonoidHom ≤ parabolicSubgroup τ k J := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem := (Set.ext_iff.1 hset a).1
      (And.intro (hAC ha) (hN a (Subgroup.mem_inf.2 ⟨hAC ha, hAR ha⟩)))
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hmem
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hmem
  have hindex : ¬ p ∣ ((parabolicLevi τ k J).subgroupOf (parabolicSubgroup τ k J)).index := by
    rw [parabolicLevi_index_eq]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := parabolic_root_radical_Levi_factors τ k J
    exact not_dvd_card_of_isPGroup hrp (hfin r).2.1
  have hA1p : IsPGroup p (A.map (MulAut.conj g'⁻¹).toMonoidHom) :=
    (IsElementaryAbelian.isPGroup p A).map _
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_not_dvd_index hA1' hA1p hindex
  have hyC : y ∈ adjointGroup τ k := parabolicSubgroup_le_adjointGroup τ k J hy
  have hxC : y * g'⁻¹ ∈ adjointGroup τ k := mul_mem hyC (inv_mem hgC)
  have hmap : A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom =
      (A.map (MulAut.conj g'⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map, map_mul]
    rfl
  set A' := A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom
  have hAx : A' ≤ parabolicLevi τ k J := hmap ▸ hyA
  have : IsElementaryAbelian p A' := IsElementaryAbelian.map _
  have : Nontrivial A' := (Subgroup.nontrivial_iff_ne_bot A').2 fun h =>
    hA1 ((Subgroup.map_eq_bot_iff_of_injective A (MulAut.conj (y * g'⁻¹)).injective).1 h)
  obtain ⟨Q, Q', hQp, hQ'p, hQC, hQ'C, hMQ, hMQ', hCX⟩ :=
    exists_radicals_of_parabolicLevi (k := k) (r := r) hJ'
  refine le_closure_hyperRSet_of_map_conj hxC (hCX.trans (sup_le ?_ ?_))
  · exact le_closure_hyperRSet_of_coprime hQp (not_dvd_card_of_isPGroup hrp hQp)
      (hAx.trans hMQ) hQC
  · exact le_closure_hyperRSet_of_coprime hQ'p (not_dvd_card_of_isPGroup hrp hQ'p)
      (hAx.trans hMQ') hQ'C

theorem fixed_root_invariant_prime_subgroup_hyperplane_generation_r (t : TwistTag) (k : Type)
    [Field k] [Finite k] (r p : ℕ) [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    (σ : k ≃+* k) (hσ : σ ^ t.order = 1) [IsSimpleGroup (graphFixedRootGroup t k σ.toRingHom)]
    (A : Subgroup (ModGL t.tag k)) (hAC : A ≤ graphFixedRootGroup t k σ.toRingHom)
    [IsElementaryAbelian p A] (hA1 : A ≠ ⊥) (R : Subgroup (ModGL t.tag k))
    (hRC : R ≤ graphFixedRootGroup t k σ.toRingHom) (hRr : IsPGroup r R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL t.tag k))) :
    graphFixedRootGroup t k σ.toRingHom ≤
      Subgroup.closure (hyperRSet (graphFixedRootGroup t k σ.toRingHom) A r p) := by
  have := finite_modGL (τ := t.tag) (K := k)
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
  refine le_closure_hyperRSet_of_map_conj hxC (hCX.trans (sup_le ?_ ?_))
  · exact le_closure_hyperRSet_of_coprime hQp (not_dvd_card_of_isPGroup hrp hQp)
      (hAx.trans hLQ) hQC
  · exact le_closure_hyperRSet_of_coprime hQ'p (not_dvd_card_of_isPGroup hrp hQ'p)
      (hAx.trans hLQ') hQ'C

end CFSG.LieType.Chevalley
