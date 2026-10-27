module

public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem map_conj_parabolicLevi_le_of_rootSubgroup
    {τ : Tag} {k : Type} [Field k]
    {u : ModGL τ k} {δ : Fin τ.rank → Fin τ.rank}
    (hH : u ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hpos : ∀ i, (rootSubgroup τ k (Pi.single i 1)).map (MulAut.conj u).toMonoidHom =
      rootSubgroup τ k (-Pi.single (δ i) 1))
    (hneg : ∀ i, (rootSubgroup τ k (-Pi.single i 1)).map (MulAut.conj u).toMonoidHom =
      rootSubgroup τ k (Pi.single (δ i) 1))
    (X : Set (Fin τ.rank)) :
    (parabolicLevi τ k X).map (MulAut.conj u).toMonoidHom ≤ parabolicLevi τ k (δ '' X) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (fun h hh => ?_) ((Subgroup.closure_le _).2 ?_)
  · exact torusGroup_le_parabolicLevi _ ((Subgroup.mem_normalizer_iff.1 hH h).1 hh)
  · rintro _ ⟨j, hj, c, rfl | rfl⟩
    · have hx : xUnit τ k j c ∈ rootSubgroup τ k (Pi.single j 1) :=
        CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨c, pinnedX_single τ k j c⟩
      have hmem : (MulAut.conj u).toMonoidHom (xUnit τ k j c) ∈
          (rootSubgroup τ k (Pi.single j 1)).map (MulAut.conj u).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hpos] at hmem
      exact rootSubgroup_neg_single_le_parabolicLevi (Set.mem_image_of_mem δ hj) hmem
    · have hy : yUnit τ k j c ∈ rootSubgroup τ k (-Pi.single j 1) :=
        CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨c, pinnedX_neg_single τ k j c⟩
      have hmem : (MulAut.conj u).toMonoidHom (yUnit τ k j c) ∈
          (rootSubgroup τ k (-Pi.single j 1)).map (MulAut.conj u).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy
      rw [hneg] at hmem
      exact rootSubgroup_single_le_parabolicLevi (Set.mem_image_of_mem δ hj) hmem

theorem map_conj_inv_map_conj {G : Type*} [Group G] (H : Subgroup G) (n : G) :
    (H.map (MulAut.conj n).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom = H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have e : n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y := by group
    rwa [e]
  · intro hx
    refine ⟨n * x * n⁻¹, ⟨x, hx, rfl⟩, ?_⟩
    group

theorem exists_longest_fixed_data
    (t : TwistTag) :
    ∃ (w₀ : WeylGroup t.tag) (δ : Fin t.tag.rank → Fin t.tag.rank),
      (∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀) ∧
      (∀ i, δ (δ i) = i) ∧
      (∀ i, w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single (δ i) 1) ∧
      ∀ i, δ (t.perm i) = t.perm (δ i) := by
  obtain ⟨w₀, hmax, -, -, hsq, -, -⟩ := weyl_longest_element t.tag
  have hsq' : w₀ * w₀ = 1 := by rw [← pow_two]; exact hsq
  choose δ hδ using exists_smul_single_eq_neg (reversesSigns_of_forall_length_le hmax) hsq'
  refine ⟨w₀, δ, hmax, fun i => ?_, hδ, fun i => ?_⟩
  · have h1 : w₀ • (w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) = Pi.single i 1 := by
      rw [smul_smul, hsq', one_smul]
    rw [hδ i, smul_neg, hδ (δ i), neg_neg] at h1
    exact single_injective_one h1
  · have h := (mem_relWeylTwist_iff_smul t).1 (mem_relWeylTwist_of_forall_length_le hmax)
      (Pi.single i 1)
    rw [permLattice_single, hδ, hδ, permLattice_neg, permLattice_single] at h
    exact single_injective_one (neg_injective h)

theorem apply_perm_pow_of_comm {t : TwistTag} {δ : Fin t.tag.rank → Fin t.tag.rank}
    (hcomm : ∀ i, δ (t.perm i) = t.perm (δ i)) (m : ℕ) (i : Fin t.tag.rank) :
    δ ((t.perm ^ m) i) = (t.perm ^ m) (δ i) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hcomm, ih]

theorem perm_pow_mem_orbitUnion {t : TwistTag} {J : Set (Fin t.foldedTag.rank)}
    {i : Fin t.tag.rank} (hi : i ∈ t.orbitUnion J) (m : ℕ) : (t.perm ^ m) i ∈ t.orbitUnion J := by
  induction m with
  | zero => exact hi
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact perm_mem_orbitUnion ih

theorem image_orbitUnion_eq {t : TwistTag} {δ : Fin t.tag.rank → Fin t.tag.rank}
    (hcomm : ∀ i, δ (t.perm i) = t.perm (δ i)) (J : Set (Fin t.foldedTag.rank)) :
    δ '' t.orbitUnion J = t.orbitUnion ((fun i => t.orbitIndex (δ i)) '' t.orbitUnion J) := by
  ext j
  rw [mem_orbitUnion_iff_orbitIndex]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, hij⟩
    have hij' : t.orbitIndex (δ i) = t.orbitIndex j := hij
    have hj : j ∈ t.orbit (t.orbitIndex (δ i)) := by
      rw [hij']
      exact t.mem_orbit_orbitIndex j
    rw [t.orbit_orbitIndex, Finset.mem_image] at hj
    obtain ⟨m, -, hm⟩ := hj
    exact ⟨(t.perm ^ m) i, perm_pow_mem_orbitUnion hi m, by rw [apply_perm_pow_of_comm hcomm, hm]⟩

theorem image_image_of_involutive {α : Type*} {δ : α → α} (hδ : ∀ i, δ (δ i) = i) (X : Set α) :
    δ '' (δ '' X) = X := by
  rw [Set.image_image]
  simp only [hδ, Set.image_id']

section Fixed

variable {t : TwistTag} {k : Type} [Field k]

theorem map_conj_graphFixedParabolicLevi_le
    {σ : k →+* k} {u : ModGL t.tag k}
    (huC : u ∈ graphFixedRootGroup t k σ) {J J' : Set (Fin t.foldedTag.rank)}
    (hM : (parabolicLevi t.tag k (t.orbitUnion J)).map (MulAut.conj u).toMonoidHom ≤
      parabolicLevi t.tag k (t.orbitUnion J')) :
    (graphFixedParabolicLevi t k σ J).map (MulAut.conj u).toMonoidHom ≤
      graphFixedParabolicLevi t k σ J' := by
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨hmM, hmC⟩ := Subgroup.mem_inf.1 hm
  exact Subgroup.mem_inf.2 ⟨hM (Subgroup.mem_map_of_mem _ hmM),
    mul_mem (mul_mem huC hmC) (inv_mem huC)⟩

theorem card_graphFixedParabolic_eq_mul
    (σ : k ≃+* k) (J : Set (Fin t.foldedTag.rank)) :
    Nat.card (graphFixedParabolic t k σ.toRingHom J) =
      Nat.card (graphFixedParabolicRadical t k σ.toRingHom J) *
        Nat.card (graphFixedParabolicLevi t k σ.toRingHom J) := by
  obtain ⟨-, -, -, -, -, -, -, -, hQP, -, hLP, huniq, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t k σ J
  let f : graphFixedParabolicRadical t k σ.toRingHom J ×
      graphFixedParabolicLevi t k σ.toRingHom J → graphFixedParabolic t k σ.toRingHom J :=
    fun qm => ⟨qm.1 * qm.2, mul_mem (hQP qm.1.2) (hLP qm.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun g => ?_⟩
    · have h := congrArg Subtype.val hxy
      obtain ⟨⟨q, m⟩, -, hu⟩ := huniq (x.1 * x.2) (mul_mem (hQP x.1.2) (hLP x.2.2))
      have h1 := hu (x.1, x.2) ⟨x.1.2, x.2.2, rfl⟩
      have h2 := hu (y.1, y.2) ⟨y.1.2, y.2.2, h⟩
      have h3 := h1.trans h2.symm
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h3)) (Subtype.ext (congrArg Prod.snd h3))
    · obtain ⟨⟨q, m⟩, ⟨hq, hm, hg⟩, -⟩ := huniq g g.2
      exact ⟨(⟨q, hq⟩, ⟨m, hm⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem graphFixedParabolicLevi_index_eq
    [Finite k] (σ : k ≃+* k)
    (J : Set (Fin t.foldedTag.rank)) :
    ((graphFixedParabolicLevi t k σ.toRingHom J).subgroupOf
      (graphFixedParabolic t k σ.toRingHom J)).index =
        Nat.card (graphFixedParabolicRadical t k σ.toRingHom J) := by
  have := finite_modGL (τ := t.tag) (K := k)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hLP, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t k σ J
  have h := ((graphFixedParabolicLevi t k σ.toRingHom J).subgroupOf
    (graphFixedParabolic t k σ.toRingHom J)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLP).toEquiv,
    card_graphFixedParabolic_eq_mul, mul_comm (Nat.card (graphFixedParabolicRadical _ _ _ _))]
    at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

theorem graphFixedPosUnipotent_le_sup
    (σ : k ≃+* k) (J : Set (Fin t.foldedTag.rank)) :
    graphFixedPosUnipotent t k σ.toRingHom ≤
      graphFixedParabolicRadical t k σ.toRingHom J ⊔ graphFixedParabolicLevi t k σ.toRingHom J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hB, -, hHV, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t k σ J
  intro u hu
  have hu' : u ∈ (graphFixedRootBorel t k σ.toRingHom : Set (ModGL t.tag k)) :=
    graphFixedPosUnipotent_le_graphFixedRootBorel hu
  rw [hB] at hu'
  obtain ⟨q, hq, x, hx, rfl⟩ := hu'
  exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right (hHV hx))

theorem le_iSup_centralizer_of_le_graphFixedParabolicLevi
    [Finite k] {r p : ℕ} [Fact r.Prime]
    [Fact p.Prime] [CharP k r] (hrp : r ≠ p) (σ : k ≃+* k)
    [IsSimpleGroup (graphFixedRootGroup t k σ.toRingHom)] {J : Set (Fin t.foldedTag.rank)}
    (hJ : J ≠ Set.univ) {A : Subgroup (ModGL t.tag k)} [IsElementaryAbelian p A]
    (hcard : p ^ 2 ≤ Nat.card A) (hAL : A ≤ graphFixedParabolicLevi t k σ.toRingHom J) :
    graphFixedRootGroup t k σ.toRingHom ≤
      ⨆ a ∈ A, ⨆ (_ : a ≠ 1), graphFixedRootGroup t k σ.toRingHom ⊓
        Subgroup.centralizer ({a} : Set (ModGL t.tag k)) := by
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
  have h1 := le_iSup_inf_centralizer_of_coprime hcard (not_dvd_card_of_isPGroup hrp hQp)
    (hAL.trans hLQ) hQC
  have h2 := le_iSup_inf_centralizer_of_coprime hcard (not_dvd_card_of_isPGroup hrp hQ'p)
    (hAL.trans hLQ') hQ'C
  exact hCX.trans (sup_le h1 h2)

end Fixed

theorem fixed_root_invariant_prime_subgroup_centralizer_generation
    (t : TwistTag) (k : Type)
    [Field k] [Finite k] (r p : ℕ) [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    (σ : k ≃+* k) (hσ : σ ^ t.order = 1) [IsSimpleGroup (graphFixedRootGroup t k σ.toRingHom)]
    (A : Subgroup (ModGL t.tag k)) (hAC : A ≤ graphFixedRootGroup t k σ.toRingHom)
    [IsElementaryAbelian p A] (hcard : p ^ 2 ≤ Nat.card A) (R : Subgroup (ModGL t.tag k))
    (hRC : R ≤ graphFixedRootGroup t k σ.toRingHom) (hRr : IsPGroup r R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL t.tag k))) :
    (⨆ a ∈ A, ⨆ (_ : a ≠ 1), graphFixedRootGroup t k σ.toRingHom ⊓
      Subgroup.centralizer ({a} : Set (ModGL t.tag k))) = graphFixedRootGroup t k σ.toRingHom := by
  have := finite_modGL (τ := t.tag) (K := k)
  refine le_antisymm (iSup₂_le fun a _ => iSup_le fun _ => inf_le_left) ?_
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
  have hA1 : A.map (MulAut.conj g'⁻¹).toMonoidHom ≤ graphFixedParabolic t k σ.toRingHom J := by
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
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_not_dvd_index hA1 hA1p hindex
  have hyC : y ∈ graphFixedRootGroup t k σ.toRingHom := graphFixedParabolic_le t k σ.toRingHom J hy
  have hxC : y * g'⁻¹ ∈ graphFixedRootGroup t k σ.toRingHom := mul_mem hyC (inv_mem hgC)
  have hmap : A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom =
      (A.map (MulAut.conj g'⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map, map_mul]
    rfl
  have hAx : A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom ≤
      graphFixedParabolicLevi t k σ.toRingHom J := hmap ▸ hyA
  have : IsElementaryAbelian p (A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hcard' : p ^ 2 ≤ Nat.card (A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (y * g'⁻¹)).injective]
    exact hcard
  exact le_iSup_inf_centralizer_of_map_conj hxC
    (le_iSup_centralizer_of_le_graphFixedParabolicLevi hrp σ hJ' hcard' hAx)

end CFSG.LieType.Chevalley
