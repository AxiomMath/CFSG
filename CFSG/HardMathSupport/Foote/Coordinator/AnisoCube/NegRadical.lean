module

public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.E6ThreeLines

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)


@[expose] def negRadicalRoots (τ : Tag) (J : Set (Fin τ.rank)) : Set (Fin τ.rank → ℤ) :=
  {α | -α ∈ parabolicRadicalRoots τ J}

@[expose] def negRadical (τ : Tag) (K : Type) [Field K]
    (J : Set (Fin τ.rank)) : Subgroup (ModGL τ K) :=
  rootSpan τ K (negRadicalRoots τ J)

section Coordinates

variable {τ : Tag} {w₀ : WeylGroup τ} {δ : Fin τ.rank → Fin τ.rank}

theorem smul_apply_delta (hδinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    (α : Fin τ.rank → ℤ) (i : Fin τ.rank) : (w₀ • α) (δ i) = -α i := by
  have hα : α = ∑ j, α j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hα]
  rw [Finset.smul_sum]
  simp only [smul_comm w₀ (α _) (Pi.single _ 1 : Fin τ.rank → ℤ), hδ, Finset.sum_apply,
    Pi.smul_apply, Pi.neg_apply, Pi.single_apply, hδinj.eq_iff, smul_neg, smul_eq_mul]
  simp

theorem height_smul_longest (hδinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    (α : Fin τ.rank → ℤ) : height (w₀ • α) = -height α := by
  have hb : Function.Bijective δ := Finite.injective_iff_bijective.1 hδinj
  unfold height
  rw [← Fintype.sum_bijective δ hb (fun i => (w₀ • α) (δ i)) (fun j => (w₀ • α) j)
    (fun _ => rfl)]
  simp only [smul_apply_delta hδinj hδ, Finset.sum_neg_distrib]

theorem mem_negRadicalRoots_iff_smul
    (hδinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ} :
    α ∈ negRadicalRoots τ J ↔ w₀ • α ∈ parabolicRadicalRoots τ (δ '' J) := by
  rw [negRadicalRoots, Set.mem_ofPred_eq, mem_parabolicRadicalRoots_iff,
    mem_parabolicRadicalRoots_iff, isRoot_neg_iff, isRoot_smul_iff, height_neg,
    height_smul_longest hδinj hδ]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · rintro ⟨i, hi, hne⟩
    refine ⟨δ i, fun ⟨j, hj, hji⟩ => hi (hδinj hji ▸ hj), ?_⟩
    rw [smul_apply_delta hδinj hδ]
    simpa using hne
  · rintro ⟨j, hj, hne⟩
    obtain ⟨i, rfl⟩ := (Finite.injective_iff_surjective.1 hδinj) j
    refine ⟨i, fun hi => hj ⟨i, hi, rfl⟩, ?_⟩
    rw [smul_apply_delta hδinj hδ] at hne
    simpa using hne

theorem image_negRadicalRoots
    (hδinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin τ.rank)) :
    (fun α => w₀ • α) '' negRadicalRoots τ J = parabolicRadicalRoots τ (δ '' J) := by
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact (mem_negRadicalRoots_iff_smul hδinj hδ).1 hα
  · intro hβ
    refine ⟨w₀⁻¹ • β, ?_, smul_inv_smul _ _⟩
    rw [mem_negRadicalRoots_iff_smul hδinj hδ, smul_inv_smul]
    exact hβ

theorem isRoot_of_mem_negRadicalRoots
    {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ} (hα : α ∈ negRadicalRoots τ J) :
    IsRoot τ α :=
  isRoot_neg_iff.1 (mem_parabolicRadicalRoots_iff.1 hα).1

end Coordinates

section Conjugate

variable {G : Type*} [Group G]

theorem map_conj_map_conj_inv (H : Subgroup G) (n : G) :
    (H.map (MulAut.conj n).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have : (MulAut.conj n⁻¹).toMonoidHom.comp (MulAut.conj n).toMonoidHom = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
    group
  rw [this, Subgroup.map_id]

end Conjugate

section Certified

set_option linter.unusedSectionVars false


variable {τ : Tag} (K : Type) [Field K]

theorem map_conj_negRadical {w₀ : WeylGroup τ} {δ : Fin τ.rank → Fin τ.rank}
    (hδinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin τ.rank)) :
    (negRadical τ K J).map (MulAut.conj (canonicalRep (coxeterSystem τ) K w₀)).toMonoidHom =
      parabolicRadical τ K (δ '' J) := by
  obtain ⟨hS, -, -⟩ := canonical_weyl_root_transport τ K
  rw [negRadical, hS w₀ _ (fun α hα => isRoot_of_mem_negRadicalRoots hα),
    image_negRadicalRoots hδinj hδ]
  rfl

theorem negRadical_eq_map {w₀ : WeylGroup τ} {δ : Fin τ.rank → Fin τ.rank}
    (hδinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin τ.rank)) :
    negRadical τ K J = (parabolicRadical τ K (δ '' J)).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) K w₀)⁻¹).toMonoidHom := by
  rw [← map_conj_negRadical K hδinj hδ J, map_conj_map_conj_inv]

theorem isPGroup_negRadical [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r]
    (J : Set (Fin τ.rank)) : IsPGroup r (negRadical τ K J) := by
  have := finite_modGL (τ := τ) (K := K)
  obtain ⟨w₀, δ, hδinj, hδ⟩ := exists_longest_simple_perm τ
  rw [negRadical_eq_map K hδinj hδ J]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := parabolic_root_radical_Levi_factors τ K (δ '' J)
  exact (hfin r).2.1.map _

theorem parabolicLevi_le_normalizer_negRadical (J : Set (Fin τ.rank)) :
    parabolicLevi τ K J ≤ Subgroup.normalizer (negRadical τ K J : Set (ModGL τ K)) := by
  obtain ⟨w₀, δ, hδinj, hδ⟩ := exists_longest_simple_perm τ
  rw [negRadical_eq_map K hδinj hδ J]
  exact fun m hm =>
    mem_normalizer_map_conj_inv (((parabolicLevi_le_parabolicSubgroup (δ '' J)).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical (δ '' J)))
      (map_conj_parabolicLevi_le hδ J (Subgroup.mem_map_of_mem _ hm)))

theorem adjointGroup_le_parabolicRadical_sup_negRadical [Finite K] {r : ℕ} [Fact r.Prime]
    [CharP K r] [IsSimpleGroup (adjointGroup τ K)] {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) :
    adjointGroup τ K ≤ parabolicRadical τ K J ⊔ negRadical τ K J := by
  have := finite_modGL (τ := τ) (K := K)
  set Q := parabolicRadical τ K J
  set Q' := negRadical τ K J
  set C := adjointGroup τ K
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := parabolic_root_radical_Levi_factors τ K J
  have hQ1 : Q ≠ ⊥ := (hfin r).2.2 hJ
  have hQC : Q ≤ C := rootSpan_le_adjointGroup K _
  have hQ'C : Q' ≤ C := rootSpan_le_adjointGroup K _
  have hMQ : parabolicLevi τ K J ≤ Subgroup.normalizer (Q : Set (ModGL τ K)) :=
    (parabolicLevi_le_parabolicSubgroup J).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical J)
  have hMQ' : parabolicLevi τ K J ≤ Subgroup.normalizer (Q' : Set (ModGL τ K)) :=
    parabolicLevi_le_normalizer_negRadical K J
  have hgen : C ≤ Q ⊔ Q' ⊔ parabolicLevi τ K J := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, hg | hg⟩
    · have hg' : g = xUnit τ K i c := Units.ext (hg.trans (coe_xUnit i c).symm)
      rw [hg']
      by_cases hi : i ∈ J
      · exact Subgroup.mem_sup_right (xUnit_mem_parabolicLevi hi c)
      · refine Subgroup.mem_sup_left (Subgroup.mem_sup_left ?_)
        rw [← pinnedX_single]
        exact pinnedX_mem_rootSpan (mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ i,
          by rw [height_single]; exact one_pos, i, hi, by simp⟩) c
    · have hg' : g = yUnit τ K i c := Units.ext (hg.trans (coe_yUnit i c).symm)
      rw [hg']
      by_cases hi : i ∈ J
      · exact Subgroup.mem_sup_right (yUnit_mem_parabolicLevi hi c)
      · refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)
        rw [← pinnedX_neg_single]
        refine pinnedX_mem_rootSpan ?_ c
        show -(-Pi.single i 1 : Fin τ.rank → ℤ) ∈ parabolicRadicalRoots τ J
        rw [neg_neg]
        exact mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ i,
          by rw [height_single]; exact one_pos, i, hi, by simp⟩
  have hXC : Q ⊔ Q' ≤ C := sup_le hQC hQ'C
  have hN : C ≤ Subgroup.normalizer ((Q ⊔ Q' : Subgroup (ModGL τ K)) : Set (ModGL τ K)) :=
    hgen.trans (sup_le Subgroup.le_normalizer fun m hm =>
      mem_normalizer_sup_of_mem (hMQ hm) (hMQ' hm))
  have : ((Q ⊔ Q').subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).2 hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q ⊔ Q').subgroupOf C) with h | h
  · exfalso
    apply hQ1
    have hdis := Subgroup.subgroupOf_eq_bot.1 h
    exact eq_bot_iff.2 fun q hq => (Subgroup.disjoint_def.1 hdis)
      (Subgroup.mem_sup_left hq) (hQC hq) ▸ Subgroup.mem_bot.2 rfl
  · exact Subgroup.subgroupOf_eq_top.1 h

end Certified

section E6

variable {K : Type} [Field K]

theorem mem_rootSpan_negRadicalRoots_inter_of_mem_centralizer
    {J : Set (Fin TwistTag.E6.tag.rank)} {a : Fin TwistTag.E6.tag.rank → Kˣ}
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ negRadical TwistTag.E6.tag K J)
    (hxa : x ∈ Subgroup.centralizer
      ({rootDiagUnit TwistTag.E6.tag a} : Set (ModGL TwistTag.E6.tag K))) :
    x ∈ rootSpan TwistTag.E6.tag K (rootCharKernel a ∩ negRadicalRoots TwistTag.E6.tag J) := by
  obtain ⟨w₀, δ, hδinj, hδ⟩ := exists_longest_simple_perm TwistTag.E6.tag
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀ with hn
  have hy : n * x * n⁻¹ ∈ parabolicRadical TwistTag.E6.tag K (δ '' J) := by
    rw [← map_conj_negRadical K hδinj hδ J]
    exact Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hx
  have hda := canonicalRep_conj_rootDiagUnit (K := K) w₀ a
  have hya : n * x * n⁻¹ ∈ Subgroup.centralizer
      ({rootDiagUnit TwistTag.E6.tag (weylTuple w₀ a)} : Set (ModGL TwistTag.E6.tag K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    rw [Set.mem_singleton_iff] at hd
    subst hd
    have hdx := Subgroup.mem_centralizer_iff.1 hxa _ (Set.mem_singleton _)
    rw [← hda]
    calc n * rootDiagUnit TwistTag.E6.tag a * n⁻¹ * (n * x * n⁻¹)
        = n * (rootDiagUnit TwistTag.E6.tag a * x) * n⁻¹ := by group
      _ = n * (x * rootDiagUnit TwistTag.E6.tag a) * n⁻¹ := by rw [hdx]
      _ = n * x * n⁻¹ * (n * rootDiagUnit TwistTag.E6.tag a * n⁻¹) := by group
  have hz : n * x * n⁻¹ ∈ rootSpan TwistTag.E6.tag K
      (rootCharKernel (weylTuple w₀ a) ∩ parabolicRadicalRoots TwistTag.E6.tag (δ '' J)) :=
    mem_rootSpan_radical_inter_of_mem_centralizer (a := weylTuple w₀ a) hy hya
  obtain ⟨hS, -, -⟩ := canonical_weyl_root_transport TwistTag.E6.tag K
  have hset : (fun α => w₀ • α) '' (rootCharKernel a ∩ negRadicalRoots TwistTag.E6.tag J) =
      rootCharKernel (weylTuple w₀ a) ∩ parabolicRadicalRoots TwistTag.E6.tag (δ '' J) := by
    ext β
    constructor
    · rintro ⟨α, ⟨⟨hαr, hαk⟩, hαN⟩, rfl⟩
      refine ⟨⟨IsRoot.smul hαr w₀, ?_⟩, (mem_negRadicalRoots_iff_smul hδinj hδ).1 hαN⟩
      rw [rootChar_weylTuple, inv_smul_smul]
      exact hαk
    · rintro ⟨⟨hβr, hβk⟩, hβR⟩
      refine ⟨w₀⁻¹ • β, ⟨⟨(isRoot_smul_iff _).2 hβr, ?_⟩, ?_⟩, smul_inv_smul _ _⟩
      · rw [← rootChar_weylTuple]
        exact hβk
      · rw [mem_negRadicalRoots_iff_smul hδinj hδ, smul_inv_smul]
        exact hβR
  have hmap : (rootSpan TwistTag.E6.tag K
      (rootCharKernel a ∩ negRadicalRoots TwistTag.E6.tag J)).map (MulAut.conj n).toMonoidHom =
      rootSpan TwistTag.E6.tag K
        (rootCharKernel (weylTuple w₀ a) ∩ parabolicRadicalRoots TwistTag.E6.tag (δ '' J)) := by
    rw [hS w₀ _ (fun α hα => hα.1.1), hset]
  rw [← hmap] at hz
  exact (Subgroup.mem_map_iff_mem (MulAut.conj n).injective).1 hz

end E6

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
