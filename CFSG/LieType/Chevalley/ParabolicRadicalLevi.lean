module

public import CFSG.LieType.Chevalley.ParabolicGradedAction
public import CFSG.LieType.Chevalley.RankOneCentralImage
public import CFSG.LieType.Chevalley.GraphFixedSimpleComplement
public import CFSG.LieType.Chevalley.ParabolicWeylStabilizer
public import CFSG.LieType.Chevalley.RootCharacterConjugation

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem mem_normalizer_of_map_eq {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h' := congrArg SetLike.coe h
  rw [Subgroup.coe_map] at h'
  exact h'

theorem torusGroup_le_normalizer_rootSpan
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) :
    torusGroup τ K ≤ Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact mem_normalizer_of_map_eq (map_rootSpan_of_forall fun α hα =>
    map_conj_torusElt_rootSubgroup i t (hS α hα))

theorem posUnipotent_le_normalizer_of_absorbs
    {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (habs : ∀ α, IsRoot τ α ∧ 0 < height α → ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • α + b • β) → a • α + b • β ∈ S) :
    posUnipotent τ K ≤ Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) := by
  obtain ⟨hle, hnorm⟩ := positive_root_ideal_normality τ K (J := S)
    (S := {α | IsRoot τ α ∧ 0 < height α}) (fun α hα => hS α hα) (fun α hα => hα)
    (fun α hα β hβ a b ha hb hr => habs α hα β hβ a b ha hb hr)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hnorm

theorem borelGroup_le_normalizer_parabolicRadical
    (J : Set (Fin τ.rank)) :
    borelGroup τ K ≤ Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) :=
  sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1.1)
    (posUnipotent_le_normalizer_of_absorbs (fun _ hα => hα.1)
      fun _ hα _ hβ _ _ ha hb hr => add_mem_parabolicRadicalRoots hα hβ ha hb hr)

theorem borelGroup_le_normalizer_parabolicRadicalGe
    (J : Set (Fin τ.rank)) (h : ℤ) :
    borelGroup τ K ≤ Subgroup.normalizer (parabolicRadicalGe τ K J h : Set (ModGL τ K)) :=
  sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1.1.1)
    (posUnipotent_le_normalizer_of_absorbs (fun _ hα => hα.1.1)
      fun _ hα _ hβ _ _ ha hb hr => add_mem_parabolicRadicalRootsGe hα hβ ha hb hr)

theorem weylElt_mem_normalizer_parabolicRadical
    {J : Set (Fin τ.rank)} {j : Fin τ.rank}
    (hj : j ∈ J) :
    weylElt τ K j 1 ∈ Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) := by
  refine mem_normalizer_of_map_eq ?_
  rw [parabolicRadical, map_conj_weylElt_rootSpan K j 1 fun _ hα => hα.1.1,
    image_reflect_parabolicRadicalRoots hj]

theorem parabolicSubgroup_le_normalizer_parabolicRadical
    (J : Set (Fin τ.rank)) :
    parabolicSubgroup τ K J ≤
      Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) :=
  sup_le (borelGroup_le_normalizer_parabolicRadical J) ((Subgroup.closure_le _).2
    fun _ ⟨_, hj, he⟩ => he ▸ weylElt_mem_normalizer_parabolicRadical hj)

theorem parabolicRadical_le_posUnipotent
    (J : Set (Fin τ.rank)) :
    parabolicRadical τ K J ≤ posUnipotent τ K :=
  rootSpan_le_posUnipotent fun _ hα => hα.1

theorem parabolicLeviUnipotent_le_posUnipotent
    (J : Set (Fin τ.rank)) :
    parabolicLeviUnipotent τ K J ≤ posUnipotent τ K :=
  rootSpan_le_posUnipotent fun _ hα => hα.2

theorem posUnipotent_le_parabolicSubgroup
    (J : Set (Fin τ.rank)) :
    posUnipotent τ K ≤ parabolicSubgroup τ K J :=
  le_trans le_sup_right (borelGroup_le_parabolicSubgroup J)

theorem torusGroup_le_parabolicLevi
    (J : Set (Fin τ.rank)) :
    torusGroup τ K ≤ parabolicLevi τ K J :=
  le_sup_left

theorem xUnit_mem_parabolicLevi
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J) (c : K) :
    xUnit τ K j c ∈ parabolicLevi τ K J :=
  Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, c, Or.inl rfl⟩)

theorem yUnit_mem_parabolicLevi
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J) (c : K) :
    yUnit τ K j c ∈ parabolicLevi τ K J :=
  Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, c, Or.inr rfl⟩)

theorem weylElt_mem_parabolicLevi
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J) :
    weylElt τ K j 1 ∈ parabolicLevi τ K J := by
  rw [weylElt_eq_yUnit_mul]
  exact mul_mem (mul_mem (yUnit_mem_parabolicLevi hj _) (xUnit_mem_parabolicLevi hj _))
    (yUnit_mem_parabolicLevi hj _)

theorem canonicalRep_mem_parabolicLevi
    {J : Set (Fin τ.rank)} {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ J) :
    canonicalRep (coxeterSystem τ) K w ∈ parabolicLevi τ K J := by
  obtain ⟨ω, hω, rfl, hletters⟩ := (parabolic_Weyl_coordinate_stabilizer τ J).2.1 w hw
  rw [canonicalRep_wordProd hω]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact weylElt_mem_parabolicLevi (hletters i hi)

theorem parabolicLeviUnipotent_le_parabolicLevi
    (J : Set (Fin τ.rank)) :
    parabolicLeviUnipotent τ K J ≤ parabolicLevi τ K J := by
  refine iSup₂_le fun α hα => ?_
  obtain ⟨w, hw, j, hj, rfl⟩ := exists_mem_parabolicWeylGroup_smul _ α rfl hα
  rw [← (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_single τ j)]
  rintro _ ⟨u, hu, rfl⟩
  have huM : u ∈ parabolicLevi τ K J := by
    refine (Subgroup.closure_le _).2 ?_ hu
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_single]
    exact xUnit_mem_parabolicLevi hj c
  have hn := canonicalRep_mem_parabolicLevi (K := K) hw
  exact mul_mem (mul_mem hn huM) (inv_mem hn)

theorem parabolicLevi_le_parabolicSubgroup
    (J : Set (Fin τ.rank)) :
    parabolicLevi τ K J ≤ parabolicSubgroup τ K J := by
  refine sup_le (torusGroup_le_parabolicSubgroup J) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · exact borelGroup_le_parabolicSubgroup J (xUnit_mem_borelGroup j c)
  · rw [yUnit_eq_conj]
    have hn := weylElt_mem_parabolicSubgroup (K := K) hj
    exact mul_mem (mul_mem hn (borelGroup_le_parabolicSubgroup J (xUnit_mem_borelGroup j _)))
      (inv_mem hn)

theorem posUnipotent_eq_mul_parabolic
    (J : Set (Fin τ.rank)) :
    (posUnipotent τ K : Set (ModGL τ K)) =
      (parabolicRadical τ K J : Set (ModGL τ K)) * (parabolicLeviUnipotent τ K J : Set _) := by
  refine Set.Subset.antisymm (fun u hu => ?_) ?_
  · have hu' : u ∈ rootSpan τ K (parabolicRadicalRoots τ J ∪ parabolicPosRoots τ J) := by
      rw [parabolicRadicalRoots_union]
      exact hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_mul_rootSpan_eq K (fun _ hα => hα.1)
      (fun α hα => hα.2) (disjoint_parabolicRadicalRoots_parabolicPosRoots J)
      (fun α hα β hβ a b ha hb hr => by
        rw [parabolicRadicalRoots_union] at hα hβ ⊢
        exact ⟨hr, by
          rw [height_nsmul_add_nsmul]
          have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
          have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
          nlinarith [hα.2, hβ.2]⟩) hu'
    exact ⟨u₁, hu₁, u₂, hu₂, rfl⟩
  · rintro _ ⟨q, hq, v, hv, rfl⟩
    exact mul_mem (parabolicRadical_le_posUnipotent J hq)
      (parabolicLeviUnipotent_le_posUnipotent J hv)

theorem borelGroup_eq_mul_parabolic
    (J : Set (Fin τ.rank)) :
    (borelGroup τ K : Set (ModGL τ K)) = (parabolicRadical τ K J : Set (ModGL τ K)) *
      ((torusGroup τ K : Set (ModGL τ K)) * (parabolicLeviUnipotent τ K J : Set _)) := by
  have hHU := (triangular_borel_structure.{0, 0} τ K).2.2.2.2.1
  refine Set.Subset.antisymm (fun b hb => ?_) ?_
  · rw [hHU] at hb
    obtain ⟨h, hh, u, hu, rfl⟩ := hb
    rw [SetLike.mem_coe, ← SetLike.mem_coe, posUnipotent_eq_mul_parabolic J] at hu
    obtain ⟨q, hq, v, hv, rfl⟩ := hu
    have hq' : h * q * h⁻¹ ∈ parabolicRadical τ K J :=
      (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSpan
        (fun _ hα => hα.1.1) hh) q).1 hq
    exact ⟨h * q * h⁻¹, hq', h * v, ⟨h, hh, v, hv, rfl⟩, by group⟩
  · rintro _ ⟨q, hq, _, ⟨h, hh, v, hv, rfl⟩, rfl⟩
    exact mul_mem (le_trans (parabolicRadical_le_posUnipotent J) le_sup_right hq)
      (mul_mem (le_sup_left (b := posUnipotent τ K) hh)
        (le_trans (parabolicLeviUnipotent_le_posUnipotent J) le_sup_right hv))

theorem parabolicRadical_sup_parabolicLevi
    (J : Set (Fin τ.rank)) :
    parabolicRadical τ K J ⊔ parabolicLevi τ K J = parabolicSubgroup τ K J := by
  refine le_antisymm (sup_le (le_trans (parabolicRadical_le_posUnipotent J)
    (posUnipotent_le_parabolicSubgroup J)) (parabolicLevi_le_parabolicSubgroup J)) ?_
  refine sup_le (fun b hb => ?_) ((Subgroup.closure_le _).2 ?_)
  · have hb' : b ∈ (parabolicRadical τ K J : Set (ModGL τ K)) *
        ((torusGroup τ K : Set (ModGL τ K)) * (parabolicLeviUnipotent τ K J : Set _)) := by
      rw [← borelGroup_eq_mul_parabolic]
      exact hb
    obtain ⟨q, hq, _, ⟨h, hh, v, hv, rfl⟩, rfl⟩ := hb'
    exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right
      (mul_mem (torusGroup_le_parabolicLevi J hh) (parabolicLeviUnipotent_le_parabolicLevi J hv)))
  · rintro _ ⟨j, hj, rfl⟩
    exact Subgroup.mem_sup_right (weylElt_mem_parabolicLevi hj)

theorem eq_of_mul_eq_of_parabolic
    {J : Set (Fin τ.rank)} {q q' m m' : ModGL τ K}
    (hq : q ∈ parabolicRadical τ K J) (hq' : q' ∈ parabolicRadical τ K J)
    (hm : m ∈ parabolicLevi τ K J) (hm' : m' ∈ parabolicLevi τ K J) (h : q * m = q' * m') :
    q = q' ∧ m = m' := by
  have hmem : q'⁻¹ * q ∈ parabolicRadical τ K J ⊓ parabolicLevi τ K J := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hq') hq, ?_⟩
    have : q'⁻¹ * q = m' * m⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hm' (inv_mem hm)
  rw [parabolicRadical_inf_parabolicLevi, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  subst hmem
  exact ⟨rfl, mul_left_cancel h⟩

theorem card_parabolicRadical
    [Finite K] (J : Set (Fin τ.rank)) :
    Nat.card (parabolicRadical τ K J) = Nat.card K ^ (parabolicRadicalRoots τ J).ncard :=
  card_rootSpan (fun _ hα => hα.1) fun _ hα _ hβ _ _ ha hb hr =>
    add_mem_parabolicRadicalRoots hα.1 hβ ha hb hr

theorem parabolicRadical_ne_bot
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) :
    parabolicRadical τ K J ≠ ⊥ := by
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  have hα : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ parabolicRadicalRoots τ J :=
    mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ i, by rw [height_single]; exact one_pos,
      i, hi, by simp⟩
  intro hbot
  have hx : pinnedX τ K (Pi.single i 1) 1 ∈ parabolicRadical τ K J :=
    pinnedX_mem_rootSpan hα 1
  rw [hbot, Subgroup.mem_bot] at hx
  exact one_ne_zero (pinnedX_injective τ K _ (hx.trans (pinnedX_zero τ K _).symm))

variable (τ K) in
theorem parabolic_root_radical_Levi_factors
    (J : Set (Fin τ.rank)) :
    parabolicRadical τ K J ≤ parabolicSubgroup τ K J ∧
    ((parabolicRadical τ K J).subgroupOf (parabolicSubgroup τ K J)).Normal ∧
    (∀ h : ℤ, borelGroup τ K ≤
      Subgroup.normalizer (parabolicRadicalGe τ K J h : Set (ModGL τ K))) ∧
    parabolicLevi τ K J ≤ parabolicSubgroup τ K J ∧
    parabolicRadical τ K J ⊓ parabolicLevi τ K J = ⊥ ∧
    parabolicRadical τ K J ⊔ parabolicLevi τ K J = parabolicSubgroup τ K J ∧
    (∀ g ∈ parabolicSubgroup τ K J, ∃! qm : ModGL τ K × ModGL τ K,
      qm.1 ∈ parabolicRadical τ K J ∧ qm.2 ∈ parabolicLevi τ K J ∧ g = qm.1 * qm.2) ∧
    (borelGroup τ K : Set (ModGL τ K)) = (parabolicRadical τ K J : Set (ModGL τ K)) *
      ((torusGroup τ K : Set (ModGL τ K)) * (parabolicLeviUnipotent τ K J : Set _)) ∧
    (∀ q ∈ parabolicRadical τ K J, ∀ q' ∈ parabolicRadical τ K J,
      ∀ t ∈ (torusGroup τ K : Set (ModGL τ K)) * (parabolicLeviUnipotent τ K J : Set _),
      ∀ t' ∈ (torusGroup τ K : Set (ModGL τ K)) * (parabolicLeviUnipotent τ K J : Set _),
        q * t = q' * t' → q = q' ∧ t = t') ∧
    parabolicLeviUnipotent τ K J ≤ parabolicLevi τ K J ∧
    (∀ g ∈ parabolicLevi τ K J, ∀ (d : ℤ) (x : RootModule τ K),
      x ∈ parabolicGraded τ K J d →
        (g : Module.End K (RootModule τ K)) x ∈ parabolicGraded τ K J d) ∧
    (∀ g ∈ parabolicRadical τ K J, ∀ (d : ℤ) (x : RootModule τ K),
      x ∈ parabolicFiltration τ K J d →
        (g : Module.End K (RootModule τ K)) x ∈ parabolicFiltration τ K J d ∧
          (g : Module.End K (RootModule τ K)) x - x ∈ parabolicFiltration τ K J (d + 1)) ∧
    ∀ [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p],
      Nat.card (parabolicRadical τ K J) = Nat.card K ^ (parabolicRadicalRoots τ J).ncard ∧
      IsPGroup p (parabolicRadical τ K J) ∧
      (J ≠ Set.univ → parabolicRadical τ K J ≠ ⊥) := by
  have hQP : parabolicRadical τ K J ≤ parabolicSubgroup τ K J :=
    le_trans (parabolicRadical_le_posUnipotent J) (posUnipotent_le_parabolicSubgroup J)
  have hMN : parabolicLevi τ K J ≤
      Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) :=
    le_trans (parabolicLevi_le_parabolicSubgroup J)
      (parabolicSubgroup_le_normalizer_parabolicRadical J)
  have hprod : (parabolicSubgroup τ K J : Set (ModGL τ K)) =
      (parabolicRadical τ K J : Set (ModGL τ K)) * (parabolicLevi τ K J : Set _) := by
    rw [← parabolicRadical_sup_parabolicLevi J,
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hMN]
  have hHV : (torusGroup τ K : Set (ModGL τ K)) * (parabolicLeviUnipotent τ K J : Set _) ⊆
      (parabolicLevi τ K J : Set (ModGL τ K)) := by
    rintro _ ⟨h, hh, v, hv, rfl⟩
    exact mul_mem (torusGroup_le_parabolicLevi J hh) (parabolicLeviUnipotent_le_parabolicLevi J hv)
  refine ⟨hQP, (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).2
      (parabolicSubgroup_le_normalizer_parabolicRadical J),
    borelGroup_le_normalizer_parabolicRadicalGe J, parabolicLevi_le_parabolicSubgroup J,
    parabolicRadical_inf_parabolicLevi J, parabolicRadical_sup_parabolicLevi J,
    fun g hg => ?_, borelGroup_eq_mul_parabolic J,
    fun q hq q' hq' t ht t' ht' h => eq_of_mul_eq_of_parabolic hq hq' (hHV ht) (hHV ht') h,
    parabolicLeviUnipotent_le_parabolicLevi J,
    fun g hg d x hx => parabolicLevi_preserves hg d hx,
    fun g hg d x hx => parabolicRadical_unipotent hg d hx, fun p _ _ => ?_⟩
  · have hg' : g ∈ (parabolicRadical τ K J : Set (ModGL τ K)) * (parabolicLevi τ K J : Set _) := by
      rw [← hprod]
      exact hg
    obtain ⟨q, hq, m, hm, rfl⟩ := hg'
    refine ⟨(q, m), ⟨hq, hm, rfl⟩, fun qm ⟨hq', hm', h⟩ => ?_⟩
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_parabolic hq' hq hm' hm h.symm
    exact Prod.ext h1 h2
  · have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hn, hcard⟩ := FiniteField.card K p
    refine ⟨card_parabolicRadical J, IsPGroup.of_card (n := n * (parabolicRadicalRoots τ J).ncard)
      ?_, parabolicRadical_ne_bot⟩
    rw [card_parabolicRadical, Nat.card_eq_fintype_card, hcard, ← pow_mul]

end CFSG.LieType.Chevalley
