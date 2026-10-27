module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2FamilyPiece
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2FieldRowCT

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

local instance e7PilotQ2FamilyAlignNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Triangle


variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

theorem TwoFieldParam.twistOn_high_seven {E E' : Subgroup G} {hX : TwoFieldParam σ e .high E}
    {hY : TwoFieldParam σ e .seven E'} {ρ : K ≃+* K}
    (h2 : hX.TwistAt hY ρ (Pi.single 2 1) ∧ hX.TwistAt hY ρ (-Pi.single 2 1)) :
    hX.TwistOn hY ρ {1, 2, 3, 4} ∧ hX.TwistAt hY ρ beta1 := by
  have h3 := TwoFieldParam.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inl rfl) h2
  have h1 := TwoFieldParam.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inl rfl)) h3
  have h4 := TwoFieldParam.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inl rfl))) h3
  have hβ := h2.1.conj_word (single_mem_orthRoots (by decide)) (single_mem_orthRoots (by decide))
    wordHS (wordElt_wordHS_mem (Or.inl rfl)) (wordElt_wordHS_mem (Or.inr rfl))
  rw [wordProd_wordHS_single] at hβ
  refine ⟨fun j hj => ?_, hβ⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4]

theorem TwoFieldParam.twistOn_high_four {E E' : Subgroup G} {hX : TwoFieldParam σ e .high E}
    {hZ : TwoFieldParam σ e .four E'} {ρ : K ≃+* K}
    (h5 : hX.TwistAt hZ ρ (Pi.single 5 1) ∧ hX.TwistAt hZ ρ (-Pi.single 5 1)) :
    hX.TwistOn hZ ρ {5, 6} ∧ hX.TwistAt hZ ρ beta1 := by
  have h6 := TwoFieldParam.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inr rfl))) h5
  have hβ := h5.2.conj_word (neg_single_mem_orthRoots (by decide))
    (neg_single_mem_orthRoots (by decide)) wordHF (wordElt_wordHF_mem (Or.inl rfl))
    (wordElt_wordHF_mem (Or.inr rfl))
  rw [wordProd_wordHF_neg_single] at hβ
  refine ⟨fun j hj => ?_, hβ⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  exacts [h5, h6]

theorem TwoFieldParam.twistOn_seven_four {E E' : Subgroup G} {hY : TwoFieldParam σ e .seven E}
    {hZ : TwoFieldParam σ e .four E'} {ρ : K ≃+* K}
    (h0 : hY.TwistAt hZ ρ (Pi.single 0 1) ∧ hY.TwistAt hZ ρ (-Pi.single 0 1)) :
    hY.TwistOn hZ ρ {0} ∧ hY.TwistAt hZ ρ beta1 := by
  have hβ := h0.2.conj_word (neg_single_mem_orthRoots (by decide))
    (neg_single_mem_orthRoots (by decide)) wordSF (wordElt_wordSF_mem (Or.inl rfl))
    (wordElt_wordSF_mem (Or.inr rfl))
  rw [wordProd_wordSF_neg_single] at hβ
  refine ⟨fun j hj => ?_, hβ⟩
  rw [Finset.mem_singleton] at hj
  subst hj
  exact h0

omit [CharP K 2] in
theorem twoField_twist_cocycle {E₁ E₂ E₃ : Subgroup G} (hX : TwoFieldParam σ e .high E₁)
    (hY : TwoFieldParam σ e .seven E₂) (hZ : TwoFieldParam σ e .four E₃) {ρhs ρsf ρhf : K ≃+* K}
    (hhs : hX.TwistAt hY ρhs beta1) (hsf : hY.TwistAt hZ ρsf beta1)
    (hhf : hX.TwistAt hZ ρhf beta1) : ρhf = ρhs.trans ρsf := by
  have hγX := beta1_mem_orthRoots .high
  have hγY := beta1_mem_orthRoots .seven
  have hγZ := beta1_mem_orthRoots .four
  ext a
  have h4 : ((hZ.Φ (leviRootElt _ hγZ (ρhf a)) : E₃) : G) =
      hZ.Φ (leviRootElt _ hγZ (ρsf (ρhs a))) := by
    rw [← hhf hγX hγZ a, hhs hγX hγY a, hsf hγY hγZ (ρhs a)]
  have h5 := hZ.Φ.injective (Subtype.ext h4)
  have h6 := congrArg (fun x : E7Neighbour.four.levi K =>
    ((x : adjointGroup .E7 K) : ModGL .E7 K)) h5
  simp only [coe_leviRootElt] at h6
  rw [RingEquiv.trans_apply]
  exact pinnedX_injective (τ := .E7) (R := K) _ h6

theorem exists_aligned_twoFieldParam [Finite K] {E₁ E₂ E₃ : Subgroup G}
    (hX : TwoFieldParam σ e .high E₁) (hY : TwoFieldParam σ e .seven E₂)
    (hZ : TwoFieldParam σ e .four E₃) {ρhs ρhf ρsf : K ≃+* K}
    (hρhs : ∀ c : fixSubfield σ, ρhs c = c) (hρhf : ∀ c : fixSubfield σ, ρhf c = c)
    (h1 : hX.TwistOn hY ρhs {1, 2, 3, 4} ∧ hX.TwistAt hY ρhs beta1)
    (h2 : hX.TwistOn hZ ρhf {5, 6} ∧ hX.TwistAt hZ ρhf beta1)
    (h3 : hY.TwistOn hZ ρsf {0} ∧ hY.TwistAt hZ ρsf beta1) :
    hX.TwistOn (hY.twist ρhs hρhs) 1 {1, 2, 3, 4} ∧
      hX.TwistOn (hZ.twist ρhf hρhf) 1 {5, 6} ∧
      (hY.twist ρhs hρhs).TwistOn (hZ.twist ρhf hρhf) 1 {0} := by
  have hcoc := twoField_twist_cocycle hX hY hZ h1.2 h3.2 h2.2
  refine ⟨fun j hj => ⟨(h1.1 j hj).1.twist hρhs, (h1.1 j hj).2.twist hρhs⟩,
    fun j hj => ⟨(h2.1 j hj).1.twist hρhf, (h2.1 j hj).2.twist hρhf⟩, fun j hj => ?_⟩
  have key : ∀ {γ : Fin (Tag.rank .E7) → ℤ}, hY.TwistAt hZ ρsf γ →
      (hY.twist ρhs hρhs).TwistAt (hZ.twist ρhf hρhf) 1 γ := by
    intro γ hT hγ hγ' a
    rw [TwoFieldParam.twist_apply, TwoFieldParam.twist_apply,
      leviEntrywiseEquiv_leviRootElt, leviEntrywiseEquiv_leviRootElt, RingAut.one_apply, hcoc,
      RingEquiv.trans_apply]
    exact hT hγ hγ' (ρhs a)
  exact ⟨key (h3.1 j hj).1, key (h3.1 j hj).2⟩

end Triangle

section Family


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 (fixSubfield σ)} {EN : E7Neighbour → Subgroup G}

@[expose] def TwoFieldAligned (Φ : ∀ N : E7Neighbour, TwoFieldParam σ e N (EN N)) : Prop :=
  ∀ (N N' : E7Neighbour) {J : Finset (Fin (Tag.rank .E7))}, J ⊆ N.nodes → J ⊆ N'.nodes →
    ∀ (x : N.levi K) (x' : N'.levi K), (x : adjointGroup .E7 K) = x' →
      x ∈ leviPiece K N J → (((Φ N).Φ x : EN N) : G) = (Φ N').Φ x'

@[expose] def twoFieldOfTriple (hX : TwoFieldParam σ e .high (EN .high))
    (hY : TwoFieldParam σ e .seven (EN .seven)) (hZ : TwoFieldParam σ e .four (EN .four)) :
    ∀ N : E7Neighbour, TwoFieldParam σ e N (EN N)
  | .high => hX
  | .seven => hY
  | .four => hZ

theorem twoFieldAligned_ofTriple {hX : TwoFieldParam σ e .high (EN .high)}
    {hY : TwoFieldParam σ e .seven (EN .seven)} {hZ : TwoFieldParam σ e .four (EN .four)}
    (h1 : hX.TwistOn hY 1 {1, 2, 3, 4}) (h2 : hX.TwistOn hZ 1 {5, 6})
    (h3 : hY.TwistOn hZ 1 {0}) : TwoFieldAligned (twoFieldOfTriple hX hY hZ) := by
  intro N N' J hJ hJ' x x' hxx' hx
  have hx' : x' ∈ leviPiece K N' J := mem_leviPiece.2 (hxx' ▸ mem_leviPiece.1 hx)
  have hS : ∀ {A B : E7Neighbour}, J ⊆ A.nodes → J ⊆ B.nodes →
      (A = .high → B = .seven → J ⊆ {1, 2, 3, 4}) ∧ (A = .high → B = .four → J ⊆ {5, 6}) ∧
        (A = .seven → B = .four → J ⊆ {0}) := fun hA hB =>
    ⟨fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).1 ha hb,
      fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).2.1 ha hb,
      fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).2.2 ha hb⟩
  have e1 : ∀ {J : Finset (Fin (Tag.rank .E7))}, J ⊆ {1, 2, 3, 4} →
      ∀ (x : E7Neighbour.high.levi K) (x' : E7Neighbour.seven.levi K),
        (x : adjointGroup .E7 K) = x' → x ∈ leviPiece K .high J →
          ((hX.Φ x : EN .high) : G) = hY.Φ x' := fun hJ x x' hxx' hx =>
    hX.eq_on_leviPiece hY (hJ.trans (by decide)) (hJ.trans (by decide))
      (fun j hj => h1 j (hJ hj)) hxx' hx
  have e2 : ∀ {J : Finset (Fin (Tag.rank .E7))}, J ⊆ {5, 6} →
      ∀ (x : E7Neighbour.high.levi K) (x' : E7Neighbour.four.levi K),
        (x : adjointGroup .E7 K) = x' → x ∈ leviPiece K .high J →
          ((hX.Φ x : EN .high) : G) = hZ.Φ x' := fun hJ x x' hxx' hx =>
    hX.eq_on_leviPiece hZ (hJ.trans (by decide)) (hJ.trans (by decide))
      (fun j hj => h2 j (hJ hj)) hxx' hx
  have e3 : ∀ {J : Finset (Fin (Tag.rank .E7))}, J ⊆ {0} →
      ∀ (x : E7Neighbour.seven.levi K) (x' : E7Neighbour.four.levi K),
        (x : adjointGroup .E7 K) = x' → x ∈ leviPiece K .seven J →
          ((hY.Φ x : EN .seven) : G) = hZ.Φ x' := fun hJ x x' hxx' hx =>
    hY.eq_on_leviPiece hZ (hJ.trans (by decide)) (hJ.trans (by decide))
      (fun j hj => h3 j (hJ hj)) hxx' hx
  cases N <;> cases N'
  · exact congrArg (fun z => ((hX.Φ z : EN .high) : G)) (Subtype.ext hxx')
  · exact e1 ((hS hJ hJ').1 rfl rfl) x x' hxx' hx
  · exact e2 ((hS hJ hJ').2.1 rfl rfl) x x' hxx' hx
  · exact (e1 ((hS hJ' hJ).1 rfl rfl) x' x hxx'.symm hx').symm
  · exact congrArg (fun z => ((hY.Φ z : EN .seven) : G)) (Subtype.ext hxx')
  · exact e3 ((hS hJ hJ').2.2 rfl rfl) x x' hxx' hx
  · exact (e2 ((hS hJ' hJ).2.1 rfl rfl) x' x hxx'.symm hx').symm
  · exact (e3 ((hS hJ' hJ).2.2 rfl rfl) x' x hxx'.symm hx').symm
  · exact congrArg (fun z => ((hZ.Φ z : EN .four) : G)) (Subtype.ext hxx')

@[expose] noncomputable def twoAlignedFamily (Φ : ∀ N : E7Neighbour, TwoFieldParam σ e N (EN N))
    (J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2}) :
    (adjDatumE7 K).leviAmalgam J →* G :=
  (EN (amalgamPlacement J.1)).subtype.comp
    ((Φ (amalgamPlacement J.1)).Φ.toMonoidHom.comp
      (Subgroup.inclusion (leviAmalgam_le_placementLevi J)))

theorem twoAlignedFamily_apply (Φ : ∀ N : E7Neighbour, TwoFieldParam σ e N (EN N))
    (J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2})
    (x : (adjDatumE7 K).leviAmalgam J) :
    twoAlignedFamily Φ J x =
      (((Φ (amalgamPlacement J.1)).Φ ⟨x, leviAmalgam_le_placementLevi J x.2⟩ :
        EN (amalgamPlacement J.1)) : G) :=
  rfl

theorem range_twoAlignedFamily (Φ : ∀ N : E7Neighbour, TwoFieldParam σ e N (EN N))
    (J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2}) :
    (twoAlignedFamily Φ J).range =
      ((leviPiece K (amalgamPlacement J.1) J.1).map
        (Φ (amalgamPlacement J.1)).Φ.toMonoidHom).map (EN (amalgamPlacement J.1)).subtype := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨_, mem_leviPiece_of_mem_leviAmalgam x.2, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hy' : (y : adjointGroup .E7 K) ∈ (adjDatumE7 K).leviAmalgam J := by
      change (y : adjointGroup .E7 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J.1
      rw [levi_adjDatumE7_eq, mem_subgroupOf]
      exact mem_leviPiece.1 hy
    exact ⟨⟨y, hy'⟩, rfl⟩

theorem isTwoFieldFamily_twoAlignedFamily {Φ : ∀ N : E7Neighbour, TwoFieldParam σ e N (EN N)}
    (hΦ : TwoFieldAligned Φ) : IsTwoFieldFamily e (twoAlignedFamily Φ) where
  compatible := by
    intro i j hij x y hxy
    have hsub : (i.1 : Finset (Fin (Tag.rank .E7))) ⊆ j.1 := hij
    rw [twoAlignedFamily_apply, twoAlignedFamily_apply]
    exact hΦ _ _ (subset_nodes_amalgamPlacement i.2)
      (hsub.trans (subset_nodes_amalgamPlacement j.2)) _ _ hxy
      (mem_leviPiece_of_mem_leviAmalgam (N := amalgamPlacement i.1) x.2)
  fix J x hx y hxy := by
    rw [twoAlignedFamily_apply]
    have hxN : x ∈ (amalgamPlacement J.1).levi (fixSubfield σ) :=
      levi_le_neighbourLevi (subset_nodes_amalgamPlacement J.2) hx
    have h1 : (⟨y, leviAmalgam_le_placementLevi J y.2⟩ : (amalgamPlacement J.1).levi K) =
        leviInclusion σ _ ⟨x, hxN⟩ :=
      Subtype.ext (Subtype.ext (by rw [coe_leviInclusion]; exact hxy))
    rw [h1]
    exact (Φ (amalgamPlacement J.1)).fix ⟨x, hxN⟩

end Family

section Normalizer


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {σ : K ≃+* K}

theorem centralizer_le_normalizer_range_twoAlignedFamily (hk : Nat.card (fixSubfield σ) = 2)
    (hK : Nat.card K = 2 ^ 2) {e : L ≃* adjointGroup .E7 (fixSubfield σ)}
    {A : Subgroup (adjointGroup .E7 (fixSubfield σ))} (hAJ : A ≤ posJE7 (fixSubfield σ))
    (hA : Nat.card A = Nat.card (fixSubfield σ) + 1)
    (Φ : ∀ N : E7Neighbour,
      TwoFieldParam σ e N (centralizerPerfectCore (nonsplitNeighbourE7G e A N)))
    (J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2}) :
    centralizer (L : Set G) ≤ normalizer ((twoAlignedFamily Φ J).range : Set G) := by
  intro c hc
  rw [range_twoAlignedFamily]
  exact (Φ (amalgamPlacement J.1)).mem_normalizer_map_leviPiece hk hK hAJ hA
    (subset_nodes_amalgamPlacement J.2) hc

end Normalizer

end CFSG.SeitzReduction.E7Pilot
