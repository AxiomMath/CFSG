module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapTwist
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCTField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG)

local instance e8PilotSwapCTNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

theorem exists_neighbour_mem_nodes_pair (i j : Fin (Tag.rank .E8)) :
    (i ∈ E8Neighbour.high.nodes ∧ j ∈ E8Neighbour.high.nodes) ∨
      (i ∈ E8Neighbour.two.nodes ∧ j ∈ E8Neighbour.two.nodes) ∨
        (i ∈ E8Neighbour.six.nodes ∧ j ∈ E8Neighbour.six.nodes) := by
  revert i j
  decide

section Generation

variable {K : Type} [Field K]

theorem top_le_of_forall_levi_singleton_le_E8 {H : Subgroup (adjointGroup .E8 K)}
    (h : ∀ i : Fin (Tag.rank .E8),
      CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup {i} ≤ H) : ⊤ ≤ H := by
  rw [← CFSG.LieType.Ree.closure_xElement_yElement, Subgroup.closure_le]
  rintro _ ⟨i, c, rfl | rfl⟩
  · exact h i (xElement_mem_levi_adjDatumE8 i c)
  · exact h i (yElement_mem_levi_adjDatumE8 i c)

end Generation

section Family

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 K} {t : G}

@[expose] def IsAlignedSwapFamily (Φ : ∀ N : E8Neighbour, SwapNeighbourIso e t N) : Prop :=
  ∀ (N N' : E8Neighbour) {J : Finset (Fin (Tag.rank .E8))} (hJ : J ⊆ N.nodes)
    (hJ' : J ⊆ N'.nodes) (x : CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J),
    (Φ N).fst hJ x = (Φ N').fst hJ' x

@[expose] def swapOfTriple (hX : SwapNeighbourIso e t .high) (hY : SwapNeighbourIso e t .two)
    (hZ : SwapNeighbourIso e t .six) : ∀ N : E8Neighbour, SwapNeighbourIso e t N
  | .high => hX
  | .two => hY
  | .six => hZ

theorem isAlignedSwapFamily_swapOfTriple {hX : SwapNeighbourIso e t .high}
    {hY : SwapNeighbourIso e t .two} {hZ : SwapNeighbourIso e t .six}
    (h1 : hX.AgreeOn hY {0, 2, 4, 5, 6}) (h2 : hX.AgreeOn hZ {0, 1, 2, 3})
    (h3 : hY.AgreeOn hZ {0, 2, 7}) : IsAlignedSwapFamily (swapOfTriple hX hY hZ) := by
  intro N N' J hJ hJ' x
  have hS : ∀ {A B : E8Neighbour}, J ⊆ A.nodes → J ⊆ B.nodes →
      (A = .high → B = .two → J ⊆ {0, 2, 4, 5, 6}) ∧ (A = .high → B = .six → J ⊆ {0, 1, 2, 3}) ∧
        (A = .two → B = .six → J ⊆ {0, 2, 7}) := fun hA hB =>
    ⟨fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).1 ha hb,
      fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).2.1 ha hb,
      fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).2.2 ha hb⟩
  cases N <;> cases N'
  · exact (swapOfTriple hX hY hZ .high).fst_eq_of_coe_eq hJ hJ' x x rfl
  · exact hX.fst_eq_of_agreeOn hY hJ hJ' (h1.mono ((hS hJ hJ').1 rfl rfl)) x
  · exact hX.fst_eq_of_agreeOn hZ hJ hJ' (h2.mono ((hS hJ hJ').2.1 rfl rfl)) x
  · exact hY.fst_eq_of_agreeOn hX hJ hJ' (h1.symm.mono ((hS hJ' hJ).1 rfl rfl)) x
  · exact (swapOfTriple hX hY hZ .two).fst_eq_of_coe_eq hJ hJ' x x rfl
  · exact hY.fst_eq_of_agreeOn hZ hJ hJ' (h3.mono ((hS hJ hJ').2.2 rfl rfl)) x
  · exact hZ.fst_eq_of_agreeOn hX hJ hJ' (h2.symm.mono ((hS hJ' hJ).2.1 rfl rfl)) x
  · exact hZ.fst_eq_of_agreeOn hY hJ hJ' (h3.symm.mono ((hS hJ' hJ).2.2 rfl rfl)) x
  · exact (swapOfTriple hX hY hZ .six).fst_eq_of_coe_eq hJ hJ' x x rfl

@[expose] noncomputable def swapFamilyE8 (Φ : ∀ N : E8Neighbour, SwapNeighbourIso e t N)
    (J : {J : Finset (Fin (adjDatumE8 K).rank) // J.card ≤ 2}) :
    (adjDatumE8 K).leviAmalgam J →* G :=
  (Φ (amalgamPlacement J.1)).fst (subset_nodes_amalgamPlacement J.2)

theorem swapFamilyE8_apply (Φ : ∀ N : E8Neighbour, SwapNeighbourIso e t N)
    (J : {J : Finset (Fin (adjDatumE8 K).rank) // J.card ≤ 2})
    (x : (adjDatumE8 K).leviAmalgam J) :
    swapFamilyE8 Φ J x = (Φ (amalgamPlacement J.1)).fst (subset_nodes_amalgamPlacement J.2) x :=
  rfl

theorem isCompatible_swapFamilyE8 {Φ : ∀ N : E8Neighbour, SwapNeighbourIso e t N}
    (hΦ : IsAlignedSwapFamily Φ) :
    IsCompatible (adjDatumE8 K).leviAmalgam (swapFamilyE8 Φ) := by
  intro i j hij x y hxy
  have hsub : (i.1 : Finset (Fin (Tag.rank .E8))) ⊆ j.1 := hij
  have hi' : (i.1 : Finset (Fin (Tag.rank .E8))) ⊆ (amalgamPlacement j.1).nodes :=
    hsub.trans (subset_nodes_amalgamPlacement j.2)
  rw [swapFamilyE8_apply, swapFamilyE8_apply,
    hΦ (amalgamPlacement i.1) (amalgamPlacement j.1) (subset_nodes_amalgamPlacement i.2) hi' x]
  exact (Φ (amalgamPlacement j.1)).fst_eq_of_coe_eq hi' _ x y hxy

end Family

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E8 K} {t : G}

theorem exists_injective_swapRow_E8 {Φ : ∀ N : E8Neighbour, SwapNeighbourIso e t N}
    (hΦ : IsAlignedSwapFamily Φ) (hq : 4 ≤ Nat.card K) :
    ∃ ψ : adjointGroup .E8 K →* G, Function.Injective ψ ∧
      (∀ x y, Commute (ψ x) (t * ψ y * t⁻¹)) ∧
      (∀ x, ψ x * (t * ψ x * t⁻¹) = ((e.symm x : L) : G)) ∧
      ψ.range ⊔ ψ.range.map (MulAut.conj t).toMonoidHom = pieceSup e := by
  have hφ : IsCompatible (adjDatumE8 K).leviAmalgam (swapFamilyE8 Φ) :=
    isCompatible_swapFamilyE8 hΦ
  have hcard : ∀ i : Fin (Tag.rank .E8), ({i} : Finset (Fin (Tag.rank .E8))).card ≤ 2 :=
    fun i => by simp
  set G₁ : Subgroup G := ⨆ J, (swapFamilyE8 Φ J).range with hG₁
  have hle : ∀ J x, swapFamilyE8 Φ J x ∈ G₁ := fun J x =>
    le_iSup (fun J => (swapFamilyE8 Φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (adjDatumE8 K).leviAmalgam J →* G₁ :=
    fun J => (swapFamilyE8 Φ J).codRestrict G₁ (hle J) with hφ'def
  have hφ' : IsCompatible (adjDatumE8 K).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hφ i j hij x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₁.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₁.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_levi_adjDatumE8 (k := K) 0
    refine ⟨⟨{0}, hcard 0⟩, ⟨u, hu⟩, fun h => hu1 ?_⟩
    have h1 : swapFamilyE8 Φ ⟨{0}, hcard 0⟩ ⟨u, hu⟩ = 1 := congrArg Subtype.val h
    rw [swapFamilyE8_apply] at h1
    have h2 := (Φ _).fst_injective _ (h1.trans (map_one _).symm)
    exact congrArg Subtype.val h2
  obtain ⟨ψ₀, hψ₀, -, hker⟩ := exists_surjective_of_isCompatible_e8 K φ' hφ' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_adjointGroup_eq_bot_field .E8 K).le
  have hψφ : ∀ J (x : adjointGroup .E8 K) (hx : x ∈ (adjDatumE8 K).leviAmalgam J),
      (G₁.subtype.comp ψ₀) x = swapFamilyE8 Φ J ⟨x, hx⟩ :=
    fun J x hx => congrArg Subtype.val (hψ₀ J ⟨x, hx⟩)
  have hinj : Function.Injective (G₁.subtype.comp ψ₀) := G₁.subtype_injective.comp hinj₀
  generalize G₁.subtype.comp ψ₀ = ψ at hinj hψφ
  have hψN : ∀ (N : E8Neighbour) (i : Fin (Tag.rank .E8))
      (hi : ({i} : Finset (Fin (Tag.rank .E8))) ⊆ N.nodes) (x : adjointGroup .E8 K)
      (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup {i}),
      ψ x = (Φ N).fst hi ⟨x, hx⟩ := by
    intro N i hi x hx
    rw [hψφ ⟨{i}, hcard i⟩ x hx, swapFamilyE8_apply]
    exact hΦ _ N _ hi ⟨x, hx⟩
  have hpair : ∀ (i j : Fin (Tag.rank .E8)) (x y : adjointGroup .E8 K),
      x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup {i} →
      y ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup {j} →
      Commute (ψ x) (t * ψ y * t⁻¹) := by
    intro i j x y hx hy
    obtain ⟨N, hiN, hjN⟩ : ∃ N : E8Neighbour, i ∈ N.nodes ∧ j ∈ N.nodes := by
      rcases exists_neighbour_mem_nodes_pair i j with h | h | h
      exacts [⟨_, h⟩, ⟨_, h⟩, ⟨_, h⟩]
    rw [hψN N i (Finset.singleton_subset_iff.2 hiN) x hx,
      hψN N j (Finset.singleton_subset_iff.2 hjN) y hy, (Φ N).conj_fst]
    exact (Φ N).commute_fst_snd _ _ _ _
  have hall : ∀ x y, Commute (ψ x) (t * ψ y * t⁻¹) := by
    have h1 : ∀ (i : Fin (Tag.rank .E8)) (x : adjointGroup .E8 K),
        x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup {i} →
        ∀ y, Commute (ψ x) (t * ψ y * t⁻¹) := by
      intro i x hx y
      have hH : ⊤ ≤ (centralizer ({ψ x} : Set G)).comap ((MulAut.conj t).toMonoidHom.comp ψ) :=
        top_le_of_forall_levi_singleton_le_E8 fun j y' hy' => by
          rw [mem_comap, mem_centralizer_iff]
          rintro _ rfl
          exact (hpair i j x y' hx hy').eq
      have hy := hH (mem_top y)
      rw [mem_comap, mem_centralizer_iff] at hy
      exact hy _ rfl
    intro x y
    have hH : ⊤ ≤ (centralizer ({t * ψ y * t⁻¹} : Set G)).comap ψ :=
      top_le_of_forall_levi_singleton_le_E8 fun i x' hx' => by
        rw [mem_comap, mem_centralizer_iff]
        rintro _ rfl
        exact (h1 i x' hx' y).symm.eq
    have hx := hH (mem_top x)
    rw [mem_comap, mem_centralizer_iff] at hx
    exact (hx _ rfl).symm
  obtain ⟨δ, hδ⟩ : ∃ δ : adjointGroup .E8 K →* G, ∀ x, δ x = ψ x * (t * ψ x * t⁻¹) :=
    ⟨{ toFun := fun x => ψ x * (t * ψ x * t⁻¹)
       map_one' := by simp
       map_mul' := fun x y => by
         simp only [map_mul]
         have hc := (hall y x).eq
         calc ψ x * ψ y * (t * (ψ x * ψ y) * t⁻¹) =
             ψ x * (ψ y * (t * ψ x * t⁻¹)) * (t * ψ y * t⁻¹) := by group
           _ = ψ x * ((t * ψ x * t⁻¹) * ψ y) * (t * ψ y * t⁻¹) := by rw [hc]
           _ = ψ x * (t * ψ x * t⁻¹) * (ψ y * (t * ψ y * t⁻¹)) := by group }, fun x => rfl⟩
  have hδe : ⊤ ≤ MonoidHom.eqLocus δ (L.subtype.comp e.symm.toMonoidHom) :=
    top_le_of_forall_levi_singleton_le_E8 fun i x hx => by
      change δ x = (L.subtype.comp e.symm.toMonoidHom) x
      have hi := subset_nodes_amalgamPlacement (hcard i)
      rw [hδ, hψN _ i hi x hx, (Φ _).conj_fst, (Φ _).fst_mul_snd]
      rfl
  have hdiag : ∀ x, ψ x * (t * ψ x * t⁻¹) = ((e.symm x : L) : G) := fun x => by
    rw [← hδ]
    exact hδe (mem_top x)
  have hpiece1 : ∀ (i : Fin (Tag.rank .E8)) (x : adjointGroup .E8 K),
      x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup {i} →
      ψ x ∈ pieceSup e ∧ t * ψ x * t⁻¹ ∈ pieceSup e := by
    intro i x hx
    have hi := subset_nodes_amalgamPlacement (hcard i)
    rw [hψN _ i hi x hx, (Φ _).conj_fst]
    exact ⟨pieceCore_le_pieceSup ⟨{i}, hcard i⟩
        ((Φ _).range_fst_le_pieceCore hq hi (hcard i) ⟨_, rfl⟩),
      pieceCore_le_pieceSup ⟨{i}, hcard i⟩
        ((Φ _).range_snd_le_pieceCore hq hi (hcard i) ⟨_, rfl⟩)⟩
  have hle1 : ψ.range ≤ pieceSup e := by
    rintro _ ⟨x, rfl⟩
    have hH : ⊤ ≤ (pieceSup e).comap ψ :=
      top_le_of_forall_levi_singleton_le_E8 fun i x hx => (hpiece1 i x hx).1
    exact hH (mem_top x)
  have hle2 : ψ.range.map (MulAut.conj t).toMonoidHom ≤ pieceSup e := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have hH : ⊤ ≤ (pieceSup e).comap ((MulAut.conj t).toMonoidHom.comp ψ) :=
      top_le_of_forall_levi_singleton_le_E8 fun i x hx => (hpiece1 i x hx).2
    exact hH (mem_top x)
  refine ⟨ψ, hinj, hall, hdiag, le_antisymm (sup_le hle1 hle2) (iSup_le fun J => ?_)⟩
  have hJ := subset_nodes_amalgamPlacement J.2
  rw [← (Φ (amalgamPlacement J.1)).range_fst_sup_range_snd hq hJ J.2]
  refine sup_le_sup ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, hψφ J x x.2⟩
  · rintro _ ⟨x, rfl⟩
    rw [← (Φ _).conj_fst]
    exact ⟨_, ⟨x, hψφ J x x.2⟩, rfl⟩

theorem exists_swapFactors_E8 {Φ : ∀ N : E8Neighbour, SwapNeighbourIso e t N}
    (hΦ : IsAlignedSwapFamily Φ) (hq : 4 ≤ Nat.card K) :
    ∃ G₁ : Subgroup G, Nonempty (G₁ ≃* adjointGroup .E8 K) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e := by
  obtain ⟨ψ, hinj, hall, -, hsup⟩ := exists_injective_swapRow_E8 hΦ hq
  refine ⟨ψ.range, ⟨(MonoidHom.ofInjective hinj).symm⟩, ?_, hsup⟩
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨x, rfl⟩
  exact (hall x y).eq

theorem exists_swapFactors_E8_of_triple (hX : SwapNeighbourIso e t .high)
    (hY : SwapNeighbourIso e t .two) (hZ : SwapNeighbourIso e t .six) (hq : 4 ≤ Nat.card K) :
    ∃ G₁ : Subgroup G, Nonempty (G₁ ≃* adjointGroup .E8 K) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e := by
  obtain ⟨hY', hZ', h1, h2, h3⟩ := exists_aligned_swapNeighbourIso hX hY hZ hq
  exact exists_swapFactors_E8 (isAlignedSwapFamily_swapOfTriple h1 h2 h3) hq

theorem exists_swapFactors_E8_of_high (hX : SwapNeighbourIso e t .high)
    (htL : t ∈ centralizer (L : Set G)) (hq : 4 ≤ Nat.card K) :
    ∃ G₁ : Subgroup G, Nonempty (G₁ ≃* adjointGroup .E8 K) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e :=
  exists_swapFactors_E8_of_triple hX
    (hX.toNeighbour .two (commute_symm_rep_of_mem_centralizer htL .two))
    (hX.toNeighbour .six (commute_symm_rep_of_mem_centralizer htL .six)) hq

end Main

end CFSG.SeitzReduction.E8Pilot
