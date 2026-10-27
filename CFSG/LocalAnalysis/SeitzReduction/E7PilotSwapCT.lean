module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotSwapTwist
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotCTField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG)

local instance e7PilotSwapCTNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

theorem exists_neighbour_mem_nodes_pair_E7 (i j : Fin (Tag.rank .E7)) :
    (i ∈ E7Neighbour.high.nodes ∧ j ∈ E7Neighbour.high.nodes) ∨
      (i ∈ E7Neighbour.seven.nodes ∧ j ∈ E7Neighbour.seven.nodes) ∨
        (i ∈ E7Neighbour.four.nodes ∧ j ∈ E7Neighbour.four.nodes) := by
  revert i j
  decide

theorem swap_nodes_inter_subset {N N' : E7Neighbour} {j : Fin (Tag.rank .E7)} (hj : j ∈ N.nodes)
    (hj' : j ∈ N'.nodes) :
    (N = .high → N' = .seven → j ∈ ({1, 2, 3, 4} : Finset (Fin (Tag.rank .E7)))) ∧
      (N = .high → N' = .four → j ∈ ({5, 6} : Finset (Fin (Tag.rank .E7)))) ∧
      (N = .seven → N' = .four → j ∈ ({0} : Finset (Fin (Tag.rank .E7)))) := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl rfl <;> revert j hj hj' <;> decide

section Generation

variable {K : Type} [Field K]

theorem top_le_of_levi_singleton_le_E7 {H : Subgroup (adjointGroup .E7 K)}
    (h : ∀ i : Fin (Tag.rank .E7),
      CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup {i} ≤ H) : ⊤ ≤ H := by
  rw [← CFSG.LieType.Ree.closure_xElement_yElement, Subgroup.closure_le]
  rintro _ ⟨i, c, rfl | rfl⟩
  · exact h i (xElement_mem_levi_adjDatumE7 i c)
  · exact h i (yElement_mem_levi_adjDatumE7 i c)

end Generation

section Family

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 K} {t : G}

@[expose] def IsAlignedSwapFamily (Φ : ∀ N : E7Neighbour, SwapNeighbourIso e t N) : Prop :=
  ∀ (N N' : E7Neighbour) {J : Finset (Fin (Tag.rank .E7))} (hJ : J ⊆ N.nodes)
    (hJ' : J ⊆ N'.nodes) (x : CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J),
    (Φ N).fst hJ x = (Φ N').fst hJ' x

@[expose] def swapOfTriple (hX : SwapNeighbourIso e t .high) (hY : SwapNeighbourIso e t .seven)
    (hZ : SwapNeighbourIso e t .four) : ∀ N : E7Neighbour, SwapNeighbourIso e t N
  | .high => hX
  | .seven => hY
  | .four => hZ

theorem isAlignedSwapFamily_swapOfTriple {hX : SwapNeighbourIso e t .high}
    {hY : SwapNeighbourIso e t .seven} {hZ : SwapNeighbourIso e t .four}
    (h1 : hX.AgreeOn hY {1, 2, 3, 4}) (h2 : hX.AgreeOn hZ {5, 6})
    (h3 : hY.AgreeOn hZ {0}) : IsAlignedSwapFamily (swapOfTriple hX hY hZ) := by
  intro N N' J hJ hJ' x
  have hS : ∀ {A B : E7Neighbour}, J ⊆ A.nodes → J ⊆ B.nodes →
      (A = .high → B = .seven → J ⊆ {1, 2, 3, 4}) ∧ (A = .high → B = .four → J ⊆ {5, 6}) ∧
        (A = .seven → B = .four → J ⊆ {0}) := fun hA hB =>
    ⟨fun ha hb j hj => (swap_nodes_inter_subset (hA hj) (hB hj)).1 ha hb,
      fun ha hb j hj => (swap_nodes_inter_subset (hA hj) (hB hj)).2.1 ha hb,
      fun ha hb j hj => (swap_nodes_inter_subset (hA hj) (hB hj)).2.2 ha hb⟩
  cases N <;> cases N'
  · exact (swapOfTriple hX hY hZ .high).fst_eq_of_coe_eq hJ hJ' x x rfl
  · exact hX.fst_eq_of_agreeOn hY hJ hJ' (h1.mono ((hS hJ hJ').1 rfl rfl)) x
  · exact hX.fst_eq_of_agreeOn hZ hJ hJ' (h2.mono ((hS hJ hJ').2.1 rfl rfl)) x
  · exact hY.fst_eq_of_agreeOn hX hJ hJ' (h1.symm.mono ((hS hJ' hJ).1 rfl rfl)) x
  · exact (swapOfTriple hX hY hZ .seven).fst_eq_of_coe_eq hJ hJ' x x rfl
  · exact hY.fst_eq_of_agreeOn hZ hJ hJ' (h3.mono ((hS hJ hJ').2.2 rfl rfl)) x
  · exact hZ.fst_eq_of_agreeOn hX hJ hJ' (h2.symm.mono ((hS hJ' hJ).2.1 rfl rfl)) x
  · exact hZ.fst_eq_of_agreeOn hY hJ hJ' (h3.symm.mono ((hS hJ' hJ).2.2 rfl rfl)) x
  · exact (swapOfTriple hX hY hZ .four).fst_eq_of_coe_eq hJ hJ' x x rfl

@[expose] noncomputable def swapFamilyE7 (Φ : ∀ N : E7Neighbour, SwapNeighbourIso e t N)
    (J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2}) :
    (adjDatumE7 K).leviAmalgam J →* G :=
  (Φ (amalgamPlacement J.1)).fst (subset_nodes_amalgamPlacement J.2)

theorem swapFamilyE7_apply (Φ : ∀ N : E7Neighbour, SwapNeighbourIso e t N)
    (J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2})
    (x : (adjDatumE7 K).leviAmalgam J) :
    swapFamilyE7 Φ J x = (Φ (amalgamPlacement J.1)).fst (subset_nodes_amalgamPlacement J.2) x :=
  rfl

theorem isCompatible_swapFamilyE7 {Φ : ∀ N : E7Neighbour, SwapNeighbourIso e t N}
    (hΦ : IsAlignedSwapFamily Φ) :
    IsCompatible (adjDatumE7 K).leviAmalgam (swapFamilyE7 Φ) := by
  intro i j hij x y hxy
  have hsub : (i.1 : Finset (Fin (Tag.rank .E7))) ⊆ j.1 := hij
  have hi' : (i.1 : Finset (Fin (Tag.rank .E7))) ⊆ (amalgamPlacement j.1).nodes :=
    hsub.trans (subset_nodes_amalgamPlacement j.2)
  rw [swapFamilyE7_apply, swapFamilyE7_apply,
    hΦ (amalgamPlacement i.1) (amalgamPlacement j.1) (subset_nodes_amalgamPlacement i.2) hi' x]
  exact (Φ (amalgamPlacement j.1)).fst_eq_of_coe_eq hi' _ x y hxy

end Family

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E7 K} {t : G}

theorem exists_injective_extension_E7 (φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G)
    (hφ : IsCompatible (adjDatumE7 K).leviAmalgam φ)
    (hinj0 : Function.Injective (φ ⟨{0}, by simp⟩)) :
    ∃ ψ : adjointGroup .E7 K →* G, Function.Injective ψ ∧
      ∀ J (x : adjointGroup .E7 K) (hx : x ∈ (adjDatumE7 K).leviAmalgam J), ψ x = φ J ⟨x, hx⟩ := by
  set G₁ : Subgroup G := ⨆ J, (φ J).range with hG₁
  have hle : ∀ J x, φ J x ∈ G₁ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (adjDatumE7 K).leviAmalgam J →* G₁ := fun J => (φ J).codRestrict G₁ (hle J)
    with hφ'def
  have hφ' : IsCompatible (adjDatumE7 K).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hφ i j hij x y hxy)
  have hφs : IsCompatible (e7Datum K).leviAmalgam (scFamilyE7 φ') := isCompatible_scFamilyE7 hφ'
  have hgen' : ⨆ J, (scFamilyE7 φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₁.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₁.symm
    rw [range_scFamilyE7, ← MonoidHom.range_comp]
    rfl
  have hcard0 : ({0} : Finset (Fin (Tag.rank .E7))).card ≤ 2 := by simp
  have hnt : ∃ J, ∃ x, scFamilyE7 φ' J x ≠ 1 := by
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_levi_adjDatumE7 (k := K) 0
    obtain ⟨y', hy'⟩ := leviIsogenyE7_surjective (K := K) {0} ⟨u, hu⟩
    refine ⟨⟨{0}, hcard0⟩, y', fun h => hu1 ?_⟩
    have h1 : φ ⟨{0}, hcard0⟩ (leviIsogenyE7 {0} y') = 1 := congrArg Subtype.val h
    rw [hy', ← map_one (φ ⟨{0}, hcard0⟩)] at h1
    exact congrArg Subtype.val (hinj0 h1)
  obtain ⟨ψs, hψs, -, hker⟩ := exists_surjective_of_isCompatible_e7 K _ hφs hgen' hnt
  have hinjs : Function.Injective ψs := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (E8Pilot.center_minGroup_e7_eq_bot (K := K)).le
  set ε := E8Pilot.e7MinEquivAdjoint K with hε
  set ψ₀ : adjointGroup .E7 K →* G₁ := ψs.comp ε.symm.toMonoidHom with hψ₀
  have hinj₀ : Function.Injective ψ₀ := hinjs.comp ε.symm.injective
  have hψφ' : ∀ J (y : (adjDatumE7 K).leviAmalgam J), ψ₀ y = φ' J y := by
    intro J y
    obtain ⟨x, rfl⟩ := leviIsogenyE7_surjective (K := K) J.1 y
    have hx : ε.symm (leviIsogenyE7 J.1 x : adjointGroup .E7 K) =
        (x : e7Data_valid.minGroup K) := by
      rw [MulEquiv.symm_apply_eq, hε, E8Pilot.e7MinEquivAdjoint_apply, coe_leviIsogenyE7]
    rw [hψ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx]
    exact hψs J x
  exact ⟨G₁.subtype.comp ψ₀, G₁.subtype_injective.comp hinj₀,
    fun J x hx => congrArg Subtype.val (hψφ' J ⟨x, hx⟩)⟩

theorem exists_injective_swapRow_E7 {Φ : ∀ N : E7Neighbour, SwapNeighbourIso e t N}
    (hΦ : IsAlignedSwapFamily Φ) (hq : 4 ≤ Nat.card K) :
    ∃ ψ : adjointGroup .E7 K →* G, Function.Injective ψ ∧
      (∀ x y, Commute (ψ x) (t * ψ y * t⁻¹)) ∧
      (∀ x, ψ x * (t * ψ x * t⁻¹) = ((e.symm x : L) : G)) ∧
      ψ.range ⊔ ψ.range.map (MulAut.conj t).toMonoidHom = pieceSup e := by
  have hcard : ∀ i : Fin (Tag.rank .E7), ({i} : Finset (Fin (Tag.rank .E7))).card ≤ 2 :=
    fun i => by simp
  obtain ⟨ψ, hinj, hψφ⟩ := exists_injective_extension_E7 (swapFamilyE7 Φ)
    (isCompatible_swapFamilyE7 hΦ) ((Φ _).fst_injective _)
  have hψN : ∀ (N : E7Neighbour) (i : Fin (Tag.rank .E7))
      (hi : ({i} : Finset (Fin (Tag.rank .E7))) ⊆ N.nodes) (x : adjointGroup .E7 K)
      (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup {i}),
      ψ x = (Φ N).fst hi ⟨x, hx⟩ := by
    intro N i hi x hx
    rw [hψφ ⟨{i}, hcard i⟩ x hx, swapFamilyE7_apply]
    exact hΦ _ N _ hi ⟨x, hx⟩
  have hpair : ∀ (i j : Fin (Tag.rank .E7)) (x y : adjointGroup .E7 K),
      x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup {i} →
      y ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup {j} →
      Commute (ψ x) (t * ψ y * t⁻¹) := by
    intro i j x y hx hy
    obtain ⟨N, hiN, hjN⟩ : ∃ N : E7Neighbour, i ∈ N.nodes ∧ j ∈ N.nodes := by
      rcases exists_neighbour_mem_nodes_pair_E7 i j with h | h | h
      exacts [⟨_, h⟩, ⟨_, h⟩, ⟨_, h⟩]
    rw [hψN N i (Finset.singleton_subset_iff.2 hiN) x hx,
      hψN N j (Finset.singleton_subset_iff.2 hjN) y hy, (Φ N).conj_fst]
    exact (Φ N).commute_fst_snd _ _ _ _
  have hall : ∀ x y, Commute (ψ x) (t * ψ y * t⁻¹) := by
    have h1 : ∀ (i : Fin (Tag.rank .E7)) (x : adjointGroup .E7 K),
        x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup {i} →
        ∀ y, Commute (ψ x) (t * ψ y * t⁻¹) := by
      intro i x hx y
      have hH : ⊤ ≤ (centralizer ({ψ x} : Set G)).comap ((MulAut.conj t).toMonoidHom.comp ψ) :=
        top_le_of_levi_singleton_le_E7 fun j y' hy' => by
          rw [mem_comap, mem_centralizer_iff]
          rintro _ rfl
          exact (hpair i j x y' hx hy').eq
      have hy := hH (mem_top y)
      rw [mem_comap, mem_centralizer_iff] at hy
      exact hy _ rfl
    intro x y
    have hH : ⊤ ≤ (centralizer ({t * ψ y * t⁻¹} : Set G)).comap ψ :=
      top_le_of_levi_singleton_le_E7 fun i x' hx' => by
        rw [mem_comap, mem_centralizer_iff]
        rintro _ rfl
        exact (h1 i x' hx' y).symm.eq
    have hx := hH (mem_top x)
    rw [mem_comap, mem_centralizer_iff] at hx
    exact (hx _ rfl).symm
  obtain ⟨δ, hδ⟩ : ∃ δ : adjointGroup .E7 K →* G, ∀ x, δ x = ψ x * (t * ψ x * t⁻¹) :=
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
    top_le_of_levi_singleton_le_E7 fun i x hx => by
      change δ x = (L.subtype.comp e.symm.toMonoidHom) x
      have hi := subset_nodes_amalgamPlacement (hcard i)
      rw [hδ, hψN _ i hi x hx, (Φ _).conj_fst, (Φ _).fst_mul_snd]
      rfl
  have hdiag : ∀ x, ψ x * (t * ψ x * t⁻¹) = ((e.symm x : L) : G) := fun x => by
    rw [← hδ]
    exact hδe (mem_top x)
  have hpiece1 : ∀ (i : Fin (Tag.rank .E7)) (x : adjointGroup .E7 K),
      x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup {i} →
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
      top_le_of_levi_singleton_le_E7 fun i x hx => (hpiece1 i x hx).1
    exact hH (mem_top x)
  have hle2 : ψ.range.map (MulAut.conj t).toMonoidHom ≤ pieceSup e := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have hH : ⊤ ≤ (pieceSup e).comap ((MulAut.conj t).toMonoidHom.comp ψ) :=
      top_le_of_levi_singleton_le_E7 fun i x hx => (hpiece1 i x hx).2
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

theorem exists_swapFactors_E7 {Φ : ∀ N : E7Neighbour, SwapNeighbourIso e t N}
    (hΦ : IsAlignedSwapFamily Φ) (hq : 4 ≤ Nat.card K) :
    ∃ G₁ : Subgroup G, Nonempty (G₁ ≃* adjointGroup .E7 K) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e := by
  obtain ⟨ψ, hinj, hall, -, hsup⟩ := exists_injective_swapRow_E7 hΦ hq
  refine ⟨ψ.range, ⟨(MonoidHom.ofInjective hinj).symm⟩, ?_, hsup⟩
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨x, rfl⟩
  exact (hall x y).eq

theorem exists_swapFactors_E7_of_triple (hX : SwapNeighbourIso e t .high)
    (hY : SwapNeighbourIso e t .seven) (hZ : SwapNeighbourIso e t .four) (hq : 4 ≤ Nat.card K) :
    ∃ G₁ : Subgroup G, Nonempty (G₁ ≃* adjointGroup .E7 K) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e := by
  obtain ⟨hY', hZ', h1, h2, h3⟩ := exists_aligned_swapNeighbourIso hX hY hZ hq
  exact exists_swapFactors_E7 (isAlignedSwapFamily_swapOfTriple h1 h2 h3) hq

theorem exists_swapFactors_E7_of_high (hX : SwapNeighbourIso e t .high)
    (htL : t ∈ centralizer (L : Set G)) (hq : 4 ≤ Nat.card K) :
    ∃ G₁ : Subgroup G, Nonempty (G₁ ≃* adjointGroup .E7 K) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e :=
  exists_swapFactors_E7_of_triple hX
    (hX.toNeighbour .seven (commute_symm_rep_of_mem_centralizer htL .seven))
    (hX.toNeighbour .four (commute_symm_rep_of_mem_centralizer htL .four)) hq

end Main

end CFSG.SeitzReduction.E7Pilot
