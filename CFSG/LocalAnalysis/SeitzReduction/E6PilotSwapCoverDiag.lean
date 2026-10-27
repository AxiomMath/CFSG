module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapPieces
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisModule
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapQuasi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)

local instance e6PilotSwapCoverDiagNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩


section Model

variable {K : Type} [Field K]

theorem commutator_levi_eq_E6 [Finite K] (hq : 4 ≤ Nat.card K) (J : Finset (Fin (Tag.rank .E6))) :
    ⁅CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J,
        CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J⁆ =
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J := by
  apply Subgroup.map_injective (adjointGroup .E6 K).subtype_injective
  rw [Subgroup.map_commutator, map_subtype_levi_adjDatumE6]
  exact commutator_rootSpan_amalgamRoots_eq_E6 (F4Pilot.three_le_natCard_top_units hq) J

theorem levi_le_centralizer_leviTorus_E6 (J : Finset (Fin (Tag.rank .E6))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J ≤
      centralizer (((leviTorus K J).subgroupOf (adjointGroup .E6 K) :
        Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro d hd
  have hxR : ((x : adjointGroup .E6 K) : ModGL .E6 K) ∈ rootSpan .E6 K (amalgamRoots J) :=
    mem_subgroupOf.1 ((levi_adjDatumE6_eq (K := K) J).le hx)
  have h1 : ((x : adjointGroup .E6 K) : ModGL .E6 K) ∈
      centralizer (leviTorus K J : Set (ModGL .E6 K)) :=
    rootSpan_amalgamRoots_le_centralizer_leviTorus J hxR
  exact Subtype.ext (mem_centralizer_iff.1 h1 _ (mem_subgroupOf.1 hd))

theorem perfect_le_levi_of_le_centralizer_E6 [Finite K] (hq : 4 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) {P : Subgroup (adjointGroup .E6 K)}
    (hP : ⁅P, P⁆ = P)
    (hPT : P ≤ centralizer (((leviTorus K J).subgroupOf (adjointGroup .E6 K) :
        Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))) :
    P ≤ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J := by
  have h1 : P.map (adjointGroup .E6 K).subtype ≤ perfectCore (adjointGroup .E6 K ⊓
      centralizer ((leviTorus K J ⊓ adjointGroup .E6 K : Subgroup (ModGL .E6 K)) :
        Set (ModGL .E6 K))) := by
    refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ (by rw [← map_commutator, hP])
    rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨x.2, mem_centralizer_iff.2 fun d hd => ?_⟩
    have hdT : (⟨d, hd.2⟩ : adjointGroup .E6 K) ∈
        (leviTorus K J).subgroupOf (adjointGroup .E6 K) := mem_subgroupOf.2 hd.1
    exact congrArg Subtype.val (mem_centralizer_iff.1 (hPT hx) _ hdT)
  rw [perfectCore_inf_centralizer_leviTorus_inf hq hJ, ← map_subtype_levi_adjDatumE6] at h1
  exact (Subgroup.map_le_map_iff_of_injective (adjointGroup .E6 K).subtype_injective).1 h1

theorem map_subtype_levi_singleton_E6 (j : Fin (Tag.rank .E6)) :
    (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}).map
        (adjointGroup .E6 K).subtype =
      rootSubgroup .E6 K (Pi.single j 1) ⊔ rootSubgroup .E6 K (-Pi.single j 1) := by
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup,
    map_subtype_rootGroup_E6 (isRoot_single _ j), map_subtype_rootGroup_E6 (isRoot_neg_single _ j)]

theorem isSimpleGroup_levi_singleton_E6 [CharP K 2] (hq : 4 ≤ Nat.card K)
    (j : Fin (Tag.rank .E6)) :
    IsSimpleGroup (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}) := by
  obtain ⟨-, -, ⟨eS, -⟩, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .E6 K (isRoot_single _ j)
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.RankThree.PartOne.KCRootAxis.sl2_isSimpleGroup hq
  have e1 := (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}).equivMapOfInjective _
    (adjointGroup .E6 K).subtype_injective
  exact (e1.trans ((MulEquiv.subgroupCongr (map_subtype_levi_singleton_E6 j)).trans
    eS.symm)).isSimpleGroup

theorem isSimpleGroup_adjointGroup_E6 [Finite K] : IsSimpleGroup (adjointGroup .E6 K) :=
  isSimpleGroup_of_isQuasisimple_of_center_eq_bot
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K)
    (center_adjointGroup_eq_bot_field .E6 K)

theorem le_centralizer_rootSubgroup_of_not_isRoot {α β : Fin (Tag.rank .E6) → ℤ}
    (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hnot : ¬ IsRoot .E6 (α + β)) :
    rootSubgroup .E6 K β ≤ centralizer (rootSubgroup .E6 K α : Set (ModGL .E6 K)) := by
  intro y hy
  rw [mem_centralizer_iff]
  intro x hx
  exact ((simply_laced_root_commutator_unit .E6 (Or.inr (Or.inl rfl)) hα hβ hne hne').2 hnot K x hx
    y hy).eq

theorem levi_singleton_le_centralizer_of_not_isRoot {i j : Fin (Tag.rank .E6)} (hij : i ≠ j)
    (h : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      ¬ IsRoot .E6 (a • Pi.single i 1 + b • Pi.single j 1)) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j} ≤
      centralizer (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {i} :
        Set (adjointGroup .E6 K)) := by
  have hroot : ∀ (k : Fin (Tag.rank .E6)) (a : ℤ), (a = 1 ∨ a = -1) →
      IsRoot .E6 (a • Pi.single k 1 : Fin (Tag.rank .E6) → ℤ) := by
    rintro k a (rfl | rfl)
    · simpa using isRoot_single .E6 k
    · simpa using isRoot_neg_single .E6 k
  have hne : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      (a • Pi.single i 1 : Fin (Tag.rank .E6) → ℤ) ≠ b • Pi.single j 1 := by
    intro a b ha _ hab
    have h1 := congrFun hab i
    simp only [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, smul_eq_mul, mul_one,
      mul_zero] at h1
    rcases ha with rfl | rfl <;> simp at h1
  have hU : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      rootSubgroup .E6 K (b • Pi.single j 1) ≤
        centralizer (rootSubgroup .E6 K (a • Pi.single i 1) : Set (ModGL .E6 K)) := by
    intro a b ha hb
    refine le_centralizer_rootSubgroup_of_not_isRoot (hroot i a ha) (hroot j b hb) (hne a b ha hb)
      ?_ (h a b ha hb)
    rw [← neg_smul]
    exact hne a (-b) ha (by rcases hb with rfl | rfl <;> simp)
  have hsub : ∀ k : Fin (Tag.rank .E6),
      rootSubgroup .E6 K (Pi.single k 1) ⊔ rootSubgroup .E6 K (-Pi.single k 1) =
        rootSubgroup .E6 K ((1 : ℤ) • Pi.single k 1) ⊔
          rootSubgroup .E6 K ((-1 : ℤ) • Pi.single k 1) := fun k => by
    rw [one_smul, neg_one_smul]
  have hA : rootSubgroup .E6 K (Pi.single j 1) ⊔ rootSubgroup .E6 K (-Pi.single j 1) ≤
      centralizer ((rootSubgroup .E6 K (Pi.single i 1) ⊔ rootSubgroup .E6 K (-Pi.single i 1) :
        Subgroup (ModGL .E6 K)) : Set (ModGL .E6 K)) := by
    rw [hsub i, hsub j, le_centralizer_iff]
    refine sup_le ?_ ?_ <;> rw [le_centralizer_iff] <;> refine sup_le ?_ ?_
    · exact hU 1 1 (Or.inl rfl) (Or.inl rfl)
    · exact hU 1 (-1) (Or.inl rfl) (Or.inr rfl)
    · exact hU (-1) 1 (Or.inr rfl) (Or.inl rfl)
    · exact hU (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  intro y hy
  rw [mem_centralizer_iff]
  intro x hx
  have hx' : (x : ModGL .E6 K) ∈ rootSubgroup .E6 K (Pi.single i 1) ⊔
      rootSubgroup .E6 K (-Pi.single i 1) := by
    rw [← map_subtype_levi_singleton_E6]
    exact ⟨x, hx, rfl⟩
  have hy' : (y : ModGL .E6 K) ∈ rootSubgroup .E6 K (Pi.single j 1) ⊔
      rootSubgroup .E6 K (-Pi.single j 1) := by
    rw [← map_subtype_levi_singleton_E6]
    exact ⟨y, hy, rfl⟩
  exact Subtype.ext (mem_centralizer_iff.1 (hA hy') _ hx')

theorem levi_one_le_centralizer_levi_E6 {j : Fin (Tag.rank .E6)}
    (hj : j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 5) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j} ≤
      centralizer (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} :
        Set (adjointGroup .E6 K)) := by
  have hcheck : ∀ j : Fin (Tag.rank .E6), (j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 5) →
      ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
        (a • Pi.single 1 1 + b • Pi.single j 1 : Fin (Tag.rank .E6) → ℤ) ∉ rootFinset .E6 := by
    have hc : ∀ j ∈ ([0, 2, 4, 5] : List (Fin (Tag.rank .E6))),
        ∀ a ∈ ([1, -1] : List ℤ), ∀ b ∈ ([1, -1] : List ℤ),
          (a • Pi.single 1 1 + b • Pi.single j 1 : Fin (Tag.rank .E6) → ℤ) ∉ rootFinset .E6 := by
      decide +kernel
    intro j hj a b ha hb
    refine hc j ?_ a ?_ b ?_
    · rcases hj with rfl | rfl | rfl | rfl <;> simp
    · rcases ha with rfl | rfl <;> simp
    · rcases hb with rfl | rfl <;> simp
  have hj1 : (1 : Fin (Tag.rank .E6)) ≠ j := by
    rcases hj with rfl | rfl | rfl | rfl <;> decide +revert
  exact levi_singleton_le_centralizer_of_not_isRoot hj1
    fun a b ha hb hr => hcheck j hj a b ha hb (mem_rootFinset.2 hr)

theorem top_le_of_forall_levi_singleton_le_E6 {H : Subgroup (adjointGroup .E6 K)}
    (h : ∀ i : Fin (Tag.rank .E6),
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {i} ≤ H) : ⊤ ≤ H := by
  rw [← CFSG.LieType.Ree.closure_xElement_yElement, Subgroup.closure_le]
  rintro _ ⟨i, c, rfl | rfl⟩
  · exact h i (xElement_mem_levi_adjDatumE6 i c)
  · exact h i (yElement_mem_levi_adjDatumE6 i c)

end Model

section Conj

variable {G : Type*} [Group G]

theorem swapConj_mem_centralizer {T : Subgroup G} {t x : G}
    (ht : T ≤ centralizer ({t} : Set G)) (hx : x ∈ centralizer (T : Set G)) :
    t * x * t⁻¹ ∈ centralizer (T : Set G) := by
  rw [mem_centralizer_iff] at hx ⊢
  intro τ hτ
  have h1 : τ * t = t * τ := mem_centralizer_singleton_iff.1 (ht hτ)
  have h2 : τ * t⁻¹ = t⁻¹ * τ := by
    calc τ * t⁻¹ = t⁻¹ * (t * τ) * t⁻¹ := by group
      _ = t⁻¹ * (τ * t) * t⁻¹ := by rw [h1]
      _ = t⁻¹ * τ := by group
  calc τ * (t * x * t⁻¹) = (τ * t) * x * t⁻¹ := by group
    _ = t * (τ * x) * t⁻¹ := by rw [h1]; group
    _ = t * (x * τ) * t⁻¹ := by rw [hx τ hτ]
    _ = t * x * (τ * t⁻¹) := by group
    _ = t * x * t⁻¹ * τ := by rw [h2]; group

theorem dichotomy_map_conj {F : Subgroup G} (t : G)
    (hF : ∀ M : Subgroup G, M ≤ F → F ≤ normalizer (M : Set G) →
      M ≤ centralizer (F : Set G) ∨ F ≤ M) :
    ∀ M : Subgroup G, M ≤ F.map (MulAut.conj t).toMonoidHom →
      F.map (MulAut.conj t).toMonoidHom ≤ normalizer (M : Set G) →
      M ≤ centralizer (F.map (MulAut.conj t).toMonoidHom : Set G) ∨
        F.map (MulAut.conj t).toMonoidHom ≤ M := by
  have hF' : ∀ M : Subgroup G, M ≤ F → F ≤ normalizer (M : Set G) →
      M ≤ centralizer (F : Set G) ∨ M = F :=
    fun M hMF hFM => (hF M hMF hFM).imp id fun h => le_antisymm hMF h
  intro M hMF hFM
  exact (F4Pilot.dichotomy_map_mulAut (MulAut.conj t) hF' M hMF hFM).imp id fun h => h.ge

end Conj

section Piece

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E6 K} {t : G}

@[expose] noncomputable def SwapFactorCover.piece {N : E6Neighbour} (h : SwapFactorCover e t N)
    (J : Finset (Fin (Tag.rank .E6))) : Subgroup G :=
  perfectCore (h.Kc ⊓ centralizer (modelToG e (leviTorus K J) : Set G))

@[expose] noncomputable def SwapFactorCover.epsC {N : E6Neighbour} (h : SwapFactorCover e t N) :
    h.Kc →* adjointGroup .E6 K :=
  (N.levi K).subtype.comp h.ε

theorem SwapFactorCover.epsC_apply {N : E6Neighbour} (h : SwapFactorCover e t N) (k : h.Kc) :
    h.epsC k = (h.ε k : adjointGroup .E6 K) :=
  rfl

theorem SwapFactorCover.mul_conj_eq {N : E6Neighbour} (h : SwapFactorCover e t N) (k : h.Kc) :
    (k : G) * (t * k * t⁻¹) = ((e.symm (h.epsC k) : L) : G) :=
  h.diag k

theorem SwapFactorCover.epsC_eq_one_iff {N : E6Neighbour} (h : SwapFactorCover e t N) (k : h.Kc) :
    h.epsC k = 1 ↔ (k : G) ∈ h.Kc.map (MulAut.conj t).toMonoidHom := by
  rw [← h.eq_one_iff k, SwapFactorCover.epsC_apply, OneMemClass.coe_eq_one]

theorem SwapFactorCover.range_epsC {N : E6Neighbour} (h : SwapFactorCover e t N) :
    h.epsC.range = N.levi K := by
  rw [SwapFactorCover.epsC, MonoidHom.range_comp, MonoidHom.range_eq_top.2 h.surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem SwapFactorCover.piece_le {N : E6Neighbour} (h : SwapFactorCover e t N)
    (J : Finset (Fin (Tag.rank .E6))) : h.piece J ≤ h.Kc :=
  (CFSG.Quasithin.perfectCore_le _).trans inf_le_left

theorem SwapFactorCover.piece_le_centralizer {N : E6Neighbour} (h : SwapFactorCover e t N)
    (J : Finset (Fin (Tag.rank .E6))) :
    h.piece J ≤ centralizer (modelToG e (leviTorus K J) : Set G) :=
  (CFSG.Quasithin.perfectCore_le _).trans inf_le_right

theorem SwapFactorCover.commutator_piece [Finite G] {N : E6Neighbour} (h : SwapFactorCover e t N)
    (J : Finset (Fin (Tag.rank .E6))) : ⁅h.piece J, h.piece J⁆ = h.piece J :=
  CFSG.Quasithin.perfectCore_perfect _

theorem SwapFactorCover.map_le_centralizer_piece {N : E6Neighbour} (h : SwapFactorCover e t N)
    (J : Finset (Fin (Tag.rank .E6))) :
    h.Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (h.piece J : Set G) :=
  h.le_centralizer.trans (centralizer_le (SetLike.coe_subset_coe.2 (h.piece_le J)))

theorem SwapFactorCover.inf_le_centralizer {N : E6Neighbour} (h : SwapFactorCover e t N)
    {P : Subgroup G} (hP : P ≤ h.Kc) :
    h.Kc ⊓ h.Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (P : Set G) := fun _ hz =>
  centralizer_le (SetLike.coe_subset_coe.2 hP) (h.le_centralizer hz.2)

theorem SwapFactorCover.inf_le_centralizer_self {N : E6Neighbour} (h : SwapFactorCover e t N) :
    h.Kc ⊓ h.Kc.map (MulAut.conj t).toMonoidHom ≤
      centralizer ((h.Kc ⊓ h.Kc.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
  fun _ hz => mem_centralizer_iff.2 fun w hw => mem_centralizer_iff.1 (h.le_centralizer hz.2) w hw.1

theorem SwapFactorCover.pieceCore_eq_piece_sup [Finite G] [Finite K] [CharP K 2]
    {N : E6Neighbour} (h : SwapFactorCover e t N) (htL : t ∈ centralizer (L : Set G))
    (htt : t * t = 1) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) :
    pieceCore e J = h.piece J ⊔ (h.piece J).map (MulAut.conj t).toMonoidHom :=
  h.pieceCore_eq_sup htL htt hf hK hJ

theorem SwapFactorCover.mem_normalizer_of_mem_leviTorus {N : E6Neighbour}
    (h : SwapFactorCover e t N) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) {τ : G}
    (hτ : τ ∈ modelToG e (leviTorus K J)) : τ ∈ normalizer (h.Kc : Set G) := by
  have hτ' := hτ
  obtain ⟨d, hdT, rfl⟩ := (mem_modelToG e).1 hτ
  refine h.normalizer_le _ (modelToG_le_centralizer e (leviTorus_le_centralizer_torus hJ) hτ') ?_
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
  exact odd_orderOf_of_mem_leviTorus hf hK hdT

theorem SwapFactorCover.epsC_mem_levi [Finite G] [Finite K] {N : E6Neighbour}
    (h : SwapFactorCover e t N) (hq : 4 ≤ Nat.card K) (htL : t ∈ centralizer (L : Set G))
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) {k : h.Kc} (hk : (k : G) ∈ h.piece J) :
    h.epsC k ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J := by
  have : Finite (adjointGroup .E6 K) := by
    have : Finite (ModGL Tag.E6 K) := finite_modGL
    infer_instance
  set T : Subgroup G := modelToG e (leviTorus K J) with hT
  have hTt : T ≤ centralizer ({t} : Set G) := fun τ hτ =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL τ (modelToG_le e _ hτ))
  set P : Subgroup (adjointGroup .E6 K) := ((h.piece J).subgroupOf h.Kc).map h.epsC with hP
  have hPp : ⁅P, P⁆ = P := by
    rw [hP, ← map_commutator,
      CFSG.SeitzReduction.commutator_subgroupOf_eq_self (h.piece_le J) (h.commutator_piece J)]
  have hPT : P ≤ centralizer (((leviTorus K J).subgroupOf (adjointGroup .E6 K) :
      Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    intro d hd
    have hdT : ((e.symm d : L) : G) ∈ T := symm_mem_modelToG e (mem_subgroupOf.1 hd)
    have hx1 : (x : G) ∈ centralizer (T : Set G) := h.piece_le_centralizer J (mem_subgroupOf.1 hx)
    have hx2 := swapConj_mem_centralizer hTt hx1
    refine e.symm.injective (Subtype.ext ?_)
    rw [map_mul, map_mul, L.coe_mul, L.coe_mul, ← h.mul_conj_eq x]
    exact mem_centralizer_iff.1 (mul_mem hx1 hx2) _ hdT
  exact perfect_le_levi_of_le_centralizer_E6 hq hJ hPp hPT ⟨k, mem_subgroupOf.2 hk, rfl⟩

theorem SwapFactorCover.exists_epsC_eq [Finite G] [Finite K] [CharP K 2] {N : E6Neighbour}
    (h : SwapFactorCover e t N) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (htL : t ∈ centralizer (L : Set G)) {J : Finset (Fin (Tag.rank .E6))}
    (hJN : J ⊆ N.nodes) {y : adjointGroup .E6 K}
    (hy : y ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) :
    ∃ k : h.Kc, (k : G) ∈ h.piece J ∧ h.epsC k = y := by
  have : Finite (adjointGroup .E6 K) := by
    have : Finite (ModGL Tag.E6 K) := finite_modGL
    infer_instance
  set Q := CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J with hQ
  have hQN : Q ≤ h.epsC.range := by rw [h.range_epsC]; exact levi_le_neighbourLevi hJN
  set P : Subgroup h.Kc := Q.comap h.epsC with hP
  have hP'Q : (perfectCore P).map h.epsC = Q := by
    rw [CFSG.Quasithin.map_perfectCore, hP, map_comap_eq_self hQN,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect (commutator_levi_eq_E6 hq J)]
  have hP'p : ⁅(perfectCore P).map h.Kc.subtype, (perfectCore P).map h.Kc.subtype⁆ =
      (perfectCore P).map h.Kc.subtype := by
    rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
  have hle : (perfectCore P).map h.Kc.subtype ≤ h.piece J := by
    refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf (map_subtype_le _) ?_) hP'p
    rw [← le_centralizer_iff]
    intro τ hτ
    refine swapMem_centralizer_of_perfect hP'p (h.inf_le_centralizer (map_subtype_le _))
      h.inf_le_centralizer_self fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := hx
    have hτN := h.mem_normalizer_of_mem_leviTorus hf hK hJN hτ
    have hτt : τ * t = t * τ := mem_centralizer_iff.1 htL τ (modelToG_le e _ hτ)
    have hτt' : t⁻¹ * τ⁻¹ = τ⁻¹ * t⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hτt]
    set k' : h.Kc := ⟨τ * k * τ⁻¹, (mem_normalizer_iff.1 hτN k).1 k.2⟩ with hk'
    have hδ : (k' : G) * (t * k' * t⁻¹) = τ * ((k : G) * (t * k * t⁻¹)) * τ⁻¹ := by
      change τ * (k : G) * τ⁻¹ * (t * (τ * k * τ⁻¹) * t⁻¹) = _
      calc τ * (k : G) * τ⁻¹ * (t * (τ * k * τ⁻¹) * t⁻¹) =
          τ * (k : G) * τ⁻¹ * ((t * τ) * k * (τ⁻¹ * t⁻¹)) := by group
        _ = τ * (k : G) * τ⁻¹ * ((τ * t) * k * (t⁻¹ * τ⁻¹)) := by rw [hτt, hτt']
        _ = τ * ((k : G) * (t * k * t⁻¹)) * τ⁻¹ := by group
    have hkQ : h.epsC k ∈ Q := CFSG.Quasithin.perfectCore_le P hk
    have hm : ((e.symm (h.epsC k) : L) : G) ∈ modelToG e (rootSpan .E6 K (amalgamRoots J)) := by
      apply symm_mem_modelToG
      rw [← map_subtype_levi_adjDatumE6]
      exact ⟨_, hkQ, rfl⟩
    have hc : τ * ((k : G) * (t * k * t⁻¹)) * τ⁻¹ = (k : G) * (t * k * t⁻¹) := by
      rw [h.mul_conj_eq k, mem_centralizer_iff.1 (modelToG_le_centralizer e
        (rootSpan_amalgamRoots_le_centralizer_leviTorus J) hm) τ hτ, mul_inv_cancel_right]
    have h1 : h.epsC (k⁻¹ * k') = 1 := by
      refine e.symm.injective (Subtype.ext ?_)
      rw [map_mul, map_inv, map_mul, map_inv, L.coe_mul, L.coe_inv, ← h.mul_conj_eq,
        ← h.mul_conj_eq, hδ, hc, map_one, inv_mul_cancel, L.coe_one]
    exact ⟨(k⁻¹ * k').2, (h.epsC_eq_one_iff _).1 h1⟩
  have hyQ : y ∈ (perfectCore P).map h.epsC := by rw [hP'Q]; exact hy
  obtain ⟨k, hk, rfl⟩ := hyQ
  exact ⟨k, hle ⟨k, hk, rfl⟩, rfl⟩

theorem SwapFactorCover.piece_le_centralizer_piece [Finite G] [Finite K] {N : E6Neighbour}
    (h : SwapFactorCover e t N) (hq : 4 ≤ Nat.card K) (htL : t ∈ centralizer (L : Set G))
    {I J : Finset (Fin (Tag.rank .E6))} (hI : I.card ≤ 2) (hJ : J.card ≤ 2)
    (hc : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J ≤
      centralizer (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I :
        Set (adjointGroup .E6 K))) :
    h.piece J ≤ centralizer (h.piece I : Set G) := by
  intro c hc'
  refine swapMem_centralizer_of_perfect (h.commutator_piece I) (h.inf_le_centralizer
    (h.piece_le I)) h.inf_le_centralizer_self fun x hx => ?_
  set kx : h.Kc := ⟨x, h.piece_le I hx⟩
  set kc : h.Kc := ⟨c, h.piece_le J hc'⟩
  have hx' := h.epsC_mem_levi hq htL hI (k := kx) hx
  have hc'' := h.epsC_mem_levi hq htL hJ (k := kc) hc'
  have hcomm : h.epsC kx * h.epsC kc = h.epsC kc * h.epsC kx :=
    mem_centralizer_iff.1 (hc hc'') _ hx'
  have h1 : h.epsC (kx⁻¹ * (kc * kx * kc⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, ← hcomm]
    group
  exact ⟨(kx⁻¹ * (kc * kx * kc⁻¹)).2, (h.epsC_eq_one_iff _).1 h1⟩

theorem SwapFactorCover.piece_le_iSup_piece [Finite G] [Finite K] [CharP K 2] {N : E6Neighbour}
    (h : SwapFactorCover e t N) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (htL : t ∈ centralizer (L : Set G)) {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J.card ≤ 2) (hJN : J ⊆ N.nodes) :
    h.piece J ≤ ⨆ j ∈ J, h.piece {j} := by
  set A : Subgroup G := ⨆ j ∈ J, h.piece {j} with hA
  have hAK : A ≤ h.Kc := iSup₂_le fun j _ => h.piece_le {j}
  refine swapPerfect_le_of_le_sup_central (h.inf_le_centralizer hAK) h.inf_le_centralizer_self
    (CFSG.Quasithin.A3.commutator_self_le A) (h.commutator_piece J) fun x hx => ?_
  set k : h.Kc := ⟨x, h.piece_le J hx⟩ with hk
  have hkJ := h.epsC_mem_levi hq htL hJ (k := k) hx
  have hS : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J ≤
      (A.subgroupOf h.Kc).map h.epsC := by
    rw [CFSG.LieType.CurtisTits.levi]
    refine iSup₂_le fun j hj => ?_
    rw [← CFSG.LieType.CurtisTits.levi_singleton]
    intro y hy
    obtain ⟨k', hk', rfl⟩ :=
      h.exists_epsC_eq hf hK hq htL (Finset.singleton_subset_iff.2 (hJN hj)) hy
    exact ⟨k', mem_subgroupOf.2 (le_iSup₂_of_le (f := fun j (_ : j ∈ J) => h.piece {j}) j hj le_rfl
      hk'), rfl⟩
  obtain ⟨a, ha, hak⟩ := hS hkJ
  have h1 : h.epsC (a⁻¹ * k) = 1 := by rw [map_mul, map_inv, hak, inv_mul_cancel]
  have hz := (h.epsC_eq_one_iff _).1 h1
  have hx' : x = (a : G) * ((a⁻¹ * k : h.Kc) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hx']
  exact mul_mem (mem_sup_left (mem_subgroupOf.1 ha)) (mem_sup_right ⟨(a⁻¹ * k).2, hz⟩)

theorem SwapFactorCover.piece_singleton_dichotomy [Finite G] [Finite K] [CharP K 2]
    {N : E6Neighbour} (h : SwapFactorCover e t N) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (htL : t ∈ centralizer (L : Set G)) {j : Fin (Tag.rank .E6)}
    (hj : j ∈ N.nodes) :
    ∀ M : Subgroup G, M ≤ h.piece {j} → h.piece {j} ≤ normalizer (M : Set G) →
      M ≤ centralizer (h.piece {j} : Set G) ∨ h.piece {j} ≤ M := by
  have hJ : ({j} : Finset (Fin (Tag.rank .E6))).card ≤ 2 := by simp
  have := isSimpleGroup_levi_singleton_E6 (K := K) hq j
  let φ : h.piece {j} →* CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j} :=
    (h.epsC.comp (Subgroup.inclusion (h.piece_le {j}))).codRestrict _ fun x =>
      h.epsC_mem_levi hq htL hJ x.2
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk, rfl⟩ := h.exists_epsC_eq hf hK hq htL (Finset.singleton_subset_iff.2 hj) hy
    exact ⟨⟨k, hk⟩, rfl⟩
  have hker : ∀ x : h.piece {j}, φ x = 1 → (x : G) ∈ centralizer (h.piece {j} : Set G) := by
    intro x hx
    have h1 : h.epsC (Subgroup.inclusion (h.piece_le {j}) x) = 1 := congrArg Subtype.val hx
    exact h.map_le_centralizer_piece {j} ((h.epsC_eq_one_iff _).1 h1)
  intro M hMF hFM
  exact swapNormal_le_centralizer_or_le φ hφ hker (h.commutator_piece {j}) hMF hFM

theorem SwapFactorCover.piece_eq_or_eq_conj [Finite G] [Finite K] [CharP K 2]
    {N N' : E6Neighbour} (h : SwapFactorCover e t N) (h' : SwapFactorCover e t N') {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1) {j : Fin (Tag.rank .E6)}
    (hj : j ∈ N.nodes) (hj' : j ∈ N'.nodes) :
    h'.piece {j} = h.piece {j} ∨ h'.piece {j} = (h.piece {j}).map (MulAut.conj t).toMonoidHom := by
  have hqs := h.piece_singleton_dichotomy hf hK hq htL hj
  refine swapEq_or_eq_conj ((map_mono (h.piece_le {j})).trans (h.map_le_centralizer_piece {j}))
    ((map_mono (h'.piece_le {j})).trans (h'.map_le_centralizer_piece {j})) ?_
    (h.commutator_piece {j}) (by rw [← map_commutator, h.commutator_piece])
    (h'.commutator_piece {j}) ?_ hqs (dichotomy_map_conj t hqs)
  · rw [← h'.pieceCore_eq_piece_sup htL htt hf hK (Finset.singleton_subset_iff.2 hj'),
      h.pieceCore_eq_piece_sup htL htt hf hK (Finset.singleton_subset_iff.2 hj)]
  · intro hbot
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_levi_adjDatumE6 (k := K) j
    obtain ⟨k, hk, rfl⟩ := h'.exists_epsC_eq hf hK hq htL (Finset.singleton_subset_iff.2 hj') hu
    rw [hbot, mem_bot] at hk
    apply hu1
    rw [show k = 1 from Subtype.ext hk, map_one]

end Piece

end CFSG.SeitzReduction.E6Pilot
