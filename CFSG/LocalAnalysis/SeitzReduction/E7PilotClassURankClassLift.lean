module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassURankClass
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUF3Core
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassURankLevi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Isogeny
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily)
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)
open scoped commutatorElement

local instance e7ClassURankClassLiftNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

theorem uYFrame_eq : uYFrame = oddDerivE6YFrame.map e6Embed := by decide

theorem uZFrame_eq : uZFrame = oddDerivE6ZFrame.map e6Embed := by decide

theorem uTopRoot_eq : uTopRoot = e6Embed (highRoot .E6) := by decide

theorem uFrames_pairwise :
    [uTopRoot].Pairwise (fun σ σ' => iform σ σ' = 0) ∧
      uYFrame.Pairwise (fun σ σ' => iform σ σ' = 0) ∧
      uZFrame.Pairwise (fun σ σ' => iform σ σ' = 0) := by
  decide +kernel

theorem uFrames_isRootB :
    (∀ g ∈ [uTopRoot], isRootB .E7 g = true) ∧ (∀ g ∈ uYFrame, isRootB .E7 g = true) ∧
      ∀ g ∈ uZFrame, isRootB .E7 g = true := by
  decide +kernel

@[expose] def IsUFrame (T : List (Fin Tag.E7.rank → ℤ)) : Prop :=
  T = [uTopRoot] ∨ T = uYFrame ∨ T = uZFrame

theorem IsUFrame.pairwise {T : List (Fin Tag.E7.rank → ℤ)} (hT : IsUFrame T) :
    T.Pairwise (fun σ σ' => iform σ σ' = 0) := by
  rcases hT with rfl | rfl | rfl
  exacts [uFrames_pairwise.1, uFrames_pairwise.2.1, uFrames_pairwise.2.2]

theorem IsUFrame.isRoot {T : List (Fin Tag.E7.rank → ℤ)} (hT : IsUFrame T) :
    ∀ g ∈ T, IsRoot .E7 g := by
  rcases hT with rfl | rfl | rfl
  exacts [fun g hg => isRootB_iff.1 (uFrames_isRootB.1 g hg),
    fun g hg => isRootB_iff.1 (uFrames_isRootB.2.1 g hg),
    fun g hg => isRootB_iff.1 (uFrames_isRootB.2.2 g hg)]

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def uFrameElt (T : List (Fin Tag.E7.rank → ℤ)) : adjointGroup .E7 K :=
  ⟨(T.map fun g => pinnedX .E7 K g 1).prod, list_prod_map_pinnedX_mem_adjointGroup T⟩

theorem coe_uFrameElt (T : List (Fin Tag.E7.rank → ℤ)) :
    (uFrameElt K T : ModGL .E7 K) = (T.map fun g => pinnedX .E7 K g 1).prod := rfl

theorem uFrameElt_sq [CharP K 2] {T : List (Fin Tag.E7.rank → ℤ)} (hTr : ∀ g ∈ T, IsRoot .E7 g)
    (hT : T.Pairwise (fun σ σ' => iform σ σ' = 0)) : uFrameElt K T ^ 2 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have sq : ∀ β : Fin Tag.E7.rank → ℤ, pinnedX .E7 K β 1 ^ 2 = 1 := fun β => by
    rw [pow_two]
    exact classD4_pinnedX_mul_self h2 β
  have key : ∀ F : List (Fin Tag.E7.rank → ℤ), (∀ β ∈ F, IsRoot .E7 β) →
      F.Pairwise (fun σ σ' => iform σ σ' = 0) →
      ((F.map fun σ => pinnedX .E7 K σ 1).prod) ^ 2 = 1 := by
    intro F
    induction F with
    | nil => intro _ _; simp
    | cons β F ih =>
      intro hF hpw
      rw [List.pairwise_cons] at hpw
      have hc : Commute (pinnedX .E7 K β 1) (F.map fun σ => pinnedX .E7 K σ 1).prod :=
        Commute.list_prod_right _ _ fun x hx => by
          obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
          exact classD4_commute_pinnedX hτ (hF β List.mem_cons_self)
            (hF σ (List.mem_cons_of_mem _ hσ)) (hpw.1 σ hσ).ge 1 1
      rw [List.map_cons, List.prod_cons, hc.mul_pow, sq,
        ih (fun σ hσ => hF σ (List.mem_cons_of_mem _ hσ)) hpw.2, one_mul]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact key T hTr hT

theorem eq_one_of_sq_eq_one_of_pow_odd {G : Type*} [Monoid G] {x : G} (h2 : x ^ 2 = 1) {m : ℕ}
    (hm : Odd m) (hxm : x ^ m = 1) : x = 1 := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hxm
  exact hxm

theorem pow_odd_eq_self_of_sq_eq_one {G : Type*} [Monoid G] {x : G} (h2 : x ^ 2 = 1) {m : ℕ}
    (hm : Odd m) : x ^ m = x := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, h2, one_pow, one_mul]

theorem odd_card_sub_one [Finite K] [CharP K 2] : Odd (Nat.card K - 1) :=
  (Nat.coprime_two_left).1 coprime_two_card_sub_one

theorem mul_pow_mul_inv_mem {G : Type*} [Group G] {N H : Subgroup G}
    (hHN : H ≤ normalizer (N : Set G)) {n h : G} (hn : n ∈ N) (hh : h ∈ H) (m : ℕ) :
    (n * h) ^ m * (h ^ m)⁻¹ ∈ N := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hconj : h ^ m * n * (h ^ m)⁻¹ ∈ N :=
      (mem_normalizer_iff.1 (hHN (pow_mem hh m)) n).1 hn
    have e : (n * h) ^ (m + 1) * (h ^ (m + 1))⁻¹ =
        ((n * h) ^ m * (h ^ m)⁻¹) * (h ^ m * n * (h ^ m)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact mul_mem ih hconj

theorem mem_e6Levi_of_mem_parabolicLevi [Finite K] [CharP K 2] {a : adjointGroup .E7 K}
    (ha : (a : ModGL .E7 K) ∈ parabolicLevi .E7 K uNodes) (ha2 : a ^ 2 = 1) : a ∈ e6Levi K := by
  have hle := parabolicLevi_le_rootSpan_parabolicRoots_sup_torusGroup (K := K) uNodes ha
  rw [parabolicRoots_uNodes] at hle
  have hHN : torusGroup .E7 K ≤ normalizer (rootSpan .E7 K e6LeviRoots : Set (ModGL .E7 K)) :=
    torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hHN] at hle
  obtain ⟨n, hn, h, hh, hnh⟩ := hle
  have hnh' : n * h = (a : ModGL .E7 K) := hnh
  have hpow := mul_pow_mul_inv_mem hHN hn hh (Nat.card K - 1)
  rw [pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh), inv_one,
    mul_one, hnh', ← Subgroup.coe_pow, pow_odd_eq_self_of_sq_eq_one ha2 odd_card_sub_one] at hpow
  exact mem_subgroupOf.2 hpow

theorem mem_e6LeviU_of_mem_leviU [Finite K] [CharP K 2] {a : adjointGroup .E7 K}
    (ha : a ∈ leviU K) (ha2 : a ^ 2 = 1) : a ∈ e6LeviU K := by
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  have h2 : a₀ ^ 2 = 1 := by
    apply (MulAut.conj (e7RepConj K 3)).injective
    rw [map_pow, map_one]
    exact ha2
  exact ⟨a₀, mem_e6Levi_of_mem_parabolicLevi (mem_subgroupOf.1 ha₀) h2, rfl⟩

theorem e6Levi_le_parabolicLevi :
    e6Levi K ≤ (parabolicLevi .E7 K uNodes).subgroupOf (adjointGroup .E7 K) := by
  intro x hx
  rw [mem_subgroupOf]
  have h := F4Pilot.rootSpan_parabolicRoots_le_parabolicLevi (K := K) (τ := .E7) uNodes
  rw [parabolicRoots_uNodes] at h
  exact h (mem_subgroupOf.1 hx)

section Classes

@[expose] noncomputable def scFrame (F : List (Fin (Tag.rank .E6) → ℤ)) :
    e6Data_valid.minGroup K :=
  (F.map fun σ => e6Data_valid.xm K σ 1).prod

theorem coe_e6Isogeny_scFrame [Finite K] [CharP K 2] {F : List (Fin (Tag.rank .E6) → ℤ)}
    (hF : ∀ σ ∈ F, IsRoot .E6 σ) :
    ((e6Isogeny K (scFrame F) : adjointGroup .E6 K) : ModGL .E6 K) =
      (F.map fun σ => pinnedX .E6 K σ 1).prod := by
  rw [scFrame, map_list_prod, Subgroup.val_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun σ hσ => E6Pilot.coe_e6Isogeny_xm (hF σ hσ) 1

theorem e6ToE7_scFrame [Finite K] [CharP K 2] {F : List (Fin (Tag.rank .E6) → ℤ)}
    (hF : ∀ σ ∈ F, IsRoot .E6 σ) : e6ToE7 K (scFrame F) = uFrameElt K (F.map e6Embed) := by
  apply Subtype.ext
  rw [scFrame, map_list_prod, Subgroup.val_list_prod, coe_uFrameElt, List.map_map, List.map_map,
    List.map_map]
  congr 1
  refine List.map_congr_left fun σ hσ => ?_
  simp only [Function.comp_apply]
  rw [e6ToE7_xm (hF σ hσ), coe_e6LeviPar]

theorem e6Isogeny_eq_one_of_mem_center [Finite K] {z : e6Data_valid.minGroup K}
    (hz : z ∈ center (e6Data_valid.minGroup K)) : e6Isogeny K z = 1 := by
  have hzc : e6Isogeny K z ∈ center (adjointGroup .E6 K) := mem_center_iff.2 fun y => by
    obtain ⟨y', rfl⟩ := e6Isogeny_surjective K y
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz y']
  rw [center_adjointGroup_eq_bot, mem_bot] at hzc
  exact hzc

theorem exists_frame_of_mem_innerRepsE6 [Finite K] [CharP K 2] {r : adjointGroup .E6 K}
    (hr : r ∈ innerRepsE6 K) :
    ∃ F : List (Fin (Tag.rank .E6) → ℤ), (∀ σ ∈ F, IsRoot .E6 σ) ∧ IsUFrame (F.map e6Embed) ∧
      e6Isogeny K (scFrame F) = r := by
  have hrootY : ∀ σ ∈ oddDerivE6YFrame, IsRoot .E6 σ := fun σ hσ => by
    have h := isRoot_e7Restrict (IsUFrame.isRoot (Or.inr (Or.inl rfl)) (e6Embed σ)
      (by rw [uYFrame_eq]; exact List.mem_map_of_mem hσ)) (e6Embed_last σ)
    rwa [e7Restrict_e6Embed] at h
  have hrootZ : ∀ σ ∈ oddDerivE6ZFrame, IsRoot .E6 σ := fun σ hσ => by
    have h := isRoot_e7Restrict (IsUFrame.isRoot (Or.inr (Or.inr rfl)) (e6Embed σ)
      (by rw [uZFrame_eq]; exact List.mem_map_of_mem hσ)) (e6Embed_last σ)
    rwa [e7Restrict_e6Embed] at h
  simp only [innerRepsE6, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨[highRoot .E6], fun σ hσ => ?_, Or.inl (by rw [uTopRoot_eq]; rfl), Subtype.ext ?_⟩
    · rw [List.mem_singleton.1 hσ]
      exact isRoot_highRoot .E6
    · rw [coe_e6Isogeny_scFrame (fun σ hσ => by
        rw [List.mem_singleton.1 hσ]; exact isRoot_highRoot .E6)]
      simp
  · exact ⟨oddDerivE6YFrame, hrootY, Or.inr (Or.inl uYFrame_eq.symm),
      Subtype.ext (coe_e6Isogeny_scFrame hrootY)⟩
  · exact ⟨oddDerivE6ZFrame, hrootZ, Or.inr (Or.inr uZFrame_eq.symm),
      Subtype.ext (coe_e6Isogeny_scFrame hrootZ)⟩

theorem exists_conj_eq_uFrameElt [Finite K] [CharP K 2] {a : adjointGroup .E7 K}
    (ha : a ∈ e6Levi K) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) :
    ∃ d ∈ e6Levi K, ∃ T, IsUFrame T ∧ d * a * d⁻¹ = uFrameElt K T := by
  rw [← range_e6ToE7] at ha
  obtain ⟨s, rfl⟩ := ha
  have hker : (e6Isogeny K).ker ≤ center (e6Data_valid.minGroup K) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.LieType.CurtisTits.isQuasisimple_e6 K) (e6Isogeny_ne_one K)
  have hodd : ∀ z ∈ center (e6Data_valid.minGroup K), e6ToE7 K z ^ (Nat.card K - 1) = 1 :=
    fun z hz => by rw [← map_pow, pow_card_sub_one_eq_one_of_mem_center_e6 hz, map_one]
  have hs2 : s ^ 2 ∈ center (e6Data_valid.minGroup K) :=
    ker_e6ToE7_le_center (by rw [MonoidHom.mem_ker, map_pow, ha2])
  have hκ2 : e6Isogeny K s ^ 2 = 1 := by
    rw [← map_pow]
    exact e6Isogeny_eq_one_of_mem_center hs2
  have hκ1 : e6Isogeny K s ≠ 1 := fun h =>
    ha1 (eq_one_of_sq_eq_one_of_pow_odd ha2 odd_card_sub_one (hodd s (hker h)))
  obtain ⟨g, hg⟩ := exists_conj_mem_innerRepsE6 hκ2 hκ1
  obtain ⟨g', rfl⟩ := e6Isogeny_surjective K g
  obtain ⟨F, hFr, hFT, hFrep⟩ := exists_frame_of_mem_innerRepsE6 hg
  set z := (scFrame F)⁻¹ * (g' * s * g'⁻¹) with hz
  have hzc : z ∈ center (e6Data_valid.minGroup K) := hker (by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hFrep, map_mul, map_mul, map_inv,
      inv_mul_cancel])
  have hgs : g' * s * g'⁻¹ = scFrame F * z := by rw [hz, mul_inv_cancel_left]
  set ρ := e6ToE7 K (scFrame F) with hρ
  set ζ := e6ToE7 K z with hζ
  have hρ2 : ρ ^ 2 = 1 := by
    rw [hρ, e6ToE7_scFrame hFr]
    exact uFrameElt_sq hFT.isRoot hFT.pairwise
  have hcomm : ρ * ζ = ζ * ρ := by
    rw [hρ, hζ, ← map_mul, ← map_mul, (mem_center_iff.1 hzc (scFrame F)).symm]
  have hconj : e6ToE7 K g' * e6ToE7 K s * (e6ToE7 K g')⁻¹ = ρ * ζ := by
    have h := congrArg (e6ToE7 K) hgs
    simpa only [map_mul, map_inv] using h
  have hζ2 : ζ ^ 2 = 1 := by
    have h1 : (ρ * ζ) ^ 2 = 1 := by
      rw [← hconj]
      have e : (e6ToE7 K g' * e6ToE7 K s * (e6ToE7 K g')⁻¹) ^ 2 =
          e6ToE7 K g' * e6ToE7 K s ^ 2 * (e6ToE7 K g')⁻¹ := by
        simp only [pow_two]
        group
      rw [e, ha2, mul_one, mul_inv_cancel]
    rw [(Commute.mul_pow hcomm 2), hρ2, one_mul] at h1
    exact h1
  have hζ1 : ζ = 1 := eq_one_of_sq_eq_one_of_pow_odd hζ2 odd_card_sub_one (hodd z hzc)
  refine ⟨e6ToE7 K g', by rw [← range_e6ToE7]; exact ⟨g', rfl⟩, F.map e6Embed, hFT, ?_⟩
  rw [hconj, hζ1, mul_one, hρ, e6ToE7_scFrame hFr]

variable (K) in
@[expose] noncomputable def uRootElt : adjointGroup .E7 K :=
  e7RepConj K 3 * uFrameElt K [uTopRoot] * (e7RepConj K 3)⁻¹

theorem coe_uFrameElt_uTopRoot :
    (uFrameElt K [uTopRoot] : ModGL .E7 K) = pinnedX .E7 K uTopRoot 1 := by
  rw [coe_uFrameElt, List.map_singleton, List.prod_singleton]

theorem uRootElt_mem_uRootGroup : uRootElt K ∈ uRootGroup K :=
  ⟨uFrameElt K [uTopRoot], mem_subgroupOf.2 (by
    rw [coe_uFrameElt_uTopRoot]; exact mem_rootSubgroup.2 ⟨1, rfl⟩), rfl⟩

theorem card_commutator_radicalU_conj {c : adjointGroup .E7 K} (hc : c ∈ leviU K)
    (x : adjointGroup .E7 K) :
    Nat.card (⁅radicalU K, zpowers (c * e7RepConj K 3 * x * (c * e7RepConj K 3)⁻¹)⁆ :
        Subgroup (adjointGroup .E7 K)) =
      Nat.card (⁅parabolicRadical .E7 K uNodes, zpowers (x : ModGL .E7 K)⁆ :
        Subgroup (ModGL .E7 K)) := by
  set m := c * e7RepConj K 3
  have hz : zpowers (m * x * m⁻¹) = (zpowers x).map (MulAut.conj m).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [radicalU_eq_map_conj hc, hz, ← map_commutator,
    card_map_of_injective (MulAut.conj m).injective]
  have hQC : parabolicRadical .E7 K uNodes ≤ adjointGroup .E7 K :=
    (parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup
  have e : (⁅(parabolicRadical .E7 K uNodes).subgroupOf (adjointGroup .E7 K), zpowers x⁆).map
      (adjointGroup .E7 K).subtype =
        ⁅parabolicRadical .E7 K uNodes, zpowers (x : ModGL .E7 K)⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le hQC, MonoidHom.map_zpowers]
    rfl
  rw [← e, card_map_of_injective (adjointGroup .E7 K).subtype_injective]

theorem isRootElt_or_pow_nine_le_card_commutator [Finite K] [CharP K 2]
    {a : adjointGroup .E7 K} (ha : a ∈ leviU K) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) :
    (∃ c ∈ leviU K, a = c * uRootElt K * c⁻¹) ∨
      Nat.card K ^ 9 ≤ Nat.card (⁅radicalU K, zpowers a⁆ : Subgroup (adjointGroup .E7 K)) := by
  obtain ⟨a₀, ha₀, rfl⟩ := mem_e6LeviU_of_mem_leviU ha ha2
  set n := e7RepConj K 3 with hn
  have h2 : a₀ ^ 2 = 1 := by
    apply (MulAut.conj n).injective
    rw [map_pow, map_one]
    exact ha2
  have h1 : a₀ ≠ 1 := by
    rintro rfl
    exact ha1 (map_one _)
  obtain ⟨d, hd, T, hT, hdT⟩ := exists_conj_eq_uFrameElt ha₀ h2 h1
  set c := n * d⁻¹ * n⁻¹ with hcdef
  have hc : c ∈ leviU K := ⟨d⁻¹, e6Levi_le_parabolicLevi (inv_mem hd), rfl⟩
  have ha' : (MulAut.conj n).toMonoidHom a₀ = c * n * uFrameElt K T * (c * n)⁻¹ := by
    have e : a₀ = d⁻¹ * uFrameElt K T * d := by rw [← hdT]; group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hcdef]
    rw [e]
    group
  rcases hT with rfl | rfl | rfl
  · refine Or.inl ⟨c, hc, ?_⟩
    rw [ha', uRootElt, ← hn]
    group
  · refine Or.inr ?_
    rw [ha', card_commutator_radicalU_conj hc, coe_uFrameElt]
    exact pow_nine_le_card_commutator_frame (Or.inl rfl)
  · refine Or.inr ?_
    rw [ha', card_commutator_radicalU_conj hc, coe_uFrameElt]
    exact pow_nine_le_card_commutator_frame (Or.inr rfl)

theorem isRootElt_of_card_commutator_lt [Finite K] [CharP K 2] {a : adjointGroup .E7 K}
    (ha : a ∈ leviU K) (ha2 : orderOf a = 2)
    (hrk : Nat.card (⁅radicalU K, zpowers a⁆ : Subgroup (adjointGroup .E7 K)) <
      Nat.card K ^ 9) :
    ∃ c ∈ leviU K, a = c * uRootElt K * c⁻¹ := by
  have hsq : a ^ 2 = 1 := by rw [← ha2]; exact pow_orderOf_eq_one a
  have hne : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha2
    exact absurd ha2 (by decide)
  rcases isRootElt_or_pow_nine_le_card_commutator ha hsq hne with h | h
  · exact h
  · exact absurd h (not_le.2 hrk)

theorem exists_mem_leviURootSubgroups_of_card_commutator_lt [Finite K] [CharP K 2]
    {a : adjointGroup .E7 K} (ha : a ∈ leviU K) (ha2 : orderOf a = 2)
    (hrk : Nat.card (⁅radicalU K, zpowers a⁆ : Subgroup (adjointGroup .E7 K)) <
      Nat.card K ^ 9) :
    ∃ X ∈ leviURootSubgroups K, a ∈ X := by
  obtain ⟨c, hc, rfl⟩ := isRootElt_of_card_commutator_lt ha ha2 hrk
  exact ⟨_, ⟨c, hc, rfl⟩, ⟨uRootElt K, uRootElt_mem_uRootGroup, rfl⟩⟩

end Classes

end CFSG.SeitzReduction.E7Pilot
