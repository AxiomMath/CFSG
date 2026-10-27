module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Classes
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.F4Sec8

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.SeitzReduction
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open scoped commutatorElement

variable {K : Type} [Field K]

theorem eq_zero_or_eq_one_of_card_two (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  classical
  by_contra h
  rw [not_or] at h
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := Fintype.ofFinite K
  have h3 : ({0, 1, c} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm h.1]), Finset.card_pair (Ne.symm h.2)]
  have hle := Finset.card_le_univ ({0, 1, c} : Finset K)
  rw [h3, ← Nat.card_eq_fintype_card, hK] at hle
  omega

theorem torusGroup_eq_bot_of_card_two
    (hK : Nat.card K = 2) (τ : Tag) : torusGroup τ K = ⊥ := by
  rw [torusGroup, Subgroup.closure_eq_bot_iff]
  rintro _ ⟨⟨i, t⟩, rfl⟩
  have ht : t = 1 := Units.ext ((eq_zero_or_eq_one_of_card_two hK (t : K)).resolve_left t.ne_zero)
  subst ht
  show torusElt τ K i 1 ∈ ({1} : Set (ModGL τ K))
  rw [torusElt_one]
  exact Set.mem_singleton 1

theorem heightSeries_le_three
    {h : ℤ} (h3 : 3 ≤ h) : heightSeries .F4 K h ≤ heightSeries .F4 K 3 :=
  iSup₂_le fun α hα => le_iSup₂_of_le α ⟨hα.1, hα.2.1, h3.trans hα.2.2⟩ le_rfl

theorem mem_posUnipotent_of_commute_heightSeries
    (hK : Nat.card K = 2) {g : adjointGroup .F4 K}
    (hg : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ heightSeries .F4 K 3 → g * u = u * g) :
    (g : ModGL .F4 K) ∈ posUnipotent .F4 K := by
  have hB := mem_borelGroup_of_normalizes_heightSeries_F4 g.2 fun h h3 x hx => by
    have hx3 := heightSeries_le_three h3 hx
    have hxC : x ∈ adjointGroup .F4 K :=
      posUnipotent_le_adjointGroup (heightSeries_le_posUnipotent 3 hx3)
    have e := congrArg Subtype.val (hg ⟨x, hxC⟩ hx3)
    simp only [Subgroup.coe_mul] at e
    rw [e, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  rwa [borelGroup, torusGroup_eq_bot_of_card_two hK, bot_sup_eq] at hB


theorem exists_eq_of_mem_zx_of_posUnipotent
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) {x : adjointGroup .F4 K}
    (hU : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ posUnipotent .F4 K → u * x = x * u)
    {g : adjointGroup .F4 K} (hg : g ∈ zx x) :
    ∃ c d : K, f4x K 44 c * f4x K 47 d = (g : ModGL .F4 K) := by
  obtain ⟨-, hgz, -⟩ := hg
  have hcent : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ posUnipotent .F4 K →
      g * u = u * g := fun u hu => hgz u (mem_centralizer_singleton_iff.2 (hU u hu))
  have hgU := mem_posUnipotent_of_commute_heightSeries hK fun u hu =>
    hcent u (heightSeries_le_posUnipotent 3 hu)
  refine CFSG.Monster.B.GSide.f4_mem_of_commute_rootElts hgU fun p hp hp' => ?_
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val
    (hcent ⟨f4x K p 1, pinnedX_mem_adjointGroup _ _⟩ (f4x_mem_posUnipotent ⟨hp, hp'⟩ 1))

theorem weylElt_mem_cent_f4Rep
    [CharP K 2] {j p : ℕ} (hj : j < 4) (hp : p < 48) (hjp : f4CollRefl j p = p) :
    (⟨weylElt .F4 K (f4CollNode j) 1, weylElt_mem_adjointGroup _ 1⟩ : adjointGroup .F4 K) ∈
      cent (f4Rep K [p]) := by
  rw [mem_centralizer_singleton_iff]
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, coe_f4Rep_singleton]
  have h := weylElt_mul_f4x_mul_inv (K := K) hj hp 1
  rw [hjp] at h
  calc weylElt .F4 K (f4CollNode j) 1 * f4x K p 1 =
      (weylElt .F4 K (f4CollNode j) 1 * f4x K p 1 * (weylElt .F4 K (f4CollNode j) 1)⁻¹) *
        weylElt .F4 K (f4CollNode j) 1 := by group
    _ = f4x K p 1 * weylElt .F4 K (f4CollNode j) 1 := by rw [h]

theorem eq_zero_of_f4x_eq
    [Finite K] [CharP K 2] {k k' : ℕ} (hk : 24 ≤ k ∧ k ≤ 47) (hk' : 24 ≤ k' ∧ k' ≤ 47)
    (hne : k' ≠ k) (hh : height (orbitCertRoot .F4 k) ≤ height (orbitCertRoot .F4 k')) {c : K}
    (h : f4x K k c = f4x K k' c) : c = 0 := by
  have := congrArg (rootCoord (f4_isRoot_pos hk)) h
  rw [rootCoord_f4x hk hk le_rfl, rootCoord_f4x hk hk' hh, ite_eq_left rfl,
    ite_eq_right hne] at this
  exact this

theorem zx_t_subset
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    ∀ g ∈ zx (f4Rep K [47]), g = 1 ∨ g = f4Rep K [47] := by
  intro g hg
  have hU : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ posUnipotent .F4 K →
      u * f4Rep K [47] = f4Rep K [47] * u := fun u hu => Subtype.ext (by
    simp only [Subgroup.coe_mul, coe_f4Rep_singleton]
    exact f4x_central (Or.inr rfl) 1 hu)
  obtain ⟨c, d, hcd⟩ := exists_eq_of_mem_zx_of_posUnipotent hK hU hg
  have hn := weylElt_mem_cent_f4Rep (K := K) (j := 3) (p := 47) (by norm_num) (by norm_num) rfl
  have hgn := congrArg Subtype.val (hg.2.1 _ hn)
  simp only [Subgroup.coe_mul] at hgn
  have e44 := weylElt_mul_f4x_mul_inv (K := K) (j := 3) (p := 44) (by norm_num) (by norm_num) c
  have e47 := weylElt_mul_f4x_mul_inv (K := K) (j := 3) (p := 47) (by norm_num) (by norm_num) d
  rw [show f4CollRefl 3 44 = 43 from rfl] at e44
  rw [show f4CollRefl 3 47 = 47 from rfl] at e47
  have key : weylElt .F4 K (f4CollNode 3) 1 * (g : ModGL .F4 K) *
      (weylElt .F4 K (f4CollNode 3) 1)⁻¹ = g := by
    rw [← hgn, mul_assoc, mul_inv_cancel, mul_one]
  have hprod : weylElt .F4 K (f4CollNode 3) 1 * (f4x K 44 c * f4x K 47 d) *
      (weylElt .F4 K (f4CollNode 3) 1)⁻¹ =
      (weylElt .F4 K (f4CollNode 3) 1 * f4x K 44 c * (weylElt .F4 K (f4CollNode 3) 1)⁻¹) *
        (weylElt .F4 K (f4CollNode 3) 1 * f4x K 47 d * (weylElt .F4 K (f4CollNode 3) 1)⁻¹) := by
    group
  rw [e44, e47, hcd, key] at hprod
  have hconj : f4x K 43 c * f4x K 47 d = f4x K 44 c * f4x K 47 d := hprod.symm.trans hcd.symm
  have hc : c = 0 := eq_zero_of_f4x_eq ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    (by norm_num) (by decide +kernel) (mul_right_cancel hconj)
  subst hc
  rw [f4x_zero, one_mul] at hcd
  rcases eq_zero_or_eq_one_of_card_two hK d with rfl | rfl
  · exact Or.inl (Subtype.ext (by rw [← hcd, f4x_zero]; rfl))
  · exact Or.inr (Subtype.ext (by rw [← hcd, coe_f4Rep_singleton]))

theorem zx_u_subset
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    ∀ g ∈ zx (f4Rep K [44]), g = 1 ∨ g = f4Rep K [44] := by
  intro g hg
  have hU : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ posUnipotent .F4 K →
      u * f4Rep K [44] = f4Rep K [44] * u := fun u hu => Subtype.ext (by
    simp only [Subgroup.coe_mul, coe_f4Rep_singleton]
    exact f4x_central (Or.inl rfl) 1 hu)
  obtain ⟨c, d, hcd⟩ := exists_eq_of_mem_zx_of_posUnipotent hK hU hg
  have hn := weylElt_mem_cent_f4Rep (K := K) (j := 0) (p := 44) (by norm_num) (by norm_num) rfl
  have hgn := congrArg Subtype.val (hg.2.1 _ hn)
  simp only [Subgroup.coe_mul] at hgn
  have e44 := weylElt_mul_f4x_mul_inv (K := K) (j := 0) (p := 44) (by norm_num) (by norm_num) c
  have e47 := weylElt_mul_f4x_mul_inv (K := K) (j := 0) (p := 47) (by norm_num) (by norm_num) d
  rw [show f4CollRefl 0 44 = 44 from rfl] at e44
  rw [show f4CollRefl 0 47 = 46 from rfl] at e47
  have key : weylElt .F4 K (f4CollNode 0) 1 * (g : ModGL .F4 K) *
      (weylElt .F4 K (f4CollNode 0) 1)⁻¹ = g := by
    rw [← hgn, mul_assoc, mul_inv_cancel, mul_one]
  have hprod : weylElt .F4 K (f4CollNode 0) 1 * (f4x K 44 c * f4x K 47 d) *
      (weylElt .F4 K (f4CollNode 0) 1)⁻¹ =
      (weylElt .F4 K (f4CollNode 0) 1 * f4x K 44 c * (weylElt .F4 K (f4CollNode 0) 1)⁻¹) *
        (weylElt .F4 K (f4CollNode 0) 1 * f4x K 47 d * (weylElt .F4 K (f4CollNode 0) 1)⁻¹) := by
    group
  rw [e44, e47, hcd, key] at hprod
  have hconj : f4x K 44 c * f4x K 46 d = f4x K 44 c * f4x K 47 d := hprod.symm.trans hcd.symm
  have hd : d = 0 := eq_zero_of_f4x_eq ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    (by norm_num) (by decide +kernel) (mul_left_cancel hconj)
  subst hd
  rw [f4x_zero, mul_one] at hcd
  rcases eq_zero_or_eq_one_of_card_two hK c with rfl | rfl
  · exact Or.inl (Subtype.ext (by rw [← hcd, f4x_zero]; rfl))
  · exact Or.inr (Subtype.ext (by rw [← hcd, coe_f4Rep_singleton]))

theorem zx_tu_subset
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    ∀ g ∈ zx (f4Rep K [47, 44]),
      g = 1 ∨ g = f4Rep K [47] ∨ g = f4Rep K [44] ∨ g = f4Rep K [47, 44] := by
  intro g hg
  have hU : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ posUnipotent .F4 K →
      u * f4Rep K [47, 44] = f4Rep K [47, 44] * u := fun u hu => Subtype.ext (by
    simp only [Subgroup.coe_mul, coe_f4Rep, f4CollProd_cons, f4CollProd_nil, mul_one]
    rw [← mul_assoc, f4x_central (Or.inr rfl) 1 hu, mul_assoc, f4x_central (Or.inl rfl) 1 hu,
      mul_assoc])
  obtain ⟨c, d, hcd⟩ := exists_eq_of_mem_zx_of_posUnipotent hK hU hg
  have hcomm : f4x K 44 1 * f4x K 47 1 = f4x K 47 1 * f4x K 44 1 :=
    (commute_f4x_of_f4CollComm_eq_nil (K := K) (p := 44) (q := 47)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (fun _ => by decide) 1 1).eq
  rcases eq_zero_or_eq_one_of_card_two hK c with rfl | rfl <;>
    rcases eq_zero_or_eq_one_of_card_two hK d with rfl | rfl
  · exact Or.inl (Subtype.ext (by rw [← hcd, f4x_zero, f4x_zero, one_mul]; rfl))
  · exact Or.inr (Or.inl (Subtype.ext (by rw [← hcd, f4x_zero, one_mul, coe_f4Rep_singleton])))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by
      rw [← hcd, f4x_zero, mul_one, coe_f4Rep_singleton]))))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by
      rw [← hcd, coe_f4Rep, f4CollProd_pair, hcomm]))))


theorem height_three_mem_f4CentListV :
    ∀ p ∈ List.range' 24 24, 3 ≤ height (orbitCertRoot .F4 p) → p ∈ f4CentListV := by
  decide +kernel

theorem coe_f4Rep_v :
    (f4Rep K [41, 45] : ModGL .F4 K) = f4x K 41 1 * f4x K 45 1 := by
  simp [coe_f4Rep]

theorem f4x_mem_cent_v
    [CharP K 2] {p : ℕ} (hp : p ∈ f4CentListV) (d : K) :
    (⟨f4x K p d, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ cent (f4Rep K [41, 45]) := by
  rw [mem_centralizer_singleton_iff]
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, coe_f4Rep_v]
  exact f4x_commute_classV hp d

theorem heightSeries_three_le_cent_v
    [CharP K 2] {u : adjointGroup .F4 K} (hu : (u : ModGL .F4 K) ∈ heightSeries .F4 K 3) :
    u ∈ cent (f4Rep K [41, 45]) :=
  mem_of_mem_heightSeries_three_of_forall_f4x (fun p hp hp' h3 d =>
    f4x_mem_cent_v (height_three_mem_f4CentListV p (List.mem_range'_1.2 ⟨hp, by omega⟩) h3) d) hu

theorem weylElt_mem_cent_v
    [CharP K 2] {j : ℕ} (hj : j = 0 ∨ j = 3) :
    (⟨weylElt .F4 K (f4CollNode j) 1, weylElt_mem_adjointGroup _ 1⟩ : adjointGroup .F4 K) ∈
      cent (f4Rep K [41, 45]) := by
  rw [mem_centralizer_singleton_iff]
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, coe_f4Rep_v]
  have hj4 : j < 4 := by omega
  have e41 := weylElt_mul_f4x_mul_inv (K := K) hj4 (p := 41) (by norm_num) 1
  have e45 := weylElt_mul_f4x_mul_inv (K := K) hj4 (p := 45) (by norm_num) 1
  have r41 : f4CollRefl j 41 = 41 := by rcases hj with rfl | rfl <;> rfl
  have r45 : f4CollRefl j 45 = 45 := by rcases hj with rfl | rfl <;> rfl
  rw [r41] at e41
  rw [r45] at e45
  have h : weylElt .F4 K (f4CollNode j) 1 * (f4x K 41 1 * f4x K 45 1) *
      (weylElt .F4 K (f4CollNode j) 1)⁻¹ =
      (weylElt .F4 K (f4CollNode j) 1 * f4x K 41 1 * (weylElt .F4 K (f4CollNode j) 1)⁻¹) *
        (weylElt .F4 K (f4CollNode j) 1 * f4x K 45 1 * (weylElt .F4 K (f4CollNode j) 1)⁻¹) := by
    group
  rw [e41, e45] at h
  calc weylElt .F4 K (f4CollNode j) 1 * (f4x K 41 1 * f4x K 45 1) =
      (weylElt .F4 K (f4CollNode j) 1 * (f4x K 41 1 * f4x K 45 1) *
        (weylElt .F4 K (f4CollNode j) 1)⁻¹) * weylElt .F4 K (f4CollNode j) 1 := by group
    _ = f4x K 41 1 * f4x K 45 1 * weylElt .F4 K (f4CollNode j) 1 := by rw [h]

theorem zx_v_subset
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    ∀ g ∈ zx (f4Rep K [41, 45]),
      g = 1 ∨ g = f4Rep K [41] ∨ g = f4Rep K [45] ∨ g = f4Rep K [41, 45] := by
  intro g hg
  have hgz := hg.2.1
  have hgU := mem_posUnipotent_of_commute_heightSeries hK fun u hu =>
    hgz u (heightSeries_three_le_cent_v hu)
  obtain ⟨c, hc⟩ := exists_f4_coords hgU
  have htest : ∀ p ∈ f4CentListV, ⁅(f4PosList.map fun i => f4x K i (c i)).prod,
      ([p].map fun q => f4x K q ((fun _ => (1 : K)) q)).prod⁆ = 1 := fun p hp => by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← hc, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (hgz _ (f4x_mem_cent_v hp 1))
  have h0 := f4_coords_eq_zero_of_commute_classV c fun p hp => by
    have h := htest p (by revert p hp; decide)
    simpa using h
  have e18 : (f4KillOrderV ++ ([46, 43] : List ℕ)).take 18 = f4KillOrderV := by decide
  have hD18 : ∀ j ∈ (f4KillOrderV ++ ([46, 43] : List ℕ)).take 18, c j = 0 := fun j hj =>
    h0 j (e18 ▸ hj)
  have k46 : c 46 = 0 := by
    simpa using f4_row_of (f4KillOrderV ++ ([46, 43] : List ℕ)) c 18 hD18 (k := 47)
      (E := [(46, 1, 33, 1)]) (by decide +kernel) (htest 33 (by decide))
  have hD19 := f4_take_succ_of hD18 k46
  have k43 : c 43 = 0 := by
    simpa using f4_row_of (f4KillOrderV ++ ([46, 43] : List ℕ)) c 19 hD19 (k := 44)
      (E := [(43, 1, 24, 1)]) (by decide +kernel) (htest 24 (by decide))
  have hcover : ∀ i ∈ f4PosList, decide (i ∈ ([41, 44, 45, 47] : List ℕ)) = false →
      i ∈ f4KillOrderV ∨ i = 46 ∨ i = 43 := by
    decide
  have hg4 : (g : ModGL .F4 K) =
      f4x K 41 (c 41) * f4x K 44 (c 44) * f4x K 45 (c 45) * f4x K 47 (c 47) := by
    rw [hc, ← list_prod_map_filter_of_eq_one f4PosList
      (fun i => decide (i ∈ ([41, 44, 45, 47] : List ℕ))) _ (fun i hi hne => by
        rcases hcover i hi hne with h | rfl | rfl
        · rw [h0 i h, f4x_zero]
        · rw [k46, f4x_zero]
        · rw [k43, f4x_zero]),
      show f4PosList.filter (fun i => decide (i ∈ ([41, 44, 45, 47] : List ℕ))) =
        [41, 44, 45, 47] by decide]
    simp [mul_assoc]
  have hfix : ∀ j : ℕ, (j = 0 ∨ j = 3) → weylElt .F4 K (f4CollNode j) 1 * (g : ModGL .F4 K) *
      (weylElt .F4 K (f4CollNode j) 1)⁻¹ = g := fun j hj => by
    have hgn := congrArg Subtype.val (hgz _ (weylElt_mem_cent_v (K := K) hj))
    simp only [Subgroup.coe_mul] at hgn
    rw [← hgn, mul_assoc, mul_inv_cancel, mul_one]
  have hconj4 : ∀ j : ℕ, j < 4 → ∀ a b d e : K,
      weylElt .F4 K (f4CollNode j) 1 * (f4x K 41 a * f4x K 44 b * f4x K 45 d * f4x K 47 e) *
        (weylElt .F4 K (f4CollNode j) 1)⁻¹ =
      f4x K (f4CollRefl j 41) a * f4x K (f4CollRefl j 44) b * f4x K (f4CollRefl j 45) d *
        f4x K (f4CollRefl j 47) e := fun j hj a b d e => by
    rw [← weylElt_mul_f4x_mul_inv hj (by norm_num) a, ← weylElt_mul_f4x_mul_inv hj (by norm_num) b,
      ← weylElt_mul_f4x_mul_inv hj (by norm_num) d, ← weylElt_mul_f4x_mul_inv hj (by norm_num) e]
    group
  have k44 : c 44 = 0 := by
    have h := hconj4 3 (by norm_num) (c 41) (c 44) (c 45) (c 47)
    rw [← hg4, hfix 3 (Or.inr rfl), hg4, show f4CollRefl 3 41 = 41 from rfl,
      show f4CollRefl 3 44 = 43 from rfl, show f4CollRefl 3 45 = 45 from rfl,
      show f4CollRefl 3 47 = 47 from rfl] at h
    have h' := mul_left_cancel (mul_right_cancel (mul_right_cancel h))
    exact eq_zero_of_f4x_eq ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)
      (by decide +kernel) h'.symm
  have k47 : c 47 = 0 := by
    have h := hconj4 0 (by norm_num) (c 41) (c 44) (c 45) (c 47)
    rw [← hg4, hfix 0 (Or.inl rfl), hg4, show f4CollRefl 0 41 = 41 from rfl,
      show f4CollRefl 0 44 = 44 from rfl, show f4CollRefl 0 45 = 45 from rfl,
      show f4CollRefl 0 47 = 46 from rfl] at h
    have h' := mul_left_cancel h
    exact eq_zero_of_f4x_eq ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)
      (by decide +kernel) h'.symm
  rw [k44, k47, f4x_zero, f4x_zero, mul_one, mul_one] at hg4
  have h41 : f4Rep K [41] = ⟨f4x K 41 1, pinnedX_mem_adjointGroup _ _⟩ :=
    Subtype.ext (coe_f4Rep_singleton 41)
  have h45 : f4Rep K [45] = ⟨f4x K 45 1, pinnedX_mem_adjointGroup _ _⟩ :=
    Subtype.ext (coe_f4Rep_singleton 45)
  rcases eq_zero_or_eq_one_of_card_two hK (c 41) with h1 | h1 <;>
    rcases eq_zero_or_eq_one_of_card_two hK (c 45) with h2 | h2 <;> rw [h1, h2] at hg4
  · exact Or.inl (Subtype.ext (by rw [hg4, f4x_zero, f4x_zero, one_mul]; rfl))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by rw [hg4, f4x_zero, one_mul, h45]))))
  · exact Or.inr (Or.inl (Subtype.ext (by rw [hg4, f4x_zero, mul_one, h41])))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by rw [hg4, coe_f4Rep_v]))))

section Clause

variable {C : Type*} [Group C]

theorem card_zx_le_of_subset [Finite C] {x : C} (S : Finset C)
    (h : ∀ g ∈ zx x, g ∈ S) : Nat.card (zx x) ≤ S.card := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun g hg => h g hg) S.finite_toSet

theorem hz2_clause_of_isConj [Finite C] {reps : List C} {x x' : C} (hxx' : IsConj x x')
    (h : Nat.card (zx x) < 4 ∨ (Nat.card (zx x) ≤ 4 ∧
      ∃ w ∈ zx x, w ≠ 1 ∧ ∃ y ∈ reps, IsConj y w ∧ Nat.card (zx y) < 4)) :
    Nat.card (zx x') < 4 ∨ (Nat.card (zx x') ≤ 4 ∧
      ∃ w ∈ zx x', w ≠ 1 ∧ ∃ y ∈ reps, IsConj y w ∧ Nat.card (zx y) < 4) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hxx'
  rw [card_zx_conj]
  refine h.imp id fun ⟨h4, w, hw, hw1, y, hy, hyw, hy4⟩ => ⟨h4, c * w * c⁻¹, ?_, ?_, y, hy, ?_, hy4⟩
  · rw [zx_conj]
    exact ⟨w, hw, rfl⟩
  · intro h1
    apply hw1
    calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group
  · exact hyw.trans (isConj_iff.2 ⟨c, rfl⟩)

end Clause

theorem f4Rep_singleton_ne_one
    (p : ℕ) : f4Rep K [p] ≠ 1 := fun h => by
  have h1 := congrArg Subtype.val h
  rw [coe_f4Rep_singleton, Subgroup.coe_one, f4x, ← pinnedX_zero (τ := .F4) (R := K)
    (α := orbitCertRoot .F4 p)] at h1
  exact one_ne_zero (pinnedX_injective .F4 K _ h1)

theorem hz2_levi
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    ∀ x ∈ [f4Rep K [32], f4Rep K [31], f4Rep K [32, 31], f4Rep K [28, 32]],
      Nat.card (zx x) < 4 ∨ (Nat.card (zx x) ≤ 4 ∧ ∃ w ∈ zx x, w ≠ 1 ∧
        ∃ y ∈ [f4Rep K [32], f4Rep K [31], f4Rep K [32, 31], f4Rep K [28, 32]],
          IsConj y w ∧ Nat.card (zx y) < 4) := by
  classical
  have : Finite (adjointGroup .F4 K) := Subtype.finite (α := ModGL .F4 K) (p := (· ∈ _))
  obtain ⟨c₁, c₂, c₃, c₄⟩ := isConj_f4Rep_levi (K := K)
  have ht : Nat.card (zx (f4Rep K [47])) ≤ 2 := by
    refine (card_zx_le_of_subset {1, f4Rep K [47]} fun g hg => ?_).trans (Finset.card_le_two)
    rcases zx_t_subset hK g hg with rfl | rfl <;> simp
  have hu : Nat.card (zx (f4Rep K [44])) ≤ 2 := by
    refine (card_zx_le_of_subset {1, f4Rep K [44]} fun g hg => ?_).trans (Finset.card_le_two)
    rcases zx_u_subset hK g hg with rfl | rfl <;> simp
  have ht' : Nat.card (zx (f4Rep K [32])) < 4 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 c₁
    rw [← hc, card_zx_conj]
    omega
  have c₅ : IsConj (f4Rep K [47]) (f4Rep K [45]) := by
    have h := f4CollWeylElt_conj_prod (K := K) (ω := [1, 0]) (by decide) [47] (by decide)
    rw [show ([47] : List ℕ).map (f4CollWeylPerm [1, 0]) = [45] by decide] at h
    exact isConj_iff.2 ⟨⟨f4CollWeylElt K [1, 0], f4CollWeylElt_mem _⟩, Subtype.ext h⟩
  have hmem : f4Rep K [32] ∈ [f4Rep K [32], f4Rep K [31], f4Rep K [32, 31], f4Rep K [28, 32]] :=
    List.mem_cons_self
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Or.inl ht'
  · refine Or.inl ?_
    obtain ⟨c, hc⟩ := isConj_iff.1 c₂
    rw [← hc, card_zx_conj]
    omega
  ·
    refine hz2_clause_of_isConj c₃ ?_
    by_cases htz : f4Rep K [47] ∈ zx (f4Rep K [47, 44])
    · refine Or.inr ⟨(card_zx_le_of_subset {1, f4Rep K [47], f4Rep K [44], f4Rep K [47, 44]}
        fun g hg => ?_).trans (Finset.card_le_four), f4Rep K [47], htz,
        f4Rep_singleton_ne_one 47, f4Rep K [32], hmem, c₁.symm, ht'⟩
      rcases zx_tu_subset hK g hg with rfl | rfl | rfl | rfl <;> simp
    · refine Or.inl (lt_of_le_of_lt (card_zx_le_of_subset {1, f4Rep K [44], f4Rep K [47, 44]}
        fun g hg => ?_) (lt_of_le_of_lt Finset.card_le_three (by norm_num)))
      rcases zx_tu_subset hK g hg with rfl | rfl | rfl | rfl
      · simp
      · exact absurd hg htz
      · simp
      · simp
  ·
    refine hz2_clause_of_isConj c₄ ?_
    by_cases hwz : f4Rep K [45] ∈ zx (f4Rep K [41, 45])
    · refine Or.inr ⟨(card_zx_le_of_subset {1, f4Rep K [41], f4Rep K [45], f4Rep K [41, 45]}
        fun g hg => ?_).trans (Finset.card_le_four), f4Rep K [45], hwz,
        f4Rep_singleton_ne_one 45, f4Rep K [32], hmem, c₁.symm.trans c₅, ht'⟩
      rcases zx_v_subset hK g hg with rfl | rfl | rfl | rfl <;> simp
    · refine Or.inl (lt_of_le_of_lt (card_zx_le_of_subset {1, f4Rep K [41], f4Rep K [41, 45]}
        fun g hg => ?_) (lt_of_le_of_lt Finset.card_le_three (by norm_num)))
      rcases zx_v_subset hK g hg with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact absurd hg hwz
      · simp

end CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
