module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassReps

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open scoped commutatorElement

variable {K : Type} [Field K]

local instance f4ClassRepsNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

namespace ClassReps

theorem commutator_subgroupOf_of_le {G : Type*} [Group G] {H C : Subgroup G} (hHC : H ≤ C) :
    ⁅H.subgroupOf C, H.subgroupOf C⁆ = (⁅H, H⁆).subgroupOf C := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hHC,
    Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_self H).trans hHC)]

@[expose] def lambdaVList : List ℕ := f4CentListV ++ [14, 23]

@[expose] def lambdaVRoots : Set (Fin Tag.F4.rank → ℤ) :=
  {γ | ∃ p ∈ lambdaVList, orbitCertRoot .F4 p = γ}

theorem lambdaV_check :
    (∀ p ∈ lambdaVList, p < 48) ∧
      f4CollWeylPerm [0, 3] 14 = 33 ∧ f4CollWeylPerm [0, 3] 23 = 24 ∧
      f4CollWeylPerm [0, 3] 41 = 41 ∧ f4CollWeylPerm [0, 3] 45 = 45 ∧
      (∀ p ∈ lambdaVList, p ≠ 41 → p ≠ 45 →
        f4Pairing (fun j => Tag.cartan .F4 0 j) (orbitCertRoot .F4 p) ∈ [1, -1, 2, -2] ∨
          f4Pairing (fun j => Tag.cartan .F4 3 j) (orbitCertRoot .F4 p) ∈ [1, -1, 2, -2]) := by
  decide +kernel

theorem orbitCertRoot_33_14_24_23 :
    orbitCertRoot .F4 33 = Pi.single 0 1 ∧ orbitCertRoot .F4 14 = -Pi.single 0 1 ∧
      orbitCertRoot .F4 24 = Pi.single 3 1 ∧ orbitCertRoot .F4 23 = -Pi.single 3 1 :=
  ⟨List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel)⟩

section Basic


variable (K) in
@[expose] noncomputable def lambdaV : Subgroup (ModGL .F4 K) := rootSpan .F4 K lambdaVRoots

theorem f4x_mem_lambdaV {p : ℕ} (hp : p ∈ lambdaVList) (c : K) : f4x K p c ∈ lambdaV K :=
  pinnedX_mem_rootSpan (S := lambdaVRoots) (α := orbitCertRoot .F4 p) ⟨p, hp, rfl⟩ c

theorem lambdaV_le_adjointGroup : lambdaV K ≤ adjointGroup .F4 K := by
  rw [lambdaV, rootSpan_eq_closure, closure_le]
  rintro _ ⟨β, -, d, rfl⟩
  exact pinnedX_mem_adjointGroup _ _

theorem pinnedX_mem_commutator_of_conj_self {Q : Subgroup (ModGL .F4 K)} {h : ModGL .F4 K}
    (hh : h ∈ Q)
    {γ : Fin Tag.F4.rank → ℤ} {l : K} (hl : l ≠ 1)
    (hconj : ∀ e : K, h * pinnedX .F4 K γ e * h⁻¹ = pinnedX .F4 K γ (l * e))
    (hγ : ∀ e : K, pinnedX .F4 K γ e ∈ Q) (c : K) : pinnedX .F4 K γ c ∈ ⁅Q, Q⁆ := by
  have hl' : l - 1 ≠ 0 := sub_ne_zero.2 hl
  have e : ⁅h, pinnedX .F4 K γ (c / (l - 1))⁆ = pinnedX .F4 K γ c := by
    rw [commutatorElement_def, hconj, pinnedX_neg, ← pinnedX_add]
    congr 1
    field_simp
    ring
  rw [← e]
  exact commutator_mem_commutator hh (hγ _)

theorem torusElt_mem_lambdaV {i : Fin Tag.F4.rank} (hi : i = 0 ∨ i = 3) (w : Kˣ) :
    torusElt .F4 K i w ∈ lambdaV K := by
  obtain ⟨h33, h14, h24, h23⟩ := orbitCertRoot_33_14_24_23
  have hpos : Pi.single i 1 ∈ lambdaVRoots := by
    rcases hi with rfl | rfl
    · exact ⟨33, by decide, h33⟩
    · exact ⟨24, by decide, h24⟩
  have hneg : -Pi.single i 1 ∈ lambdaVRoots := by
    rcases hi with rfl | rfl
    · exact ⟨14, by decide, h14⟩
    · exact ⟨23, by decide, h23⟩
  have hx : ∀ c : K, xUnit .F4 K i c ∈ lambdaV K := fun c => by
    rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan hpos c
  have hy : ∀ c : K, yUnit .F4 K i c ∈ lambdaV K := fun c => by
    rw [← pinnedX_neg_single]
    exact pinnedX_mem_rootSpan hneg c
  have hw : ∀ t : Kˣ, weylElt .F4 K i t ∈ lambdaV K := fun t => by
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  have e : torusElt .F4 K i w = weylElt .F4 K i w * (weylElt .F4 K i 1)⁻¹ :=
    eq_mul_inv_of_mul_eq (weylElt_eq_torusElt_mul_weylElt_one i w).symm
  rw [e]
  exact mul_mem (hw w) (inv_mem (hw 1))

end Basic

section TorusConj


theorem torusElt_conj_pinnedX (i : Fin Tag.F4.rank) (w : Kˣ) {γ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot .F4 γ) (e : K) :
    torusElt .F4 K i w * pinnedX .F4 K γ e * (torusElt .F4 K i w)⁻¹ =
      pinnedX .F4 K γ (((w ^ f4Pairing (fun j => Tag.cartan .F4 i j) γ : Kˣ) : K) * e) := by
  rw [torusElt_eq_rootDiagUnit, rootDiagUnit_conj_pinnedX _ hγ, rootChar_zpow]

end TorusConj


theorem f4x_commute_classV_of_weyl [CharP K 2] {p : ℕ} (hp : p < 48)
    (hq : f4CollWeylPerm [0, 3] p ∈ f4CentListV) (d : K) :
    f4x K p d * (f4x K 41 1 * f4x K 45 1) = (f4x K 41 1 * f4x K 45 1) * f4x K p d := by
  have hω : ∀ j ∈ ([0, 3] : List ℕ), j < 4 := by decide
  obtain ⟨-, -, -, p41, p45, -⟩ := lambdaV_check
  set n := f4CollWeylElt K [0, 3]
  have hx := (f4CollWeylElt_conj (K := K) [0, 3] hω hp d).1
  have h41 := (f4CollWeylElt_conj (K := K) [0, 3] hω (p := 41) (by norm_num) 1).1
  have h45 := (f4CollWeylElt_conj (K := K) [0, 3] hω (p := 45) (by norm_num) 1).1
  rw [p41] at h41
  rw [p45] at h45
  have hc := f4x_commute_classV hq d
  have hv : n * (f4x K 41 1 * f4x K 45 1) * n⁻¹ = f4x K 41 1 * f4x K 45 1 :=
    calc n * (f4x K 41 1 * f4x K 45 1) * n⁻¹ =
          (n * f4x K 41 1 * n⁻¹) * (n * f4x K 45 1 * n⁻¹) := by group
      _ = f4x K 41 1 * f4x K 45 1 := by rw [h41, h45]
  calc f4x K p d * (f4x K 41 1 * f4x K 45 1) =
        n⁻¹ * ((n * f4x K p d * n⁻¹) * (n * (f4x K 41 1 * f4x K 45 1) * n⁻¹)) * n := by group
    _ = n⁻¹ * (f4x K (f4CollWeylPerm [0, 3] p) d * (f4x K 41 1 * f4x K 45 1)) * n := by
        rw [hx, hv]
    _ = n⁻¹ * ((f4x K 41 1 * f4x K 45 1) * f4x K (f4CollWeylPerm [0, 3] p) d) * n := by rw [hc]
    _ = n⁻¹ * ((n * (f4x K 41 1 * f4x K 45 1) * n⁻¹) * (n * f4x K p d * n⁻¹)) * n := by
        rw [hx, hv]
    _ = (f4x K 41 1 * f4x K 45 1) * f4x K p d := by group

theorem lambdaV_le_centralizer [CharP K 2] :
    lambdaV K ≤ centralizer ({f4x K 41 1 * f4x K 45 1} : Set (ModGL .F4 K)) := by
  rw [lambdaV, rootSpan_eq_closure, closure_le]
  rintro _ ⟨β, ⟨p, hp, rfl⟩, d, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  change f4x K p d * _ = _ * f4x K p d
  obtain ⟨hlt, p14, p23, -, -, -⟩ := lambdaV_check
  rcases List.mem_append.1 hp with hp | hp
  · exact f4x_commute_classV hp d
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact f4x_commute_classV_of_weyl (by norm_num) (by rw [p14]; decide) d
    · exact f4x_commute_classV_of_weyl (by norm_num) (by rw [p23]; decide) d

theorem commutator_lambdaV [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅lambdaV K, lambdaV K⁆ = lambdaV K := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  obtain ⟨c₀, hc₀0, hc₀1⟩ : ∃ c₀ : K, c₀ ≠ 0 ∧ c₀ ≠ 1 := by
    by_contra hcon'
    have hcon : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by_contra fun h => hcon' ⟨x, hx, h⟩
    have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
      intro x
      by_cases hx : x = 0
      · exact ⟨false, by simp [hx]⟩
      · exact ⟨true, by simp [hcon x hx]⟩
    have hle := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hle
    omega
  set w : Kˣ := Units.mk0 c₀ hc₀0
  have hw : w ≠ 1 := fun h => hc₀1 (by simpa [w] using congrArg Units.val h)
  obtain ⟨hlt, -, -, -, -, hpair⟩ := lambdaV_check
  have hgen : ∀ p ∈ lambdaVList, ∀ c : K, f4x K p c ∈ lambdaV K := fun p hp c =>
    f4x_mem_lambdaV hp c
  have htorus : ∀ p ∈ lambdaVList, p ≠ 41 → p ≠ 45 → ∀ c : K,
      f4x K p c ∈ ⁅lambdaV K, lambdaV K⁆ := by
    intro p hp h41 h45 c
    have hroot : IsRoot .F4 (orbitCertRoot .F4 p) :=
      isRoot_decodeVec_witness (by rw [show Tag.F4.witnesses.roots.length = 48 from rfl]
                                   exact hlt p hp)
    have hstep : ∀ i : Fin Tag.F4.rank, (i = 0 ∨ i = 3) →
        f4Pairing (fun j => Tag.cartan .F4 i j) (orbitCertRoot .F4 p) ∈ [1, -1, 2, -2] →
        f4x K p c ∈ ⁅lambdaV K, lambdaV K⁆ := by
      intro i hi hmem
      refine pinnedX_mem_commutator_of_conj_self (torusElt_mem_lambdaV hi w) ?_
        (fun e => torusElt_conj_pinnedX i w hroot e) (fun e => hgen p hp e) c
      rw [Ne, Units.val_eq_one]
      refine zpow_ne_one_of_charTwo hw ?_
      simpa using hmem
    rcases hpair p hp h41 h45 with h | h
    · exact hstep 0 (Or.inl rfl) h
    · exact hstep 3 (Or.inr rfl) h
  have hcomm : ∀ {i j k : ℕ}, i ∈ lambdaVList → j ∈ lambdaVList → (24 ≤ i ∧ i ≤ 47) →
      (24 ≤ j ∧ j ≤ 47) → i ≠ j →
      (f4OddCommutatorFactors.lookup (i, j)).getD [] = [(1, 1, k)] → ∀ c : K,
      f4x K k c ∈ ⁅lambdaV K, lambdaV K⁆ := by
    intro i j k hi hj hi' hj' hij hl c
    have h := f4x_commutator_eq (K := K) hi' hj' hij 1 c
    rw [hl] at h
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
      one_mul, pow_one] at h
    rw [← h]
    exact commutator_mem_commutator (hgen i hi 1) (hgen j hj c)
  conv_lhs => rw [lambdaV, rootSpan_eq_closure]
  rw [closure_le]
  rintro _ ⟨β, ⟨p, hp, rfl⟩, d, rfl⟩
  rw [SetLike.mem_coe]
  change f4x K p d ∈ _
  by_cases h41 : p = 41
  · subst h41
    exact hcomm (i := 29) (j := 35) (by decide) (by decide) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num) (by decide +kernel) d
  by_cases h45 : p = 45
  · subst h45
    exact hcomm (i := 32) (j := 37) (by decide) (by decide) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num) (by decide +kernel) d
  exact htorus p hp h41 h45 d

end ClassReps

section FactF4b


open ClassReps

theorem factF4b [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) : FactF4b K := by
  set n : ModGL .F4 K := f4CollWeylElt K weylWordV with hn
  have hnC : n ∈ adjointGroup .F4 K := f4CollWeylElt_mem _
  set Q : Subgroup (ModGL .F4 K) := (lambdaV K).map (MulAut.conj n).toMonoidHom with hQ
  have hQC : Q ≤ adjointGroup .F4 K := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hnC (lambdaV_le_adjointGroup hx)) (inv_mem hnC)
  have hQQ : ⁅Q, Q⁆ = Q := by
    rw [hQ, ← Subgroup.map_commutator, commutator_lambdaV hq]
  have hyV : ((yV K : adjointGroup .F4 K) : ModGL .F4 K) =
      n * (f4x K 41 1 * f4x K 45 1) * n⁻¹ := by
    have h := congrArg Subtype.val (weylEltC_conj_frame (K := K)).2.2.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h.symm
  refine ⟨Q.subgroupOf (adjointGroup .F4 K), ?_, ?_, ?_⟩
  · rw [commutator_subgroupOf_of_le hQC, hQQ]
  · rw [Subgroup.mem_subgroupOf, hyV]
    exact ⟨_, mul_mem (f4x_mem_lambdaV (by decide) 1) (f4x_mem_lambdaV (by decide) 1), rfl⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [hyV, ← hyx]
    have hc := mem_centralizer_singleton_iff.1 (lambdaV_le_centralizer hy)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc n * y * n⁻¹ * (n * (f4x K 41 1 * f4x K 45 1) * n⁻¹) =
          n * (y * (f4x K 41 1 * f4x K 45 1)) * n⁻¹ := by group
      _ = n * ((f4x K 41 1 * f4x K 45 1) * y) * n⁻¹ := by rw [hc]
      _ = n * (f4x K 41 1 * f4x K 45 1) * n⁻¹ * (n * y * n⁻¹) := by group

end FactF4b

end CFSG.SeitzReduction.F4Pilot
