module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.Models.Blueprint
public import CFSG.RankThree.GF2n.Stroth80.GriessLinear
public import CFSG.CharacterTheory.Burnside
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPositive
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise
open CFSG.Blueprint (LieModel)
open CFSG.Quasithin (perfectCore)
open CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K] {r : ℕ}

@[expose] noncomputable def rankOneParabolic (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  Subgroup.closure ((borel r K : Set _) ∪ {weylElt r K i})

theorem borel_le_rankOneParabolic (r : ℕ) (i : Fin r) :
    borel r K ≤ rankOneParabolic K r i :=
  fun _ hb => Subgroup.subset_closure (Or.inl hb)

theorem weylElt_mem_rankOneParabolic (r : ℕ) (i : Fin r) :
    weylElt r K i ∈ rankOneParabolic K r i :=
  Subgroup.subset_closure (Or.inr rfl)

@[expose] noncomputable def rankOneRootSup (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  rootSubgroup r K (simpleRoot r i) ⊔ rootSubgroup r K (-simpleRoot r i)

@[expose] noncomputable def rankOneA (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  rankOneRootSup K r i ⊔ unipotentExcept r K i

theorem rootSubgroup_simpleRoot_le_rankOneRootSup (i : Fin r) :
    rootSubgroup r K (simpleRoot r i) ≤ rankOneRootSup K r i :=
  le_sup_left

theorem rootSubgroup_neg_le_rankOneRootSup (i : Fin r) :
    rootSubgroup r K (-simpleRoot r i) ≤ rankOneRootSup K r i :=
  le_sup_right

theorem rankOneRootSup_le_rankOneA (i : Fin r) :
    rankOneRootSup K r i ≤ rankOneA K r i :=
  le_sup_left

theorem unipotentExcept_le_rankOneA (i : Fin r) :
    unipotentExcept r K i ≤ rankOneA K r i :=
  le_sup_right

theorem rootSubgroup_simpleRoot_le_rankOneA (i : Fin r) :
    rootSubgroup r K (simpleRoot r i) ≤ rankOneA K r i :=
  (rootSubgroup_simpleRoot_le_rankOneRootSup (K := K) i).trans
    (rankOneRootSup_le_rankOneA (K := K) i)

theorem rootSubgroup_neg_le_rankOneA (i : Fin r) :
    rootSubgroup r K (-simpleRoot r i) ≤ rankOneA K r i :=
  (rootSubgroup_neg_le_rankOneRootSup (K := K) i).trans
    (rankOneRootSup_le_rankOneA (K := K) i)

theorem rootSubgroup_simpleRoot_le_rankOneParabolic (hr : 2 ≤ r) (i : Fin r) :
    rootSubgroup r K (simpleRoot r i) ≤ rankOneParabolic K r i :=
  le_trans (rootSubgroup_le_unipotent (simpleRoot_mem_posRoots hr i))
    (le_trans unipotent_le_borel (borel_le_rankOneParabolic r i))

theorem rootSubgroup_neg_simpleRoot_le_rankOneParabolic (hr : 2 ≤ r) (i : Fin r) :
    rootSubgroup r K (-simpleRoot r i) ≤ rankOneParabolic K r i := by
  have hα : simpleRoot r i ∈ roots r := posRoots_subset_roots (simpleRoot_mem_posRoots hr i)
  have hmap := map_conj_rootSubgroup_torusWeyl hr
    (⟨weylElt r K i, weylElt_mem_torusWeyl i⟩ : torusWeyl r K) hα
  rw [torusWeylNu_weylElt hr i, simpleRefl_simpleRoot hr i] at hmap
  rw [← hmap]
  rintro x ⟨y, hy, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact mul_mem (mul_mem (weylElt_mem_rankOneParabolic r i)
    (rootSubgroup_simpleRoot_le_rankOneParabolic hr i hy))
    (inv_mem (weylElt_mem_rankOneParabolic r i))

theorem unipotentExcept_le_rankOneParabolic (i : Fin r) :
    unipotentExcept r K i ≤ rankOneParabolic K r i :=
  le_trans (unipotentExcept_le_unipotent i)
    (le_trans unipotent_le_borel (borel_le_rankOneParabolic r i))

theorem etaLin_range_le_rootSubgroup_sup {i : Fin r} {a b : Fin r ⊕ Fin r}
    (hab : coordIdx a ≠ coordIdx b)
    (h1 : ∀ t : K, rootElt r K (simpleRoot r i) t = rpElt a b t)
    (h2 : ∀ t : K, rootElt r K (-simpleRoot r i) t = rpElt b a t) :
    (etaLin hab).range ≤
      rootSubgroup r K (simpleRoot r i) ⊔ rootSubgroup r K (-simpleRoot r i) := by
  rw [MonoidHom.range_eq_map,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  obtain ⟨p, q, hpq, c⟩ := t
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases p <;> fin_cases q
  · exact absurd rfl hpq
  · rw [etaLin_of_upper hab (coe_transvection_zero_one hpq c)]
    have hmem := rootElt_mem_rootSubgroup (r := r) (K := K) (simpleRoot r i) c
    rw [h1 c] at hmem
    exact Subgroup.mem_sup_left hmem
  · rw [etaLin_of_lower hab (coe_transvection_one_zero hpq c)]
    have hmem := rootElt_mem_rootSubgroup (r := r) (K := K) (-simpleRoot r i) c
    rw [h2 c] at hmem
    exact Subgroup.mem_sup_right hmem
  · exact absurd rfl hpq

theorem rootSubgroup_sup_eq_etaLin_range (hr : 2 ≤ r) (i : Fin r) {a b : Fin r ⊕ Fin r}
    (hab : coordIdx a ≠ coordIdx b)
    (h1 : ∀ t : K, rootElt r K (simpleRoot r i) t = rpElt a b t)
    (h2 : ∀ t : K, rootElt r K (-simpleRoot r i) t = rpElt b a t) :
    rootSubgroup r K (simpleRoot r i) ⊔ rootSubgroup r K (-simpleRoot r i) =
      (etaLin hab).range := by
  refine le_antisymm ?_ (etaLin_range_le_rootSubgroup_sup hab h1 h2)
  refine sup_le ?_ ?_
  · rintro _ ⟨t, rfl⟩
    refine ⟨SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t, ?_⟩
    rw [etaLin_of_upper hab (coe_transvection_zero_one (show (0 : Fin 2) ≠ 1 by decide) t)]
    exact (h1 t).symm
  · rintro _ ⟨t, rfl⟩
    refine ⟨SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t, ?_⟩
    rw [etaLin_of_lower hab (coe_transvection_one_zero (show (1 : Fin 2) ≠ 0 by decide) t)]
    exact (h2 t).symm

theorem isPerfect_rootSubgroup_sup_simpleRoot (hr : 2 ≤ r) (i : Fin r) [CharP K 2]
    (h4 : ∃ s : Finset K, s.card = 4) :
    Group.IsPerfect ↥(rootSubgroup r K (simpleRoot r i) ⊔
      rootSubgroup r K (-simpleRoot r i)) := by
  have hα : simpleRoot r i ∈ roots r := posRoots_subset_roots (simpleRoot_mem_posRoots hr i)
  obtain ⟨a, b, hab, -, h1, h2⟩ := exists_rootElt_eq_rpElt (K := K) hα
  rw [rootSubgroup_sup_eq_etaLin_range hr i hab h1 h2]
  haveI : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  exact Group.IsPerfect.range (etaLin hab)

theorem isSolvable_sl2_F2 [Finite K] (hK : Nat.card K = 2) :
    Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (SpecialLinearGroup (Fin 2) K) := Fintype.ofFinite _
  have hcard : Fintype.card (SpecialLinearGroup (Fin 2) K) = 2 ^ 1 * 3 ^ 1 := by
    rw [← Nat.card_eq_fintype_card, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  exact Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num) hcard

theorem isSolvable_etaLin_range_F2 [Finite K] (hK : Nat.card K = 2)
    {a b : Fin r ⊕ Fin r} (hab : coordIdx a ≠ coordIdx b) :
    Group.IsSolvable ↥(etaLin (k := K) hab).range := by
  haveI : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := isSolvable_sl2_F2 hK
  exact Group.isSolvable_of_surjective (f := (etaLin (k := K) hab).rangeRestrict)
    (etaLin (k := K) hab).rangeRestrict_surjective

theorem isSolvable_rankOneRootSup_F2 (hr : 2 ≤ r) (i : Fin r) [CharP K 2] [Finite K]
    (hK : Nat.card K = 2) :
    Group.IsSolvable ↥(rankOneRootSup K r i) := by
  have hα : simpleRoot r i ∈ roots r := posRoots_subset_roots (simpleRoot_mem_posRoots hr i)
  obtain ⟨a, b, hab, -, h1, h2⟩ := exists_rootElt_eq_rpElt (K := K) hα
  rw [rankOneRootSup, rootSubgroup_sup_eq_etaLin_range hr i hab h1 h2]
  exact isSolvable_etaLin_range_F2 hK hab

theorem isPGroup_unipotent [Finite K] [CharP K 2] :
    IsPGroup 2 ↥(unipotent r K) := by
  let _ := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hm' : Nat.card K = 2 ^ (m : ℕ) := by rwa [← Nat.card_eq_fintype_card] at hm
  refine IsPGroup.of_card (n := (m : ℕ) * (r * (r - 1))) ?_
  rw [unipotent_eq_posUnip, card_posUnip, hm', ← pow_mul]

theorem isPGroup_unipotentExcept [Finite K] [CharP K 2] (i : Fin r) :
    IsPGroup 2 ↥(unipotentExcept r K i) :=
  (isPGroup_unipotent (K := K) (r := r)).of_injective
    (Subgroup.inclusion (unipotentExcept_le_unipotent i))
    (Subgroup.inclusion_injective _)

theorem rootSubgroup_sup_le_Hinf_rankOneParabolic (hr : 2 ≤ r) (i : Fin r) [CharP K 2]
    (h4 : ∃ s : Finset K, s.card = 4) :
    rootSubgroup r K (simpleRoot r i) ⊔ rootSubgroup r K (-simpleRoot r i) ≤
      Hinf (rankOneParabolic K r i) := by
  have hS : rootSubgroup r K (simpleRoot r i) ⊔ rootSubgroup r K (-simpleRoot r i) ≤
      rankOneParabolic K r i :=
    sup_le (rootSubgroup_simpleRoot_le_rankOneParabolic hr i)
      (rootSubgroup_neg_simpleRoot_le_rankOneParabolic hr i)
  have hperf := isPerfect_rootSubgroup_sup_simpleRoot (K := K) hr i h4
  have hpc : rootSubgroup r K (simpleRoot r i) ⊔ rootSubgroup r K (-simpleRoot r i) ≤
      perfectCore (rankOneParabolic K r i) :=
    CFSG.Quasithin.le_perfectCore_of_perfect hS (Subgroup.isPerfect_iff.mp hperf)
  rw [Hinf, CFSG.inSubgroup, ← CFSG.Quasithin.perfectCore_eq_map_perfectResidual]
  exact hpc

theorem map_conj_weylElt_unipotentExcept_le_self (hr : 2 ≤ r) (i : Fin r) :
    (unipotentExcept r K i).map (MulAut.conj (weylElt r K i)).toMonoidHom ≤
      unipotentExcept r K i := by
  rw [unipotentExcept, Subgroup.map_iSup]
  refine iSup_le fun β => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hβ => ?_
  have h := map_conj_rootSubgroup_torusWeyl hr
    (⟨weylElt r K i, weylElt_mem_torusWeyl i⟩ : torusWeyl r K) (posRoots_subset_roots hβ.1)
  rw [torusWeylNu_weylElt hr i] at h
  change (rootSubgroup r K β).map (MulAut.conj (weylElt r K i)).toMonoidHom = _ at h
  rw [h]
  change rootSubgroup r K (simpleRefl r i β) ≤ unipotentExcept r K i
  exact rootSubgroup_le_unipotentExcept ((bijOn_simpleRefl hr i).mapsTo hβ)

theorem map_conj_torusElt_unipotentExcept_le_self (i : Fin r) (d : Fin r → Kˣ) :
    (unipotentExcept r K i).map (MulAut.conj (torusElt r K d)).toMonoidHom ≤
      unipotentExcept r K i := by
  have hν : nuMono r K (⟨torusElt r K d, torusElt_mem_monoAut d⟩ : monoAut r K) = 1 :=
    nuMono_torusElt d
  rw [unipotentExcept, Subgroup.map_iSup]
  refine iSup_le fun β => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hβ => ?_
  rw [map_conj_rootSubgroup (⟨torusElt r K d, torusElt_mem_monoAut d⟩ : monoAut r K)
    (posRoots_subset_roots hβ.1), hν]
  change rootSubgroup r K β ≤ unipotentExcept r K i
  exact rootSubgroup_le_unipotentExcept hβ

theorem map_conj_rootElt_simpleRoot_le (hr : 2 ≤ r) (i : Fin r) {γ : Fin r → ℤ}
    (hγ : γ ∈ posRoots r) (s : K) :
    (rootSubgroup r K (simpleRoot r i)).map
        (MulAut.conj (rootElt r K γ s)).toMonoidHom ≤ rankOneA K r i := by
  have hα : simpleRoot r i ∈ roots r := posRoots_subset_roots (simpleRoot_mem_posRoots hr i)
  obtain ⟨-, hcomm, hcomm'⟩ := orthogonal_geometry_split_root_commutators (K := K) (r := r)
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  have hconj : (MulAut.conj (rootElt r K γ s)).toMonoidHom (rootElt r K (simpleRoot r i) t) =
      ⁅rootElt r K γ s, rootElt r K (simpleRoot r i) t⁆ *
        rootElt r K (simpleRoot r i) t := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
    group
  rw [hconj]
  refine mul_mem ?_ (rootSubgroup_simpleRoot_le_rankOneA (K := K) i
    (rootElt_mem_rootSubgroup _ _))
  by_cases hsum : γ + simpleRoot r i ∈ roots r
  · obtain ⟨c, -, hc⟩ := hcomm' γ (posRoots_subset_roots hγ) (simpleRoot r i) hα hsum
    rw [hc]
    exact unipotentExcept_le_rankOneA (K := K) i (rootSubgroup_le_unipotentExcept
      ⟨add_mem_posRoots hγ (simpleRoot_mem_posRoots hr i) hsum,
        add_ne_simpleRoot hr hγ (simpleRoot_mem_posRoots hr i) i⟩
      (rootElt_mem_rootSubgroup _ _))
  · rw [commutatorElement_eq_one_iff_commute.2 (hcomm γ (posRoots_subset_roots hγ)
      (simpleRoot r i) hα (ne_neg_of_mem_posRoots (simpleRoot_mem_posRoots hr i) hγ) hsum s t)]
    exact one_mem _

theorem map_conj_rootElt_neg_simpleRoot_le (hr : 2 ≤ r) (i : Fin r) {γ : Fin r → ℤ}
    (hγ : γ ∈ posRoots r) (s : K) :
    (rootSubgroup r K (-simpleRoot r i)).map
        (MulAut.conj (rootElt r K γ s)).toMonoidHom ≤ rankOneA K r i := by
  have hα : simpleRoot r i ∈ roots r := posRoots_subset_roots (simpleRoot_mem_posRoots hr i)
  obtain ⟨-, hcomm, hcomm'⟩ := orthogonal_geometry_split_root_commutators (K := K) (r := r)
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  rcases eq_or_ne γ (simpleRoot r i) with rfl | hne
  · have hx : rootElt r K (simpleRoot r i) s ∈ rankOneRootSup K r i :=
      rootSubgroup_simpleRoot_le_rankOneRootSup (K := K) i (rootElt_mem_rootSubgroup _ _)
    have hy : rootElt r K (-simpleRoot r i) t ∈ rankOneRootSup K r i :=
      rootSubgroup_neg_le_rankOneRootSup (K := K) i (rootElt_mem_rootSubgroup _ _)
    exact rankOneRootSup_le_rankOneA (K := K) i
      ((rankOneRootSup K r i).mul_mem ((rankOneRootSup K r i).mul_mem hx hy)
        ((rankOneRootSup K r i).inv_mem hx))
  · have hconj : (MulAut.conj (rootElt r K γ s)).toMonoidHom
        (rootElt r K (-simpleRoot r i) t) =
        ⁅rootElt r K γ s, rootElt r K (-simpleRoot r i) t⁆ *
          rootElt r K (-simpleRoot r i) t := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [hconj]
    refine mul_mem ?_ (rootSubgroup_neg_le_rankOneA (K := K) i
      (rootElt_mem_rootSubgroup _ _))
    by_cases hsum : γ + (-simpleRoot r i) ∈ roots r
    · obtain ⟨c, -, hc⟩ := hcomm' γ (posRoots_subset_roots hγ) (-simpleRoot r i)
        (neg_mem_roots hα) hsum
      rw [hc]
      have hroot : γ - simpleRoot r i ∈ roots r := by simpa [sub_eq_add_neg] using hsum
      have hle : 0 ≤ simpleHeight r (γ - simpleRoot r i) := by
        rw [sub_eq_add_neg, map_add, map_neg, simpleHeight_simpleRoot hr i]
        have := one_le_simpleHeight hγ
        omega
      have hpos : γ - simpleRoot r i ∈ posRoots r := by
        rcases (mem_posRoots_or_neg_mem_posRoots hroot).1 with h | h
        · exact h
        · have h1 := one_le_simpleHeight h
          rw [map_neg] at h1
          omega
      by_cases hcase : γ - simpleRoot r i = simpleRoot r i
      · rw [show γ + -simpleRoot r i = simpleRoot r i from hcase]
        exact rootSubgroup_simpleRoot_le_rankOneA (K := K) i (rootElt_mem_rootSubgroup _ _)
      · exact unipotentExcept_le_rankOneA (K := K) i
          (rootSubgroup_le_unipotentExcept ⟨hpos, hcase⟩ (rootElt_mem_rootSubgroup _ _))
    · rw [commutatorElement_eq_one_iff_commute.2 (hcomm γ (posRoots_subset_roots hγ)
        (-simpleRoot r i) (neg_mem_roots hα)
        (by simpa using hne) hsum s t)]
      exact one_mem _

theorem map_conj_rootElt_rankOneA_le (hr : 2 ≤ r) (i : Fin r) {γ : Fin r → ℤ}
    (hγ : γ ∈ posRoots r) (s : K) :
    (rankOneA K r i).map (MulAut.conj (rootElt r K γ s)).toMonoidHom ≤
      rankOneA K r i := by
  rw [rankOneA, Subgroup.map_sup]
  refine sup_le ?_ ((map_conj_unipotentExcept_le hr i hγ s).trans le_sup_right)
  rw [rankOneRootSup, Subgroup.map_sup]
  exact sup_le (map_conj_rootElt_simpleRoot_le hr i hγ s)
    (map_conj_rootElt_neg_simpleRoot_le hr i hγ s)

theorem map_conj_torusElt_rankOneA_le (hr : 2 ≤ r) (i : Fin r) (d : Fin r → Kˣ) :
    (rankOneA K r i).map (MulAut.conj (torusElt r K d)).toMonoidHom ≤
      rankOneA K r i := by
  have hα : simpleRoot r i ∈ roots r := posRoots_subset_roots (simpleRoot_mem_posRoots hr i)
  let g : monoAut r K := ⟨torusElt r K d, torusElt_mem_monoAut d⟩
  have hν : nuMono r K g = 1 := nuMono_torusElt d
  rw [rankOneA, Subgroup.map_sup]
  refine sup_le ?_ ((map_conj_torusElt_unipotentExcept_le_self i d).trans le_sup_right)
  rw [rankOneRootSup, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · change (rootSubgroup r K (simpleRoot r i)).map
        (MulAut.conj (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))).toMonoidHom ≤
      rootSubgroup r K (simpleRoot r i) ⊔ rootSubgroup r K (-simpleRoot r i) ⊔
        unipotentExcept r K i
    rw [map_conj_rootSubgroup g hα, hν]
    change rootSubgroup r K (simpleRoot r i) ≤ rankOneA K r i
    exact rootSubgroup_simpleRoot_le_rankOneA (K := K) i
  · change (rootSubgroup r K (-simpleRoot r i)).map
        (MulAut.conj (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))).toMonoidHom ≤
      rootSubgroup r K (simpleRoot r i) ⊔ rootSubgroup r K (-simpleRoot r i) ⊔
        unipotentExcept r K i
    rw [map_conj_rootSubgroup g (neg_mem_roots hα), hν]
    change rootSubgroup r K (-simpleRoot r i) ≤ rankOneA K r i
    exact rootSubgroup_neg_le_rankOneA (K := K) i

theorem map_conj_weylElt_rankOneA_le (hr : 2 ≤ r) (i : Fin r) :
    (rankOneA K r i).map (MulAut.conj (weylElt r K i)).toMonoidHom ≤
      rankOneA K r i := by
  have hα : simpleRoot r i ∈ roots r := posRoots_subset_roots (simpleRoot_mem_posRoots hr i)
  rw [rankOneA, Subgroup.map_sup]
  refine sup_le ?_ ((map_conj_weylElt_unipotentExcept_le_self hr i).trans le_sup_right)
  rw [rankOneRootSup, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [map_conj_rootSubgroup_torusWeyl hr
      (⟨weylElt r K i, weylElt_mem_torusWeyl i⟩ : torusWeyl r K) hα,
      torusWeylNu_weylElt hr i]
    change rootSubgroup r K (simpleRefl r i (simpleRoot r i)) ≤ rankOneA K r i
    rw [simpleRefl_simpleRoot hr i]
    exact rootSubgroup_neg_le_rankOneA (K := K) i
  · rw [map_conj_rootSubgroup_torusWeyl hr
      (⟨weylElt r K i, weylElt_mem_torusWeyl i⟩ : torusWeyl r K) (neg_mem_roots hα),
      torusWeylNu_weylElt hr i]
    change rootSubgroup r K (simpleRefl r i (-simpleRoot r i)) ≤ rankOneA K r i
    rw [map_neg, simpleRefl_simpleRoot hr i, neg_neg]
    exact rootSubgroup_simpleRoot_le_rankOneA (K := K) i

theorem mem_normalizer_of_map_conj_le {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom ≤ A)
    (hinv : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ A) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm h ?_
  have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hinv
  rw [Subgroup.map_map] at h1
  have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    change g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
    group
  rw [hcomp, Subgroup.map_id] at h1
  exact h1

theorem torus_le_normalizer_rankOneA (hr : 2 ≤ r) (i : Fin r) :
    torus r K ≤ Subgroup.normalizer (rankOneA K r i : Set _) := by
  rintro _ ⟨-, d, rfl⟩
  exact mem_normalizer_of_map_conj_le
    (map_conj_torusElt_rankOneA_le hr i d)
    (by simpa using map_conj_torusElt_rankOneA_le hr i d⁻¹)

theorem rootSubgroup_le_normalizer_rankOneA (hr : 2 ≤ r) (i : Fin r) {γ : Fin r → ℤ}
    (hγ : γ ∈ posRoots r) :
    rootSubgroup r K γ ≤ Subgroup.normalizer (rankOneA K r i : Set _) := by
  rintro _ ⟨s, rfl⟩
  exact mem_normalizer_of_map_conj_le
    (map_conj_rootElt_rankOneA_le hr i hγ s)
    (by simpa [rootElt_inv] using map_conj_rootElt_rankOneA_le hr i hγ (-s))

theorem unipotentExcept_le_normalizer_rankOneA (hr : 2 ≤ r) (i : Fin r) :
    unipotentExcept r K i ≤ Subgroup.normalizer (rankOneA K r i : Set _) := by
  rw [unipotentExcept]
  refine iSup₂_le fun γ hγ => rootSubgroup_le_normalizer_rankOneA hr i hγ.1

theorem unipotent_le_normalizer_rankOneA (hr : 2 ≤ r) (i : Fin r) :
    unipotent r K ≤ Subgroup.normalizer (rankOneA K r i : Set _) := by
  rw [← unipotentExcept_sup hr i]
  exact sup_le (unipotentExcept_le_normalizer_rankOneA hr i)
    (rootSubgroup_le_normalizer_rankOneA hr i (simpleRoot_mem_posRoots hr i))

theorem map_conj_weylElt_inv_rankOneA_le (hr : 2 ≤ r) (i : Fin r) :
    (rankOneA K r i).map (MulAut.conj ((weylElt r K i)⁻¹)).toMonoidHom ≤
      rankOneA K r i := by
  have hα : simpleRoot r i ∈ roots r := posRoots_subset_roots (simpleRoot_mem_posRoots hr i)
  let d : Fin r → Kˣ := fun j => (-1 : Kˣ) ^ simpleRoot r i j
  have hsq : weylElt r K i ^ 2 = torusElt r K d := by
    rw [show weylElt r K i = rootN r K (simpleRoot r i) 1 by rw [weylElt, rootN, inv_one]]
    exact rootN_one_sq_eq_torusElt hα
  have hinv_eq : (weylElt r K i)⁻¹ = weylElt r K i * torusElt r K d⁻¹ := by
    rw [show (weylElt r K i)⁻¹ = weylElt r K i * (weylElt r K i ^ 2)⁻¹ by group,
      hsq, map_inv]
  rw [hinv_eq]
  have hcomp : (MulAut.conj (weylElt r K i * torusElt r K d⁻¹)).toMonoidHom =
      (MulAut.conj (weylElt r K i)).toMonoidHom.comp
        (MulAut.conj (torusElt r K d⁻¹)).toMonoidHom := by
    rw [map_mul]
    rfl
  rw [hcomp, ← Subgroup.map_map]
  exact (Subgroup.map_mono (f := (MulAut.conj (weylElt r K i)).toMonoidHom)
    (map_conj_torusElt_rankOneA_le hr i d⁻¹)).trans (map_conj_weylElt_rankOneA_le hr i)

theorem weylElt_mem_normalizer_rankOneA (hr : 2 ≤ r) (i : Fin r) :
    weylElt r K i ∈ Subgroup.normalizer (rankOneA K r i : Set _) :=
  mem_normalizer_of_map_conj_le (map_conj_weylElt_rankOneA_le hr i)
    (map_conj_weylElt_inv_rankOneA_le hr i)

theorem borel_le_normalizer_rankOneA (hr : 2 ≤ r) (i : Fin r) :
    borel r K ≤ Subgroup.normalizer (rankOneA K r i : Set _) := by
  intro x hx
  have hx' : x ∈ (borel r K : Set _) := hx
  rw [borel_eq_torus_mul_unipotent.1, Set.mem_mul] at hx'
  obtain ⟨t, ht, u, hu, rfl⟩ := hx'
  exact Subgroup.mul_mem _ (torus_le_normalizer_rankOneA hr i ht)
    (unipotent_le_normalizer_rankOneA hr i hu)

theorem rankOneParabolic_le_normalizer_rankOneA (hr : 2 ≤ r) (i : Fin r) :
    rankOneParabolic K r i ≤ Subgroup.normalizer (rankOneA K r i : Set _) := by
  rw [rankOneParabolic, Subgroup.closure_le]
  rintro x (hx | rfl)
  · exact borel_le_normalizer_rankOneA hr i hx
  · exact weylElt_mem_normalizer_rankOneA hr i

theorem rankOneA_le_rankOneParabolic (hr : 2 ≤ r) (i : Fin r) :
    rankOneA K r i ≤ rankOneParabolic K r i := by
  rw [rankOneA, rankOneRootSup]
  exact sup_le (sup_le (rootSubgroup_simpleRoot_le_rankOneParabolic hr i)
    (rootSubgroup_neg_simpleRoot_le_rankOneParabolic hr i))
    (unipotentExcept_le_rankOneParabolic i)

theorem rankOneA_normal_in_rankOneParabolic (hr : 2 ≤ r) (i : Fin r) :
    ((rankOneA K r i).subgroupOf (rankOneParabolic K r i)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (rankOneA_le_rankOneParabolic hr i)).mpr
    (rankOneParabolic_le_normalizer_rankOneA hr i)

theorem unipotent_le_normalizer_unipotentExcept (hr : 2 ≤ r) (i : Fin r) :
    unipotent r K ≤ Subgroup.normalizer (unipotentExcept r K i : Set _) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (unipotentExcept_le_unipotent i)).mp
    (unipotentExcept_normal hr i)

theorem torus_le_normalizer_unipotentExcept (i : Fin r) :
    torus r K ≤ Subgroup.normalizer (unipotentExcept r K i : Set _) := by
  rintro _ ⟨-, d, rfl⟩
  exact mem_normalizer_of_map_conj_le
    (map_conj_torusElt_unipotentExcept_le_self i d)
    (by simpa using map_conj_torusElt_unipotentExcept_le_self i d⁻¹)

theorem map_conj_weylElt_inv_unipotentExcept_le_self (hr : 2 ≤ r) (i : Fin r) :
    (unipotentExcept r K i).map (MulAut.conj ((weylElt r K i)⁻¹)).toMonoidHom ≤
      unipotentExcept r K i := by
  have hα : simpleRoot r i ∈ roots r := posRoots_subset_roots (simpleRoot_mem_posRoots hr i)
  let d : Fin r → Kˣ := fun j => (-1 : Kˣ) ^ simpleRoot r i j
  have hsq : weylElt r K i ^ 2 = torusElt r K d := by
    rw [show weylElt r K i = rootN r K (simpleRoot r i) 1 by rw [weylElt, rootN, inv_one]]
    exact rootN_one_sq_eq_torusElt hα
  have hinv_eq : (weylElt r K i)⁻¹ = weylElt r K i * torusElt r K d⁻¹ := by
    rw [show (weylElt r K i)⁻¹ = weylElt r K i * (weylElt r K i ^ 2)⁻¹ by group,
      hsq, map_inv]
  rw [hinv_eq]
  have hcomp : (MulAut.conj (weylElt r K i * torusElt r K d⁻¹)).toMonoidHom =
      (MulAut.conj (weylElt r K i)).toMonoidHom.comp
        (MulAut.conj (torusElt r K d⁻¹)).toMonoidHom := by
    rw [map_mul]
    rfl
  rw [hcomp, ← Subgroup.map_map]
  exact (Subgroup.map_mono (f := (MulAut.conj (weylElt r K i)).toMonoidHom)
    (map_conj_torusElt_unipotentExcept_le_self i d⁻¹)).trans
      (map_conj_weylElt_unipotentExcept_le_self hr i)

theorem weylElt_mem_normalizer_unipotentExcept (hr : 2 ≤ r) (i : Fin r) :
    weylElt r K i ∈ Subgroup.normalizer (unipotentExcept r K i : Set _) :=
  mem_normalizer_of_map_conj_le (map_conj_weylElt_unipotentExcept_le_self hr i)
    (map_conj_weylElt_inv_unipotentExcept_le_self hr i)

theorem borel_le_normalizer_unipotentExcept (hr : 2 ≤ r) (i : Fin r) :
    borel r K ≤ Subgroup.normalizer (unipotentExcept r K i : Set _) := by
  intro x hx
  have hx' : x ∈ (borel r K : Set _) := hx
  rw [borel_eq_torus_mul_unipotent.1, Set.mem_mul] at hx'
  obtain ⟨t, ht, u, hu, rfl⟩ := hx'
  exact Subgroup.mul_mem _ (torus_le_normalizer_unipotentExcept (K := K) i ht)
    (unipotent_le_normalizer_unipotentExcept hr i hu)

theorem rankOneParabolic_le_normalizer_unipotentExcept (hr : 2 ≤ r) (i : Fin r) :
    rankOneParabolic K r i ≤ Subgroup.normalizer (unipotentExcept r K i : Set _) := by
  rw [rankOneParabolic, Subgroup.closure_le]
  rintro x (hx | rfl)
  · exact borel_le_normalizer_unipotentExcept hr i hx
  · exact weylElt_mem_normalizer_unipotentExcept hr i

theorem unipotentExcept_normal_in_rankOneParabolic (hr : 2 ≤ r) (i : Fin r) :
    ((unipotentExcept r K i).subgroupOf (rankOneParabolic K r i)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (unipotentExcept_le_rankOneParabolic i)).mpr
    (rankOneParabolic_le_normalizer_unipotentExcept hr i)

theorem isMulCommutative_torus : IsMulCommutative ↥(torus r K) := by
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  obtain ⟨-, hx⟩ := x.2
  obtain ⟨-, hy⟩ := y.2
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  change (x : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) * (y : _) =
    (y : _) * (x : _)
  rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm a b]

theorem rankOneRootSup_le_rankOneParabolic (hr : 2 ≤ r) (i : Fin r) :
    rankOneRootSup K r i ≤ rankOneParabolic K r i :=
  (rankOneRootSup_le_rankOneA (K := K) i).trans (rankOneA_le_rankOneParabolic (K := K) hr i)

theorem rankOneParabolic_eq_rankOneA_sup_torus (hr : 2 ≤ r) (i : Fin r) :
    rankOneParabolic K r i = rankOneA K r i ⊔ torus r K := by
  have hn : weylElt r K i ∈ rankOneA K r i := by
    rw [weylElt]
    refine rankOneRootSup_le_rankOneA (K := K) (r := r) i ?_
    exact (rankOneRootSup K r i).mul_mem
      ((rankOneRootSup K r i).mul_mem
        (Subgroup.mem_sup_left (rootElt_mem_rootSubgroup _ _))
        (Subgroup.mem_sup_right (rootElt_mem_rootSubgroup _ _)))
      (Subgroup.mem_sup_left (rootElt_mem_rootSubgroup _ _))
  have hU : unipotent r K ≤ rankOneA K r i := by
    rw [← unipotentExcept_sup (K := K) (r := r) hr i]
    exact sup_le (unipotentExcept_le_rankOneA (K := K) (r := r) i)
      (rootSubgroup_simpleRoot_le_rankOneA (K := K) (r := r) i)
  refine le_antisymm ?_ ?_
  · rw [rankOneParabolic, Subgroup.closure_le]
    rintro x (hb | rfl)
    · have hb' : x ∈
          (torus r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) *
          (unipotent r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) := by
        rw [← borel_eq_torus_mul_unipotent.1]
        exact hb
      obtain ⟨t, ht, u, hu, rfl⟩ := Set.mem_mul.mp hb'
      exact mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left (hU hu))
    · exact Subgroup.mem_sup_left hn
  · refine sup_le (rankOneA_le_rankOneParabolic (K := K) (r := r) hr i) ?_
    exact (torus_le_borel (K := K) (r := r)).trans (borel_le_rankOneParabolic r i)

theorem hinf_rankOneParabolic_le_rankOneA (hr : 2 ≤ r) (i : Fin r) :
    Hinf (rankOneParabolic K r i) ≤ rankOneA K r i := by
  haveI : IsMulCommutative ↥(torus r K) := isMulCommutative_torus (K := K) (r := r)
  rw [Hinf, CFSG.inSubgroup, ← CFSG.Quasithin.perfectCore_eq_map_perfectResidual]
  exact CFSG.Quasithin.perfectCore_le_of_sup_solvable
    (rankOneA_le_rankOneParabolic (K := K) (r := r) hr i)
    (rankOneA_normal_in_rankOneParabolic (K := K) (r := r) hr i)
    (rankOneParabolic_eq_rankOneA_sup_torus (K := K) (r := r) hr i)
    inferInstance

theorem rankOneRootSup_equiv_sl2 (hr : 2 ≤ r) (i : Fin r) :
    Nonempty (↥(rankOneRootSup K r i) ≃* SpecialLinearGroup (Fin 2) K) := by
  have hα : simpleRoot r i ∈ roots r := posRoots_subset_roots (simpleRoot_mem_posRoots hr i)
  obtain ⟨a, b, hab, -, h1, h2⟩ := exists_rootElt_eq_rpElt (K := K) hα
  have hInj : Function.Injective (etaLin (k := K) hab) := fun x y hxy =>
    etaGL_injective hab
      ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin r ⊕ Fin r) K).injective hxy)
  have hS : rankOneRootSup K r i = (etaLin (k := K) hab).range :=
    rootSubgroup_sup_eq_etaLin_range hr i hab h1 h2
  exact ⟨((MonoidHom.ofInjective hInj).trans (MulEquiv.subgroupCongr hS.symm)).symm⟩

theorem unipotentExcept_inf_rankOneRootSup_eq_bot (hr : 2 ≤ r) (i : Fin r) [Finite K]
    [CharP K 2] (h4 : ∃ s : Finset K, s.card = 4) :
    unipotentExcept r K i ⊓ rankOneRootSup K r i = ⊥ := by
  haveI : Finite ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
    Finite.of_injective
      (fun e : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) =>
        (e : (Fin r ⊕ Fin r → K) → (Fin r ⊕ Fin r → K)))
      (fun e₁ e₂ h => LinearEquiv.ext (fun x => congrFun h x))
  obtain ⟨e⟩ := rankOneRootSup_equiv_sl2 (K := K) hr i
  haveI : IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := sl2_isSimple (K := K) h4
  haveI : IsSimpleGroup ↥(rankOneRootSup K r i) := e.isSimpleGroup
  have hnorm : ((unipotentExcept r K i).subgroupOf (rankOneRootSup K r i)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨rankOneParabolic_le_normalizer_unipotentExcept (K := K) (r := r) hr i
          (rankOneRootSup_le_rankOneParabolic (K := K) (r := r) hr i hx),
        Subgroup.le_normalizer hx⟩
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((unipotentExcept r K i).subgroupOf (rankOneRootSup K r i)) with hbot | htop
  · refine le_bot_iff.mp ?_
    intro x hx
    have hmem : (⟨x, hx.2⟩ : ↥(rankOneRootSup K r i)) ∈
        (unipotentExcept r K i).subgroupOf (rankOneRootSup K r i) := hx.1
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext_iff.mp hmem
  · exfalso
    have hSleU : rankOneRootSup K r i ≤ unipotentExcept r K i := by
      intro x hx
      have hmem : (⟨x, hx⟩ : ↥(rankOneRootSup K r i)) ∈
          (unipotentExcept r K i).subgroupOf (rankOneRootSup K r i) := by
        rw [htop]
        exact Subgroup.mem_top _
      exact hmem
    haveI : IsPGroup 2 ↥(rankOneRootSup K r i) :=
      (isPGroup_unipotentExcept (K := K) (r := r) i).of_injective
        (Subgroup.inclusion hSleU) (Subgroup.inclusion_injective _)
    haveI : Group.IsNilpotent ↥(rankOneRootSup K r i) :=
      IsPGroup.isNilpotent (G := ↥(rankOneRootSup K r i)) (p := 2) ‹_›
    haveI : Group.IsPerfect ↥(rankOneRootSup K r i) :=
      isPerfect_rootSubgroup_sup_simpleRoot (K := K) hr i h4
    exact (Group.IsPerfect.not_isNilpotent ↥(rankOneRootSup K r i)) inferInstance

theorem unipotentExcept_normal_in_rankOneA (hr : 2 ≤ r) (i : Fin r) :
    ((unipotentExcept r K i).subgroupOf (rankOneA K r i)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (unipotentExcept_le_rankOneA (K := K) (r := r) i)]
  intro h k hh hk
  exact (Subgroup.normal_subgroupOf_iff
    (unipotentExcept_le_rankOneParabolic (K := K) (r := r) i)).mp
    (unipotentExcept_normal_in_rankOneParabolic (K := K) (r := r) hr i) h k hh
    (rankOneA_le_rankOneParabolic (K := K) (r := r) hr i hk)

theorem rankOneA_coe_eq_mul_rankOneRootSup_unipotentExcept (hr : 2 ≤ r) (i : Fin r) :
    (rankOneA K r i : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) =
      (rankOneRootSup K r i :
        Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) *
      (unipotentExcept r K i :
        Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) :=
  (coe_eq_mul_of_normal (L := rankOneA K r i) (N := unipotentExcept r K i)
    (H := rankOneRootSup K r i) (unipotentExcept_le_rankOneA (K := K) (r := r) i)
    (rankOneRootSup_le_rankOneA (K := K) (r := r) i)
    (unipotentExcept_normal_in_rankOneA (K := K) (r := r) hr i)
    (by rw [sup_comm]; rfl)).2

theorem rankOneA_quotient_unipotentExcept_equiv_sl2 (hr : 2 ≤ r) (i : Fin r) [Finite K]
    [CharP K 2] (h4 : ∃ s : Finset K, s.card = 4) :
    letI := unipotentExcept_normal_in_rankOneA (K := K) (r := r) hr i
    Nonempty ((↥(rankOneA K r i) ⧸
        (unipotentExcept r K i).subgroupOf (rankOneA K r i)) ≃*
      SpecialLinearGroup (Fin 2) K) := by
  have hUSbot : unipotentExcept r K i ⊓ rankOneRootSup K r i = ⊥ :=
    unipotentExcept_inf_rankOneRootSup_eq_bot (K := K) hr i h4
  have hUSbot' : (unipotentExcept r K i).subgroupOf (rankOneRootSup K r i) = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff]
    exact hUSbot
  have hUA : ((unipotentExcept r K i).subgroupOf (rankOneA K r i)).Normal :=
    unipotentExcept_normal_in_rankOneA (K := K) (r := r) hr i
  let UA : Subgroup ↥(rankOneA K r i) :=
    (unipotentExcept r K i).subgroupOf (rankOneA K r i)
  haveI : UA.Normal := hUA
  have hSU := rankOneA_coe_eq_mul_rankOneRootSup_unipotentExcept (K := K) (r := r) hr i
  let φ : ↥(rankOneRootSup K r i) →* (↥(rankOneA K r i) ⧸ UA) :=
    (QuotientGroup.mk' UA).comp
      (Subgroup.inclusion (rankOneRootSup_le_rankOneA (K := K) (r := r) i))
  have hkerφ : φ.ker = (unipotentExcept r K i).subgroupOf (rankOneRootSup K r i) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk' UA) (Subgroup.inclusion
      (rankOneRootSup_le_rankOneA (K := K) (r := r) i) x) = 1 ↔
      (x : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈ unipotentExcept r K i
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hinj : Function.Injective φ :=
    φ.ker_eq_bot_iff.mp (by rw [hkerφ]; exact hUSbot')
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective UA y
    have ha : (a : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈
        (rankOneRootSup K r i :
          Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) *
        (unipotentExcept r K i :
          Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) := by
      rw [← hSU]
      exact a.2
    obtain ⟨s, hs, u, hu, hsu⟩ := Set.mem_mul.mp ha
    have hsA : s ∈ rankOneA K r i := rankOneRootSup_le_rankOneA (K := K) (r := r) i hs
    have huA : u ∈ rankOneA K r i := unipotentExcept_le_rankOneA (K := K) (r := r) i hu
    refine ⟨⟨s, hs⟩, ?_⟩
    have haeq : a = (⟨s, hsA⟩ : ↥(rankOneA K r i)) * (⟨u, huA⟩ : ↥(rankOneA K r i)) :=
      Subtype.ext hsu.symm
    have hu_one : (QuotientGroup.mk' UA) (⟨u, huA⟩ : ↥(rankOneA K r i)) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hu
    change (QuotientGroup.mk' UA) (Subgroup.inclusion
      (rankOneRootSup_le_rankOneA (K := K) (r := r) i) ⟨s, hs⟩) =
      (QuotientGroup.mk' UA) a
    rw [haeq, map_mul, hu_one, mul_one]
    rfl
  obtain ⟨e⟩ := rankOneRootSup_equiv_sl2 (K := K) hr i
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm.trans e⟩

theorem exists_sl2Surjection_rankOneParabolic (hr : 2 ≤ r) (i : Fin r) [Finite K] [CharP K 2]
    (h4 : ∃ s : Finset K, s.card = 4) :
    ∃ f : ↥(Hinf (rankOneParabolic K r i)) →* SpecialLinearGroup (Fin 2) K,
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  let UA : Subgroup ↥(rankOneA K r i) :=
    (unipotentExcept r K i).subgroupOf (rankOneA K r i)
  haveI : UA.Normal := unipotentExcept_normal_in_rankOneA (K := K) (r := r) hr i
  obtain ⟨eA⟩ := rankOneA_quotient_unipotentExcept_equiv_sl2 (K := K) (r := r) hr i h4
  have hHA : Hinf (rankOneParabolic K r i) ≤ rankOneA K r i :=
    hinf_rankOneParabolic_le_rankOneA (K := K) (r := r) hr i
  have hSH : rankOneRootSup K r i ≤ Hinf (rankOneParabolic K r i) :=
    rootSubgroup_sup_le_Hinf_rankOneParabolic (K := K) hr i h4
  let q : ↥(Hinf (rankOneParabolic K r i)) →* (↥(rankOneA K r i) ⧸ UA) :=
    (QuotientGroup.mk' UA).comp (Subgroup.inclusion hHA)
  let f : ↥(Hinf (rankOneParabolic K r i)) →* SpecialLinearGroup (Fin 2) K :=
    eA.toMonoidHom.comp q
  refine ⟨f, ?_, ?_⟩
  · have hq : Function.Surjective q := by
      intro y
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective UA y
      have ha : (a : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈
          (rankOneRootSup K r i :
            Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) *
          (unipotentExcept r K i :
            Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) := by
        rw [← rankOneA_coe_eq_mul_rankOneRootSup_unipotentExcept (K := K) (r := r) hr i]
        exact a.2
      obtain ⟨s, hs, u, hu, hsu⟩ := Set.mem_mul.mp ha
      have hsH : s ∈ Hinf (rankOneParabolic K r i) := hSH hs
      have hsA : s ∈ rankOneA K r i := rankOneRootSup_le_rankOneA (K := K) (r := r) i hs
      have huA : u ∈ rankOneA K r i := unipotentExcept_le_rankOneA (K := K) (r := r) i hu
      refine ⟨⟨s, hsH⟩, ?_⟩
      have haeq : a = (⟨s, hsA⟩ : ↥(rankOneA K r i)) *
          (⟨u, huA⟩ : ↥(rankOneA K r i)) := Subtype.ext hsu.symm
      have hu_one : (QuotientGroup.mk' UA) (⟨u, huA⟩ : ↥(rankOneA K r i)) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hu
      change (QuotientGroup.mk' UA) (Subgroup.inclusion hHA ⟨s, hsH⟩) =
        (QuotientGroup.mk' UA) a
      rw [haeq, map_mul, hu_one, mul_one]
      rfl
    exact eA.surjective.comp hq
  · have hfker : f.ker = q.ker :=
      MonoidHom.ker_comp_of_injective q eA.toMonoidHom eA.injective
    have hqker : q.ker =
        (unipotentExcept r K i).subgroupOf (Hinf (rankOneParabolic K r i)) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change (QuotientGroup.mk' UA) (Subgroup.inclusion hHA x) = 1 ↔
        (x : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈ unipotentExcept r K i
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    rw [hfker, hqker]
    let ψ : ↥((unipotentExcept r K i).subgroupOf (Hinf (rankOneParabolic K r i))) →*
        ↥(unipotentExcept r K i) :=
      { toFun := fun x => ⟨(x : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)),
          Subgroup.mem_subgroupOf.mp x.2⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun _ _ => Subtype.ext rfl }
    have hψ : Function.Injective ψ := by
      intro x y hxy
      have h : (x : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
          (y : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
        congrArg (fun z : ↥(unipotentExcept r K i) =>
          (z : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) hxy
      exact Subtype.ext (Subtype.ext_iff.mpr h)
    exact (isPGroup_unipotentExcept (K := K) (r := r) i).of_injective ψ hψ

theorem torus_eq_bot_of_card_two [Finite K] (hK : Nat.card K = 2) :
    torus r K = ⊥ := by
  haveI : Subsingleton Kˣ := by
    rw [← Finite.card_le_one_iff_subsingleton, Nat.card_units, hK]
  have hrange : (torusElt r K).range = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_bot, Subsingleton.elim a 1, map_one]
  simp [torus, hrange]

theorem borel_eq_unipotent_of_card_two [Finite K] (hK : Nat.card K = 2) :
    borel r K = unipotent r K := by
  refine le_antisymm ?_ unipotent_le_borel
  intro g hg
  obtain ⟨t, ht, u, hu, rfl⟩ := exists_torus_mul_unipotent hg
  rw [torus_eq_bot_of_card_two (K := K) (r := r) hK, Subgroup.mem_bot] at ht
  rw [ht, one_mul]
  exact hu

theorem rankOneParabolic_eq_rankOneA_sup_zpowers (hr : 2 ≤ r) (i : Fin r) [Finite K]
    (hK : Nat.card K = 2) :
    rankOneParabolic K r i = rankOneA K r i ⊔ Subgroup.zpowers (weylElt r K i) := by
  refine le_antisymm ?_ ?_
  · rw [rankOneParabolic, Subgroup.closure_le]
    rintro x (hb | rfl)
    · rw [borel_eq_unipotent_of_card_two (K := K) (r := r) hK, ← unipotentExcept_sup hr i] at hb
      exact Subgroup.mem_sup_left (sup_le (unipotentExcept_le_rankOneA (K := K) (r := r) i)
        (rootSubgroup_simpleRoot_le_rankOneA (K := K) (r := r) i) hb)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · refine sup_le (rankOneA_le_rankOneParabolic hr i) ?_
    exact Subgroup.zpowers_le.mpr (weylElt_mem_rankOneParabolic r i)

theorem isSolvable_rankOneA_F2 (hr : 2 ≤ r) (i : Fin r) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : Group.IsSolvable ↥(rankOneA K r i) := by
  haveI : Finite ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
    Finite.of_injective
      (fun e : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) =>
        (e : (Fin r ⊕ Fin r → K) → (Fin r ⊕ Fin r → K)))
      (fun e₁ e₂ h => LinearEquiv.ext (fun x => congrFun h x))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable ↥(unipotentExcept r K i) := by
    haveI : Group.IsNilpotent ↥(unipotentExcept r K i) :=
      (isPGroup_unipotentExcept (K := K) (r := r) i).isNilpotent
    infer_instance
  have hUA : ((unipotentExcept r K i).subgroupOf (rankOneA K r i)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (unipotentExcept_le_rankOneA (K := K) (r := r) i)]
    intro h k hh hk
    exact (Subgroup.normal_subgroupOf_iff
      (unipotentExcept_le_rankOneParabolic (K := K) (r := r) i)).mp
      (unipotentExcept_normal_in_rankOneParabolic (K := K) (r := r) hr i) h k hh
      (rankOneA_le_rankOneParabolic (K := K) (r := r) hr i hk)
  haveI : ((unipotentExcept r K i).subgroupOf (rankOneA K r i)).Normal := hUA
  haveI : Group.IsSolvable ↥((unipotentExcept r K i).subgroupOf (rankOneA K r i)) := by
    let e := Subgroup.subgroupOfEquivOfLe (unipotentExcept_le_rankOneA (K := K) (r := r) i)
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) (fun x => ⟨e x, by simp⟩)
  haveI : Group.IsSolvable
      (↥(rankOneA K r i) ⧸ ((unipotentExcept r K i).subgroupOf (rankOneA K r i))) := by
    haveI : Group.IsSolvable ↥(rankOneRootSup K r i) :=
      isSolvable_rankOneRootSup_F2 (K := K) (r := r) hr i hK
    have hL : unipotentExcept r K i ⊔ rankOneRootSup K r i = rankOneA K r i := by
      rw [sup_comm]
      rfl
    let f : ↥(rankOneRootSup K r i) →*
        (↥(rankOneA K r i) ⧸ ((unipotentExcept r K i).subgroupOf (rankOneA K r i))) :=
      (QuotientGroup.mk' ((unipotentExcept r K i).subgroupOf (rankOneA K r i))).comp
        (Subgroup.inclusion (rankOneRootSup_le_rankOneA (K := K) (r := r) i))
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
        (N := (unipotentExcept r K i).subgroupOf (rankOneA K r i)) x
      have hy : (y : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈
          ((rankOneRootSup K r i : Set _) * (unipotentExcept r K i : Set _) :
            Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) := by
        rw [← (coe_eq_mul_of_normal (L := rankOneA K r i) (N := unipotentExcept r K i)
          (H := rankOneRootSup K r i) (unipotentExcept_le_rankOneA (K := K) (r := r) i)
          (rankOneRootSup_le_rankOneA (K := K) (r := r) i) hUA hL).2]
        exact y.2
      obtain ⟨s, hs, u, hu, hsu⟩ := Set.mem_mul.mp hy
      have huR : u ∈ rankOneA K r i := unipotentExcept_le_rankOneA (K := K) (r := r) i hu
      have hone : QuotientGroup.mk' ((unipotentExcept r K i).subgroupOf (rankOneA K r i))
          (⟨u, huR⟩ : ↥(rankOneA K r i)) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hu
      refine ⟨⟨s, hs⟩, ?_⟩
      have hy_eq : y = (Subgroup.inclusion (rankOneRootSup_le_rankOneA (K := K) (r := r) i)
          ⟨s, hs⟩) * (⟨u, huR⟩ : ↥(rankOneA K r i)) := Subtype.ext hsu.symm
      have hcalc : QuotientGroup.mk' ((unipotentExcept r K i).subgroupOf (rankOneA K r i)) y =
          f ⟨s, hs⟩ := by
        calc QuotientGroup.mk' ((unipotentExcept r K i).subgroupOf (rankOneA K r i)) y
            = QuotientGroup.mk' ((unipotentExcept r K i).subgroupOf (rankOneA K r i))
                ((Subgroup.inclusion (rankOneRootSup_le_rankOneA (K := K) (r := r) i)
                  ⟨s, hs⟩) * (⟨u, huR⟩ : ↥(rankOneA K r i))) := by rw [hy_eq]
          _ = QuotientGroup.mk' ((unipotentExcept r K i).subgroupOf (rankOneA K r i))
                (Subgroup.inclusion (rankOneRootSup_le_rankOneA (K := K) (r := r) i) ⟨s, hs⟩) *
              QuotientGroup.mk' ((unipotentExcept r K i).subgroupOf (rankOneA K r i))
                (⟨u, huR⟩ : ↥(rankOneA K r i)) := map_mul _ _ _
          _ = QuotientGroup.mk' ((unipotentExcept r K i).subgroupOf (rankOneA K r i))
                (Subgroup.inclusion (rankOneRootSup_le_rankOneA (K := K) (r := r) i)
                  ⟨s, hs⟩) * 1 := by rw [hone]
          _ = f ⟨s, hs⟩ := by rw [mul_one]; rfl
      exact hcalc.symm
    exact Group.isSolvable_of_surjective (f := f) hf
  exact Group.isSolvable_of_subgroup_quotient
    ((unipotentExcept r K i).subgroupOf (rankOneA K r i))

theorem isSolvable_rankOneParabolic_F2 (hr : 2 ≤ r) (i : Fin r) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : Group.IsSolvable ↥(rankOneParabolic K r i) := by
  have hRA : ((rankOneA K r i).subgroupOf (rankOneParabolic K r i)).Normal :=
    rankOneA_normal_in_rankOneParabolic (K := K) (r := r) hr i
  haveI : ((rankOneA K r i).subgroupOf (rankOneParabolic K r i)).Normal := hRA
  haveI : Group.IsSolvable ↥(rankOneA K r i) :=
    isSolvable_rankOneA_F2 (K := K) (r := r) hr i hK
  haveI : Group.IsSolvable ↥((rankOneA K r i).subgroupOf (rankOneParabolic K r i)) := by
    let e := Subgroup.subgroupOfEquivOfLe (rankOneA_le_rankOneParabolic (K := K) (r := r) hr i)
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) (fun x => ⟨e x, by simp⟩)
  haveI : Group.IsSolvable
      (↥(rankOneParabolic K r i) ⧸ ((rankOneA K r i).subgroupOf (rankOneParabolic K r i))) := by
    haveI : Group.IsSolvable ↥(Subgroup.zpowers (weylElt r K i)) := inferInstance
    have hL : rankOneA K r i ⊔ Subgroup.zpowers (weylElt r K i) = rankOneParabolic K r i :=
      (rankOneParabolic_eq_rankOneA_sup_zpowers (K := K) (r := r) hr i hK).symm
    let f : ↥(Subgroup.zpowers (weylElt r K i)) →*
        (↥(rankOneParabolic K r i) ⧸ ((rankOneA K r i).subgroupOf (rankOneParabolic K r i))) :=
      (QuotientGroup.mk' ((rankOneA K r i).subgroupOf (rankOneParabolic K r i))).comp
        (Subgroup.inclusion (Subgroup.zpowers_le.mpr (weylElt_mem_rankOneParabolic r i)))
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
        (N := (rankOneA K r i).subgroupOf (rankOneParabolic K r i)) x
      have hy : (y : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈
          ((Subgroup.zpowers (weylElt r K i) : Set _) * (rankOneA K r i : Set _) :
            Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) := by
        rw [← (coe_eq_mul_of_normal (L := rankOneParabolic K r i) (N := rankOneA K r i)
          (H := Subgroup.zpowers (weylElt r K i))
          (rankOneA_le_rankOneParabolic (K := K) (r := r) hr i)
          (Subgroup.zpowers_le.mpr (weylElt_mem_rankOneParabolic r i)) hRA hL).2]
        exact y.2
      obtain ⟨m, hm, a, haA, hmr⟩ := Set.mem_mul.mp hy
      have haP : a ∈ rankOneParabolic K r i :=
        rankOneA_le_rankOneParabolic (K := K) (r := r) hr i haA
      have hone : QuotientGroup.mk' ((rankOneA K r i).subgroupOf (rankOneParabolic K r i))
          (⟨a, haP⟩ : ↥(rankOneParabolic K r i)) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact haA
      refine ⟨⟨m, hm⟩, ?_⟩
      have hy_eq : y = (Subgroup.inclusion
          (Subgroup.zpowers_le.mpr (weylElt_mem_rankOneParabolic r i)) ⟨m, hm⟩) *
          (⟨a, haP⟩ : ↥(rankOneParabolic K r i)) := Subtype.ext hmr.symm
      have hcalc : QuotientGroup.mk' ((rankOneA K r i).subgroupOf (rankOneParabolic K r i)) y =
          f ⟨m, hm⟩ := by
        calc QuotientGroup.mk' ((rankOneA K r i).subgroupOf (rankOneParabolic K r i)) y
            = QuotientGroup.mk' ((rankOneA K r i).subgroupOf (rankOneParabolic K r i))
                ((Subgroup.inclusion (Subgroup.zpowers_le.mpr
                  (weylElt_mem_rankOneParabolic r i)) ⟨m, hm⟩) *
                  (⟨a, haP⟩ : ↥(rankOneParabolic K r i))) := by rw [hy_eq]
          _ = QuotientGroup.mk' ((rankOneA K r i).subgroupOf (rankOneParabolic K r i))
                (Subgroup.inclusion (Subgroup.zpowers_le.mpr
                  (weylElt_mem_rankOneParabolic r i)) ⟨m, hm⟩) *
              QuotientGroup.mk' ((rankOneA K r i).subgroupOf (rankOneParabolic K r i))
                (⟨a, haP⟩ : ↥(rankOneParabolic K r i)) := map_mul _ _ _
          _ = QuotientGroup.mk' ((rankOneA K r i).subgroupOf (rankOneParabolic K r i))
                (Subgroup.inclusion (Subgroup.zpowers_le.mpr
                  (weylElt_mem_rankOneParabolic r i)) ⟨m, hm⟩) * 1 := by rw [hone]
          _ = f ⟨m, hm⟩ := by rw [mul_one]; rfl
      exact hcalc.symm
    exact Group.isSolvable_of_surjective (f := f) hf
  exact Group.isSolvable_of_subgroup_quotient
    ((rankOneA K r i).subgroupOf (rankOneParabolic K r i))

theorem isL2_rankOneParabolic_split_of_surjection [Finite K]
    (i : Fin r) {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (f : ↥(Hinf (rankOneParabolic K r i)) →* SpecialLinearGroup (Fin 2) K)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    IsL2 (Bar2 (Hinf (Subgroup.closure
      (((borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)))) ∪
        {weylElt r K i})))) n := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hnab : ∃ a b : SpecialLinearGroup (Fin 2) K, a * b ≠ b * a :=
    sl2_nonabelian (K := K) hK4
  haveI : IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := sl2_isSimple (K := K) hK4
  have hmodel : LieModel (StatedProj (StatedSL 2 K)) .PSL 2 2 n :=
    CFSG.Models.LieModel.toBlueprint (by decide)
      (CFSG.RankThree.GF2n.Stroth80.lieModel_statedProj_sl (K := K) (m := 2) (f := n)
        (by norm_num) hn hK)
  let e : Bar2 (Hinf (rankOneParabolic K r i)) ≃* StatedProj (StatedSL 2 K) :=
    (modO2EquivOfHom hnab f hf hker).trans sl2EquivStatedProj
  exact LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n) e.symm hmodel

theorem hinf_rankOneParabolic_split_eq_bot_of_solvable [Finite K]
    [Finite ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))] (i : Fin r)
    (hsolv : Group.IsSolvable ↥(rankOneParabolic K r i)) :
    Hinf (rankOneParabolic K r i) = ⊥ := by
  rw [Hinf, CFSG.inSubgroup, ← CFSG.Quasithin.perfectCore_eq_map_perfectResidual]
  exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot _).mp hsolv

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

end
