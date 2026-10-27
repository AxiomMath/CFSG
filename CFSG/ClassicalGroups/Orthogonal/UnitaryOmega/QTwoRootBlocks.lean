module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.QTwoFrame
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f)) {ω : K} (hω : IsTraceNormOne E ω)

theorem coe_qTwoLambda_symm_longRoot {i j : Fin 5} (hij : i ≠ j) (s t : Bool) (c : F) :
    (((qTwoLambda E hω).symm ((plusFrame 5 F (by norm_num)).longRoot hij s t (.ofAdd c)) :
        normOmega E 4) : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) =
      eichler (normHypForm E 4) (qTwoVec F ω j t) (c • qTwoVec F ω i s) := by
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  exact (coe_commutatorEquivSpinPlus_symm_longRoot (qTwoFrame hω) (finrank_normHypForm E 4)
    (by norm_num) CharTwo.two_eq_zero hij s t c).trans
    ((qTwoFrame hω).spinAction_longRoot_eq_eichler hij s t c)

theorem rankOne_plusRootGroup_eq_sup {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    rankOne (plusRootGroup n F hn) k = (rootD F hn k).range ⊔ (negRootD F hn k).range := by
  rw [rankOne, plusRootGroup_single, plusRootGroup_neg_single]

private theorem coe_symm_rootD (j : Fin 5) (a : F) :
    (((qTwoLambda E hω).symm (rootD F (by norm_num : 3 ≤ 5) j (.ofAdd a)) : normOmega E 4) :
      ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) =
      eichler (normHypForm E 4) (qTwoVec F ω (rootIdxD' 5 j) (rootSignD 5 j))
        (a • qTwoVec F ω (rootIdxD 5 j) true) := by
  have h : rootD F (by norm_num : 3 ≤ 5) j =
      (plusFrame 5 F (by norm_num : 3 ≤ 5)).longRoot (rootIdxD_ne 5 (by norm_num) j) true
        (rootSignD 5 j) := rfl
  rw [h]
  exact coe_qTwoLambda_symm_longRoot E hω (rootIdxD_ne 5 (by norm_num) j) true (rootSignD 5 j) a

private theorem coe_symm_negRootD (j : Fin 5) (a : F) :
    (((qTwoLambda E hω).symm (negRootD F (by norm_num : 3 ≤ 5) j (.ofAdd a)) : normOmega E 4) :
      ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) =
      eichler (normHypForm E 4) (qTwoVec F ω (rootIdxD 5 j) false)
        (a • qTwoVec F ω (rootIdxD' 5 j) (!rootSignD 5 j)) := by
  have h : negRootD F (by norm_num : 3 ≤ 5) j =
      (plusFrame 5 F (by norm_num : 3 ≤ 5)).longRoot (rootIdxD_ne 5 (by norm_num) j).symm
        (!rootSignD 5 j) false := rfl
  rw [h]
  exact coe_qTwoLambda_symm_longRoot E hω (rootIdxD_ne 5 (by norm_num) j).symm (!rootSignD 5 j)
    false a

private theorem normBlock_apply_of_mem_suppPerp {S : Finset (Fin 4)} {g : normOmega E 4}
    (hg : g ∈ normBlock E 4 S) {v : (F × F) × (Fin 4 → K)}
    (hv : v ∈ suppPerp (normHypForm E 4)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) S)) :
    (g : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) v = v :=
  supportedDerived_apply_perp (Subgroup.mem_subgroupOf.mp hg) hv

private theorem commute_of_coe_eq_eichler {g y : normOmega E 4} {u w : (F × F) × (Fin 4 → K)}
    (hy : (y : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) =
      eichler (normHypForm E 4) u w)
    (hu : (g : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) u = u)
    (hw : (g : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) w = w) :
    Commute y g := by
  have hgO : (g : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) ∈
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 4) :=
    Subgroup.commutator_le_self _ g.2
  have hconj := eichler_conj hgO u w
  rw [hu, hw] at hconj
  have hamb : (g : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) *
      eichler (normHypForm E 4) u w =
      eichler (normHypForm E 4) u w *
        (g : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) := by
    calc (g : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) *
          eichler (normHypForm E 4) u w
        = ((g : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) *
            eichler (normHypForm E 4) u w *
            (g : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)))⁻¹) *
            (g : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) := by group
      _ = eichler (normHypForm E 4) u w *
            (g : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) := by rw [hconj]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hy]
  exact hamb.symm

private theorem normPlaneVec_mem_suppPerp {S : Finset (Fin 4)} {i : Fin 4} (hi : i ∉ S) (x : K) :
    normPlaneVec F i x ∈ suppPerp (normHypForm E 4)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) S) := by
  refine (mem_suppPerp_coordSupport_refl_iff E S _).mpr ⟨rfl, fun j hj => ?_⟩
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp [normPlaneVec, Pi.single_eq_of_ne hji]

private theorem qTwoVec_mem_suppPerp_of_lt_two {S : Finset (Fin 4)}
    (hS : ∀ j ∈ S, 2 ≤ (j : ℕ)) {m : Fin 5} (hm : (m : ℕ) < 2) (r : Bool) :
    qTwoVec F ω m r ∈ suppPerp (normHypForm E 4)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) S) := by
  have h0 : (0 : Fin 4) ∉ S := fun h => by have := hS 0 h; omega
  have h1 : (1 : Fin 4) ∉ S := fun h => by have := hS 1 h; omega
  have hm' : m = 0 ∨ m = 1 := by
    rcases m with ⟨v, hv⟩
    simp only at hm
    rcases (show v = 0 ∨ v = 1 by omega) with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rcases hm' with rfl | rfl
  · cases r
    · rw [show qTwoVec F ω (0 : Fin 5) false =
          normPlaneVec F 0 ω + normPlaneVec F 1 1 from rfl]
      exact Submodule.add_mem _ (normPlaneVec_mem_suppPerp (E := E) h0 ω)
        (normPlaneVec_mem_suppPerp (E := E) h1 1)
    · rw [show qTwoVec F ω (0 : Fin 5) true =
          normPlaneVec F 0 1 + normPlaneVec F 1 1 from rfl]
      exact Submodule.add_mem _ (normPlaneVec_mem_suppPerp (E := E) h0 1)
        (normPlaneVec_mem_suppPerp (E := E) h1 1)
  · cases r
    · rw [show qTwoVec F ω (1 : Fin 5) false =
          normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 (1 + ω) from rfl]
      exact Submodule.add_mem _ (normPlaneVec_mem_suppPerp (E := E) h0 (1 + ω))
        (normPlaneVec_mem_suppPerp (E := E) h1 (1 + ω))
    · rw [show qTwoVec F ω (1 : Fin 5) true =
          normPlaneVec F 0 (1 + ω) + normPlaneVec F 1 ω from rfl]
      exact Submodule.add_mem _ (normPlaneVec_mem_suppPerp (E := E) h0 (1 + ω))
        (normPlaneVec_mem_suppPerp (E := E) h1 ω)

private theorem qTwoVec_mem_suppPerp_of_three_le {S : Finset (Fin 4)}
    (hS : ∀ j ∈ S, (j : ℕ) < 2) {m : Fin 5} (hm : 3 ≤ (m : ℕ)) (r : Bool) :
    qTwoVec F ω m r ∈ suppPerp (normHypForm E 4)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) S) := by
  have h2 : (2 : Fin 4) ∉ S := fun h => by have := hS 2 h; omega
  have h3 : (3 : Fin 4) ∉ S := fun h => by have := hS 3 h; omega
  have hm' : m = 3 ∨ m = 4 := by
    rcases m with ⟨v, hv⟩
    simp only at hm
    have : v = 3 ∨ v = 4 := by omega
    rcases this with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rcases hm' with rfl | rfl
  · cases r
    · rw [show qTwoVec F ω (3 : Fin 5) false =
          normPlaneVec F 3 ω + normPlaneVec F 2 1 from rfl]
      exact Submodule.add_mem _ (normPlaneVec_mem_suppPerp (E := E) h3 ω)
        (normPlaneVec_mem_suppPerp (E := E) h2 1)
    · rw [show qTwoVec F ω (3 : Fin 5) true =
          normPlaneVec F 3 1 + normPlaneVec F 2 1 from rfl]
      exact Submodule.add_mem _ (normPlaneVec_mem_suppPerp (E := E) h3 1)
        (normPlaneVec_mem_suppPerp (E := E) h2 1)
  · cases r
    · rw [show qTwoVec F ω (4 : Fin 5) false =
          normPlaneVec F 3 (1 + ω) + normPlaneVec F 2 (1 + ω) from rfl]
      exact Submodule.add_mem _ (normPlaneVec_mem_suppPerp (E := E) h3 (1 + ω))
        (normPlaneVec_mem_suppPerp (E := E) h2 (1 + ω))
    · rw [show qTwoVec F ω (4 : Fin 5) true =
          normPlaneVec F 3 (1 + ω) + normPlaneVec F 2 ω from rfl]
      exact Submodule.add_mem _ (normPlaneVec_mem_suppPerp (E := E) h3 (1 + ω))
        (normPlaneVec_mem_suppPerp (E := E) h2 ω)

private theorem rootIdxD'_val_ge {j : Fin 5} (hj : 3 ≤ (j : ℕ)) :
    3 ≤ ((rootIdxD' 5 j : Fin 5) : ℕ) := by
  fin_cases j <;> simp_all [rootIdxD']

private theorem rootIdxD_val_ge {j : Fin 5} (hj : 3 ≤ (j : ℕ)) :
    3 ≤ ((rootIdxD 5 j : Fin 5) : ℕ) := by
  fin_cases j <;> simp_all [rootIdxD]

theorem commute_map_rankOne_zero {k : Fin 4} (hk : 2 ≤ (k : ℕ)) :
    ∀ x ∈ (rankOne (plusRootGroup 5 F (by norm_num)) 0).map (qTwoLambda E hω).symm.toMonoidHom,
      ∀ g ∈ normBlock E 4 {k}, Commute x g := by
  have hS : ∀ j ∈ ({k} : Finset (Fin 4)), 2 ≤ (j : ℕ) := by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact hk
  intro x hx g hg
  have hle : (rankOne (plusRootGroup 5 F (by norm_num)) 0).map
      (qTwoLambda E hω).symm.toMonoidHom ≤
      Subgroup.centralizer ({g} : Set (normOmega E 4)) := by
    rw [rankOne_plusRootGroup_eq_sup (n := 5) (by norm_num) (0 : Fin 5), Subgroup.map_sup,
      MonoidHom.map_range, MonoidHom.map_range]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine commute_of_coe_eq_eichler (E := E) (coe_symm_rootD (E := E) (hω := hω) 0 c) ?_ ?_
      · exact normBlock_apply_of_mem_suppPerp (E := E) hg
          (qTwoVec_mem_suppPerp_of_lt_two (E := E) hS (m := rootIdxD' 5 0) (by decide)
            (rootSignD 5 0))
      · rw [LinearEquiv.map_smul, normBlock_apply_of_mem_suppPerp (E := E) hg
          (qTwoVec_mem_suppPerp_of_lt_two (E := E) hS (m := rootIdxD 5 0) (by decide) true)]
    · rintro _ ⟨a, rfl⟩
      obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine commute_of_coe_eq_eichler (E := E) (coe_symm_negRootD (E := E) (hω := hω) 0 c) ?_ ?_
      · exact normBlock_apply_of_mem_suppPerp (E := E) hg
          (qTwoVec_mem_suppPerp_of_lt_two (E := E) hS (m := rootIdxD 5 0) (by decide) false)
      · rw [LinearEquiv.map_smul, normBlock_apply_of_mem_suppPerp (E := E) hg
          (qTwoVec_mem_suppPerp_of_lt_two (E := E) hS (m := rootIdxD' 5 0) (by decide)
            (!rootSignD 5 0))]
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem commute_map_rankOne_of_three_le {j : Fin 5} (hj : 3 ≤ (j : ℕ)) {k : Fin 4}
    (hk : (k : ℕ) < 2) :
    ∀ x ∈ (rankOne (plusRootGroup 5 F (by norm_num)) j).map (qTwoLambda E hω).symm.toMonoidHom,
      ∀ g ∈ normBlock E 4 {k}, Commute x g := by
  have hS : ∀ j' ∈ ({k} : Finset (Fin 4)), (j' : ℕ) < 2 := by
    intro j' hj'
    rw [Finset.mem_singleton] at hj'
    subst hj'
    exact hk
  intro x hx g hg
  have hle : (rankOne (plusRootGroup 5 F (by norm_num)) j).map
      (qTwoLambda E hω).symm.toMonoidHom ≤
      Subgroup.centralizer ({g} : Set (normOmega E 4)) := by
    rw [rankOne_plusRootGroup_eq_sup (n := 5) (by norm_num) j, Subgroup.map_sup,
      MonoidHom.map_range, MonoidHom.map_range]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine commute_of_coe_eq_eichler (E := E) (coe_symm_rootD (E := E) (hω := hω) j c) ?_ ?_
      · exact normBlock_apply_of_mem_suppPerp (E := E) hg
          (qTwoVec_mem_suppPerp_of_three_le (E := E) hS (rootIdxD'_val_ge hj) (rootSignD 5 j))
      · rw [LinearEquiv.map_smul, normBlock_apply_of_mem_suppPerp (E := E) hg
          (qTwoVec_mem_suppPerp_of_three_le (E := E) hS (rootIdxD_val_ge hj) true)]
    · rintro _ ⟨a, rfl⟩
      obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine commute_of_coe_eq_eichler (E := E) (coe_symm_negRootD (E := E) (hω := hω) j c) ?_ ?_
      · exact normBlock_apply_of_mem_suppPerp (E := E) hg
          (qTwoVec_mem_suppPerp_of_three_le (E := E) hS (rootIdxD_val_ge hj) false)
      · rw [LinearEquiv.map_smul, normBlock_apply_of_mem_suppPerp (E := E) hg
          (qTwoVec_mem_suppPerp_of_three_le (E := E) hS (rootIdxD'_val_ge hj) (!rootSignD 5 j))]
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
