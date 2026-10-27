module

public import CFSG.LieType.Steinberg.Classical.Symplectic.Commutator
public import CFSG.LieType.Steinberg.PartB
import all CFSG.LieType.Universal.SymplecticRoots
import CFSG.LieType.Universal.SymplecticRoots.Weyl
import CFSG.LieType.Universal.SymplecticExtras.RankOne

public noncomputable section

namespace CFSG.LieType.Steinberg.Sp

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.RootSystem TauCeti.GLSymplecticFin
  CFSG.Assembly.LowTwoRank

variable {n : ℕ} {F : Type} [Field F]

private def sgnAt (a k : Fin n) : ℤ := if a = k then -1 else 1

private theorem sgnAt_mul (a b k : Fin n) :
    sgnAt a k * sgnAt b k = 1 ∨ sgnAt a k * sgnAt b k = -1 := by
  unfold sgnAt
  split_ifs <;> simp

private theorem cast_sgnAt_mul (a b k : Fin n) (c : F) :
    ((sgnAt a k * sgnAt b k : ℤ) : F) * c =
      (if a = k then -1 else 1) * (if b = k then -1 else 1) * c := by
  unfold sgnAt
  split_ifs <;> simp

private theorem weylElt_conj_sign (k : Fin n) (r : RootSubgroupIndex n) :
    ∃ (r' : RootSubgroupIndex n) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
      stdVec r' = stdRefl n k (stdVec r) ∧ ∀ c : F,
        weylElt n F k * r.hom (Multiplicative.ofAdd c) * (weylElt n F k)⁻¹ =
          r'.hom (Multiplicative.ofAdd ((ε : F) * c)) := by
  by_cases h : k.val + 1 < n
  · rw [weylElt_of_lt n F h, stdRefl_of_lt n h]
    have hk := ne_succ n h
    cases r with
    | positiveLong a =>
      refine ⟨.positiveLong (Equiv.swap k ⟨k.val + 1, h⟩ a), 1, Or.inl rfl, ?_, fun c => ?_⟩
      · simp only [stdVec]
        rw [Pi.smul_comp, single_comp_swap]
      · simp only [RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply,
          toAdd_ofAdd, Int.cast_one, one_mul]
        exact shortWeyl_conj_positiveLong hk a c
    | negativeLong a =>
      refine ⟨.negativeLong (Equiv.swap k ⟨k.val + 1, h⟩ a), 1, Or.inl rfl, ?_, fun c => ?_⟩
      · simp only [stdVec]
        rw [Pi.neg_comp, Pi.smul_comp, single_comp_swap]
      · simp only [RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply,
          toAdd_ofAdd, Int.cast_one, one_mul]
        exact shortWeyl_conj_negativeLong hk a c
    | difference a b hab =>
      refine ⟨.difference _ _ ((Equiv.swap k ⟨k.val + 1, h⟩).injective.ne hab),
        sgnAt a k * sgnAt b k, sgnAt_mul a b k, ?_, fun c => ?_⟩
      · simp only [stdVec]
        rw [Pi.sub_comp, single_comp_swap, single_comp_swap]
      · simp only [RootSubgroupIndex.hom_difference, differenceShortRootHom_apply, toAdd_ofAdd]
        rw [cast_sgnAt_mul]
        exact shortWeyl_conj_difference hk hab c
    | positiveSum a b hab =>
      refine ⟨.short .positiveSum _ _ ((Equiv.swap k ⟨k.val + 1, h⟩).injective.ne hab.ne),
        sgnAt a k * sgnAt b k, sgnAt_mul a b k, ?_, fun c => ?_⟩
      · rw [stdVec_short_positiveSum]
        simp only [stdVec]
        rw [Pi.add_comp, single_comp_swap, single_comp_swap]
      · simp only [RootSubgroupIndex.hom_short, ShortRootFamily.hom_positiveSum,
          positiveSumShortRootHom_apply, RootSubgroupIndex.hom_positiveSum, toAdd_ofAdd]
        rw [cast_sgnAt_mul]
        exact shortWeyl_conj_positiveSum hk hab.ne c
    | negativeSum a b hab =>
      refine ⟨.short .negativeSum _ _ ((Equiv.swap k ⟨k.val + 1, h⟩).injective.ne hab.ne),
        sgnAt a k * sgnAt b k, sgnAt_mul a b k, ?_, fun c => ?_⟩
      · rw [stdVec_short_negativeSum]
        simp only [stdVec]
        rw [Pi.neg_comp, Pi.add_comp, single_comp_swap, single_comp_swap]
      · simp only [RootSubgroupIndex.hom_short, ShortRootFamily.hom_negativeSum,
          negativeSumShortRootHom_apply, RootSubgroupIndex.hom_negativeSum, toAdd_ofAdd]
        rw [cast_sgnAt_mul]
        exact shortWeyl_conj_negativeSum hk hab.ne c
  · rw [weylElt_of_not_lt n F h, stdRefl_of_not_lt n h]
    have hmax : ∀ a : Fin n, a ≠ k → a.val < k.val := fun a ha => by
      have := Fin.val_ne_of_ne ha
      omega
    have hneg : ∀ c : F, ((-1 : ℤ) : F) * c = -c := fun c => by push_cast; ring
    cases r with
    | positiveLong a =>
      rcases eq_or_ne k a with rfl | ha
      · refine ⟨.negativeLong k, -1, Or.inr rfl, ?_, fun c => ?_⟩
        · funext x
          simp only [stdVec, Pi.neg_apply, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
          split_ifs <;> simp_all
        · simp only [RootSubgroupIndex.hom_positiveLong, RootSubgroupIndex.hom_negativeLong,
            positiveLongRootTransvectionHom_apply, negativeLongRootTransvectionHom_apply,
            toAdd_ofAdd]
          rw [positiveLongRootWeylElement_inv, hneg]
          exact positiveLongRootWeylElement_mul_positiveLongRootTransvectionUnit_mul_inv k c
      · refine ⟨.positiveLong a, 1, Or.inl rfl, ?_, fun c => ?_⟩
        · funext x
          simp only [stdVec, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
          split_ifs <;> simp_all
        · simp only [RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply,
            toAdd_ofAdd, Int.cast_one, one_mul]
          exact longWeyl_conj_positiveLong_of_ne ha.symm c
    | negativeLong a =>
      rcases eq_or_ne k a with rfl | ha
      · refine ⟨.positiveLong k, -1, Or.inr rfl, ?_, fun c => ?_⟩
        · funext x
          simp only [stdVec, Pi.neg_apply, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
          split_ifs <;> simp_all
        · simp only [RootSubgroupIndex.hom_positiveLong, RootSubgroupIndex.hom_negativeLong,
            positiveLongRootTransvectionHom_apply, negativeLongRootTransvectionHom_apply,
            toAdd_ofAdd]
          rw [positiveLongRootWeylElement_inv, hneg]
          exact positiveLongRootWeylElement_mul_negativeLongRootTransvectionUnit_mul_inv k c
      · refine ⟨.negativeLong a, 1, Or.inl rfl, ?_, fun c => ?_⟩
        · funext x
          simp only [stdVec, Pi.neg_apply, nsmul_eq_mul]
          split_ifs <;> simp_all
        · simp only [RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply,
            toAdd_ofAdd, Int.cast_one, one_mul]
          exact longWeyl_conj_negativeLong_of_ne ha.symm c
    | difference a b hab =>
      rcases eq_or_ne k a with rfl | ha
      · refine ⟨.short .negativeSum k b hab, -1, Or.inr rfl, ?_, fun c => ?_⟩
        · rw [stdVec_short_negativeSum]
          funext x
          simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
        · simp only [RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_short,
            ShortRootFamily.hom_negativeSum, differenceShortRootHom_apply,
            negativeSumShortRootHom_apply, toAdd_ofAdd]
          rw [hneg]
          exact longWeyl_conj_difference_left hab c
      rcases eq_or_ne k b with rfl | hb
      · refine ⟨.short .positiveSum a k hab, -1, Or.inr rfl, ?_, fun c => ?_⟩
        · rw [stdVec_short_positiveSum]
          funext x
          simp only [stdVec, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
        · simp only [RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_short,
            ShortRootFamily.hom_positiveSum, differenceShortRootHom_apply,
            positiveSumShortRootHom_apply, toAdd_ofAdd]
          rw [hneg]
          exact longWeyl_conj_difference_right hab c
      · refine ⟨.difference a b hab, 1, Or.inl rfl, ?_, fun c => ?_⟩
        · funext x
          simp only [stdVec, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
        · simp only [RootSubgroupIndex.hom_difference, differenceShortRootHom_apply,
            toAdd_ofAdd, Int.cast_one, one_mul]
          exact longWeyl_conj_difference_of_ne hab ha.symm hb.symm c
    | positiveSum a b hab =>
      have ha : a ≠ k := fun e => by
        have := hmax b (fun e' => by subst e e'; exact lt_irrefl _ hab)
        have : a.val < b.val := hab
        omega
      rcases eq_or_ne k b with rfl | hb
      · refine ⟨.difference a k hab.ne, 1, Or.inl rfl, ?_, fun c => ?_⟩
        · funext x
          simp only [stdVec, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
        · simp only [RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_positiveSum,
            differenceShortRootHom_apply, positiveSumShortRootHom_apply, toAdd_ofAdd,
            Int.cast_one, one_mul]
          exact longWeyl_conj_positiveSum_right hab.ne c
      · refine ⟨.positiveSum a b hab, 1, Or.inl rfl, ?_, fun c => ?_⟩
        · funext x
          simp only [stdVec, Pi.add_apply, Pi.single_apply]
          split_ifs <;> simp_all
        · simp only [RootSubgroupIndex.hom_positiveSum, positiveSumShortRootHom_apply,
            toAdd_ofAdd, Int.cast_one, one_mul]
          exact longWeyl_conj_positiveSum_of_ne hab.ne ha hb.symm c
    | negativeSum a b hab =>
      have ha : a ≠ k := fun e => by
        have := hmax b (fun e' => by subst e e'; exact lt_irrefl _ hab)
        have : a.val < b.val := hab
        omega
      rcases eq_or_ne k b with rfl | hb
      · refine ⟨.difference k a hab.ne.symm, 1, Or.inl rfl, ?_, fun c => ?_⟩
        · funext x
          simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
        · simp only [RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_negativeSum,
            differenceShortRootHom_apply, negativeSumShortRootHom_apply, toAdd_ofAdd,
            Int.cast_one, one_mul]
          exact longWeyl_conj_negativeSum_right hab.ne c
      · refine ⟨.negativeSum a b hab, 1, Or.inl rfl, ?_, fun c => ?_⟩
        · funext x
          simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.single_apply]
          split_ifs <;> simp_all
        · simp only [RootSubgroupIndex.hom_negativeSum, negativeSumShortRootHom_apply,
            toAdd_ofAdd, Int.cast_one, one_mul]
          exact longWeyl_conj_negativeSum_of_ne hab.ne ha hb.symm c

theorem weylRep_conj_x (k : Fin n) {β : Fin n → ℤ} (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ u : F,
      weylRep n F k * x n F β u * (weylRep n F k)⁻¹ =
        x n F (reflection (cartanC n) k β) ((ε : F) * u) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hβ
  obtain ⟨r', ε, hε, hstd, hconj⟩ := weylElt_conj_sign (F := F) k r
  refine ⟨ε, hε, fun u => ?_⟩
  rw [x_eq hr, x_eq (r := r') (by rw [hstd, hr, toStd_reflection]), weylRep_eq, elt, elt,
    ← map_inv, ← map_mul, ← map_mul, hconj u]

theorem character_zpow (r : RootSubgroupIndex n) (t : Fˣ) (u : Fin n → ℤ) :
    r.character (fun a => t ^ u a) = t ^ (stdVec r ⬝ᵥ u) := by
  cases r with
  | positiveLong i =>
    rw [RootSubgroupIndex.character_positiveLong, ← _root_.zpow_add]
    simp [stdVec, two_mul]
  | negativeLong i =>
    rw [RootSubgroupIndex.character_negativeLong, ← _root_.zpow_add, ← _root_.zpow_neg]
    simp [stdVec, two_mul]
  | difference i j hij =>
    rw [RootSubgroupIndex.character_difference, ← _root_.zpow_neg, ← _root_.zpow_add]
    simp [stdVec, sub_eq_add_neg]
  | positiveSum i j hij =>
    rw [RootSubgroupIndex.character_positiveSum, ← _root_.zpow_add]
    simp [stdVec]
  | negativeSum i j hij =>
    rw [RootSubgroupIndex.character_negativeSum, ← _root_.zpow_add, ← _root_.zpow_neg]
    simp [stdVec]

private theorem coroot_eq_dot (k : Fin n) (v : Fin n → ℤ) :
    coroot (cartanC n) k v = toStd n v ⬝ᵥ cvec n k := by
  by_cases h : k.val + 1 < n
  · rw [coroot_cartanC_of_lt n h]
    have hc : cvec n k = Pi.single k 1 - Pi.single ⟨k.val + 1, h⟩ 1 := by
      funext a
      simp only [cvec, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
    rw [hc, dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]
  · rw [coroot_cartanC_of_not_lt n h]
    have hc : cvec n k = Pi.single k 1 := by
      funext a
      have := a.2
      simp only [cvec, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
    rw [hc, dotProduct_single, mul_one]

theorem torus_conj_x (k : Fin n) (t : Fˣ) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) (v : F) :
    equivStatedSp n F (diagonal (corootVec n F k t)) * x n F γ v *
        (equivStatedSp n F (diagonal (corootVec n F k t)))⁻¹ =
      x n F γ (((t ^ coroot (cartanC n) k γ : Fˣ) : F) * v) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  rw [x_eq hr, x_eq hr, elt, elt, ← map_inv, ← map_mul, ← map_mul,
    diagonal_mul_rootSubgroup_mul_inv, toAdd_ofAdd, corootVec_eq_zpow, character_zpow, hr,
    ← coroot_eq_dot]

private theorem elt_difference_eq {i j : Fin n} (hij : i ≠ j) (c : F) :
    elt (.difference i j hij) c = equivStatedSp n F (differenceShortRootUnit hij c) := by
  rw [elt, RootSubgroupIndex.hom_difference, differenceShortRootHom_apply, toAdd_ofAdd]

private theorem elt_positiveLong_eq (i : Fin n) (c : F) :
    elt (.positiveLong i) c = equivStatedSp n F (positiveLongRootTransvectionUnit i c) := by
  rw [elt, RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply, toAdd_ofAdd]

private theorem elt_negativeLong_eq (i : Fin n) (c : F) :
    elt (.negativeLong i) c = equivStatedSp n F (negativeLongRootTransvectionUnit i c) := by
  rw [elt, RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply, toAdd_ofAdd]

theorem weylElement_eq (k : Fin n) (t : Fˣ) :
    weylElement (x n F) k t =
      equivStatedSp n F (diagonal (corootVec n F k t)) * weylRep n F k := by
  by_cases hk : k.val + 1 < n
  · have hk' := ne_succ' hk
    rw [weylElement, x_eq (stdVec_shortPos_eq hk), x_eq (stdVec_shortNeg_eq hk),
      weylRep_eq_short hk, corootVec_of_lt n F hk, diagonal_twoPoint_eq hk' t]
    simp only [map_mul, ← elt_difference_eq]
    have e1 : elt (.difference k ⟨k.val + 1, hk⟩ hk') (-1 : F) =
        (elt (.difference k ⟨k.val + 1, hk⟩ hk') 1)⁻¹ := elt_neg _ _
    have e2 : elt (.difference ⟨k.val + 1, hk⟩ k hk'.symm) (1 : F) =
        (elt (.difference ⟨k.val + 1, hk⟩ k hk'.symm) (-1))⁻¹ := by
      rw [← elt_neg, neg_neg]
    rw [e1, e2]
    group
  · rw [weylElement, x_eq (stdVec_positiveLong_eq hk), x_eq (stdVec_negativeLong_eq hk),
      weylRep_eq_long hk, corootVec_of_not_lt n F hk, diagonal_mulSingle_eq k t]
    simp only [map_mul, ← elt_positiveLong_eq, ← elt_negativeLong_eq]
    have e1 : elt (.positiveLong k) (-1 : F) = (elt (.positiveLong k) 1)⁻¹ := elt_neg _ _
    have e2 : elt (.negativeLong k) (1 : F) = (elt (.negativeLong k) (-1))⁻¹ := by
      rw [← elt_neg, neg_neg]
    rw [e1, e2]
    group

theorem weyl (i : Fin n) {β : Fin n → ℤ} (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (t : Fˣ) (u : F),
      weylElement (x n F) i t * x n F β u * (weylElement (x n F) i t)⁻¹ =
        x n F (reflection (cartanC n) i β)
          ((ε : F) * ((t ^ (-(∑ j, cartanC n i j * β j)) : Fˣ) : F) * u) := by
  obtain ⟨ε, hε, hn⟩ := weylRep_conj_x (F := F) i hβ
  refine ⟨ε, hε, fun t u => ?_⟩
  have hrefl : reflection (cartanC n) i β ∈ roots (isFiniteType_cartanC n) ∅ :=
    (Φ n F).refl_mem i β hβ
  have hii : cartanC n i i = 2 := by simp [cartanC]
  rw [weylElement_eq, _root_.mul_inv_rev,
    show ∀ a b c : StatedSp n F, a * b * c * (b⁻¹ * a⁻¹) = a * (b * c * b⁻¹) * a⁻¹ by
      intros; group,
    hn u, torus_conj_x i t hrefl, coroot_reflection hii, ← coroot_apply]
  congr 1
  ring

end CFSG.LieType.Steinberg.Sp
