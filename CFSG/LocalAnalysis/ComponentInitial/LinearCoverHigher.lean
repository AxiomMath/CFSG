module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigherRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverDihedral

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup Matrix LinearFlag
open scoped commutatorElement

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def rootSL (i j : Fin n) : Matrix.SpecialLinearGroup (Fin n) K :=
  if h : i = j then 1 else Matrix.SpecialLinearGroup.transvection h 1

theorem rootSL_self (i : Fin n) : rootSL (K := K) i i = 1 :=
  dite_eq_left rfl

theorem rootSL_of_ne {i j : Fin n} (h : i ≠ j) :
    rootSL (K := K) i j = Matrix.SpecialLinearGroup.transvection h 1 :=
  dite_eq_right h

theorem coe_rootSL_of_ne {i j : Fin n} (h : i ≠ j) :
    (rootSL (K := K) i j : Matrix (Fin n) (Fin n) K) = transvection i j 1 := by
  rw [rootSL_of_ne (K := K) h]
  rfl

theorem rootSL_mul_self [CharP K 2] (i j : Fin n) : rootSL (K := K) i j * rootSL i j = 1 := by
  by_cases h : i = j
  · rw [h, rootSL_self (K := K), mul_one]
  · rw [rootSL_of_ne (K := K) h, ← Matrix.SpecialLinearGroup.transvection_add,
      CharTwo.add_self_eq_zero, Matrix.SpecialLinearGroup.transvection_coeff_zero]

theorem rootSL_mul_comm {i j k l : Fin n} (hjk : j ≠ k) (hli : l ≠ i) :
    rootSL (K := K) i j * rootSL k l = rootSL k l * rootSL i j := by
  by_cases hij : i = j
  · rw [hij, rootSL_self (K := K), one_mul, mul_one]
  by_cases hkl : k = l
  · rw [hkl, rootSL_self (K := K), one_mul, mul_one]
  rw [rootSL_of_ne (K := K) hij, rootSL_of_ne (K := K) hkl]
  exact (Matrix.SpecialLinearGroup.commute_transvection hij hkl hjk hli 1 1).eq

theorem commutatorElement_rootSL {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    ⁅rootSL (K := K) i j, rootSL (K := K) j l⁆ = rootSL i l := by
  rw [rootSL_of_ne (K := K) hij, rootSL_of_ne (K := K) hjl, rootSL_of_ne (K := K) hil,
    Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjl hil, mul_one]

theorem rootSL_mem_unitriangular {i j : Fin n} (h : i < j) :
    rootSL (K := K) i j ∈ unitriangular n K := by
  rw [mem_unitriangular, coe_rootSL_of_ne (K := K) h.ne]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [transvection, Matrix.add_apply, one_apply_ne hab.ne', single_apply, ite_eq_right,
      add_zero]
    rintro ⟨rfl, rfl⟩
    exact absurd (h.trans hab) (lt_irrefl _)
  · rw [transvection, Matrix.add_apply, one_apply_eq, single_apply, ite_eq_right, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_irrefl _ h

theorem unitriangular_le_closure_rootSL (hK : Nat.card K = 2) :
    unitriangular n K ≤ Subgroup.closure {g | ∃ i j : Fin n, i < j ∧ rootSL i j = g} := by
  have := Classical.decEq K
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two le_rfl (by rw [hK, pow_one])
  set X := {g | ∃ i j : Fin n, i < j ∧ rootSL (K := K) i j = g}
  let supp : Matrix.SpecialLinearGroup (Fin n) K → Finset (Fin n × Fin n) := fun u =>
    Finset.univ.filter fun p => p.1 < p.2 ∧ (u : Matrix (Fin n) (Fin n) K) p.1 p.2 ≠ 0
  have hsupp : ∀ u p, p ∈ supp u ↔ p.1 < p.2 ∧ (u : Matrix (Fin n) (Fin n) K) p.1 p.2 ≠ 0 :=
    fun u p => by simp [supp]
  suffices h : ∀ (m : ℕ) (u : Matrix.SpecialLinearGroup (Fin n) K), u ∈ unitriangular n K →
      (supp u).card ≤ m → u ∈ Subgroup.closure X from fun u hu => h _ u hu le_rfl
  intro m
  induction m with
  | zero =>
    intro u hu hm
    have hempty : supp u = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hm)
    have hu1 : u = 1 := by
      ext a b
      rcases lt_trichotomy a b with hab | rfl | hab
      · rw [Matrix.SpecialLinearGroup.coe_one, one_apply_ne hab.ne]
        by_contra hne
        have hmem : (a, b) ∈ supp u := (hsupp u (a, b)).mpr ⟨hab, hne⟩
        rw [hempty] at hmem
        exact Finset.notMem_empty _ hmem
      · rw [hu.2 a, Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
      · rw [hu.1 a b hab, Matrix.SpecialLinearGroup.coe_one, one_apply_ne hab.ne']
    rw [hu1]
    exact one_mem _
  | succ m ih =>
    intro u hu hm
    rcases (supp u).eq_empty_or_nonempty with hempty | hne
    · exact ih u hu (by rw [hempty]; exact Nat.zero_le _)
    obtain ⟨⟨i, j⟩, hij, hmin⟩ := Finset.exists_min_image (supp u) (fun p => p.2) hne
    replace hmin : ∀ p ∈ supp u, j ≤ p.2 := hmin
    obtain ⟨hij', hu0⟩ : i < j ∧ (u : Matrix (Fin n) (Fin n) K) i j ≠ 0 := (hsupp u (i, j)).mp hij
    have huij : (u : Matrix (Fin n) (Fin n) K) i j = 1 :=
      (eq_zero_or_eq_one_of_card_eq_two hK _).resolve_left hu0
    have hcol : ∀ a, (u : Matrix (Fin n) (Fin n) K) a i = if a = i then 1 else 0 := by
      intro a
      rcases lt_trichotomy a i with hai | rfl | hai
      · rw [ite_eq_right hai.ne]
        by_contra hne
        have hji : j ≤ i := hmin (a, i) ((hsupp u (a, i)).mpr ⟨hai, hne⟩)
        exact absurd (hji.trans_lt hij') (lt_irrefl _)
      · rw [ite_eq_left rfl, hu.2]
      · rw [ite_eq_right hai.ne', hu.1 a i hai]
    set u' := u * rootSL i j with hu'def
    have hu' : u' ∈ unitriangular n K := mul_mem hu (rootSL_mem_unitriangular (K := K) hij')
    have hentry : ∀ a b, (u' : Matrix (Fin n) (Fin n) K) a b = if b = j then
        (u : Matrix (Fin n) (Fin n) K) a j + (if a = i then 1 else 0)
        else (u : Matrix (Fin n) (Fin n) K) a b := by
      intro a b
      rw [hu'def, Matrix.SpecialLinearGroup.coe_mul, coe_rootSL_of_ne (K := K) hij'.ne]
      by_cases hb : b = j
      · rw [ite_eq_left hb, hb, mul_transvection_apply_same, one_mul, hcol]
      · rw [ite_eq_right hb, mul_transvection_apply_of_ne _ _ _ _ hb]
    have hsub : supp u' ⊆ (supp u).erase (i, j) := by
      rintro ⟨a, b⟩ hab
      obtain ⟨hab', hne⟩ := (hsupp u' (a, b)).mp hab
      rw [hentry] at hne
      rw [Finset.mem_erase, hsupp]
      by_cases hb : b = j
      · rw [ite_eq_left hb] at hne
        rw [hb] at hab' ⊢
        by_cases ha : a = i
        · rw [ite_eq_left ha, ha, huij, CharTwo.add_self_eq_zero] at hne
          exact absurd rfl hne
        · rw [ite_eq_right ha, add_zero] at hne
          exact ⟨fun h => ha (Prod.mk.inj h).1, hab', hne⟩
      · rw [ite_eq_right hb] at hne
        exact ⟨fun h => hb (Prod.mk.inj h).2, hab', hne⟩
    have hcard : (supp u').card ≤ m := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hij] at h1
      omega
    have hu_eq : u = u' * rootSL i j := by
      rw [hu'def, mul_assoc, rootSL_mul_self (K := K), mul_one]
    rw [hu_eq]
    exact mul_mem (ih u' hu' hcard) (Subgroup.subset_closure ⟨i, j, hij', rfl⟩)

@[expose] def projTypeARoots [CharP K 2] (n : ℕ) : TypeARoots (projectiveSL n K) n where
  x i j := proj n K (rootSL i j)
  mul_self i j _ := by rw [← map_mul, rootSL_mul_self (K := K), map_one]
  comm i j k l _ _ hjk hil := by
    rw [← map_mul, ← map_mul, rootSL_mul_comm (K := K) hjk hil.symm]
  commutator i j l hij hjl hil := by
    rw [← map_commutatorElement, commutatorElement_rootSL (K := K) hij hjl hil]


theorem ker_eq_bot_of_projectiveSL [Finite K] (hK : Nat.card K = 2) (hn : 5 ≤ n) {E : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] (η : E →* projectiveSL n K)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) :
    η.ker = ⊥ := by
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two le_rfl (by rw [hK, pow_one])
  refine (projTypeARoots (K := K) n).ker_eq_bot η hn (projUnitriangular n K)
    (exists_sylow_projUnitriangular (K := K) 2 (n := n) (by omega)) ?_ ?_ hη hC h2
  · rw [projUnitriangular]
    refine (map_mono (unitriangular_le_closure_rootSL hK)).trans ?_
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩
    exact ⟨i, j, hij, rfl⟩
  · rw [card_projUnitriangular, hK]

theorem even_higher_linear_prime_field_central_two_cover_trivial {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) {n : ℕ}
    (hn : 5 ≤ n) (hJ : CFSG.Blueprint.LieModel J .PSL n 2 1) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hJ
  have hK : Nat.card K = 2 := by rw [hcard, pow_one]
  set η' : E →* projectiveSL n K := e.toMonoidHom.comp η
  have hη' : Function.Surjective η' := e.surjective.comp hη
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_projectiveSL hK hn η' hη' (hker' ▸ hC) (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
