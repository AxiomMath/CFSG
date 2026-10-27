module

public import CFSG.Assembly.Defs

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix
open scoped commutatorElement

@[expose] def binaryAltMatrices (r : ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) (ZMod 2)) where
  carrier := {X | Xᵀ = X ∧ ∀ i, X i i = 0}
  add_mem' {X Y} hX hY := ⟨by rw [transpose_add, hX.1, hY.1], fun i => by
    rw [Matrix.add_apply, hX.2 i, hY.2 i, add_zero]⟩
  zero_mem' := ⟨transpose_zero, fun _ => rfl⟩
  neg_mem' {X} hX := ⟨by rw [transpose_neg, hX.1], fun i => by simp [hX.2 i]⟩

theorem mem_binaryAltMatrices {r : ℕ} {X : Matrix (Fin r) (Fin r) (ZMod 2)} :
    X ∈ binaryAltMatrices r ↔ Xᵀ = X ∧ ∀ i, X i i = 0 :=
  Iff.rfl

section BinarySection

variable {r : ℕ}

@[expose] def binaryUpperPairs (r : ℕ) : Finset (Fin r × Fin r) :=
  Finset.univ.filter fun p => p.1 < p.2

theorem binaryUpperSum_apply (X : Matrix (Fin r) (Fin r) (ZMod 2)) (a b : Fin r) :
    (∑ p ∈ binaryUpperPairs r, X p.1 p.2 • (single p.1 p.2 (1 : ZMod 2) + single p.2 p.1 1) :
      Matrix (Fin r) (Fin r) (ZMod 2)) a b =
      if a < b then X a b else if b < a then X b a else 0 := by
  have h1 : ∀ p : Fin r × Fin r, (p.1 = a ∧ p.2 = b) ↔ p = (a, b) := fun p => by
    rw [Prod.ext_iff]
  have h2 : ∀ p : Fin r × Fin r, (p.2 = a ∧ p.1 = b) ↔ p = (b, a) := fun p => by
    rw [Prod.ext_iff, and_comm]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply, single_apply, smul_eq_mul,
    h1, h2, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [binaryUpperPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with hab hba hba <;> first | exact absurd hab (lt_asymm hba) | simp

variable {G : Type*} [CommGroup G]

@[expose] def binarySectionHom (S : Fin r → Fin r → G) (hS : ∀ i j, S i j ^ 2 = 1) :
    Multiplicative (Matrix (Fin r) (Fin r) (ZMod 2)) →* G where
  toFun X := ∏ p ∈ binaryUpperPairs r, S p.1 p.2 ^ (X.toAdd p.1 p.2).val
  map_one' := by simp
  map_mul' X Y := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [toAdd_mul, Matrix.add_apply, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ (hS _ _)).symm

theorem binarySectionHom_apply (S : Fin r → Fin r → G) (hS : ∀ i j, S i j ^ 2 = 1)
    (X : Multiplicative (Matrix (Fin r) (Fin r) (ZMod 2))) :
    binarySectionHom S hS X = ∏ p ∈ binaryUpperPairs r, S p.1 p.2 ^ (X.toAdd p.1 p.2).val :=
  rfl

theorem binarySectionHom_single (S : Fin r → Fin r → G) (hS : ∀ i j, S i j ^ 2 = 1)
    {i j : Fin r} (hij : i < j) :
    binarySectionHom S hS (Multiplicative.ofAdd (single i j 1)) = S i j := by
  rw [binarySectionHom_apply, Finset.prod_eq_single (i, j)]
  · rw [toAdd_ofAdd, single_apply, ite_eq_left ⟨rfl, rfl⟩]
    exact pow_one _
  · intro p _ hp
    rw [toAdd_ofAdd, single_apply, ite_eq_right_iff.mpr fun h => absurd
      (Prod.ext h.1.symm h.2.symm) hp, ZMod.val_zero, pow_zero]
  · intro h
    exact absurd (show (i, j) ∈ binaryUpperPairs r from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩) h

theorem map_binarySectionHom (S : Fin r → Fin r → G) (hS : ∀ i j, S i j ^ 2 = 1)
    (τ : G →* Multiplicative (Matrix (Fin r) (Fin r) (ZMod 2)))
    (hτS : ∀ i j, i ≠ j → τ (S i j) = Multiplicative.ofAdd (single i j 1 + single j i 1))
    (X : Multiplicative (Matrix (Fin r) (Fin r) (ZMod 2))) :
    τ (binarySectionHom S hS X) = Multiplicative.ofAdd (∑ p ∈ binaryUpperPairs r,
      X.toAdd p.1 p.2 • (single p.1 p.2 (1 : ZMod 2) + single p.2 p.1 1)) := by
  rw [binarySectionHom_apply, map_prod, ofAdd_sum]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2.ne
  rw [map_pow, hτS _ _ hne, ← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2),
    ZMod.natCast_zmod_val]

theorem binarySection_closure_spec (S : Fin r → Fin r → G) (hS2 : ∀ i j, S i j ^ 2 = 1)
    (hSdiag : ∀ i, S i i = 1) (hSsymm : ∀ i j, S i j = S j i)
    (τ : G →* Multiplicative (Matrix (Fin r) (Fin r) (ZMod 2)))
    (hτS : ∀ i j, i ≠ j → τ (S i j) = Multiplicative.ofAdd (single i j 1 + single j i 1)) :
    (∀ x ∈ Subgroup.closure (Set.range fun p : Fin r × Fin r => S p.1 p.2), τ x = 1 → x = 1) ∧
    ∀ X ∈ binaryAltMatrices r,
      ∃ x ∈ Subgroup.closure (Set.range fun p : Fin r × Fin r => S p.1 p.2),
        τ x = Multiplicative.ofAdd X := by
  have hle : Subgroup.closure (Set.range fun p : Fin r × Fin r => S p.1 p.2) ≤
      (binarySectionHom S hS2).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    rcases lt_trichotomy i j with h | rfl | h
    · exact ⟨Multiplicative.ofAdd (single i j 1), binarySectionHom_single S hS2 h⟩
    · exact ⟨1, (map_one _).trans (hSdiag i).symm⟩
    · exact ⟨Multiplicative.ofAdd (single j i 1), by rw [binarySectionHom_single S hS2 h, hSsymm]⟩
  refine ⟨fun x hx hτx => ?_, fun X hX => ?_⟩
  · obtain ⟨Y, rfl⟩ := hle hx
    rw [map_binarySectionHom S hS2 τ hτS] at hτx
    have hzero : ∀ p ∈ binaryUpperPairs r, Y.toAdd p.1 p.2 = 0 := by
      intro p hp
      have h := congrArg Multiplicative.toAdd hτx
      rw [toAdd_ofAdd, toAdd_one] at h
      have h' := congrFun₂ h p.1 p.2
      rw [binaryUpperSum_apply, ite_eq_left (Finset.mem_filter.mp hp).2] at h'
      exact h'
    rw [binarySectionHom_apply]
    exact Finset.prod_eq_one fun p hp => by rw [hzero p hp, ZMod.val_zero, pow_zero]
  · refine ⟨binarySectionHom S hS2 (Multiplicative.ofAdd X), ?_, ?_⟩
    · rw [binarySectionHom_apply]
      exact Subgroup.prod_mem _ fun p _ =>
        Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self p)) _
    · rw [map_binarySectionHom S hS2 τ hτS, toAdd_ofAdd]
      congr 1
      ext a b
      rw [binaryUpperSum_apply]
      obtain ⟨hXt, hXd⟩ := hX
      split_ifs with hab hba
      · rfl
      · exact congrFun₂ hXt a b
      · rw [le_antisymm (not_lt.mp hba) (not_lt.mp hab), hXd]

end BinarySection

section ClassTwo

variable {M : Type*} [Group M]

@[expose] def binaryPolarComm (a b : M) : M :=
  a⁻¹ * b⁻¹ * a * b

theorem binaryPolarComm_eq_commutatorElement (a b : M) :
    binaryPolarComm a b = ⁅a⁻¹, b⁻¹⁆ := by
  rw [binaryPolarComm, commutatorElement_def, inv_inv, inv_inv]

theorem binaryPolarComm_self (a : M) : binaryPolarComm a a = 1 := by
  rw [binaryPolarComm]
  group

theorem binaryPolarComm_inv (a b : M) : (binaryPolarComm a b)⁻¹ = binaryPolarComm b a := by
  rw [binaryPolarComm, binaryPolarComm]
  group

theorem binaryPolarComm_eq_one_of_mem_center_left {a : M} (ha : a ∈ Subgroup.center M) (b : M) :
    binaryPolarComm a b = 1 := by
  have h := Subgroup.mem_center_iff.mp ha b⁻¹
  rw [binaryPolarComm, mul_assoc a⁻¹, h]
  group

theorem binaryPolarComm_eq_one_of_mem_center_right (a : M) {b : M}
    (hb : b ∈ Subgroup.center M) : binaryPolarComm a b = 1 := by
  rw [← binaryPolarComm_inv, binaryPolarComm_eq_one_of_mem_center_left hb, inv_one]

theorem binaryPolarComm_mul_left {a b : M} (h : binaryPolarComm a b ∈ Subgroup.center M)
    (a' : M) : binaryPolarComm (a * a') b = binaryPolarComm a b * binaryPolarComm a' b := by
  have hc := Subgroup.mem_center_iff.mp h a'⁻¹
  calc binaryPolarComm (a * a') b = a'⁻¹ * binaryPolarComm a b * (b⁻¹ * a' * b) := by
        simp only [binaryPolarComm]
        group
    _ = binaryPolarComm a b * a'⁻¹ * (b⁻¹ * a' * b) := by rw [hc]
    _ = binaryPolarComm a b * binaryPolarComm a' b := by
        simp only [binaryPolarComm]
        group

theorem binaryPolarComm_mul_right {a b : M} (h : binaryPolarComm a b ∈ Subgroup.center M)
    (b' : M) : binaryPolarComm a (b * b') = binaryPolarComm a b' * binaryPolarComm a b := by
  have hc := Subgroup.mem_center_iff.mp h b'
  calc binaryPolarComm a (b * b') = a⁻¹ * b'⁻¹ * a * (binaryPolarComm a b * b') := by
        simp only [binaryPolarComm]
        group
    _ = a⁻¹ * b'⁻¹ * a * (b' * binaryPolarComm a b) := by rw [← hc]
    _ = binaryPolarComm a b' * binaryPolarComm a b := by
        simp only [binaryPolarComm]
        group

end ClassTwo

section Binary

variable {r : ℕ}

@[expose] def binaryTransvection {k i : Fin r} (h : k ≠ i) : GL (Fin r) (ZMod 2) :=
  ⟨transvection k i (1 : ZMod 2), transvection k i (1 : ZMod 2),
    by rw [transvection_mul_transvection_same _ _ h, show (1 : ZMod 2) + 1 = 0 from rfl,
      transvection_zero],
    by rw [transvection_mul_transvection_same _ _ h, show (1 : ZMod 2) + 1 = 0 from rfl,
      transvection_zero]⟩

theorem binaryTransvection_mulVec {k i : Fin r} (h : k ≠ i) (v : Fin r → ZMod 2) :
    (binaryTransvection h : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ v = v + Pi.single k (v i) := by
  change transvection k i 1 *ᵥ v = _
  rw [transvection, add_mulVec, one_mulVec, single_mulVec, one_mul]
  rfl

theorem binaryTransvection_mulVec_single_self {k i : Fin r} (h : k ≠ i) :
    (binaryTransvection h : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ Pi.single i 1 =
      Pi.single i 1 + Pi.single k 1 := by
  rw [binaryTransvection_mulVec, Pi.single_eq_same]

theorem binaryTransvection_mulVec_single_of_ne {k i j : Fin r} (h : k ≠ i) (hj : j ≠ i) :
    (binaryTransvection h : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ Pi.single j 1 = Pi.single j 1 := by
  rw [binaryTransvection_mulVec, Pi.single_eq_of_ne hj.symm, Pi.single_zero, add_zero]

theorem exists_ne_ne_of_three_le (hr : 3 ≤ r) (j k : Fin r) : ∃ i : Fin r, i ≠ j ∧ i ≠ k := by
  by_contra! h
  have hsub : (Finset.univ : Finset (Fin r)) ⊆ {j, k} := fun z _ => by
    rcases eq_or_ne z j with hz | hz
    · simp [hz]
    · simp [h z hz]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at this
  have := Finset.card_le_two (a := j) (b := k)
  omega

theorem vecMulVec_single_single (i j : Fin r) :
    vecMulVec (Pi.single i (1 : ZMod 2)) (Pi.single j 1) = single i j 1 := by
  ext a b
  simp only [vecMulVec_apply, Pi.single_apply, single_apply]
  split_ifs <;> simp_all

theorem binary_add_self (X : Matrix (Fin r) (Fin r) (ZMod 2)) : X + X = 0 := by
  ext a b
  exact CharTwo.add_self_eq_zero _

theorem binary_add_add_add_self (X Y : Matrix (Fin r) (Fin r) (ZMod 2)) : X + Y + X + Y = 0 := by
  rw [add_right_comm X Y X, binary_add_self, zero_add, binary_add_self]

theorem binary_prod_add_self (v : (Fin r → ZMod 2) × (Fin r → ZMod 2)) : v + v = 0 :=
  Prod.ext (funext fun _ => CharTwo.add_self_eq_zero _) (funext fun _ => CharTwo.add_self_eq_zero _)

end Binary

theorem eq_top_of_binary_lifts {r : ℕ} {M : Type*} [Group M]
    (π : M →* Multiplicative ((Fin r → ZMod 2) × (Fin r → ZMod 2))) {p q : Fin r → M}
    (hp : ∀ i, π (p i) = Multiplicative.ofAdd (Pi.single i 1, 0))
    (hq : ∀ i, π (q i) = Multiplicative.ofAdd (0, Pi.single i 1)) {K : Subgroup M}
    (hK : π.ker ≤ K) (hpK : ∀ i, p i ∈ K) (hqK : ∀ i, q i ∈ K) : K = ⊤ := by
  refine eq_top_iff.mpr fun m _ => ?_
  have hsum : ∀ x : Fin r → ZMod 2, ∑ i, (x i).val • (Pi.single i (1 : ZMod 2)) = x := by
    intro x
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j (fun i _ hij => by
      rw [Pi.smul_apply, Pi.single_eq_of_ne hij.symm, smul_zero]) (by simp), Pi.smul_apply,
      Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  have hmap : ∀ u, u ∈ K.map π := by
    intro u
    have hu : u = (∏ i, π (p i) ^ (u.toAdd.1 i).val) * ∏ i, π (q i) ^ (u.toAdd.2 i).val := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_prod, toAdd_prod]
      simp only [toAdd_pow, hp, hq, toAdd_ofAdd]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero,
          add_zero, hsum]
      · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero,
          zero_add, hsum]
    rw [hu]
    exact Subgroup.mul_mem _
      (Subgroup.prod_mem _ fun i _ => Subgroup.pow_mem _ (Subgroup.mem_map_of_mem π (hpK i)) _)
      (Subgroup.prod_mem _ fun i _ => Subgroup.pow_mem _ (Subgroup.mem_map_of_mem π (hqK i)) _)
  obtain ⟨k, hk, hkm⟩ := hmap (π m)
  have hkm' : k⁻¹ * m ∈ K := hK (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkm]
    exact inv_mul_cancel _)
  have := K.mul_mem hk hkm'
  rwa [mul_inv_cancel_left] at this

section Complement

variable {r : ℕ} {M : Type*} [Group M]

open CFSG.Assembly in
theorem binaryPolar_commutator_complement (hr : 3 ≤ r) {C T : Subgroup M} (hCT : C ≤ T)
    (hTZ : T ≤ Subgroup.center M)
    (π : M →* Multiplicative ((Fin r → ZMod 2) × (Fin r → ZMod 2))) (hπ : Function.Surjective π)
    (hπT : π.ker = T) (τ : T →* Multiplicative (binaryAltMatrices r))
    (hτC : τ.ker = C.subgroupOf T) (act : GL (Fin r) (ZMod 2) →* MulAut M)
    (hactC : ∀ g, ∀ c ∈ C, act g c = c)
    (hπact : ∀ g m, π (act g m) = Multiplicative.ofAdd
      ((g : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ (π m).toAdd.1,
        (g : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ (π m).toAdd.2))
    (hτcomm : ∀ (m n : M) (h : m⁻¹ * n⁻¹ * m * n ∈ T),
      ((τ ⟨m⁻¹ * n⁻¹ * m * n, h⟩).toAdd : Matrix (Fin r) (Fin r) (ZMod 2)) =
        vecMulVec (π m).toAdd.1 (π n).toAdd.2 + vecMulVec (π n).toAdd.2 (π m).toAdd.1 +
          vecMulVec (π m).toAdd.2 (π n).toAdd.1 + vecMulVec (π n).toAdd.1 (π m).toAdd.2) :
    IsElemAbelian 2 (commutator M) ∧
      (∃ h : commutator M ≤ T, Function.Bijective (τ.comp (Subgroup.inclusion h))) ∧
      C ⊓ commutator M = ⊥ ∧ C ⊔ commutator M = T ∧
      ∀ g, ∀ x ∈ commutator M, act g x ∈ commutator M := by
  classical
  have hmemT : ∀ a b : M, binaryPolarComm a b ∈ T := fun a b => by
    rw [← hπT, MonoidHom.mem_ker, binaryPolarComm_eq_commutatorElement, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hc : ∀ a b : M, binaryPolarComm a b ∈ Subgroup.center M := fun a b => hTZ (hmemT a b)
  have hτc : ∀ a b : M, ((τ ⟨binaryPolarComm a b, hmemT a b⟩).toAdd :
      Matrix (Fin r) (Fin r) (ZMod 2)) =
        vecMulVec (π a).toAdd.1 (π b).toAdd.2 + vecMulVec (π b).toAdd.2 (π a).toAdd.1 +
          vecMulVec (π a).toAdd.2 (π b).toAdd.1 + vecMulVec (π b).toAdd.1 (π a).toAdd.2 :=
    fun a b => hτcomm a b (hmemT a b)
  have hCof : ∀ a b : M, ((τ ⟨binaryPolarComm a b, hmemT a b⟩).toAdd :
      Matrix (Fin r) (Fin r) (ZMod 2)) = 0 → binaryPolarComm a b ∈ C := fun a b h => by
    have h1 : τ ⟨binaryPolarComm a b, hmemT a b⟩ = 1 :=
      Multiplicative.toAdd.injective (Subtype.ext h)
    have h2 : (⟨binaryPolarComm a b, hmemT a b⟩ : T) ∈ C.subgroupOf T := hτC ▸ h1
    exact h2
  have hdep : ∀ a a' b b' : M, π a = π a' → π b = π b' →
      binaryPolarComm a b = binaryPolarComm a' b' := by
    intro a a' b b' ha hb
    have hta : a⁻¹ * a' ∈ Subgroup.center M := hTZ (by
      rw [← hπT, MonoidHom.mem_ker, map_mul, map_inv, ha]
      exact inv_mul_cancel _)
    have htb : b⁻¹ * b' ∈ Subgroup.center M := hTZ (by
      rw [← hπT, MonoidHom.mem_ker, map_mul, map_inv, hb]
      exact inv_mul_cancel _)
    rw [← mul_inv_cancel_left a a', ← mul_inv_cancel_left b b', binaryPolarComm_mul_left (hc _ _),
      binaryPolarComm_eq_one_of_mem_center_left hta, mul_one, binaryPolarComm_mul_right (hc _ _),
      binaryPolarComm_eq_one_of_mem_center_right _ htb, one_mul]
  have hsq : ∀ a b : M, binaryPolarComm a b * binaryPolarComm a b = 1 := fun a b => by
    rw [← binaryPolarComm_mul_left (hc _ _)]
    refine binaryPolarComm_eq_one_of_mem_center_left (hTZ ?_) b
    rw [← hπT, MonoidHom.mem_ker, map_mul]
    exact Multiplicative.toAdd.injective (binary_prod_add_self _)
  have hinv : ∀ (g : GL (Fin r) (ZMod 2)) (a b : M), binaryPolarComm a b ∈ C →
      binaryPolarComm (act g a) (act g b) = binaryPolarComm a b := by
    intro g a b h
    rw [← hactC g _ h]
    simp only [binaryPolarComm, map_mul, map_inv]
  obtain ⟨p, hp⟩ : ∃ p : Fin r → M, ∀ i, π (p i) = Multiplicative.ofAdd (Pi.single i 1, 0) :=
    ⟨fun i => (hπ _).choose, fun i => (hπ _).choose_spec⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin r → M, ∀ i, π (q i) = Multiplicative.ofAdd (0, Pi.single i 1) :=
    ⟨fun i => (hπ _).choose, fun i => (hπ _).choose_spec⟩
  have hp1 : ∀ i, (π (p i)).toAdd.1 = Pi.single i 1 := fun i => by rw [hp, toAdd_ofAdd]
  have hp2 : ∀ i, (π (p i)).toAdd.2 = 0 := fun i => by rw [hp, toAdd_ofAdd]
  have hq1 : ∀ i, (π (q i)).toAdd.1 = 0 := fun i => by rw [hq, toAdd_ofAdd]
  have hq2 : ∀ i, (π (q i)).toAdd.2 = Pi.single i 1 := fun i => by rw [hq, toAdd_ofAdd]
  have hgp : ∀ {k i : Fin r} (h : k ≠ i) (j : Fin r), π (act (binaryTransvection h) (p j)) =
      Multiplicative.ofAdd ((binaryTransvection h : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ
        Pi.single j 1, 0) := by
    intro k i h j
    rw [hπact, hp1, hp2, mulVec_zero]
  have hgq : ∀ {k i : Fin r} (h : k ≠ i) (j : Fin r), π (act (binaryTransvection h) (q j)) =
      Multiplicative.ofAdd (0, (binaryTransvection h : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ
        Pi.single j 1) := by
    intro k i h j
    rw [hπact, hq1, hq2, mulVec_zero]
  have hpp : ∀ k j, binaryPolarComm (p k) (p j) = 1 := by
    intro k j
    rcases eq_or_ne k j with rfl | hkj
    · exact binaryPolarComm_self _
    obtain ⟨i, hij, hik⟩ := exists_ne_ne_of_three_le hr j k
    have hC : binaryPolarComm (p i) (p j) ∈ C := hCof _ _ (by
      rw [hτc, hp1, hp2, hp1, hp2]
      simp)
    have h1 : π (act (binaryTransvection (Ne.symm hik)) (p i)) = π (p i * p k) := by
      rw [hgp, binaryTransvection_mulVec_single_self, map_mul, hp, hp, ← ofAdd_add,
        Prod.mk_add_mk, add_zero]
    have h2 : π (act (binaryTransvection (Ne.symm hik)) (p j)) = π (p j) := by
      rw [hgp, binaryTransvection_mulVec_single_of_ne _ (Ne.symm hij), hp]
    have h := hinv (binaryTransvection (Ne.symm hik)) _ _ hC
    rw [hdep _ _ _ _ h1 h2, binaryPolarComm_mul_left (hc _ _)] at h
    exact mul_eq_left.mp h
  have hqq : ∀ k j, binaryPolarComm (q k) (q j) = 1 := by
    intro k j
    rcases eq_or_ne k j with rfl | hkj
    · exact binaryPolarComm_self _
    obtain ⟨i, hij, hik⟩ := exists_ne_ne_of_three_le hr j k
    have hC : binaryPolarComm (q i) (q j) ∈ C := hCof _ _ (by
      rw [hτc, hq1, hq2, hq1, hq2]
      simp)
    have h1 : π (act (binaryTransvection (Ne.symm hik)) (q i)) = π (q i * q k) := by
      rw [hgq, binaryTransvection_mulVec_single_self, map_mul, hq, hq, ← ofAdd_add,
        Prod.mk_add_mk, add_zero]
    have h2 : π (act (binaryTransvection (Ne.symm hik)) (q j)) = π (q j) := by
      rw [hgq, binaryTransvection_mulVec_single_of_ne _ (Ne.symm hij), hq]
    have h := hinv (binaryTransvection (Ne.symm hik)) _ _ hC
    rw [hdep _ _ _ _ h1 h2, binaryPolarComm_mul_left (hc _ _)] at h
    exact mul_eq_left.mp h
  have hsymm : ∀ k j, binaryPolarComm (p k) (q j) = binaryPolarComm (p j) (q k) := by
    intro k j
    rcases eq_or_ne k j with rfl | hkj
    · rfl
    obtain ⟨i, hij, hik⟩ := exists_ne_ne_of_three_le hr j k
    have hd1 : ∀ l, (π (p l * q l)).toAdd.1 = Pi.single l 1 := fun l => by
      rw [map_mul, toAdd_mul, Prod.fst_add, hp1, hq1, add_zero]
    have hd2 : ∀ l, (π (p l * q l)).toAdd.2 = Pi.single l 1 := fun l => by
      rw [map_mul, toAdd_mul, Prod.snd_add, hp2, hq2, zero_add]
    have hC : binaryPolarComm (p i * q i) (p j * q j) ∈ C := hCof _ _ (by
      rw [hτc, hd1, hd2, hd1, hd2, binary_add_add_add_self])
    have hgd : ∀ l, π (act (binaryTransvection (Ne.symm hik)) (p l * q l)) =
        Multiplicative.ofAdd ((binaryTransvection (Ne.symm hik) : Matrix (Fin r) (Fin r) (ZMod 2))
          *ᵥ Pi.single l 1, (binaryTransvection (Ne.symm hik) : Matrix (Fin r) (Fin r) (ZMod 2))
          *ᵥ Pi.single l 1) := fun l => by
      rw [map_mul, map_mul, hgp, hgq, ← ofAdd_add, Prod.mk_add_mk, add_zero, zero_add]
    have h1 : π (act (binaryTransvection (Ne.symm hik)) (p i * q i)) =
        π (p i * q i * (p k * q k)) := by
      rw [hgd, binaryTransvection_mulVec_single_self, map_mul, map_mul, map_mul, hp, hq, hp, hq,
        ← ofAdd_add, ← ofAdd_add, ← ofAdd_add]
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    have h2 : π (act (binaryTransvection (Ne.symm hik)) (p j * q j)) = π (p j * q j) := by
      rw [hgd, binaryTransvection_mulVec_single_of_ne _ (Ne.symm hij), map_mul, hp, hq,
        ← ofAdd_add, Prod.mk_add_mk, add_zero, zero_add]
    have h := hinv (binaryTransvection (Ne.symm hik)) _ _ hC
    rw [hdep _ _ _ _ h1 h2, binaryPolarComm_mul_left (hc _ _)] at h
    have h' := mul_eq_left.mp h
    rw [binaryPolarComm_mul_left (hc _ _), binaryPolarComm_mul_right (hc _ _),
      binaryPolarComm_mul_right (hc _ _), hpp, hqq, mul_one, one_mul,
      ← binaryPolarComm_inv (p j) (q k)] at h'
    exact mul_inv_eq_one.mp h'
  have hdiag : ∀ j, binaryPolarComm (p j) (q j) = 1 := by
    intro j
    obtain ⟨i, hij, -⟩ := exists_ne_ne_of_three_le hr j j
    have hC : binaryPolarComm (p i) (q i) ∈ C := hCof _ _ (by
      rw [hτc, hp1, hp2, hq1, hq2]
      simp [binary_add_self])
    have h1 : π (act (binaryTransvection (Ne.symm hij)) (p i)) = π (p i * p j) := by
      rw [hgp, binaryTransvection_mulVec_single_self, map_mul, hp, hp, ← ofAdd_add,
        Prod.mk_add_mk, add_zero]
    have h2 : π (act (binaryTransvection (Ne.symm hij)) (q i)) = π (q i * q j) := by
      rw [hgq, binaryTransvection_mulVec_single_self, map_mul, hq, hq, ← ofAdd_add,
        Prod.mk_add_mk, add_zero]
    have h := hinv (binaryTransvection (Ne.symm hij)) _ _ hC
    rw [hdep _ _ _ _ h1 h2, binaryPolarComm_mul_left (hc _ _), binaryPolarComm_mul_right (hc _ _),
      binaryPolarComm_mul_right (hc _ _), hsymm j i] at h
    have hX := Subgroup.mem_center_iff.mp (hc (p i) (q j))
    have hrw : binaryPolarComm (p i) (q j) * binaryPolarComm (p i) (q i) *
        (binaryPolarComm (p j) (q j) * binaryPolarComm (p i) (q j)) =
        binaryPolarComm (p i) (q j) * binaryPolarComm (p i) (q j) *
          (binaryPolarComm (p i) (q i) * binaryPolarComm (p j) (q j)) := by
      rw [hX (binaryPolarComm (p j) (q j)), ← mul_assoc, mul_assoc _ (binaryPolarComm (p i) (q i)),
        hX (binaryPolarComm (p i) (q i))]
      group
    rw [hrw, hsq, one_mul] at h
    exact mul_eq_left.mp h
  let S : Fin r → Fin r → T := fun i j => ⟨binaryPolarComm (p i) (q j), hmemT _ _⟩
  let τ' : T →* Multiplicative (Matrix (Fin r) (Fin r) (ZMod 2)) :=
    (AddMonoidHom.toMultiplicative (binaryAltMatrices r).subtype).comp τ
  have hτ' : ∀ t : T, τ' t = Multiplicative.ofAdd ((τ t).toAdd : Matrix (Fin r) (Fin r) (ZMod 2)) :=
    fun _ => rfl
  have hτ'S : ∀ i j, i ≠ j → τ' (S i j) = Multiplicative.ofAdd (single i j 1 + single j i 1) := by
    intro i j _
    rw [hτ']
    congr 1
    rw [hτc, hp1, hp2, hq1, hq2]
    simp [vecMulVec_single_single]
  set N : Subgroup T := Subgroup.closure (Set.range fun p : Fin r × Fin r => S p.1 p.2) with hN
  have key : (∀ x ∈ N, τ' x = 1 → x = 1) ∧
      ∀ X ∈ binaryAltMatrices r, ∃ x ∈ N, τ' x = Multiplicative.ofAdd X := by
    let _ : CommGroup T :=
      { (inferInstance : Group T) with
        mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hTZ b.2) a) }
    exact binarySection_closure_spec S (fun i j => Subtype.ext (by
        change binaryPolarComm (p i) (q j) ^ 2 = 1
        rw [sq, hsq])) (fun i => Subtype.ext (hdiag i)) (fun i j => Subtype.ext (hsymm i j)) τ'
      hτ'S
  obtain ⟨hinj, hsurj⟩ := key
  have hNle : N.map T.subtype ≤ commutator M := by
    rw [Subgroup.map_le_iff_le_comap, hN, Subgroup.closure_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    change binaryPolarComm (p i) (q j) ∈ commutator M
    rw [binaryPolarComm_eq_commutatorElement, commutator_eq_closure]
    exact Subgroup.subset_closure ⟨_, _, rfl⟩
  have hSN : ∀ i j, binaryPolarComm (p i) (q j) ∈ N.map T.subtype := fun i j =>
    ⟨S i j, Subgroup.subset_closure ⟨(i, j), rfl⟩, rfl⟩
  let Kr : M → Subgroup M := fun a =>
    { carrier := {b | binaryPolarComm a b ∈ N.map T.subtype}
      mul_mem' := fun {b b'} hb hb' => by
        change binaryPolarComm a (b * b') ∈ N.map T.subtype
        rw [binaryPolarComm_mul_right (hc _ _)]
        exact Subgroup.mul_mem _ hb' hb
      one_mem' := by
        change binaryPolarComm a 1 ∈ N.map T.subtype
        rw [binaryPolarComm_eq_one_of_mem_center_right a (Subgroup.one_mem _)]
        exact Subgroup.one_mem _
      inv_mem' := fun {b} hb => by
        change binaryPolarComm a b⁻¹ ∈ N.map T.subtype
        have h := binaryPolarComm_mul_right (hc a b) b⁻¹
        rw [mul_inv_cancel, binaryPolarComm_eq_one_of_mem_center_right a (Subgroup.one_mem _)] at h
        rw [eq_inv_of_mul_eq_one_left h.symm]
        exact Subgroup.inv_mem _ hb }
  have hTK : ∀ a, T ≤ Kr a := fun a t ht => by
    change binaryPolarComm a t ∈ N.map T.subtype
    rw [binaryPolarComm_eq_one_of_mem_center_right a (hTZ ht)]
    exact Subgroup.one_mem _
  have hKp : ∀ i, Kr (p i) = ⊤ := fun i => eq_top_of_binary_lifts π hp hq (hπT ▸ hTK _)
    (fun j => by
      change binaryPolarComm (p i) (p j) ∈ N.map T.subtype
      rw [hpp]
      exact Subgroup.one_mem _) (hSN i)
  have hKq : ∀ i, Kr (q i) = ⊤ := fun i => eq_top_of_binary_lifts π hp hq (hπT ▸ hTK _)
    (fun j => by
      change binaryPolarComm (q i) (p j) ∈ N.map T.subtype
      rw [← binaryPolarComm_inv]
      exact Subgroup.inv_mem _ (hSN j i))
    (fun j => by
      change binaryPolarComm (q i) (q j) ∈ N.map T.subtype
      rw [hqq]
      exact Subgroup.one_mem _)
  let Kl : Subgroup M :=
    { carrier := {a | ∀ b, binaryPolarComm a b ∈ N.map T.subtype}
      mul_mem' := fun {a a'} ha ha' b => by
        rw [binaryPolarComm_mul_left (hc _ _)]
        exact Subgroup.mul_mem _ (ha b) (ha' b)
      one_mem' := fun b => by
        rw [binaryPolarComm_eq_one_of_mem_center_left (Subgroup.one_mem _)]
        exact Subgroup.one_mem _
      inv_mem' := fun {a} ha b => by
        have h := binaryPolarComm_mul_left (hc a b) a⁻¹
        rw [mul_inv_cancel, binaryPolarComm_eq_one_of_mem_center_left (Subgroup.one_mem _)] at h
        rw [eq_inv_of_mul_eq_one_right h.symm]
        exact Subgroup.inv_mem _ (ha b) }
  have hKl : Kl = ⊤ := eq_top_of_binary_lifts π hp hq
    (hπT ▸ fun t ht b => by
      rw [binaryPolarComm_eq_one_of_mem_center_left (hTZ ht)]
      exact Subgroup.one_mem _)
    (fun i b => by
      have h : b ∈ Kr (p i) := (hKp i).symm ▸ Subgroup.mem_top b
      exact h)
    (fun i b => by
      have h : b ∈ Kr (q i) := (hKq i).symm ▸ Subgroup.mem_top b
      exact h)
  have hM'N : commutator M = N.map T.subtype := by
    refine le_antisymm ?_ hNle
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, b, rfl⟩
    have h : a⁻¹ ∈ Kl := hKl.symm ▸ Subgroup.mem_top _
    have h' := h b⁻¹
    rwa [binaryPolarComm_eq_commutatorElement, inv_inv, inv_inv] at h'
  have hM'T : commutator M ≤ T := hM'N ▸ Subgroup.map_subtype_le N
  have hbij : Function.Bijective (τ.comp (Subgroup.inclusion hM'T)) := by
    refine ⟨(injective_iff_map_eq_one _).mpr fun x hx => ?_, fun z => ?_⟩
    · have hxN : (x : M) ∈ N.map T.subtype := hM'N ▸ x.2
      obtain ⟨y, hy, hyx⟩ := hxN
      have hxy : Subgroup.inclusion hM'T x = y := Subtype.ext hyx.symm
      rw [MonoidHom.comp_apply, hxy] at hx
      have h1 : y = 1 := hinj y hy (by rw [hτ', hx]; rfl)
      exact Subtype.ext (by rw [← hyx, h1]; rfl)
    · obtain ⟨y, hy, hyz⟩ := hsurj _ z.toAdd.2
      have hyM : (y : M) ∈ commutator M := hM'N ▸ Subgroup.mem_map_of_mem _ hy
      refine ⟨⟨y, hyM⟩, ?_⟩
      have hxy : Subgroup.inclusion hM'T ⟨y, hyM⟩ = y := rfl
      rw [MonoidHom.comp_apply, hxy]
      rw [hτ'] at hyz
      exact Multiplicative.toAdd.injective (Subtype.ext (Multiplicative.ofAdd.injective hyz))
  have hinf : C ⊓ commutator M = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hτx : τ.comp (Subgroup.inclusion hM'T) ⟨x, hx.2⟩ = 1 := by
      have h : (⟨x, hM'T hx.2⟩ : T) ∈ τ.ker := hτC ▸ hx.1
      exact h
    have h := hbij.1 (hτx.trans (map_one _).symm)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h)
  have hsup : C ⊔ commutator M = T := by
    refine le_antisymm (sup_le hCT hM'T) fun t ht => ?_
    obtain ⟨x, hx⟩ := hbij.2 (τ ⟨t, ht⟩)
    have hc' : (⟨t, ht⟩ * (Subgroup.inclusion hM'T x)⁻¹ : T) ∈ C.subgroupOf T := by
      rw [← hτC, MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, hx,
        mul_inv_cancel]
    have hct : t * (x : M)⁻¹ ∈ C := hc'
    have := Subgroup.mul_mem_sup hct x.2
    rwa [inv_mul_cancel_right] at this
  refine ⟨⟨⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp (hTZ (hM'T b.2)) a)⟩⟩, fun x hx => ?_⟩,
    ⟨hM'T, hbij⟩, hinf, hsup, fun g x hx => ?_⟩
  ·
    rw [commutator_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, b, rfl⟩ := hx
      rw [← inv_inv a, ← inv_inv b, ← binaryPolarComm_eq_commutatorElement, sq, hsq]
    | one => exact one_pow 2
    | mul x y hx hy hx2 hy2 =>
      have hyc := Subgroup.mem_center_iff.mp
        (hTZ (hM'T (by rw [commutator_eq_closure]; exact hy))) x
      rw [sq, mul_assoc, ← mul_assoc y, ← hyc, mul_assoc, ← mul_assoc, ← sq, ← sq, hx2, hy2,
        one_mul]
    | inv x _ hx2 => rw [inv_pow, hx2, inv_one]
  ·
    have h : (commutator M).map (act g).toMonoidHom ≤ commutator M := by
      rw [commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h ⟨x, hx, rfl⟩

open CFSG.Assembly in
theorem binary_polar_radical_commutator_complement (hr : 3 ≤ r) [Finite M] {C T : Subgroup M}
    (hCT : C ≤ T) (hTZ : T ≤ Subgroup.center M)
    (π : M →* Multiplicative ((Fin r → ZMod 2) × (Fin r → ZMod 2))) (hπ : Function.Surjective π)
    (hπT : π.ker = T) (τ : T →* Multiplicative (binaryAltMatrices r))
    (_hτ : Function.Surjective τ) (hτC : τ.ker = C.subgroupOf T)
    (act : GL (Fin r) (ZMod 2) →* MulAut M) (_hactT : ∀ g, ∀ t ∈ T, act g t ∈ T)
    (hactC : ∀ g, ∀ c ∈ C, act g c = c)
    (hπact : ∀ g m, π (act g m) = Multiplicative.ofAdd
      ((g : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ (π m).toAdd.1,
        (g : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ (π m).toAdd.2))
    (_hτact : ∀ (g : GL (Fin r) (ZMod 2)) (t : T) (ht : act g t ∈ T),
      ((τ ⟨act g t, ht⟩).toAdd : Matrix (Fin r) (Fin r) (ZMod 2)) =
        (g : Matrix (Fin r) (Fin r) (ZMod 2)) * ((τ t).toAdd : Matrix (Fin r) (Fin r) (ZMod 2)) *
          (g : Matrix (Fin r) (Fin r) (ZMod 2))ᵀ)
    (hτcomm : ∀ (m n : M) (h : m⁻¹ * n⁻¹ * m * n ∈ T),
      ((τ ⟨m⁻¹ * n⁻¹ * m * n, h⟩).toAdd : Matrix (Fin r) (Fin r) (ZMod 2)) =
        vecMulVec (π m).toAdd.1 (π n).toAdd.2 + vecMulVec (π n).toAdd.2 (π m).toAdd.1 +
          vecMulVec (π m).toAdd.2 (π n).toAdd.1 + vecMulVec (π n).toAdd.1 (π m).toAdd.2) :
    IsElemAbelian 2 (commutator M) ∧
      (∃ h : commutator M ≤ T, Function.Bijective (τ.comp (Subgroup.inclusion h))) ∧
      C ⊓ commutator M = ⊥ ∧ C ⊔ commutator M = T ∧
      ∀ g, ∀ x ∈ commutator M, act g x ∈ commutator M :=
  binaryPolar_commutator_complement hr hCT hTZ π hπ hπT τ hτC act hactC hπact hτcomm

end Complement

end CFSG.LocalAnalysis.ComponentInitial
