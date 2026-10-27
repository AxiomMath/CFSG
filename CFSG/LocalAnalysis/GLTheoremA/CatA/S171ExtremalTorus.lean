module

public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.KP.CentralCoverThree
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Lift
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S171Extremal

open CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CentralCoverThree Matrix

section Lift

variable {X Y : Type*} [Group X] [Group Y] {φ : Y →* X} (hφ : Function.Surjective φ)
  (hker : φ.ker ≤ Subgroup.center Y) (ι : Multiplicative sumZero6 →* X)
  (hσ : ∀ σ : Equiv.Perm (Fin 6), ∃ n : X, ∀ a : sumZero6,
    n * ι (Multiplicative.ofAdd a) * n⁻¹ = ι (Multiplicative.ofAdd (permSumZero σ a)))

theorem permSumZero_swap_zero_dvec {i : Fin 6} (hi : i ≠ 0) :
    permSumZero (Equiv.swap 0 i) (dvec i) = -dvec i := by
  apply Subtype.ext
  funext k
  rw [permSumZero_apply, AddSubgroup.coe_neg, Pi.neg_apply, dvec_apply, dvec_apply,
    Equiv.symm_swap]
  revert i k
  decide

include hφ hker hσ in
theorem commute_of_mem_range {x y : Y} (hx : φ x ∈ ι.range) (hy : φ y ∈ ι.range) :
    Commute x y := by
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hx
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 hy
  have h := torusPairing_eq hφ ι hker (a := Multiplicative.toAdd a) (b := Multiplicative.toAdd b)
    (y := x) (z := y) (by rw [ofAdd_toAdd]; exact ha.symm) (by rw [ofAdd_toAdd]; exact hb.symm)
  rw [torusPairing_eq_one hφ ι hker hσ] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

include hφ hker hσ in
theorem exists_lift_pow_three (a : sumZero6) :
    ∃ x : Y, φ x = ι (Multiplicative.ofAdd a) ∧ x ^ 3 = 1 := by
  have hcen : ∀ z : Y, φ z = 1 → ∀ g : Y, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.1 (hker hz) g
  refine AddSubgroup.closure_induction (k := Set.range dvec)
    (p := fun a _ => ∃ x : Y, φ x = ι (Multiplicative.ofAdd a) ∧ x ^ 3 = 1) ?_ ?_ ?_ ?_
    (mem_closure_dvec a)
  · rintro _ ⟨i, rfl⟩
    by_cases hi : i = 0
    · subst hi
      exact ⟨1, by rw [dvec_zero, map_one, ofAdd_zero, map_one], one_pow 3⟩
    obtain ⟨n, hn⟩ := hσ (Equiv.swap 0 i)
    have hnt : n * ι (Multiplicative.ofAdd (dvec i)) * n⁻¹ =
        (ι (Multiplicative.ofAdd (dvec i)))⁻¹ := by
      rw [hn, permSumZero_swap_zero_dvec hi, ofAdd_neg, map_inv]
    have ht3 : ι (Multiplicative.ofAdd (dvec i)) ^ 3 = 1 := by
      rw [← map_pow, pow_three_eq_one_sumZero6, map_one]
    obtain ⟨x, hx⟩ := hφ (ι (Multiplicative.ofAdd (dvec i)))
    obtain ⟨N, hN⟩ := hφ n
    have hφz : φ (N * x * N⁻¹ * x) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hN, hx, hnt, inv_mul_cancel]
    have hφw : φ (x ^ 3) = 1 := by rw [map_pow, hx, ht3]
    refine ⟨x * ((x ^ 3)⁻¹ * (N * x * N⁻¹ * x)), ?_,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.exists_cube_adjust (N := N) (hcen _ hφz)
        (hcen _ hφw) (by group) rfl⟩
    rw [map_mul, map_mul, map_inv, hφw, hφz, inv_one, one_mul, mul_one, hx]
  · exact ⟨1, by rw [ofAdd_zero, map_one, map_one], one_pow 3⟩
  · rintro a b - - ⟨x, hx, hx3⟩ ⟨y, hy, hy3⟩
    refine ⟨x * y, by rw [map_mul, hx, hy, ofAdd_add, map_mul], ?_⟩
    have hxy : Commute x y := commute_of_mem_range hφ hker ι hσ
      (MonoidHom.mem_range.2 ⟨_, hx.symm⟩) (MonoidHom.mem_range.2 ⟨_, hy.symm⟩)
    rw [hxy.mul_pow, hx3, hy3, one_mul]
  · rintro a - ⟨x, hx, hx3⟩
    exact ⟨x⁻¹, by rw [map_inv, hx, ofAdd_neg, map_inv], by rw [inv_pow, hx3, inv_one]⟩

include hφ hker hσ in
theorem exists_elemAbelian_map_eq :
    ∃ U : Subgroup Y, IsElemAbelian 3 U ∧ U.map φ = ι.range := by
  let U : Subgroup Y :=
    { carrier := {x | φ x ∈ ι.range ∧ x ^ 3 = 1}
      mul_mem' := fun {x y} hx hy => ⟨by rw [map_mul]; exact mul_mem hx.1 hy.1, by
        rw [(commute_of_mem_range hφ hker ι hσ hx.1 hy.1).mul_pow, hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨by rw [map_one]; exact one_mem _, one_pow 3⟩
      inv_mem' := fun {x} hx => ⟨by rw [map_inv]; exact inv_mem hx.1, by
        rw [inv_pow, hx.2, inv_one]⟩ }
  refine ⟨U, ⟨IsMulCommutative.of_comm fun x y =>
    Subtype.ext (commute_of_mem_range hφ hker ι hσ x.2.1 y.2.1).eq, fun x hx => hx.2⟩,
    le_antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact hx.1
  · intro y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hy
    obtain ⟨x, hx, hx3⟩ := exists_lift_pow_three hφ hker ι hσ (Multiplicative.toAdd a)
    rw [ofAdd_toAdd] at hx
    exact Subgroup.mem_map.2 ⟨x, ⟨MonoidHom.mem_range.2 ⟨a, hx.symm⟩, hx3⟩, hx⟩

end Lift

section Torus

variable {K : Type} [Field K]

@[expose] def cubeRoot (ω : Kˣ) (k : ZMod 3) : Kˣ := ω ^ k.val

variable {ω : Kˣ}

theorem cubeRoot_zero : cubeRoot ω 0 = 1 := by
  rw [cubeRoot, ZMod.val_zero, pow_zero]

theorem cubeRoot_add (hω : orderOf ω = 3) (a b : ZMod 3) :
    cubeRoot ω (a + b) = cubeRoot ω a * cubeRoot ω b := by
  have h := pow_mod_orderOf ω (a.val + b.val)
  rw [hω] at h
  simp only [cubeRoot]
  rw [← pow_add, ZMod.val_add, h]

theorem cubeRoot_injective (hω : orderOf ω = 3) : Function.Injective (cubeRoot ω) := by
  intro a b h
  have h' : a.val ≡ b.val [MOD orderOf ω] := pow_eq_pow_iff_modEq.1 h
  rw [hω] at h'
  exact ZMod.val_injective 3 (h'.eq_of_lt_of_lt (ZMod.val_lt a) (ZMod.val_lt b))

theorem cubeRoot_pow_succ {Q : ℕ} (hQ : ω ^ (Q + 1) = 1) (k : ZMod 3) :
    cubeRoot ω k ^ (Q + 1) = 1 := by
  rw [cubeRoot, ← pow_mul, pow_mul', hQ, one_pow]

theorem prod_cubeRoot (hω : orderOf ω = 3) {s : Finset (Fin 6)} (f : Fin 6 → ZMod 3) :
    ∏ i ∈ s, cubeRoot ω (f i) = cubeRoot ω (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp [cubeRoot_zero]
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, cubeRoot_add hω]

@[expose] def diagGL (d : Fin 6 → Kˣ) : GL (Fin 6) K where
  val := diagonal fun i => (d i : K)
  inv := diagonal fun i => ((d i)⁻¹ : Kˣ)
  val_inv := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [diagonal_apply_ne _ h, one_apply_ne h]
  inv_val := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [diagonal_apply_ne _ h, one_apply_ne h]

theorem coe_diagGL (d : Fin 6 → Kˣ) :
    ((diagGL d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal fun i => (d i : K) :=
  rfl

theorem diagGL_mul (d e : Fin 6 → Kˣ) : diagGL d * diagGL e = diagGL (d * e) := by
  apply Units.ext
  simp only [Units.val_mul, coe_diagGL, diagonal_mul_diagonal]
  rfl

variable (ω) in
@[expose] def torusGL (a : Fin 6 → ZMod 3) : GL (Fin 6) K := diagGL fun i => cubeRoot ω (a i)

theorem torusGL_add (hω : orderOf ω = 3) (a b : Fin 6 → ZMod 3) :
    torusGL ω (a + b) = torusGL ω a * torusGL ω b := by
  rw [torusGL, torusGL, torusGL, diagGL_mul]
  congr 1
  funext i
  exact cubeRoot_add hω _ _

theorem torusGL_zero : torusGL ω 0 = 1 := by
  apply Units.ext
  simp only [torusGL, coe_diagGL, Pi.zero_apply, cubeRoot_zero, Units.val_one]
  exact diagonal_one

theorem torusGL_mem (hω : orderOf ω = 3) {Q : ℕ} (hQ0 : Q ≠ 0) (hQ : ω ^ (Q + 1) = 1)
    (a : Fin 6 → ZMod 3) (ha : ∑ i, a i = 0) : torusGL ω a ∈ StatedSU 6 Q K := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · show (diagonal fun i => (cubeRoot ω (a i) : K)).det = 1
    rw [det_diagonal, ← Units.coe_prod, prod_cubeRoot hω, ha, cubeRoot_zero]
    rfl
  · show ((diagonal fun i => (cubeRoot ω (a i) : K)).map (· ^ Q))ᵀ *
      diagonal (fun i => (cubeRoot ω (a i) : K)) = 1
    rw [diagonal_map (by simp [hQ0]), diagonal_transpose, diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp only [diagonal_apply_eq, one_apply_eq]
      rw [← pow_succ, ← Units.val_pow_eq_pow_val, cubeRoot_pow_succ hQ, Units.val_one]
    · simp [diagonal_apply_ne _ h, one_apply_ne h]

@[expose] def torusElt (hω : orderOf ω = 3) {Q : ℕ} (hQ0 : Q ≠ 0) (hQ : ω ^ (Q + 1) = 1)
    (a : sumZero6) : StatedSU 6 Q K :=
  ⟨torusGL ω a, torusGL_mem hω hQ0 hQ a (mem_sumZero6.1 a.2)⟩

@[expose] noncomputable def torusHom (hω : orderOf ω = 3) {Q : ℕ} (hQ0 : Q ≠ 0)
    (hQ : ω ^ (Q + 1) = 1) : Multiplicative sumZero6 →* StatedProj (StatedSU 6 Q K) where
  toFun a := QuotientGroup.mk (torusElt hω hQ0 hQ (Multiplicative.toAdd a))
  map_one' := by
    show (QuotientGroup.mk (torusElt hω hQ0 hQ 0) : StatedProj (StatedSU 6 Q K)) = 1
    have : torusElt hω hQ0 hQ 0 = 1 := Subtype.ext torusGL_zero
    rw [this]
    rfl
  map_mul' a b := by
    show (QuotientGroup.mk (torusElt hω hQ0 hQ (Multiplicative.toAdd a + Multiplicative.toAdd b)) :
      StatedProj (StatedSU 6 Q K)) = _
    have : torusElt hω hQ0 hQ (Multiplicative.toAdd a + Multiplicative.toAdd b) =
        torusElt hω hQ0 hQ (Multiplicative.toAdd a) *
          torusElt hω hQ0 hQ (Multiplicative.toAdd b) :=
      Subtype.ext (torusGL_add hω _ _)
    rw [this]
    rfl

theorem torusHom_eq_one_iff (hω : orderOf ω = 3) {Q : ℕ} (hQ0 : Q ≠ 0) (hQ : ω ^ (Q + 1) = 1)
    (a : sumZero6) : torusHom hω hQ0 hQ (Multiplicative.ofAdd a) = 1 ↔
      ∃ k : ZMod 3, ∀ i, (a : Fin 6 → ZMod 3) i = k := by
  show (QuotientGroup.mk (torusElt hω hQ0 hQ a) : StatedProj (StatedSU 6 Q K)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  show torusGL ω a ∈ StatedScalars (Fin 6) K ↔ _
  constructor
  · rintro ⟨c, hc⟩
    have hdiag : ∀ i, ((cubeRoot ω ((a : Fin 6 → ZMod 3) i) : Kˣ) : K) = (c : K) := by
      intro i
      have h1 := congrArg (fun M : GL (Fin 6) K => (M : Matrix (Fin 6) (Fin 6) K) i i) hc
      simpa [Matrix.GeneralLinearGroup.coe_scalar, torusGL, coe_diagGL] using h1.symm
    refine ⟨(a : Fin 6 → ZMod 3) 0, fun i => ?_⟩
    apply cubeRoot_injective hω
    apply Units.ext
    rw [hdiag i, hdiag 0]
  · rintro ⟨k, hk⟩
    refine ⟨cubeRoot ω k, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, torusGL, coe_diagGL, Matrix.scalar_apply]
    congr 1
    funext i
    rw [hk i]

theorem permMatrix_mul_diagonal (σ : Equiv.Perm (Fin 6)) (d : Fin 6 → K) :
    σ.permMatrix K * diagonal d = diagonal (fun i => d (σ i)) * σ.permMatrix K := by
  ext i j
  have h1 : (σ.permMatrix K * diagonal d) i j = if σ i = j then d j else 0 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ i)]
    · by_cases h : σ i = j
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
    · intro k _ hk
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Ne.symm hk]
    · simp
  have h2 : (diagonal (fun i => d (σ i)) * σ.permMatrix K) i j = if σ i = j then d j else 0 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · by_cases h : σ i = j
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  rw [h1, h2]

theorem det_permMatrix (h2 : (-1 : K) = 1) (σ : Equiv.Perm (Fin 6)) : (σ.permMatrix K).det = 1 := by
  rw [det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simp only [h, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    exact h2

@[expose] def permGL (σ : Equiv.Perm (Fin 6)) : GL (Fin 6) K where
  val := σ.permMatrix K
  inv := σ⁻¹.permMatrix K
  val_inv := by rw [← permMatrix_mul, inv_mul_cancel, permMatrix_one]
  inv_val := by rw [← permMatrix_mul, mul_inv_cancel, permMatrix_one]

theorem permGL_mem (h2 : (-1 : K) = 1) {Q : ℕ} (hQ0 : Q ≠ 0) (σ : Equiv.Perm (Fin 6)) :
    permGL σ ∈ StatedSU 6 Q K := by
  apply Subgroup.subset_closure
  refine ⟨det_permMatrix h2 σ, ?_⟩
  show ((σ.permMatrix K).map (· ^ Q))ᵀ * σ.permMatrix K = 1
  have hmap : (σ.permMatrix K).map (· ^ Q) = σ.permMatrix K := by
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs
    · exact one_pow Q
    · exact zero_pow hQ0
  rw [hmap, transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]

theorem torus_conj (h2 : (-1 : K) = 1) (hω : orderOf ω = 3) {Q : ℕ} (hQ0 : Q ≠ 0)
    (hQ : ω ^ (Q + 1) = 1) (σ : Equiv.Perm (Fin 6)) :
    ∃ n : StatedProj (StatedSU 6 Q K), ∀ a : sumZero6,
      n * torusHom hω hQ0 hQ (Multiplicative.ofAdd a) * n⁻¹ =
        torusHom hω hQ0 hQ (Multiplicative.ofAdd (permSumZero σ a)) := by
  refine ⟨QuotientGroup.mk ⟨permGL σ⁻¹, permGL_mem h2 hQ0 σ⁻¹⟩, fun a => ?_⟩
  show (QuotientGroup.mk ⟨permGL σ⁻¹, permGL_mem h2 hQ0 σ⁻¹⟩ : StatedProj (StatedSU 6 Q K)) *
      QuotientGroup.mk (torusElt hω hQ0 hQ a) *
        (QuotientGroup.mk ⟨permGL σ⁻¹, permGL_mem h2 hQ0 σ⁻¹⟩)⁻¹ =
    QuotientGroup.mk (torusElt hω hQ0 hQ (permSumZero σ a))
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  show permGL σ⁻¹ * torusGL ω a * (permGL σ⁻¹)⁻¹ = torusGL ω (permSumZero σ a)
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  simp only [Units.val_mul, permGL, torusGL, coe_diagGL]
  rw [permMatrix_mul_diagonal]
  rfl

theorem exists_elemAbelian_card_map_eq (h2 : (-1 : K) = 1) (hω : orderOf ω = 3) {Q : ℕ}
    (hQ0 : Q ≠ 0) (hQ : ω ^ (Q + 1) = 1) {Y : Type*} [Group Y]
    (φ : Y →* StatedProj (StatedSU 6 Q K)) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) :
    ∃ U : Subgroup Y, IsElemAbelian 3 U ∧ Nat.card (U.map φ) = 3 ^ 4 := by
  obtain ⟨U, hU, hUmap⟩ := exists_elemAbelian_map_eq hφ hker (torusHom hω hQ0 hQ)
    (torus_conj h2 hω hQ0 hQ)
  exact ⟨U, hU, by rw [hUmap, card_range_eq _ (torusHom_eq_one_iff hω hQ0 hQ)]⟩

end Torus

theorem exists_of_map_card {G : Type} [Group G] [Finite G] {L : Subgroup G} {X : Type*} [Group X]
    (π : ↥L →* X) (hker : π.ker = Subgroup.center ↥L) {U : Subgroup ↥L}
    (hU : IsElemAbelian 3 U) {m : ℕ} (hm : 3 ^ m ≤ Nat.card (U.map π)) :
    ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧
      3 ^ m * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card E := by
  refine ⟨U.map L.subtype, Subgroup.map_subtype_le _, hU.map L.subtype, ?_⟩
  have h1 := Subgroup.card_ker_mul_card_of_surjective (MonoidHom.subgroupMap_surjective π U)
  rw [Subgroup.ker_subgroupMap, hker] at h1
  have hle : U.map L.subtype ⊓ Subgroup.centralizer (L : Set G) ≤
      (((Subgroup.center ↥L).subgroupOf U).map U.subtype).map L.subtype := by
    rintro _ ⟨⟨u, hu, rfl⟩, hc⟩
    refine ⟨u, ⟨⟨u, hu⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_center_iff.mpr fun l =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hc l l.2)), rfl⟩, rfl⟩
  have h2 : Nat.card ↥(U.map L.subtype ⊓ Subgroup.centralizer (L : Set G)) ≤
      Nat.card ((Subgroup.center ↥L).subgroupOf U) := by
    refine (Subgroup.card_le_of_le hle).trans_eq ?_
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective U.subtype_injective]
  rw [Subgroup.card_map_of_injective L.subtype_injective, ← h1]
  calc 3 ^ m * Nat.card ↥(U.map L.subtype ⊓ Subgroup.centralizer (L : Set G))
      ≤ Nat.card (U.map π) * Nat.card ((Subgroup.center ↥L).subgroupOf U) := Nat.mul_le_mul hm h2
    _ = Nat.card ((Subgroup.center ↥L).subgroupOf U) * Nat.card (U.map π) := Nat.mul_comm _ _

end CFSG.LocalAnalysis.GLTheoremA.S171Extremal
