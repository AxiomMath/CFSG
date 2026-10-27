module

public import CFSG.LieType.Steinberg.CentralExt.PosLiftSplit
public import CFSG.LieType.Steinberg.CentralExt.SUBruhatExtras
public import CFSG.LieType.Steinberg.CentralExt.SpTorus
public import CFSG.LieType.Steinberg.CentralExt.SpinTorus
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRootGroups
public import CFSG.LieType.Universal.Unitary.Extras.Commutator

public section

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SUClosed

attribute [local instance] TorusLift.centerCommGroup

section General

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

abbrev IsShortPos (γ : Fin (n / 2) → ℤ) (i j : Fin n) : Prop :=
  i ≠ j ∧ i ≠ Fin.rev i ∧ j ≠ Fin.rev j ∧ j ≠ Fin.rev i ∧ weight n i - weight n j = toStd n γ

abbrev IsLongPos (γ : Fin (n / 2) → ℤ) (i : Fin n) : Prop :=
  i ≠ Fin.rev i ∧ 2 • weight n i = toStd n γ

theorem not_isShortPos_of_isLongPos {γ : Fin (n / 2) → ℤ} {k : Fin n} (hk : IsLongPos γ k)
    (i j : Fin n) : ¬ IsShortPos γ i j := by
  rintro ⟨-, -, -, hji, hw⟩
  obtain ⟨h1, h2⟩ := eq_of_weight_sub_eq_two_smul hk.1 (hw.trans hk.2.symm)
  rw [h1, h2] at hji
  exact hji rfl

theorem short_or_long (he : Even n) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) :
    (∃ ij : Fin n × Fin n, IsShortPos γ ij.1 ij.2) ∨ ∃ i, IsLongPos γ i := by
  rw [Unitary.roots_eq] at hγ
  rcases hγ with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he', -⟩
  · exact Or.inl ⟨(i, j), hij, hi, hj, hji, h.symm⟩
  · exact Or.inr ⟨i, hi, h.symm⟩
  · exact absurd he he'

theorem weight_ne_zero {i : Fin n} (hi : i ≠ Fin.rev i) : weight n i ≠ 0 := by
  intro h0
  obtain ⟨c, hc⟩ := exists_weight_ne_zero hi
  have h1 := congrFun h0 c
  rw [weight_apply', Pi.zero_apply] at h1
  have := c.isLt
  split_ifs at h1 <;> omega

@[expose] def trDiff (c : F) : traceZero σ :=
  ⟨c - σ c, by rw [mem_traceZero, map_sub, hσ]; ring⟩

theorem coe_trDiff (c : F) : (trDiff hσ c : F) = c - σ c := rfl

theorem trDiff_add (c d : F) : trDiff hσ (c + d) = trDiff hσ c + trDiff hσ d :=
  Subtype.ext (by simp only [coe_trDiff, AddSubgroup.coe_add, map_add]; ring)

open _root_.Classical in
@[expose] noncomputable def x (γ : Fin (n / 2) → ℤ) (c : F) : SU σ n :=
  if h : ∃ ij : Fin n × Fin n, IsShortPos γ ij.1 ij.2 then
    rootHom σ hσ h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2.1 (Multiplicative.ofAdd c)
  else if h' : ∃ i : Fin n, IsLongPos γ i then
    longRootHom σ h'.choose_spec.1 (Multiplicative.ofAdd (trDiff hσ c))
  else 1

theorem x_short {γ : Fin (n / 2) → ℤ} (h : ∃ ij : Fin n × Fin n, IsShortPos γ ij.1 ij.2) :
    ∃ (i j : Fin n) (hs : IsShortPos γ i j),
      ∀ c, x hσ γ c = rootHom σ hσ hs.1 hs.2.1 hs.2.2.1 (Multiplicative.ofAdd c) :=
  ⟨_, _, h.choose_spec, fun c => by classical rw [x, dite_eq_left h]⟩

theorem x_long {γ : Fin (n / 2) → ℤ} {k : Fin n} (hk : IsLongPos γ k) :
    ∃ (i : Fin n) (hl : IsLongPos γ i),
      ∀ c, x hσ γ c = longRootHom σ hl.1 (Multiplicative.ofAdd (trDiff hσ c)) := by
  classical
  have hns : ¬ ∃ ij : Fin n × Fin n, IsShortPos γ ij.1 ij.2 := fun ⟨ij, hij⟩ =>
    not_isShortPos_of_isLongPos hk _ _ hij
  have hl : ∃ i, IsLongPos γ i := ⟨k, hk⟩
  exact ⟨_, hl.choose_spec, fun c => by rw [x, dite_eq_right hns, dite_eq_left hl]⟩

theorem x_add (γ : Fin (n / 2) → ℤ) (c d : F) : x hσ γ (c + d) = x hσ γ c * x hσ γ d := by
  unfold x
  split_ifs with h h'
  · rw [ofAdd_add, map_mul]
  · rw [trDiff_add, ofAdd_add, map_mul]
  · rw [mul_one]

theorem x_mem (γ : Fin (n / 2) → ℤ) (c : F) : x hσ γ c ∈ rootGroup σ hσ n γ := by
  unfold x
  split_ifs with h h'
  · exact rootHom_mem hσ h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2.1
      h.choose_spec.2.2.2.1 h.choose_spec.2.2.2.2 _
  · exact longRootHom_mem hσ h'.choose_spec.1 h'.choose_spec.2 _
  · exact Subgroup.one_mem _

theorem x_mul_eq_one {γ : Fin (n / 2) → ℤ} {c : F} (h : x hσ γ c = 1) {b : F} (hb : σ b = b) :
    x hσ γ (b * c) = 1 := by
  unfold x at h ⊢
  split_ifs at h ⊢ with hs hl
  · have h1 : mat σ n (rootHom σ hσ hs.choose_spec.1 hs.choose_spec.2.1 hs.choose_spec.2.2.1
        (Multiplicative.ofAdd c)) hs.choose.1 hs.choose.2 = mat σ n 1 hs.choose.1 hs.choose.2 := by
      rw [h]
    rw [mat_apply (rootHom _ _ _ _ _ _), coe_rootHom, toAdd_ofAdd,
      rootMatrix_apply_pq hs.choose_spec.1 hs.choose_spec.2.2.2.1, map_one,
      one_apply_ne hs.choose_spec.1] at h1
    rw [h1, mul_zero, ofAdd_zero, map_one]
  · have h1 : mat σ n (longRootHom σ hl.choose_spec.1 (Multiplicative.ofAdd (trDiff hσ c)))
        hl.choose (Fin.rev hl.choose) = mat σ n 1 hl.choose (Fin.rev hl.choose) := by
      rw [h]
    rw [mat_apply (longRootHom _ _ _), coe_longRootHom, toAdd_ofAdd, coe_trDiff,
      longRootMatrix_apply hl.choose_spec.1, map_one, one_apply_ne hl.choose_spec.1] at h1
    have hc : σ c = c := (sub_eq_zero.1 h1).symm
    have h2 : trDiff hσ (b * c) = 0 :=
      Subtype.ext (by simp only [coe_trDiff, ZeroMemClass.coe_zero, map_mul, hb, hc, sub_self])
    rw [h2, ofAdd_zero, map_one]
  · rfl

theorem mat_add_map_eq_zero {γ : Fin (n / 2) → ℤ} (hγ : 0 < ht γ) {g : SU σ n}
    (hg : g ∈ rootGroup σ hσ n γ) {p q : Fin n} (hpq : weight n p - weight n q = toStd n γ) :
    mat σ n g p q + σ (mat σ n g (Fin.rev q) (Fin.rev p)) = 0 := by
  have hpq' := ht_eq_of_weight_sub hpq
  refine mat_add_map_eq_zero_of_idBelow (s := fun a => 2 * (a.val : ℤ) - ((n : ℤ) - 1))
    (fun i => ?_) (d := 2 * ht γ) (by omega) (fun a b hab => ?_) ?_
  · simp only [Fin.val_rev]
    have := i.isLt
    omega
  · have hab' : 2 * (b.val : ℤ) - ((n : ℤ) - 1) - (2 * (a.val : ℤ) - ((n : ℤ) - 1)) <
        2 * ht γ := hab
    apply mat_apply_of_mem_rootGroup hσ hg
    · intro hw
      have := ht_eq_of_weight_sub hw
      omega
    · intro hw
      have := two_mul_ht_eq_of_weight_sub hw
      omega
  · show 2 * (q.val : ℤ) - ((n : ℤ) - 1) - (2 * (p.val : ℤ) - ((n : ℤ) - 1)) = 2 * ht γ
    omega

theorem exists_x_eq_of_mem (he : Even n) {γ : Fin (n / 2) → ℤ}
    (hγr : γ ∈ roots (isFiniteType_cartan n) (divisible n)) (hγ : 0 < ht γ)
    (htr : ∀ z : F, z + σ z = 0 → ∃ c, c - σ c = z) {g : SU σ n}
    (hg : g ∈ rootGroup σ hσ n γ) : ∃ c, x hσ γ c = g := by
  rcases short_or_long he hγr with hs | ⟨k, hk⟩
  · obtain ⟨i, j, hij, hxij⟩ := x_short hσ hs
    refine ⟨mat σ n g i j, eq_of_mem_rootGroup hσ (x_mem hσ γ _) hg fun a b hab => ?_⟩
    rw [hxij, mat_apply (rootHom _ _ _ _ _ _), coe_rootHom, toAdd_ofAdd]
    rcases hab with hab | hab
    · rcases eq_of_weight_sub_eq_sub hij.1 hij.2.1 hij.2.2.1 hij.2.2.2.1
        (hab.trans hij.2.2.2.2.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [rootMatrix_apply_pq hij.1 hij.2.2.2.1]
      · rw [rootMatrix_apply_rev hij.1 hij.2.2.2.1]
        have h0 := mat_add_map_eq_zero hσ hγ hg hij.2.2.2.2
        have h1 : σ (mat σ n g (Fin.rev j) (Fin.rev i)) = -mat σ n g i j := by
          linear_combination h0
        rw [← hσ (mat σ n g (Fin.rev j) (Fin.rev i)), h1, map_neg]
    · exfalso
      obtain ⟨-, hwa⟩ := eq_rev_of_weight_sub_eq_two_smul hab (toStd_ne_zero_of_mem_roots hγr)
      exact weight_ne_weight_sub hij.1 hij.2.1 hij.2.2.1 hij.2.2.2.1 (hwa.trans hij.2.2.2.2.symm)
  · obtain ⟨i, hl, hxi⟩ := x_long hσ hk
    have h0 := mat_add_map_eq_zero hσ hγ hg (p := i) (q := Fin.rev i)
      (by rw [weight_rev', sub_neg_eq_add, ← two_nsmul]; exact hl.2)
    rw [Fin.rev_rev] at h0
    obtain ⟨c, hc⟩ := htr _ h0
    refine ⟨c, eq_of_mem_rootGroup hσ (x_mem hσ γ c) hg fun a b hab => ?_⟩
    rw [hxi, mat_apply (longRootHom _ _ _), coe_longRootHom, toAdd_ofAdd, coe_trDiff]
    rcases hab with hab | hab
    · obtain ⟨rfl, rfl⟩ := eq_of_weight_sub_eq_two_smul hl.1 (hab.trans hl.2.symm)
      rw [longRootMatrix_apply hl.1, hc]
    · exfalso
      have h4 : weight n a - weight n b = 4 • weight n i := by
        rw [hab, ← hl.2, smul_smul]
        norm_num
      exact weight_ne_zero hl.1 (eq_zero_of_weight_sub_eq_nsmul h4 (by norm_num))

theorem diag_unitary {t : SU σ n} {d : Fin n → F} (ht : mat σ n t = diagonal d) (s : Fin n) :
    σ (d s) * d (Fin.rev s) = 1 := by
  have h := congrFun (congrFun (mem_SU.1 t.2).2 s) (Fin.rev s)
  rw [← mat_apply, ht] at h
  simpa [conjTr, antidiag, Matrix.mul_apply, Matrix.diagonal_apply] using h

theorem conj_rootHom {t : SU σ n} {d : Fin n → F} (ht : mat σ n t = diagonal d) {i j : Fin n}
    (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (c : F) :
    t * rootHom σ hσ hij hi hj (Multiplicative.ofAdd c) * t⁻¹ =
      rootHom σ hσ hij hi hj (Multiplicative.ofAdd (d i * c * (d j)⁻¹)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply mat_injective
  rw [map_mul, map_mul, ht, mat_apply (rootHom _ _ _ _ _ _), mat_apply (rootHom _ _ _ _ _ _),
    coe_rootHom, coe_rootHom, toAdd_ofAdd, toAdd_ofAdd, ← SpecialLinear.signedPerm_one,
    signedPerm_mul_rootMatrix (fun s => rfl) (diag_unitary ht)]
  rfl

theorem conj_longRootHom {t : SU σ n} {d : Fin n → F} (ht : mat σ n t = diagonal d) {i : Fin n}
    (hi : i ≠ Fin.rev i) (c : traceZero σ) :
    t * longRootHom σ hi (Multiplicative.ofAdd c) * t⁻¹ =
      longRootHom σ hi (Multiplicative.ofAdd ⟨d i * c * (d (Fin.rev i))⁻¹,
        mul_mem_traceZero_of_unitary (diag_unitary ht) i ((mem_traceZero σ).1 c.2)⟩) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply mat_injective
  rw [map_mul, map_mul, ht, mat_apply (longRootHom _ _ _), mat_apply (longRootHom _ _ _),
    coe_longRootHom, coe_longRootHom, toAdd_ofAdd, toAdd_ofAdd, ← SpecialLinear.signedPerm_one,
    signedPerm_mul_longRootMatrix (fun s => rfl) (diag_unitary ht)]
  rfl

theorem conj_x_short {γ : Fin (n / 2) → ℤ} {t : SU σ n} {d : Fin n → F}
    (ht : mat σ n t = diagonal d) {i j : Fin n} (hs : IsShortPos γ i j)
    (hx : ∀ c, x hσ γ c = rootHom σ hσ hs.1 hs.2.1 hs.2.2.1 (Multiplicative.ofAdd c)) (c : F) :
    t * x hσ γ c * t⁻¹ = x hσ γ (d i * (d j)⁻¹ * c) := by
  rw [hx, hx, conj_rootHom hσ ht]
  congr 2
  ring

theorem conj_x_long {γ : Fin (n / 2) → ℤ} {t : SU σ n} {d : Fin n → F}
    (ht : mat σ n t = diagonal d) {i : Fin n} (hl : IsLongPos γ i)
    (hx : ∀ c, x hσ γ c = longRootHom σ hl.1 (Multiplicative.ofAdd (trDiff hσ c))) (c : F) :
    t * x hσ γ c * t⁻¹ = x hσ γ (d i * (d (Fin.rev i))⁻¹ * c) := by
  rw [hx, hx, conj_longRootHom ht]
  congr 2
  apply Subtype.ext
  have hu := diag_unitary ht
  simp only [coe_trDiff, map_mul, map_inv₀, map_eq_inv_of_unitary hu, Fin.rev_rev, inv_inv]
  ring

@[expose] noncomputable def diagGL (u : Fin n → Fˣ) : GL (Fin n) F :=
  ⟨diagonal fun s => (u s : F), diagonal fun s => ((u s)⁻¹ : Fˣ),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

theorem coe_diagGL (u : Fin n → Fˣ) :
    ((diagGL u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal fun s => (u s : F) :=
  rfl

theorem diagGL_mem {u : Fin n → Fˣ} (hu : ∀ s, σ (u s : F) * u (Fin.rev s) = 1)
    (hdet : ∏ s, (u s : F) = 1) : diagGL u ∈ SU σ n := by
  refine mem_SU.2 ⟨by rw [coe_diagGL, det_diagonal, hdet], ?_⟩
  have hc : conjTr σ (diagonal fun s => (u s : F)) = diagonal fun s => σ (u s : F) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp [conjTr]
    · simp [conjTr, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]
  rw [coe_diagGL, hc]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [antidiag, Matrix.of_apply]
  split_ifs with hb
  · subst hb
    rw [mul_one, hu a]
  · simp

variable (σ) in
@[expose] def fixField : Subfield F := σ.toRingHom.eqLocusField (RingHom.id F)

theorem map_coe_fixField (c : fixField σ) : σ (c : F) = c := c.2

variable (σ) in
noncomputable abbrev toF : (fixField σ)ˣ →* Fˣ := Units.map (fixField σ).subtype.toMonoidHom

theorem coe_toF (u : (fixField σ)ˣ) : (toF σ u : F) = ((u : fixField σ) : F) := rfl

theorem map_coe_toF (u : (fixField σ)ˣ) : σ (toF σ u : F) = toF σ u := map_coe_fixField _

theorem chi_zero' {m : ℕ} {K : Type} [Field K] (t : Fin m → Kˣ) : SpTorus.chi 0 t = 1 := by
  simp [SpTorus.chi]

theorem prod_chi {m : ℕ} {K : Type} [Field K] {ι : Type*} (S : Finset ι)
    (v : ι → Fin m → ℤ) (t : Fin m → Kˣ) :
    ∏ s ∈ S, SpTorus.chi (v s) t = SpTorus.chi (∑ s ∈ S, v s) t := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, chi_zero']
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, SpTorus.chi_add]

omit [Field F] in
theorem sum_weight : ∑ s : Fin n, weight n s = 0 := by
  have h : ∑ s : Fin n, weight n (Fin.rev s) = ∑ s : Fin n, weight n s :=
    Fintype.sum_equiv Fin.revPerm _ _ fun s => rfl
  simp only [weight_rev', Finset.sum_neg_distrib] at h
  funext c
  have := congrFun h c
  simp only [Pi.neg_apply, Finset.sum_apply, Pi.zero_apply] at this ⊢
  omega

@[expose] noncomputable def splitDiag (t : Fin (n / 2) → (fixField σ)ˣ) (s : Fin n) : Fˣ :=
  toF σ (SpTorus.chi (weight n s) t)

theorem splitDiag_unitary (t : Fin (n / 2) → (fixField σ)ˣ) (s : Fin n) :
    σ (splitDiag t s : F) * splitDiag t (Fin.rev s) = 1 := by
  rw [splitDiag, map_coe_toF, splitDiag, ← Units.val_mul, ← map_mul, ← SpTorus.chi_add,
    weight_rev', add_neg_cancel, chi_zero', map_one, Units.val_one]

theorem prod_splitDiag (t : Fin (n / 2) → (fixField σ)ˣ) : ∏ s, (splitDiag t s : F) = 1 := by
  simp only [splitDiag]
  rw [← Units.coe_prod, ← map_prod, prod_chi, sum_weight, chi_zero', map_one, Units.val_one]

@[expose] noncomputable def splitTorus (t : Fin (n / 2) → (fixField σ)ˣ) : SU σ n :=
  ⟨diagGL (splitDiag t), diagGL_mem (splitDiag_unitary t) (prod_splitDiag t)⟩

theorem mat_splitTorus (t : Fin (n / 2) → (fixField σ)ˣ) :
    mat σ n (splitTorus t) = diagonal fun s => (splitDiag t s : F) :=
  rfl

@[expose] noncomputable def chiF (γ : Fin (n / 2) → ℤ) (t : Fin (n / 2) → (fixField σ)ˣ) : F :=
  toF σ (SpTorus.chi (toStd n γ) t)

theorem map_chiF (γ : Fin (n / 2) → ℤ) (t : Fin (n / 2) → (fixField σ)ˣ) :
    σ (chiF γ t) = chiF γ t :=
  map_coe_toF _

theorem chiF_eq_one_iff {γ : Fin (n / 2) → ℤ} {t : Fin (n / 2) → (fixField σ)ˣ} :
    chiF γ t = 1 ↔ SpTorus.chi (toStd n γ) t = 1 := by
  constructor
  · intro h
    apply Units.ext
    apply Subtype.ext
    exact h
  · intro h
    rw [chiF, h, map_one, Units.val_one]

theorem splitDiag_mul_inv (t : Fin (n / 2) → (fixField σ)ˣ) (a b : Fin n) :
    (splitDiag t a : F) * (splitDiag t b : F)⁻¹ =
      toF σ (SpTorus.chi (weight n a - weight n b) t) := by
  rw [SpTorus.chi_sub, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  rfl

theorem splitTorus_conj_x (he : Even n) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) (t : Fin (n / 2) → (fixField σ)ˣ)
    (c : F) : splitTorus t * x hσ γ c * (splitTorus t)⁻¹ = x hσ γ (chiF γ t * c) := by
  rcases short_or_long he hγ with hs | ⟨k, hk⟩
  · obtain ⟨i, j, hij, hx⟩ := x_short hσ hs
    rw [conj_x_short hσ (mat_splitTorus t) hij hx, splitDiag_mul_inv, hij.2.2.2.2]
    rfl
  · obtain ⟨i, hl, hx⟩ := x_long hσ hk
    rw [conj_x_long hσ (mat_splitTorus t) hl hx, splitDiag_mul_inv, weight_rev', sub_neg_eq_add,
      ← two_nsmul, hl.2]
    rfl

theorem splitTorus_comm (t t' : Fin (n / 2) → (fixField σ)ˣ) :
    splitTorus t' * splitTorus t * (splitTorus t')⁻¹ = (splitTorus t : SU σ n) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply mat_injective
  rw [map_mul, map_mul, mat_splitTorus, mat_splitTorus, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext s
  ring

theorem commutator_rootHom_rootHom {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (hji : j ≠ Fin.rev i) (a b : F) :
    ⁅rootHom σ hσ hij hi hj (Multiplicative.ofAdd a),
      rootHom σ hσ hji hj (rev_ne_rev_rev hi) (Multiplicative.ofAdd b)⁆ =
      longRootHom σ hi (Multiplicative.ofAdd (trDiff hσ (a * b))) := by
  rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  apply mat_injective
  simp only [map_mul, mat_apply, coe_rootHom, coe_longRootHom, toAdd_ofAdd, coe_trDiff,
    rootMatrix, longRootMatrix, Fin.rev_rev]
  have h1 : Fin.rev i ≠ j := fun h => hji h.symm
  have h2 : Fin.rev i ≠ i := fun h => hi h.symm
  have h3 : Fin.rev j ≠ i := fun h => hji (by rw [← h, Fin.rev_rev])
  have h4 : Fin.rev i ≠ Fin.rev j := fun h => hij (Fin.rev_injective h)
  have h5 : j ≠ i := fun h => hij h.symm
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, single_mul_single_same, single_mul_single_of_ne _ _ _ _ h1,
    single_mul_single_of_ne _ _ _ _ h2, single_mul_single_of_ne _ _ _ _ h3,
    single_mul_single_of_ne _ _ _ _ h4, single_mul_single_of_ne _ _ _ _ h5, add_zero,
    sub_zero]
  have key : single i (Fin.rev i) (a * b) = single i (Fin.rev i) (σ b * σ a) +
      single i (Fin.rev i) (a * b - σ a * σ b) := by
    rw [← single_add]
    ring_nf
  rw [key]
  abel

theorem commute_longRootHom_rootHom_left {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (a : F) (c : Multiplicative (traceZero σ)) :
    longRootHom σ hi c * rootHom σ hσ hij hi hj (Multiplicative.ofAdd a) =
      rootHom σ hσ hij hi hj (Multiplicative.ofAdd a) * longRootHom σ hi c := by
  apply mat_injective
  simp only [map_mul, mat_apply, coe_rootHom, coe_longRootHom, toAdd_ofAdd, rootMatrix,
    longRootMatrix]
  have h2 : Fin.rev i ≠ i := fun h => hi h.symm
  have h4 : Fin.rev i ≠ Fin.rev j := fun h => hij (Fin.rev_injective h)
  have h5 : j ≠ i := fun h => hij h.symm
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, single_mul_single_of_ne _ _ _ _ h2, single_mul_single_of_ne _ _ _ _ h4,
    single_mul_single_of_ne _ _ _ _ h5, sub_zero, add_zero]
  abel

theorem commute_longRootHom_rootHom_right {i j : Fin n} (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (hji : j ≠ Fin.rev i) (b : F)
    (c : Multiplicative (traceZero σ)) :
    longRootHom σ hi c * rootHom σ hσ hji hj (rev_ne_rev_rev hi) (Multiplicative.ofAdd b) =
      rootHom σ hσ hji hj (rev_ne_rev_rev hi) (Multiplicative.ofAdd b) * longRootHom σ hi c := by
  apply mat_injective
  simp only [map_mul, mat_apply, coe_rootHom, coe_longRootHom, toAdd_ofAdd, rootMatrix,
    longRootMatrix, Fin.rev_rev]
  have h1 : Fin.rev i ≠ j := fun h => hji h.symm
  have h2 : Fin.rev i ≠ i := fun h => hi h.symm
  have h3 : Fin.rev j ≠ i := fun h => hji (by rw [← h, Fin.rev_rev])
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, single_mul_single_of_ne _ _ _ _ h1, single_mul_single_of_ne _ _ _ _ h2,
    single_mul_single_of_ne _ _ _ _ h3, sub_zero, add_zero]
  abel

theorem toStd_even (he : Even n) (v : Fin (n / 2) → ℤ) :
    toStd n v = Symplectic.toStd (n / 2) v := by
  unfold Unitary.toStd
  rw [ite_eq_left he]

theorem roots_even (he : Even n) : roots (isFiniteType_cartan n) (divisible n) =
    roots (Symplectic.isFiniteType_cartanC (n / 2)) ∅ := by
  have h1 : cartan n = Symplectic.cartanC (n / 2) := by
    unfold cartan
    rw [ite_eq_left he]
  have h2 : divisible n = ∅ := by
    unfold divisible
    rw [ite_eq_left he]
  rw [h2]
  generalize isFiniteType_cartan n = hA
  revert hA
  rw [h1]
  intro hA
  rfl

theorem rev_ne_self_of_even (he : Even n) (j : Fin n) : j ≠ Fin.rev j := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [Fin.val_rev] at h1
  obtain ⟨r, hr⟩ := he
  have := j.isLt
  omega

omit [Field F] in
theorem exists_ne_ne (hn : 3 ≤ n) (i j : Fin n) : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  obtain ⟨k, hk⟩ : ((Finset.univ : Finset (Fin n)) \ {i, j}).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.card_le_two (a := i) (b := j)
    have h2 := Finset.le_card_sdiff ({i, j} : Finset (Fin n)) Finset.univ
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    omega
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hk
  exact ⟨k, hk⟩

theorem exists_chiF_ne_one (he : Even n) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) {w : (fixField σ)ˣ}
    (hw : w ^ 2 ≠ 1) : ∃ t : Fin (n / 2) → (fixField σ)ˣ, chiF γ t ≠ 1 := by
  have hγ' : γ ∈ roots (Symplectic.isFiniteType_cartanC (n / 2)) ∅ := by
    rw [← roots_even he]
    exact hγ
  obtain ⟨t, ht⟩ := SpTorus.exists_tor_ne_one hγ' hw
  exact ⟨t, fun h => ht (by rw [← toStd_even he]; exact chiF_eq_one_iff.1 h)⟩

theorem exists_chiF_sep (he : Even n) {a b : Fin (n / 2) → ℤ}
    (ha : a ∈ roots (isFiniteType_cartan n) (divisible n))
    (hb : b ∈ roots (isFiniteType_cartan n) (divisible n)) (hli : LinIndepPair a b)
    {w : (fixField σ)ˣ} (hw : w ^ 2 ≠ 1) :
    ∃ t : Fin (n / 2) → (fixField σ)ˣ, chiF a t = 1 ∧ chiF b t ≠ 1 := by
  have ha' : a ∈ roots (Symplectic.isFiniteType_cartanC (n / 2)) ∅ := by
    rw [← roots_even he]
    exact ha
  have hb' : b ∈ roots (Symplectic.isFiniteType_cartanC (n / 2)) ∅ := by
    rw [← roots_even he]
    exact hb
  obtain ⟨t, h1, h2⟩ := SpTorus.exists_tor_sep ha' hb' hli hw
  refine ⟨t, chiF_eq_one_iff.2 (by rw [toStd_even he]; exact h1), fun h => h2 ?_⟩
  rw [← toStd_even he]
  exact chiF_eq_one_iff.1 h

section Lift

variable {E : Type*} [Group E] {π : E →* SU σ n}

variable (π) in
@[expose] def IsRootLift (γ : Fin (n / 2) → ℤ) (Y : F → E) : Prop :=
  (∀ s t, Y (s + t) = Y s * Y t) ∧ (∀ s, π (Y s) = x hσ γ s) ∧ (∀ s, x hσ γ s = 1 → Y s = 1) ∧
    ∀ (t : Fin (n / 2) → (fixField σ)ˣ) (e : E), π e = splitTorus t → ∀ s,
      e * Y s * e⁻¹ = Y (chiF γ t * s)

variable (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen in
theorem commPairing_eq_zero_short [Finite F] (hF4 : Nat.card F ≠ 4) (hF9 : Nat.card F ≠ 9)
    {γ : Fin (n / 2) → ℤ} (hs : ∃ ij : Fin n × Fin n, IsShortPos γ ij.1 ij.2) :
    TorusLift.commPairing hcen hπ (x_add hσ γ) = 0 := by
  obtain ⟨i, j, hij, hx⟩ := x_short hσ hs
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := F)
  refine Pairing.pairing_eq_zero_of_sq p hF4 hF9
    (TorusLift.commPairing_self hcen hπ (x_add hσ γ)) fun u hu s t => ?_
  refine TorusLift.commPairing_smul hcen hπ (x_add hσ γ)
    (g := shortTorus σ hσ hij.1 hij.2.1 hij.2.2.1 u) (fun c => ?_) s t
  rw [conj_x_short hσ ((mat_apply _).trans (coe_shortTorus σ hσ hij.1 hij.2.1 hij.2.2.1
    hij.2.2.2.1 hu)) hij hx, shortTorusFun_left, shortTorusFun_right hij.1, inv_inv]
  congr 1
  ring

include hcen in
theorem commPairing_eq_zero_long (he : Even n) (hn : 4 ≤ n) {γ : Fin (n / 2) → ℤ} {k : Fin n}
    (hk : IsLongPos γ k) : TorusLift.commPairing hcen hπ (x_add hσ γ) = 0 := by
  obtain ⟨i, hl, hx⟩ := x_long hσ hk
  obtain ⟨j, hji, hji'⟩ := exists_ne_ne (by omega) i (Fin.rev i)
  have hj : j ≠ Fin.rev j := rev_ne_self_of_even he j
  have hij : i ≠ j := fun h => hji h.symm
  refine AddMonoidHom.ext fun c => AddMonoidHom.ext fun d => ?_
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [TorusLift.commPairing_apply, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, toMul_zero,
    Subgroup.coe_one]
  set a := TorusLift.lift hπ (rootHom σ hσ hij hl.1 hj (Multiplicative.ofAdd c))
  set b := TorusLift.lift hπ
    (rootHom σ hσ hji' hj (rev_ne_rev_rev hl.1) (Multiplicative.ofAdd 1))
  set y := TorusLift.lift hπ (x hσ γ d)
  have hab : π ⁅a, b⁆ = x hσ γ c := by
    rw [map_commutatorElement, TorusLift.map_lift, TorusLift.map_lift,
      commutator_rootHom_rootHom hσ hij hl.1 hj hji', mul_one, hx]
  rw [TorusLift.commutatorElement_eq_of_map_eq hcen ((TorusLift.map_lift hπ _).trans hab.symm)
    rfl, commutatorElement_eq_one_iff_mul_comm]
  refine (SpinTorus.commute_commutatorElement_of_central hcen ?_ ?_).symm
  · rw [TorusLift.map_lift, TorusLift.map_lift, hx]
    exact commute_longRootHom_rootHom_left hσ hij hl.1 hj c _
  · rw [TorusLift.map_lift, TorusLift.map_lift, hx]
    exact commute_longRootHom_rootHom_right hσ hl.1 hj hji' 1 _

include hcen hπ in
theorem exists_isRootLift (he : Even n) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n))
    (h0 : TorusLift.commPairing hcen hπ (x_add hσ γ) = 0) {t₀ : Fin (n / 2) → (fixField σ)ˣ}
    (ht₀ : chiF γ t₀ ≠ 1) : ∃ Y : F → E, IsRootLift hσ π γ Y := by
  refine ⟨TorusLift.canonLift hπ (x := x hσ γ) (splitTorus t₀) (chiF γ t₀),
    TorusLift.canonLift_add hcen hπ (x_add hσ γ) h0 (splitTorus_conj_x hσ he hγ t₀) ht₀,
    TorusLift.map_canonLift hπ (x_add hσ γ) (splitTorus_conj_x hσ he hγ t₀) ht₀,
    fun s hs => ?_,
    fun t e he' s => TorusLift.conj_canonLift hcen hπ (splitTorus_comm t₀ t)
      (splitTorus_conj_x hσ he hγ t) he' s⟩
  have hb : σ ((chiF γ t₀ - 1)⁻¹) = (chiF γ t₀ - 1)⁻¹ := by
    rw [map_inv₀, map_sub, map_one, map_chiF]
  have h1 : x hσ γ ((chiF γ t₀ - 1)⁻¹ * s) = 1 := x_mul_eq_one hσ hs hb
  have hz : TorusLift.lift hπ (1 : SU σ n) ∈ Subgroup.center E :=
    hcen (by rw [MonoidHom.mem_ker, TorusLift.map_lift])
  show ⁅TorusLift.lift hπ (splitTorus t₀),
    TorusLift.lift hπ (x hσ γ ((chiF γ t₀ - 1)⁻¹ * s))⁆ = 1
  rw [h1, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_center_iff.1 hz _

variable (π) in
open _root_.Classical in
@[expose] noncomputable def X (γ : Fin (n / 2) → ℤ) : F → E :=
  if h : ∃ Y : F → E, IsRootLift hσ π γ Y then h.choose else fun _ => 1

theorem X_isRootLift {γ : Fin (n / 2) → ℤ} (h : ∃ Y : F → E, IsRootLift hσ π γ Y) :
    IsRootLift hσ π γ (X hσ π γ) := by
  classical
  rw [X, dite_eq_left h]
  exact h.choose_spec

end Lift

end General

section Finite

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}

include hF in
theorem exists_sub_eq {z : F} (hz : z + unitaryInvolution F p f z = 0) :
    ∃ c, c - unitaryInvolution F p f c = z := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hσζ : unitaryInvolution F p f (ζ : F) = -ζ := by
    have := ζ.2
    rw [mem_traceZero] at this
    linear_combination this
  have hfix : unitaryInvolution F p f (z / ζ) = z / ζ := by
    rw [map_div₀, hσζ, show unitaryInvolution F p f z = -z by linear_combination hz,
      neg_div_neg_eq]
  obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq hF hfix
  refine ⟨ζ * c, ?_⟩
  rw [map_mul, hσζ]
  calc ζ * c - -ζ * unitaryInvolution F p f c = ζ * (c + unitaryInvolution F p f c) := by ring
    _ = z := by rw [hc]; field_simp

include hF in
theorem coprime_card_torus :
    p.Coprime (Nat.card (⨆ i, levelTorus (unitaryInvolution F p f) i :
      Subgroup (SU (unitaryInvolution F p f) n))) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨d, hd⟩ : ∃ d : Fin n → F,
      mat (unitaryInvolution F p f) n (g : SU (unitaryInvolution F p f) n) = diagonal d :=
    Subgroup.iSup_induction (C := fun y => ∃ d : Fin n → F,
      mat (unitaryInvolution F p f) n y = diagonal d) _ g.2
      (fun k y hy => exists_diagonal_of_mem_levelTorus hy)
      ⟨1, by rw [map_one]; exact diagonal_one.symm⟩ fun y z ⟨d, hd⟩ ⟨d', hd'⟩ =>
        ⟨d * d', by rw [map_mul, hd, hd', diagonal_mul_diagonal]; rfl⟩
  have hd0 : ∀ s, d s ≠ 0 := fun s h => by
    have := diag_unitary hd (Fin.rev s)
    rw [Fin.rev_rev, h, mul_zero] at this
    exact zero_ne_one this
  have hpow : (g : SU (unitaryInvolution F p f) n) ^ (Fintype.card F - 1) = 1 := by
    apply mat_injective
    rw [map_pow, hd, diagonal_pow, map_one]
    convert (diagonal_one : (diagonal fun _ => (1 : F)) = (1 : Matrix (Fin n) (Fin n) F))
      using 2
    funext s
    exact FiniteField.pow_card_sub_one_eq_one (d s) (hd0 s)
  have hdvd' : p ∣ Fintype.card F - 1 := by
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow, hpow,
      Subgroup.coe_one]))
  have hF1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hf : f ≠ 0 := by
    rintro rfl
    rw [Fintype.card_eq_nat_card, hF] at hF1
    simp at hF1
  have hpF : p ∣ Fintype.card F := by
    rw [Fintype.card_eq_nat_card, hF]
    exact dvd_pow (dvd_pow_self p hf) two_ne_zero
  have h1 := Nat.dvd_sub hpF hdvd'
  rw [show Fintype.card F - (Fintype.card F - 1) = 1 by omega] at h1
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h1)

include hF in
theorem su_exists_section_of_pKernel (he : Even n) (hn : 4 ≤ n) (hq : 4 ≤ p ^ f) {E : Type*}
    [Group E] [Finite E] {π : E →* SU (unitaryInvolution F p f) n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    ∃ s : SU (unitaryInvolution F p f) n →* E, ∀ g, π (s g) = g := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hD : (rootDatum hF n).divisible = ∅ := show divisible n = ∅ by
    unfold divisible
    rw [ite_eq_left he]
  have hcardq : Nat.card (fixField (unitaryInvolution F p f)) = p ^ f := card_fixedSubfield hF
  obtain ⟨w, hw⟩ := SpinTorus.exists_unit_sq_ne_one (F := fixField (unitaryInvolution F p f))
    (by rw [hcardq]; exact hq)
  have h16 : 16 ≤ Nat.card F := by
    rw [hF]
    nlinarith
  have hspec : ∀ γ ∈ PosLift.posRoots (rootDatum hF n), IsRootLift hσ π γ (X hσ π γ) := by
    intro γ hγ
    have hγr : γ ∈ roots (isFiniteType_cartan n) (divisible n) := hγ.1
    have h0 : TorusLift.commPairing hcen hπ (x_add hσ γ) = 0 := by
      rcases short_or_long he hγr with hs | ⟨k, hk⟩
      · exact commPairing_eq_zero_short hσ hcen hπ (by omega) (by omega) hs
      · exact commPairing_eq_zero_long hσ hcen hπ he hn hk
    obtain ⟨t, ht⟩ := exists_chiF_ne_one he hγr hw
    exact X_isRootLift hσ (exists_isRootLift hσ hcen hπ he hγr h0 ht)
  refine PosLift.exists_section_of_posLift (isCTGroupDatum hF n (by omega) ζ hζ)
    (steinbergExtras hF n (by omega) ζ hζ) (SUBruhat.bruhatExtras hF (by omega) ζ hζ) hD
    (p := p) (fun γ hγ => isPGroup_rootGroup hσ (toStd_ne_zero_of_mem_roots hγ))
    (coprime_card_torus hF) hπ hcen hpk (x := x hσ)
    (fun γ hγ g => ⟨fun hg => exists_x_eq_of_mem hσ he hγ.1 hγ.2
      (fun z hz => exists_sub_eq hF hz) hg, fun ⟨c, hc⟩ => hc ▸ x_mem hσ γ c⟩)
    (fun γ _ => x_add hσ γ) (X := X hσ π) (fun γ hγ => (hspec γ hγ).1)
    (fun γ hγ => (hspec γ hγ).2.1) (fun γ hγ => (hspec γ hγ).2.2.1)
    (tor := fun t => TorusLift.lift hπ (splitTorus t)) (χ := fun t γ => chiF γ t)
    (fun t γ hγ c => (hspec γ hγ).2.2.2 t _ (TorusLift.map_lift hπ _) c) ?_
  intro a ha b hb hab
  have hli : LinIndepPair a b := by
    by_contra h
    rcases eq_or_eq_neg_of_not_linIndepPair (rootDatum hF n).isFiniteType hD ha.1 hb.1 h with
      h | h
    · exact hab h.symm
    · have h2 := hb.2
      rw [h] at h2
      have : ht (-a) = -ht a := by simp [ht, Finset.sum_neg_distrib]
      rw [this] at h2
      linarith [ha.2]
  exact exists_chiF_sep he ha.1 hb.1 hli hw

end Finite

end CFSG.LieType.Steinberg.CentralExt.SUClosed
