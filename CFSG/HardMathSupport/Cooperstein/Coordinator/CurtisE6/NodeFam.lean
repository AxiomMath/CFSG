module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Copies
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.ClassSep

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CoxeterSystem
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
open scoped MatrixGroups


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem liSub {ι : Type*} [Subsingleton ι] {V : Type} {k : Type} [Field k] [AddCommGroup V]
    [Module k V] (v : ι → V) (h : ∀ i, v i ≠ 0) : LinearIndependent k v := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · exact linearIndependent_empty_type
  · exact LinearIndependent.of_subsingleton i (h i)

@[expose] def famB (s : N6) {A : ℕ} (wW : Fin A → List N6) (i : Fin A) : N6 → ℤ :=
  (wW i).foldr refE (alphaF s)

@[expose] def famY (s : N6) {B : ℕ} (uW : Fin B → List N6) (j : Fin B) : N6 → ℤ :=
  (uW j).foldr refE (omegaF s)

@[expose] def famX (s : N6) {A B : ℕ} (wW : Fin A → List N6) (uW : Fin B → List N6) (i : Fin A)
    (j : Fin B) : N6 → ℤ :=
  (wW i).foldr refE (famY s uW j)

variable {s : N6} {A B : ℕ} (wW : Fin A → List N6) (uW : Fin B → List N6)

theorem famVec_weight (a b : ℕ) (hU : ∀ j, (uW j).foldr refE (alphaF s) = alphaF s)
    (i : Fin A) (j : Fin B) :
    (wW i ++ uW j).foldr refE ((a : ℤ) • omegaF s - (2 : ℤ) ^ b • alphaF s) =
      (a : ℤ) • famX s wW uW i j - (2 : ℤ) ^ b • famB s wW i := by
  rw [List.foldr_append, foldr_refE_comb, hU j, foldr_refE_comb]
  rfl

theorem node_dim_of_sep [Module.Finite k V] {ρ : Representation k ↥(e6Data_valid.minGroup K) V}
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (a b : ℕ)
    (hU : ∀ j, (uW j).foldr refE (alphaF s) = alphaF s) {e : V} (he0 : e ≠ 0)
    (hew : e ∈ wt ρ ((a : ℤ) • omegaF s - (2 : ℤ) ^ b • alphaF s))
    (hsep : ∀ p q : Fin A × Fin B,
      (∀ i, ((2 ^ n - 1 : ℕ) : ℤ) ∣
        (((a : ℤ) • famX s wW uW p.1 p.2 - (2 : ℤ) ^ b • famB s wW p.1) i -
         ((a : ℤ) • famX s wW uW q.1 q.2 - (2 : ℤ) ^ b • famB s wW q.1) i)) → p = q) :
    A * B ≤ Module.finrank k V := by
  classical
  have hinj : ∀ g' : ↥(e6Data_valid.minGroup K), Function.Injective (ρ g') :=
    fun g' => (repEquiv ρ g').injective
  let x : Fin A × Fin B → N6 → ℤ := fun p =>
    (a : ℤ) • famX s wW uW p.1 p.2 - (2 : ℤ) ^ b • famB s wW p.1
  let v : Fin A × Fin B → V := fun p => ρ (nProd K (wW p.1 ++ uW p.2)) e
  have hv : ∀ p, v p ∈ wt ρ (x p) := by
    intro p
    have := wt_nProd ρ (wW p.1 ++ uW p.2) hew
    rwa [famVec_weight wW uW a b hU p.1 p.2] at this
  have hv0 : ∀ p, v p ≠ 0 := fun p h0 =>
    he0 (hinj (nProd K (wW p.1 ++ uW p.2)) (by rw [map_zero]; exact h0))
  have hcard : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  have hli : LinearIndependent k v := by
    refine linearIndependent_of_wt ρ v x hv (fun c => ?_)
    haveI : Subsingleton {p : Fin A × Fin B // wcls K k (x p) = c} :=
      ⟨fun p q => Subtype.ext (hsep p.1 q.1 (fun i => by
        have := dvd_of_wcls_eq (p.2.trans q.2.symm) i
        rwa [hcard] at this))⟩
    exact liSub _ (fun p => hv0 p.1)
  simpa using hli.fintype_card_le_finrank

theorem foldr_refE_neg_smul (l : List N6) (c : ℤ) (x : N6 → ℤ) :
    l.foldr refE (-(c • x)) = -(c • l.foldr refE x) := by
  have := foldr_refE_comb l 0 c x x
  have h1 : (0 : ℤ) • x - c • x = -(c • x) := by simp
  rw [h1] at this
  rw [this]
  have h2 : (0 : ℤ) • l.foldr refE x - c • l.foldr refE x = -(c • l.foldr refE x) := by simp
  rw [h2]

@[expose] def mE (ν : N6 → ℤ) : N6 → ℤ := fun i => ∑ j, Tag.cartan .E6 i j * ν j

theorem mE_reflect (j : N6) (ν : N6 → ℤ) : mE (reflect Tag.E6 j ν) = refE j (mE ν) := by
  unfold mE refE reflect
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_sub,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem mE_foldr (l : List N6) (ν : N6 → ℤ) :
    mE (l.foldr (reflect Tag.E6) ν) = l.foldr refE (mE ν) := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [List.foldr_cons, List.foldr_cons, mE_reflect, ih]

theorem wt_canonMin (ρ : Representation k ↥(e6Data_valid.minGroup K) V) (w : WeylGroup Tag.E6)
    {ν : N6 → ℤ} {v : V} (hv : v ∈ wt ρ (mE ν)) :
    ρ (canonMin K w) v ∈ wt ρ (mE (w • ν)) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  have hcm : canonMin K ((coxeterSystem Tag.E6).wordProd ω) = nProd K ω := canonMin_wordProd hω
  rw [hcm, wordProd_smul_foldr, mE_foldr]
  exact wt_nProd ρ ω hv

theorem node_dim_R2 [Module.Finite k V] {ρ : Representation k ↥(e6Data_valid.minGroup K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (hs : s ∉ J) {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n) (b : ℕ)
    (hU : ∀ j, (uW j).foldr refE (alphaF s) = alphaF s)
    (hU2 : ∀ j, (uW j).foldr (reflect Tag.E6) (Pi.single s 1 : N6 → ℤ) = Pi.single s 1)
    (v₀ : N6 → ℤ) (hv₀ : ∀ j, reflect Tag.E6 j v₀ ≠ v₀ → j ∉ J)
    (hdist : ∀ j j' : Fin B, j ≠ j' →
      (uW j).foldr (reflect Tag.E6) v₀ ≠ (uW j').foldr (reflect Tag.E6) v₀)
    (hβinj : ∀ i i' : Fin A, famB s wW i = famB s wW i' → i = i')
    (hβ : ∀ i i' : Fin A, famB s wW i ≠ famB s wW i' →
      Cont2 (famB s wW i - famB s wW i'))
    {e : V} (he : e ∈ orbitSpan (ρ.comp (rankOne6 K s)) y) (he0 : e ≠ 0)
    (hew : e ∈ wt ρ (((2 ^ n - 1 : ℕ) : ℤ) • omegaF s - (2 : ℤ) ^ b • alphaF s)) :
    A * B ≤ Module.finrank k V := by
  classical
  have hcard : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  have hinj : ∀ g' : ↥(e6Data_valid.minGroup K), Function.Injective (ρ g') :=
    fun g' => (repEquiv ρ g').injective
  let u' : Fin B → WeylGroup Tag.E6 := fun j => (coxeterSystem Tag.E6).wordProd (uW j)
  have hu : ∀ j, u' j • (Pi.single s 1 : N6 → ℤ) = Pi.single s 1 := by
    intro j; rw [wordProd_smul_foldr, hU2 j]
  have hli : LinearIndependent k (fun j => ρ (canonMin K (u' j)) y) := by
    refine linearIndependent_translates_support hρ ht hv₀ u' ?_
    intro j j' hjj h
    apply hdist j j' hjj
    have := h
    simp only [u', wordProd_smul_foldr] at this
    exact this
  have hcop := copies_linearIndependent hρ ht (s := s) u' hu hli he he0
  set ν0 : N6 → ℤ := -((2 : ℤ) ^ b • (Pi.single s 1 : N6 → ℤ)) with hν0
  have hmE : ∀ i, mE ν0 i = (-((2 : ℤ) ^ b • alphaF s)) i := by
    intro i
    simp only [hν0, mE, alphaF, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_neg, Finset.sum_neg_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring
  have heν : e ∈ wt ρ (mE ν0) := by
    intro i t
    rw [hew i t, hmE]
    congr 1
    have : (((2 ^ n - 1 : ℕ) : ℤ) • omegaF s - (2 : ℤ) ^ b • alphaF s) i =
        ((2 ^ n - 1 : ℕ) : ℤ) * (if i = s then 1 else 0) + (-((2 : ℤ) ^ b • alphaF s)) i := by
      simp only [omegaF, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Pi.neg_apply]
      ring
    rw [this, kp_add, kp_mul_card t _ hcard, one_mul]
  have hf : ∀ j, ρ (canonMin K (u' j)) e ∈ wt ρ (-((2 : ℤ) ^ b • alphaF s)) := by
    intro j
    have h1 := wt_canonMin ρ (u' j) heν
    have h2 : u' j • ν0 = ν0 := by
      rw [hν0, smul_neg, smul_comm, hu j]
    rw [h2] at h1
    intro i t
    rw [h1 i t, hmE]
  let x : Fin A × Fin B → N6 → ℤ := fun p => -((2 : ℤ) ^ b • famB s wW p.1)
  let v : Fin A × Fin B → V := fun p => ρ (nProd K (wW p.1)) (ρ (canonMin K (u' p.2)) e)
  have hv : ∀ p, v p ∈ wt ρ (x p) := by
    intro p
    have := wt_nProd ρ (wW p.1) (hf p.2)
    rwa [foldr_refE_neg_smul] at this
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ m - 1, by rw [pow_succ]; have := Nat.one_le_two_pow (n := m); omega⟩
  have hM2 : ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ (2 : ℤ) ^ b) := by
    intro h
    have h1 : (((2 ^ n - 1 : ℕ) : ℤ) ∣ 1) := by
      have := (odd_isCoprime_two_pow hodd b).dvd_of_dvd_mul_left
        (by simpa using h : (((2 ^ n - 1 : ℕ) : ℤ) ∣ (2 : ℤ) ^ b * 1))
      exact this
    have h2 : 2 ^ n - 1 = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hli2 : LinearIndependent k v := by
    refine linearIndependent_of_wt ρ v x hv (fun c => ?_)
    rcases isEmpty_or_nonempty {p : Fin A × Fin B // wcls K k (x p) = c} with hE | ⟨⟨p0, hp0⟩⟩
    · exact linearIndependent_empty_type
    · have hsame : ∀ p : {p : Fin A × Fin B // wcls K k (x p) = c}, p.1.1 = p0.1 := by
        intro p
        apply hβinj
        by_contra hne
        have hCB := hβ p.1.1 p0.1 hne
        have hdv : ∀ i, (((2 ^ n - 1 : ℕ) : ℤ)) ∣
            (2 : ℤ) ^ b * (famB s wW p.1.1 - famB s wW p0.1) i := by
          intro i
          have h1 := dvd_of_wcls_eq (p.2.trans hp0.symm) i
          rw [hcard] at h1
          have e1 : x p.1 i - x p0 i =
              -((2 : ℤ) ^ b * (famB s wW p.1.1 - famB s wW p0.1) i) := by
            simp only [x, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
            ring
          rw [e1, dvd_neg] at h1
          exact h1
        exact hM2 (dvd_of_cont2 hCB hodd hdv)
      have hf' : Function.Injective
          (fun p : {p : Fin A × Fin B // wcls K k (x p) = c} => p.1.2) := by
        intro p q hpq
        exact Subtype.ext (Prod.ext ((hsame p).trans (hsame q).symm) hpq)
      have hcop' : LinearIndependent k (fun j : Fin B =>
          ρ (nProd K (wW p0.1)) (ρ (canonMin K (u' j)) e)) :=
        hcop.map' (ρ (nProd K (wW p0.1))) (LinearMap.ker_eq_bot.2 (hinj _))
      have := hcop'.comp (fun p : {p : Fin A × Fin B // wcls K k (x p) = c} => p.1.2) hf'
      convert this using 2 with p
      simp only [Function.comp, v]
      rw [hsame p]
  simpa using hli2.fintype_card_le_finrank

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
