module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.WeightsE
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.StringWts
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Copies
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.ClassSep

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem

section NodeFamily


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem liSub {ι : Type*} [Subsingleton ι] {V : Type} {k : Type} [Field k] [AddCommGroup V] [Module k V]
    (v : ι → V) (h : ∀ i, v i ≠ 0) : LinearIndependent k v := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · exact linearIndependent_empty_type
  · exact LinearIndependent.of_subsingleton i (h i)

@[expose] def alphaF (τ : Tag) (s : Fin τ.rank) : Fin τ.rank → ℤ := fun i => τ.cartan i s

@[expose] def omegaF (τ : Tag) (s : Fin τ.rank) : Fin τ.rank → ℤ := Pi.single s 1

@[expose] def famB (τ : Tag) (s : Fin τ.rank) {A : ℕ} (wW : Fin A → List (Fin τ.rank)) (i : Fin A) :
    Fin τ.rank → ℤ := (wW i).foldr (refE τ) (alphaF τ s)

@[expose] def famY (τ : Tag) (s : Fin τ.rank) {B : ℕ} (uW : Fin B → List (Fin τ.rank)) (j : Fin B) :
    Fin τ.rank → ℤ := (uW j).foldr (refE τ) (omegaF τ s)

@[expose] def famX (τ : Tag) (s : Fin τ.rank) {A B : ℕ} (wW : Fin A → List (Fin τ.rank))
    (uW : Fin B → List (Fin τ.rank)) (i : Fin A) (j : Fin B) : Fin τ.rank → ℤ :=
  (wW i).foldr (refE τ) (famY τ s uW j)

theorem string_wt_vec {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} (hJ : ∀ s', s' ≠ s → s' ∈ J) :
    ∃ J' : Finset ℕ, (∀ i ∈ J', i < n) ∧
      (∀ z : Kˣ, χ (dC τ K s z) = (algebraMap K k (z : K)) ^ (∑ i ∈ J', 2 ^ i)) ∧
      (J' = ∅ → ∀ g, ρ (rankOne τ K s g) y = y) ∧
      Module.finrank k (orbitSpan (ρ.comp (rankOne τ K s)) y) = 2 ^ J'.card ∧
      ∀ b ∈ J', ∃ e ∈ orbitSpan (ρ.comp (rankOne τ K s)) y, e ≠ 0 ∧
        e ∈ wtE ρ (((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) • omegaF τ s - (2 : ℤ) ^ b • alphaF τ s) := by
  obtain ⟨J', hJ', hε, hdim, hJ0, hwt⟩ := string_of_highest (hw := hw) hK hρ ht s
  refine ⟨J', hJ', hε, hJ0, hdim, fun b hb => ?_⟩
  obtain ⟨e, he, he0, hed⟩ := hwt b hb
  refine ⟨e, he, he0, ?_⟩
  set a : ℤ := ((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) with ha
  have hy : ∀ i t, ρ (dC τ K i t) y = kpow (k := k) K t (a * (if i = s then 1 else 0)) • y := by
    intro i t
    have h1 := ht.2.2.1 _ (dC_mem_H i t)
    rw [h1]
    congr 1
    by_cases hi : i = s
    · subst hi
      rw [hε t]
      simp only [↓reduceIte, mul_one]
      unfold kpow
      rw [ha, zpow_natCast]
    · have hiJ := hJ i hi
      have h3 := ((ht.2.2.2 i).1 hiJ).1 t
      rw [h3]
      simp [kpow, hi]
  have hes : ∀ z : Kˣ, ρ (dC τ K s z) e =
      kpow (k := k) K z (a * (if s = s then 1 else 0) - 2 * (2 : ℤ) ^ b) • e := by
    intro z
    rw [hed z]
    simp only [↓reduceIte, mul_one]
    congr 2
    ring
  intro i t
  have := weight_shift ρ s (fun i => a * (if i = s then 1 else 0)) hy ((2 : ℤ) ^ b) he hes i t
  rw [this]
  congr 1
  simp only [omegaF, alphaF, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  ring_nf

variable {s : Fin τ.rank} {A B : ℕ} (wW : Fin A → List (Fin τ.rank)) (uW : Fin B → List (Fin τ.rank))

theorem famVec_weight (a b : ℕ) (hU : ∀ j, (uW j).foldr (refE τ) (alphaF τ s) = alphaF τ s)
    (i : Fin A) (j : Fin B) :
    (wW i ++ uW j).foldr (refE τ) ((a : ℤ) • omegaF τ s - (2 : ℤ) ^ b • alphaF τ s) =
      (a : ℤ) • famX τ s wW uW i j - (2 : ℤ) ^ b • famB τ s wW i := by
  rw [List.foldr_append, foldr_refE_comb, hU j, foldr_refE_comb]
  rfl

include hw in
theorem node_dim_of_sep [Module.Finite k V] {ρ : Representation k (adjointGroup τ K) V}
    (hρ : IsSimpleRep ρ) {n : ℕ} (hK : Nat.card K = 2 ^ n) (a b : ℕ)
    (hU : ∀ j, (uW j).foldr (refE τ) (alphaF τ s) = alphaF τ s) {e : V} (he0 : e ≠ 0)
    (hew : e ∈ wtE ρ ((a : ℤ) • omegaF τ s - (2 : ℤ) ^ b • alphaF τ s))
    (hsep : ∀ p q : Fin A × Fin B,
      (∀ i, ((2 ^ n - 1 : ℕ) : ℤ) ∣
        (((a : ℤ) • famX τ s wW uW p.1 p.2 - (2 : ℤ) ^ b • famB τ s wW p.1) i -
         ((a : ℤ) • famX τ s wW uW q.1 q.2 - (2 : ℤ) ^ b • famB τ s wW q.1) i)) → p = q) :
    A * B ≤ Module.finrank k V := by
  classical
  have hinj : ∀ g' : adjointGroup τ K, Function.Injective (ρ g') :=
    fun g' => (repEquiv ρ g').injective
  let x : Fin A × Fin B → Fin τ.rank → ℤ := fun p =>
    (a : ℤ) • famX τ s wW uW p.1 p.2 - (2 : ℤ) ^ b • famB τ s wW p.1
  let v : Fin A × Fin B → V := fun p => ρ (nProd τ K (wW p.1 ++ uW p.2)) e
  have hv : ∀ p, v p ∈ wtE ρ (x p) := by
    intro p
    have := wt_nProd ρ (wW p.1 ++ uW p.2) hew
    rwa [famVec_weight wW uW a b hU p.1 p.2] at this
  have hv0 : ∀ p, v p ≠ 0 := fun p h0 =>
    he0 (hinj (nProd τ K (wW p.1 ++ uW p.2)) (by rw [map_zero]; exact h0))
  have hcard : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  have hli : LinearIndependent k v := by
    refine linearIndependent_of_wtE hw ρ v x hv (fun c => ?_)
    haveI : Subsingleton {p : Fin A × Fin B // wclsE τ K k (x p) = c} :=
      ⟨fun p q => Subtype.ext (hsep p.1 q.1 (fun i => by
        have := dvd_of_wclsE_eq (p.2.trans q.2.symm) i
        rwa [hcard] at this))⟩
    exact liSub _ (fun p => hv0 p.1)
  simpa using hli.fintype_card_le_finrank

theorem foldr_refE_neg_smul (l : List (Fin τ.rank)) (c : ℤ) (x : Fin τ.rank → ℤ) :
    l.foldr (refE τ) (-(c • x)) = -(c • l.foldr (refE τ) x) := by
  have := foldr_refE_comb l 0 c x x
  have h1 : (0 : ℤ) • x - c • x = -(c • x) := by simp
  rw [h1] at this
  rw [this]
  have h2 : (0 : ℤ) • l.foldr (refE τ) x - c • l.foldr (refE τ) x = -(c • l.foldr (refE τ) x) := by simp
  rw [h2]

theorem kpow_mul_card (t : Kˣ) (M : ℕ) (hM : Nat.card Kˣ = M) (c : ℤ) :
    kpow (k := k) K t (M * c) = 1 := by
  unfold kpow
  rw [zpow_mul, zpow_natCast]
  have h : (algebraMap K k (t : K)) ^ M = 1 := by
    have h1 : t ^ M = 1 := by rw [← hM]; exact pow_card_eq_one'
    have h2 := congrArg (fun u : Kˣ => algebraMap K k (u : K)) h1
    simpa using h2
  rw [h, one_zpow]

include hw in
theorem node_dim_R2 [Module.Finite k V] {ρ : Representation k (adjointGroup τ K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) (hs : s ∉ J) {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n) (b : ℕ)
    (hU : ∀ j, (uW j).foldr (refE τ) (alphaF τ s) = alphaF τ s)
    (hU2 : ∀ j, (uW j).foldr (reflect τ) (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1)
    (v₀ : Fin τ.rank → ℤ) (hv₀ : ∀ j, j ≠ s → reflect τ j v₀ = v₀)
    (hdist : ∀ j j' : Fin B, j ≠ j' →
      (uW j).foldr (reflect τ) v₀ ≠ (uW j').foldr (reflect τ) v₀)
    (hβinj : ∀ i i' : Fin A, famB τ s wW i = famB τ s wW i' → i = i')
    (hβ : ∀ i i' : Fin A, famB τ s wW i ≠ famB τ s wW i' →
      Cont2 (famB τ s wW i - famB τ s wW i'))
    {e : V} (he : e ∈ orbitSpan (ρ.comp (rankOne τ K s)) y) (he0 : e ≠ 0)
    (hew : e ∈ wtE ρ (((2 ^ n - 1 : ℕ) : ℤ) • omegaF τ s - (2 : ℤ) ^ b • alphaF τ s)) :
    A * B ≤ Module.finrank k V := by
  classical
  have hcard : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  have hinj : ∀ g' : adjointGroup τ K, Function.Injective (ρ g') :=
    fun g' => (repEquiv ρ g').injective
  let u' : Fin B → WeylGroup τ := fun j => (coxeterSystem τ).wordProd (uW j)
  have hu : ∀ j, u' j • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1 := by
    intro j; rw [wordProd_smul', hU2 j]
  have hli : LinearIndependent k (fun j => ρ (nWC τ K (u' j)) y) := by
    refine linearIndependent_translates_of_isChevType hρ ht hs hv₀ u' ?_
    intro j j' hjj h
    apply hdist j j' hjj
    have := h
    simp only [u', wordProd_smul'] at this
    exact this
  have hcop := copies_linearIndependent hρ ht (s := s) u' hu hli he he0
  set ν0 : Fin τ.rank → ℤ := -((2 : ℤ) ^ b • (Pi.single s 1 : Fin τ.rank → ℤ)) with hν0
  have hmE : ∀ i, mExp τ i ν0 = (-((2 : ℤ) ^ b • alphaF τ s)) i := by
    intro i
    simp only [hν0, mExp, alphaF, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_neg, Finset.sum_neg_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring
  have heν : e ∈ wtSpace ρ ν0 := by
    intro i t
    rw [hew i t, hmE]
    congr 1
    have : (((2 ^ n - 1 : ℕ) : ℤ) • omegaF τ s - (2 : ℤ) ^ b • alphaF τ s) i =
        ((2 ^ n - 1 : ℕ) : ℤ) * (if i = s then 1 else 0) + (-((2 : ℤ) ^ b • alphaF τ s)) i := by
      simp only [omegaF, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Pi.neg_apply]
      ring
    rw [this, kpow_add, kpow_mul_card t _ hcard, one_mul]
  have hf : ∀ j, ρ (nWC τ K (u' j)) e ∈ wtE ρ (-((2 : ℤ) ^ b • alphaF τ s)) := by
    intro j
    have h1 := wt_nWC hw ρ (u' j) heν
    have h2 : u' j • ν0 = ν0 := by
      rw [hν0, smul_neg, smul_comm, hu j]
    rw [h2] at h1
    intro i t
    rw [h1 i t, hmE]
  let x : Fin A × Fin B → Fin τ.rank → ℤ := fun p => -((2 : ℤ) ^ b • famB τ s wW p.1)
  let v : Fin A × Fin B → V := fun p => ρ (nProd τ K (wW p.1)) (ρ (nWC τ K (u' p.2)) e)
  have hv : ∀ p, v p ∈ wtE ρ (x p) := by
    intro p
    have := wt_nProd ρ (wW p.1) (hf p.2)
    rwa [foldr_refE_neg_smul] at this
  have hM2 : ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ (2 : ℤ) ^ b) := by
    intro h
    have hodd : Odd (2 ^ n - 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact ⟨2 ^ m - 1, by rw [pow_succ]; have := Nat.one_le_two_pow (n := m); omega⟩
    have h1 : (((2 ^ n - 1 : ℕ) : ℤ) ∣ 1) := by
      have := (odd_isCoprime_two_pow hodd b).dvd_of_dvd_mul_left
        (by simpa using h : (((2 ^ n - 1 : ℕ) : ℤ) ∣ (2 : ℤ) ^ b * 1))
      exact this
    have h2 : 2 ^ n - 1 = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ m - 1, by rw [pow_succ]; have := Nat.one_le_two_pow (n := m); omega⟩
  have hli2 : LinearIndependent k v := by
    refine linearIndependent_of_wtE hw ρ v x hv (fun c => ?_)
    rcases isEmpty_or_nonempty {p : Fin A × Fin B // wclsE τ K k (x p) = c} with hE | ⟨⟨p0, hp0⟩⟩
    · exact linearIndependent_empty_type
    · have hsame : ∀ p : {p : Fin A × Fin B // wclsE τ K k (x p) = c}, p.1.1 = p0.1 := by
        intro p
        apply hβinj
        by_contra hne
        have hCB := hβ p.1.1 p0.1 hne
        have hdv : ∀ i, (((2 ^ n - 1 : ℕ) : ℤ)) ∣ (2 : ℤ) ^ b * (famB τ s wW p.1.1 - famB τ s wW p0.1) i := by
          intro i
          have h1 := dvd_of_wclsE_eq (p.2.trans hp0.symm) i
          rw [hcard] at h1
          have e1 : x p.1 i - x p0 i = -((2 : ℤ) ^ b * (famB τ s wW p.1.1 - famB τ s wW p0.1) i) := by
            simp only [x, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
            ring
          rw [e1, dvd_neg] at h1
          exact h1
        exact hM2 (dvd_of_cont2 hCB hodd hdv)
      have hf' : Function.Injective
          (fun p : {p : Fin A × Fin B // wclsE τ K k (x p) = c} => p.1.2) := by
        intro p q hpq
        exact Subtype.ext (Prod.ext ((hsame p).trans (hsame q).symm) hpq)
      have hcop' : LinearIndependent k (fun j : Fin B =>
          ρ (nProd τ K (wW p0.1)) (ρ (nWC τ K (u' j)) e)) :=
        hcop.map' (ρ (nProd τ K (wW p0.1))) (LinearMap.ker_eq_bot.2 (hinj _))
      have := hcop'.comp (fun p : {p : Fin A × Fin B // wclsE τ K k (x p) = c} => p.1.2) hf'
      convert this using 2 with p
      simp only [Function.comp, v]
      rw [hsame p]
  simpa using hli2.fintype_card_le_finrank

end NodeFamily

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
