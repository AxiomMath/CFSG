module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBigOvergroup
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOp
import CFSG.RankThree.PartOne.KF.BloomCyclic
import CFSG.Mathlib.GroupTheory.SylowConj
import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

private lemma card_submodule_modEq_one {p d : ℕ} [Fact p.Prime] (hdp : d.Prime)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMd : M ^ d = 1)
    (hfix : ∀ v : Fin 3 → ZMod p, Matrix.mulVec M v = v → v = 0)
    {W : Submodule (ZMod p) (Fin 3 → ZMod p)} (hWM : ∀ w ∈ W, Matrix.mulVec M w ∈ W) :
    Nat.card W ≡ 1 [MOD d] := by
  classical
  let f : Function.End W := fun w => ⟨Matrix.mulVec M (w : Fin 3 → ZMod p), hWM w w.2⟩
  have hfpow : ∀ n : ℕ, ∀ w : W,
      ((f ^ n) w : Fin 3 → ZMod p) = Matrix.mulVec (M ^ n) (w : Fin 3 → ZMod p) := by
    intro n
    induction n with
    | zero =>
      intro w
      change (w : Fin 3 → ZMod p) = Matrix.mulVec (M ^ 0) (w : Fin 3 → ZMod p)
      rw [pow_zero, Matrix.one_mulVec]
    | succ n ih =>
      intro w
      rw [pow_succ']
      change (f ((f ^ n) w) : Fin 3 → ZMod p) =
        Matrix.mulVec (M ^ (n + 1)) (w : Fin 3 → ZMod p)
      rw [show ((f ((f ^ n) w) : W) : Fin 3 → ZMod p) =
          Matrix.mulVec M (((f ^ n) w : W) : Fin 3 → ZMod p) from rfl, ih w,
        Matrix.mulVec_mulVec, ← pow_succ']
  have hfd : f ^ d ^ 1 = 1 := by
    rw [pow_one]
    funext w
    apply Subtype.ext
    change ((f ^ d) w : Fin 3 → ZMod p) = (w : Fin 3 → ZMod p)
    rw [hfpow d w, hMd, Matrix.one_mulVec]
  have hfixpts : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, ?_⟩, ?_⟩
    · apply Subtype.ext
      change Matrix.mulVec M ((0 : W) : Fin 3 → ZMod p) = ((0 : W) : Fin 3 → ZMod p)
      simp
    · intro y
      apply Subtype.ext
      apply Subtype.ext
      exact hfix _ (by simpa [f] using congrArg Subtype.val y.2)
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := W) (f := f) (p := d) (n := 1)
    (hp := ⟨hdp⟩) hfd
  rw [Nat.card_eq_fintype_card]
  simpa [hfixpts] using hmod

private lemma card_ker_adjoin_modEq {p d : ℕ} [Fact p.Prime] (hdp : d.Prime)
    {X : GL (Fin 3) (ZMod p)}
    (hfix : ∀ v : Fin 3 → ZMod p,
      Matrix.mulVec (X : Matrix (Fin 3) (Fin 3) (ZMod p)) v = v → v = 0)
    (hXo : orderOf X = d)
    {a : Matrix (Fin 3) (Fin 3) (ZMod p)}
    (ha : a ∈ Algebra.adjoin (ZMod p) {(X : Matrix (Fin 3) (Fin 3) (ZMod p))}) :
    Nat.card (LinearMap.ker (Matrix.toLin' a)) ≡ 1 [MOD d] := by
  set X' : Matrix (Fin 3) (Fin 3) (ZMod p) :=
    (X : Matrix (Fin 3) (Fin 3) (ZMod p)) with hX'
  have hX'A : X' ∈ Algebra.adjoin (ZMod p) {X'} :=
    Algebra.self_mem_adjoin_singleton (ZMod p) X'
  have hXd : X' ^ d = 1 := by
    have h1 : X ^ d = 1 := by rw [← hXo]; exact pow_orderOf_eq_one X
    have h2 := congrArg Units.val h1
    simpa [hX', Units.val_pow_eq_pow_val] using h2
  refine card_submodule_modEq_one hdp hXd hfix fun w hw => ?_
  have hw' : Matrix.mulVec a w = 0 := hw
  show Matrix.mulVec a (Matrix.mulVec X' w) = 0
  rw [Matrix.mulVec_mulVec,
    CFSG.RankThree.PartOne.KFBloom.adjoin_singleton_comm X' ha hX'A,
    ← Matrix.mulVec_mulVec, hw', Matrix.mulVec_zero]

private lemma finrank_eq_zero_of_pow_modEq {p d : ℕ} [Fact p.Prime]
    (hd : ¬ d ∣ (p ^ 2 - 1) * (p ^ 2 - p))
    {W : Submodule (ZMod p) (Fin 3 → ZMod p)}
    (hW : p ^ Module.finrank (ZMod p) W ≡ 1 [MOD d]) (hWtop : W ≠ ⊤) :
    Module.finrank (ZMod p) W = 0 := by
  have hu : Module.finrank (ZMod p) W ≤ 3 := by
    have h := Submodule.finrank_le W
    rwa [Module.finrank_pi, Fintype.card_fin] at h
  set u := Module.finrank (ZMod p) W with hu_def
  have hWu : p ^ u ≡ 1 [MOD d] := by rw [hu_def]; exact hW
  interval_cases u
  · omega
  · exfalso
    have h1 : p ≡ 1 [MOD d] := by simpa using hWu
    have h2 : p ^ 2 ≡ 1 [MOD d] := by simpa using h1.pow 2
    have hdvd : d ∣ p ^ 2 - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow 2 p (Fact.out : p.Prime).pos)).mp h2.symm
    exact hd (dvd_mul_of_dvd_left hdvd _)
  · exfalso
    have h2 : p ^ 2 ≡ 1 [MOD d] := by simpa using hWu
    have hdvd : d ∣ p ^ 2 - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow 2 p (Fact.out : p.Prime).pos)).mp h2.symm
    exact hd (dvd_mul_of_dvd_left hdvd _)
  · exfalso
    apply hWtop
    apply Submodule.eq_top_of_finrank_eq
    have h3 : Module.finrank (ZMod p) W = 3 := by omega
    rw [h3, Module.finrank_pi, Fintype.card_fin]

private lemma injective_of_mem_adjoin_of_prime_order {p d : ℕ} [Fact p.Prime] (hdp : d.Prime)
    {X : GL (Fin 3) (ZMod p)}
    (hfix : ∀ v : Fin 3 → ZMod p,
      Matrix.mulVec (X : Matrix (Fin 3) (Fin 3) (ZMod p)) v = v → v = 0)
    (hXo : orderOf X = d) (hd : ¬ d ∣ (p ^ 2 - 1) * (p ^ 2 - p)) :
    ∀ a ∈ Algebra.adjoin (ZMod p) {(X : Matrix (Fin 3) (Fin 3) (ZMod p))}, a ≠ 0 →
      ∀ v : Fin 3 → ZMod p, Matrix.mulVec a v = 0 → v = 0 := by
  classical
  intro a ha ha0 v hv
  let W : Submodule (ZMod p) (Fin 3 → ZMod p) := LinearMap.ker (Matrix.toLin' a)
  have hmod : Nat.card W ≡ 1 [MOD d] := card_ker_adjoin_modEq hdp hfix hXo ha
  have hcardW : Nat.card W = p ^ Module.finrank (ZMod p) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := W), Nat.card_zmod]
  have hWmod : p ^ Module.finrank (ZMod p) W ≡ 1 [MOD d] := by
    rw [← hcardW]
    exact hmod
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply ha0
    ext i j
    have hmem : (Pi.single j (1 : ZMod p) : Fin 3 → ZMod p) ∈ W := by
      rw [htop]; trivial
    have h2 := congrFun (show Matrix.mulVec a (Pi.single j (1 : ZMod p)) = 0 from hmem) i
    simpa [Matrix.mulVec_single_one] using h2
  have hzero : Module.finrank (ZMod p) W = 0 :=
    finrank_eq_zero_of_pow_modEq hd hWmod hWtop
  have hbot : W = ⊥ := (Submodule.finrank_eq_zero).mp hzero
  have hvW : v ∈ W := by
    show (Matrix.toLin' a) v = 0
    rw [Matrix.toLin'_apply]
    exact hv
  rw [hbot] at hvW
  simpa using hvW

private lemma aeval_pow_prime_zmod {p : ℕ} [Fact p.Prime]
    (r : Matrix (Fin 3) (Fin 3) (ZMod p)) (q : Polynomial (ZMod p)) :
    Polynomial.aeval (r ^ p) q = (Polynomial.aeval r q) ^ p := by
  rw [← Polynomial.expand_aeval (R := ZMod p) p q r, ZMod.expand_card, map_pow]

private lemma prime_pow_not_modEq {p d : ℕ} [Fact p.Prime]
    (hd : ¬ d ∣ (p ^ 2 - 1) * (p ^ 2 - p)) :
    ¬ 1 ≡ p [MOD d] ∧ ¬ 1 ≡ p ^ 2 [MOD d] ∧ ¬ p ≡ p ^ 2 [MOD d] := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h2 : 1 ≡ p ^ 2 [MOD d] := by simpa [pow_two] using h.mul h
    exact hd (dvd_mul_of_dvd_left
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow 2 p (Fact.out : p.Prime).pos)).mp h2) _)
  · intro h
    exact hd (dvd_mul_of_dvd_left
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow 2 p (Fact.out : p.Prime).pos)).mp h) _)
  · intro h
    exact hd (dvd_mul_of_dvd_right
      ((Nat.modEq_iff_dvd' (Nat.le_self_pow (by norm_num : 2 ≠ 0) p)).mp h) _)

private lemma adjoin_pow_prime_ne {p d : ℕ} [Fact p.Prime]
    {X : GL (Fin 3) (ZMod p)} (hXo : orderOf X = d)
    (hd : ¬ d ∣ (p ^ 2 - 1) * (p ^ 2 - p))
    {A : Subalgebra (ZMod p) (Matrix (Fin 3) (Fin 3) (ZMod p))}
    {X' : Matrix (Fin 3) (Fin 3) (ZMod p)}
    (hX' : X' = (X : Matrix (Fin 3) (Fin 3) (ZMod p)))
    {x xp xp2 : A}
    (hx : (x : Matrix (Fin 3) (Fin 3) (ZMod p)) = X')
    (hxp : (xp : Matrix (Fin 3) (Fin 3) (ZMod p)) = X' ^ p)
    (hxp2 : (xp2 : Matrix (Fin 3) (Fin 3) (ZMod p)) = X' ^ (p ^ 2)) :
    x ≠ xp ∧ x ≠ xp2 ∧ xp ≠ xp2 := by
  have hiff : ∀ m n : ℕ, X ^ m = X ^ n ↔ m ≡ n [MOD d] := by
    intro m n
    rw [pow_eq_pow_iff_modEq, hXo]
  have hval : ∀ n : ℕ,
      ((X ^ n : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = X' ^ n := by
    intro n
    rw [hX']
    exact Units.val_pow_eq_pow_val X n
  obtain ⟨hmod01, hmod02, hmod12⟩ := prime_pow_not_modEq hd
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hmod01
    have h' : X ^ 1 = X ^ p := Units.ext (by
      rw [hval 1, hval p, pow_one]
      simpa [hx, hxp] using
        congrArg (fun a : A => (a : Matrix (Fin 3) (Fin 3) (ZMod p))) h)
    exact (hiff 1 p).mp h'
  · intro h
    apply hmod02
    have h' : X ^ 1 = X ^ (p ^ 2) := Units.ext (by
      rw [hval 1, hval (p ^ 2), pow_one]
      simpa [hx, hxp2] using
        congrArg (fun a : A => (a : Matrix (Fin 3) (Fin 3) (ZMod p))) h)
    exact (hiff 1 (p ^ 2)).mp h'
  · intro h
    apply hmod12
    have h' : X ^ p = X ^ (p ^ 2) := Units.ext (by
      rw [hval p, hval (p ^ 2)]
      simpa [hxp, hxp2] using
        congrArg (fun a : A => (a : Matrix (Fin 3) (Fin 3) (ZMod p))) h)
    exact (hiff p (p ^ 2)).mp h'

private lemma aeval_minpoly_pow_eq_zero {p k : ℕ} [Fact p.Prime]
    {X Y : GL (Fin 3) (ZMod p)}
    {X' : Matrix (Fin 3) (Fin 3) (ZMod p)}
    (hX' : X' = (X : Matrix (Fin 3) (Fin 3) (ZMod p))) (hk : Y * X * Y⁻¹ = X ^ k) :
    (∀ n : ℕ, Polynomial.aeval (X' ^ (p ^ n)) (minpoly (ZMod p) X') = 0) ∧
      Polynomial.aeval (X' ^ k) (minpoly (ZMod p) X') = 0 := by
  have hrootX : Polynomial.aeval X' (minpoly (ZMod p) X') = 0 := minpoly.aeval (ZMod p) X'
  refine ⟨?_, ?_⟩
  · intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : X' ^ (p ^ (n + 1)) = (X' ^ (p ^ n)) ^ p := by
        rw [show p ^ (n + 1) = p ^ n * p by rw [pow_succ], pow_mul]
      rw [h1, aeval_pow_prime_zmod, ih, zero_pow (Fact.out : p.Prime).ne_zero]
  · have hk' : X' ^ k = (Y : Matrix (Fin 3) (Fin 3) (ZMod p)) * X' *
        ((Y⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
      have h := congrArg Units.val hk
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, ← hX'] at h
      exact h.symm
    rw [hk', CFSG.RankThree.PartOne.KFBloom.aeval_conj_unit, hrootX,
      Matrix.mul_zero, Matrix.zero_mul]

private lemma exists_modEq_pow_of_four_roots {p d k : ℕ} [Fact p.Prime]
    {X : GL (Fin 3) (ZMod p)} (hXo : orderOf X = d)
    {A : Subalgebra (ZMod p) (Matrix (Fin 3) (Fin 3) (ZMod p))}
    {X' : Matrix (Fin 3) (Fin 3) (ZMod p)}
    (hX' : X' = (X : Matrix (Fin 3) (Fin 3) (ZMod p)))
    {R : Finset A}
    (hR : ∀ b : A, b ∈ R ↔
      Polynomial.aeval (b : Matrix (Fin 3) (Fin 3) (ZMod p)) (minpoly (ZMod p) X') = 0)
    (hRcard : R.card ≤ 3)
    {x xp xp2 xk : A}
    (hx : (x : Matrix (Fin 3) (Fin 3) (ZMod p)) = X')
    (hxp : (xp : Matrix (Fin 3) (Fin 3) (ZMod p)) = X' ^ p)
    (hxp2 : (xp2 : Matrix (Fin 3) (Fin 3) (ZMod p)) = X' ^ (p ^ 2))
    (hxk : (xk : Matrix (Fin 3) (Fin 3) (ZMod p)) = X' ^ k)
    (hrootX : Polynomial.aeval X' (minpoly (ZMod p) X') = 0)
    (hrootp : ∀ n : ℕ, Polynomial.aeval (X' ^ (p ^ n)) (minpoly (ZMod p) X') = 0)
    (hrootk : Polynomial.aeval (X' ^ k) (minpoly (ZMod p) X') = 0)
    (hxne : x ≠ xp) (hxne2 : x ≠ xp2) (hxpne2 : xp ≠ xp2) :
    ∃ j < 3, k ≡ p ^ j [MOD d] := by
  have hiff : ∀ m n : ℕ, X ^ m = X ^ n ↔ m ≡ n [MOD d] := by
    intro m n
    rw [pow_eq_pow_iff_modEq, hXo]
  have hval : ∀ n : ℕ,
      ((X ^ n : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = X' ^ n := by
    intro n
    rw [hX']
    exact Units.val_pow_eq_pow_val X n
  by_cases h0 : xk = x
  · refine ⟨0, by norm_num, ?_⟩
    have h' : X ^ k = X ^ 1 := Units.ext (by
      rw [hval k, hval 1, pow_one]
      simpa [hxk, hx] using
        congrArg (fun a : A => (a : Matrix (Fin 3) (Fin 3) (ZMod p))) h0)
    simpa using (hiff k 1).mp h'
  by_cases h1 : xk = xp
  · refine ⟨1, by norm_num, ?_⟩
    have h' : X ^ k = X ^ p := Units.ext (by
      rw [hval k, hval p]
      simpa [hxk, hxp] using
        congrArg (fun a : A => (a : Matrix (Fin 3) (Fin 3) (ZMod p))) h1)
    simpa using (hiff k p).mp h'
  by_cases h2 : xk = xp2
  · refine ⟨2, by norm_num, ?_⟩
    have h' : X ^ k = X ^ (p ^ 2) := Units.ext (by
      rw [hval k, hval (p ^ 2)]
      simpa [hxk, hxp2] using
        congrArg (fun a : A => (a : Matrix (Fin 3) (Fin 3) (ZMod p))) h2)
    simpa using (hiff k (p ^ 2)).mp h'
  · exfalso
    have hxnek : x ≠ xk := fun h => h0 h.symm
    have hxpnek : xp ≠ xk := fun h => h1 h.symm
    have hxp2nek : xp2 ≠ xk := fun h => h2 h.symm
    have hSsub : ({x, xp, xp2, xk} : Finset A) ⊆ R := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rw [hR]
      rcases hb with rfl | rfl | rfl | rfl
      · rw [hx]
        exact hrootX
      · simpa [hxp] using hrootp 1
      · simpa [hxp2] using hrootp 2
      · simpa [hxk] using hrootk
    have hcard4 : ({x, xp, xp2, xk} : Finset A).card = 4 :=
      Finset.card_eq_four.mpr
        ⟨x, xp, xp2, xk, hxne, hxne2, hxnek, hxpne2, hxpnek, hxp2nek, rfl⟩
    have := Finset.card_le_card hSsub
    omega

private theorem exists_modEq_pow_of_conj_matrix {p d k : ℕ} [Fact p.Prime] (hdp : d.Prime)
    {X Y : GL (Fin 3) (ZMod p)}
    (hfix : ∀ v : Fin 3 → ZMod p, Matrix.mulVec (X : Matrix (Fin 3) (Fin 3) (ZMod p)) v = v →
      v = 0)
    (hXo : orderOf X = d) (hd : ¬ d ∣ (p ^ 2 - 1) * (p ^ 2 - p)) (hk : Y * X * Y⁻¹ = X ^ k) :
    ∃ j < 3, k ≡ p ^ j [MOD d] := by
  classical
  set X' : Matrix (Fin 3) (Fin 3) (ZMod p) :=
    (X : Matrix (Fin 3) (Fin 3) (ZMod p)) with hX'
  set A : Subalgebra (ZMod p) (Matrix (Fin 3) (Fin 3) (ZMod p)) :=
    Algebra.adjoin (ZMod p) {X'} with hA
  have hinj : ∀ a ∈ A, a ≠ 0 →
      ∀ v : Fin 3 → ZMod p, Matrix.mulVec a v = 0 → v = 0 := by
    rw [hA, hX']
    exact injective_of_mem_adjoin_of_prime_order hdp hfix hXo hd
  obtain ⟨R, hR, hRcard⟩ := CFSG.RankThree.PartOne.KFBloom.card_roots_adjoin_le X' hinj
  have hrootX : Polynomial.aeval X' (minpoly (ZMod p) X') = 0 := minpoly.aeval (ZMod p) X'
  obtain ⟨hrootp, hrootk⟩ := aeval_minpoly_pow_eq_zero hX' hk
  let x : A := ⟨X', Algebra.self_mem_adjoin_singleton (ZMod p) X'⟩
  let xp : A := ⟨X' ^ p, A.pow_mem x.2 p⟩
  let xp2 : A := ⟨X' ^ (p ^ 2), A.pow_mem x.2 (p ^ 2)⟩
  let xk : A := ⟨X' ^ k, A.pow_mem x.2 k⟩
  obtain ⟨hxne, hxne2, hxpne2⟩ :=
    adjoin_pow_prime_ne (A := A) (x := x) (xp := xp) (xp2 := xp2)
      hXo hd hX' rfl rfl rfl
  exact exists_modEq_pow_of_four_roots (A := A) (x := x) (xp := xp) (xp2 := xp2)
    (xk := xk) hXo hX' hR hRcard rfl rfl rfl rfl hrootX hrootp hrootk hxne hxne2 hxpne2

private theorem normalizerAction_mulVec {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {V : Subgroup G} {e : ↥V ≃* Multiplicative (Fin 3 → ZMod p)}
    (n : Subgroup.normalizer (V : Set G)) {u v : ↥V}
    (huv : (v : G) = (n : G) * u * (n : G)⁻¹) :
    Matrix.mulVec (((CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp
        V.normalizerMonoidHom) n : Matrix (Fin 3) (Fin 3) (ZMod p))
        (Multiplicative.toAdd (e u)) = Multiplicative.toAdd (e v) := by
  have h : V.normalizerMonoidHom n u = v := Subtype.ext huv.symm
  have hstep := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e (V.normalizerMonoidHom n) u
  rw [h] at hstep
  simpa using hstep

private theorem eq_zero_of_mulVec_eq_self {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {V : Subgroup G} {e : ↥V ≃* Multiplicative (Fin 3 → ZMod p)} {a : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G))
    (hfix : ∀ v ∈ V, a * v * a⁻¹ = v → v = 1) {v : Fin 3 → ZMod p}
    (hv : Matrix.mulVec (((CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp
        V.normalizerMonoidHom) ⟨a, ha⟩ : Matrix (Fin 3) (Fin 3) (ZMod p)) v = v) :
    v = 0 := by
  let w : ↥V := e.symm (Multiplicative.ofAdd v)
  have hw : Multiplicative.toAdd (e w) = v := by simp [w]
  let w' : ↥V :=
    ⟨a * (w : G) * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha (w : G)).mp w.2⟩
  have hstep := normalizerAction_mulVec (e := e) ⟨a, ha⟩ (u := w) (v := w') rfl
  have hsame : Multiplicative.toAdd (e w') = Multiplicative.toAdd (e w) := by
    rw [← hstep, hw, hv]
  have hw' : w' = w := e.injective (Multiplicative.toAdd.injective hsame)
  have hone : (w : G) = 1 := hfix (w : G) w.2 (by
    have hcoe := congrArg (fun z : ↥V => (z : G)) hw'
    simpa [w'] using hcoe)
  calc v = Multiplicative.toAdd (e w) := hw.symm
    _ = Multiplicative.toAdd (e 1) := by rw [show w = 1 from Subtype.ext hone]
    _ = 0 := by simp

private theorem subsingleton_of_conjAction_eq_one {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {V : Subgroup G} {e : ↥V ≃* Multiplicative (Fin 3 → ZMod p)} {a : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G))
    (hfix : ∀ v ∈ V, a * v * a⁻¹ = v → v = 1)
    (h1 : ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp
      V.normalizerMonoidHom) ⟨a, ha⟩ = 1) : Subsingleton ↥V := by
  have hker : V.normalizerMonoidHom ⟨a, ha⟩ = 1 := by
    apply (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective
    simpa using h1
  have hax : ∀ x : ↥V, a * (x : G) * a⁻¹ = (x : G) := by
    intro x
    have hx : V.normalizerMonoidHom ⟨a, ha⟩ x = x := by rw [hker]; rfl
    have hcoe := congrArg (fun y : ↥V => (y : G)) hx
    simpa using hcoe
  refine ⟨fun x y => ?_⟩
  exact Subtype.ext ((hfix x x.2 (hax x)).trans (hfix y y.2 (hax y)).symm)

theorem false_of_conj_pow_of_card_eq_cube {G : Type*} [Group G] [Finite G] {p d k : ℕ}
    [Fact p.Prime] (hdp : d.Prime) {V : Subgroup G} (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hVp : ∀ v ∈ V, v ^ p = 1) (hV : Nat.card V = p ^ 3) {a b : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G)) (hb : b ∈ Subgroup.normalizer (V : Set G))
    (hfix : ∀ v ∈ V, a * v * a⁻¹ = v → v = 1) (hao : orderOf a = d)
    (hd : ¬ d ∣ (p ^ 2 - 1) * (p ^ 2 - p)) (hk : b * a * b⁻¹ = a ^ k)
    (hkp : ∀ j < 3, ¬ k ≡ p ^ j [MOD d]) : False := by
  have hVcard : Nat.card ↥V = p ^ 3 := by simpa using hV
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := ↥V) (p := p)
    (n := 3) (fun x y => Subtype.ext (hVab x x.2 y y.2)) (fun x => Subtype.ext (hVp x x.2)) hVcard
  let f : Subgroup.normalizer (V : Set G) →* GL (Fin 3) (ZMod p) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp V.normalizerMonoidHom
  let X : GL (Fin 3) (ZMod p) := f ⟨a, ha⟩
  let Y : GL (Fin 3) (ZMod p) := f ⟨b, hb⟩
  have hconj : (⟨b, hb⟩ : Subgroup.normalizer (V : Set G)) * ⟨a, ha⟩ * ⟨b, hb⟩⁻¹ =
      ⟨a, ha⟩ ^ k := by
    apply Subtype.ext
    simpa using hk
  have hYX : Y * X * Y⁻¹ = X ^ k := by
    change f ⟨b, hb⟩ * f ⟨a, ha⟩ * (f ⟨b, hb⟩)⁻¹ = f ⟨a, ha⟩ ^ k
    rw [← map_mul, ← map_inv, ← map_mul, hconj, map_pow]
  have hfixX : ∀ v : Fin 3 → ZMod p,
      Matrix.mulVec (X : Matrix (Fin 3) (Fin 3) (ZMod p)) v = v → v = 0 := by
    intro v hv
    exact eq_zero_of_mulVec_eq_self (e := e) ha hfix hv
  have hXne : X ≠ 1 := by
    intro hX1
    have hsub : Subsingleton ↥V := subsingleton_of_conjAction_eq_one (e := e) ha hfix hX1
    have hcard1 : Nat.card ↥V = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [hVcard] at hcard1
    have hpdvd : p ∣ p ^ 3 := dvd_pow_self p (by norm_num)
    rw [hcard1] at hpdvd
    exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hpdvd)
  have hXo : orderOf X = d := by
    have hdvd : orderOf X ∣ d := by
      have h := orderOf_map_dvd ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp
        V.normalizerMonoidHom) (⟨a, ha⟩ : Subgroup.normalizer (V : Set G))
      have hda : orderOf (⟨a, ha⟩ : Subgroup.normalizer (V : Set G)) = d :=
        (Subgroup.orderOf_mk (H := Subgroup.normalizer (V : Set G)) a ha).trans hao
      rwa [hda] at h
    rcases hdp.eq_one_or_self_of_dvd (orderOf X) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hXne
    · exact h
  obtain ⟨j, hj, hjk⟩ := exists_modEq_pow_of_conj_matrix hdp hfixX hXo hd hYX
  exact hkp j hj hjk

variable {L : Type} [Group L] [Finite L] {p d : ℕ} {Y : Subgroup L}

private lemma dvd_gl2_of_dvd_sub_pow {p d w : ℕ} (hp : p.Prime) (hd : d.Prime) (hne : d ≠ p)
    (hw1 : 1 ≤ w) (hw2 : w ≤ 2) (hdvd : d ∣ p ^ 3 - p ^ w) :
    d ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
  interval_cases w
  · rw [pow_one] at hdvd
    have hp3 : p ^ 3 - p = p * (p ^ 2 - 1) := by
      rw [Nat.mul_sub]
      ring_nf
    rw [hp3] at hdvd
    have hdvd' : d ∣ p ^ 2 - 1 := by
      rcases hd.dvd_mul.mp hdvd with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hd hp).mp h) hne
      · exact h
    exact hdvd'.trans (dvd_mul_right (p ^ 2 - 1) (p ^ 2 - p))
  · have hp3 : p ^ 3 - p ^ 2 = p ^ 2 * (p - 1) := by
      rw [Nat.mul_sub]
      ring_nf
    rw [hp3] at hdvd
    have hdvd' : d ∣ p - 1 := by
      rcases hd.dvd_mul.mp hdvd with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hd hp).mp (hd.dvd_of_dvd_pow h)) hne
      · exact h
    have hdvd'' : d ∣ p ^ 2 - 1 := by
      have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
        rw [Nat.sub_mul]
        ring_nf
        omega
      rw [hsq]
      exact hdvd'.trans (dvd_mul_right (p - 1) (p + 1))
    exact hdvd''.trans (dvd_mul_right (p ^ 2 - 1) (p ^ 2 - p))

private lemma conj_pow_core (h : SporOvergroupData L p d Y)
    {a b : L} {k : ℕ} (ha : orderOf a = d) (hk : b * a * b⁻¹ = a ^ k) :
    ∃ a' b' : L, orderOf a' = d ∧ b' * a' * b'⁻¹ = a' ^ k ∧ a' ∈ Y ∧ b' ∈ Y := by
  obtain ⟨D, hDsyl, hDne, hnorm⟩ := h.sylowD
  have : Fact d.Prime := ⟨h.d_prime⟩
  have hDcard : Nat.card D = d ^ (Nat.card (⊤ : Subgroup L)).factorization d := hDsyl.card_eq
  have hza : IsPGroup d (Subgroup.zpowers a) :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, ha, pow_one]⟩
  obtain ⟨g, -, hg⟩ := IsPGroup.exists_mem_conj_mem_of_card_eq (G := L) (p := d)
    (P := ⊤) (Q := D) (R := Subgroup.zpowers a) le_top hDcard le_top hza
  have hga : g⁻¹ * a * g ∈ D := hg a (Subgroup.mem_zpowers a)
  let a' := g⁻¹ * a * g
  let b' := g⁻¹ * b * g
  let φ : L ≃* L := MulAut.conj (g⁻¹)
  have hφa : φ a = a' := by
    dsimp [a', φ]
    group
  have hφb : φ b = b' := by
    dsimp [b', φ]
    group
  have ha'_order : orderOf a' = d := by
    rw [← hφa, ← ha]
    exact φ.orderOf_eq a
  have ha'_ne : a' ≠ 1 := by
    intro h1
    have h2 : orderOf a' = 1 := by rw [h1]; exact orderOf_one
    rw [ha'_order] at h2; exact h.d_prime.ne_one h2
  have ha'_D : a' ∈ D := hga
  have hb'_eq : b' * a' * b'⁻¹ = a' ^ k := by
    rw [← hφb, ← hφa, ← map_inv, ← map_mul, ← map_mul, hk, map_pow]
  have ha'_Y : a' ∈ Y := by
    have hle : Subgroup.zpowers a' ≤ D := Subgroup.zpowers_le.mpr ha'_D
    have hne : Subgroup.zpowers a' ≠ ⊥ := by
      simpa [Subgroup.zpowers_eq_bot] using ha'_ne
    exact hnorm (Subgroup.zpowers a') hle hne
      (Subgroup.le_normalizer (Subgroup.mem_zpowers a'))
  have hb'_Y : b' ∈ Y := by
    have hle : Subgroup.zpowers a' ≤ D := Subgroup.zpowers_le.mpr ha'_D
    have hne : Subgroup.zpowers a' ≠ ⊥ := by
      simpa [Subgroup.zpowers_eq_bot] using ha'_ne
    have hmem : b' ∈ Subgroup.normalizer ((Subgroup.zpowers a') : Set L) := by
      rw [CFSG.GroupTheory.mem_normalizer_zpowers_iff]
      rw [hb'_eq]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a') k
    exact hnorm (Subgroup.zpowers a') hle hne hmem
  exact ⟨a', b', ha'_order, hb'_eq, ha'_Y, hb'_Y⟩

private lemma fixedPoints_zpowers_eq_comap {G : Type*} [Group G] {V : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G)) :
    letI : MulDistribMulAction (Subgroup.zpowers a) V :=
      MulDistribMulAction.compHom (A := V) (Subgroup.inclusion (Subgroup.zpowers_le.mpr ha))
    MulAction.fixedPoints (Subgroup.zpowers a) V =
      ((V ⊓ Subgroup.centralizer ({a} : Set G)).comap V.subtype : Set V) := by
  classical
  let P := Subgroup.zpowers a
  have hPleN : P ≤ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr ha
  let act : P →* Subgroup.normalizer (V : Set G) := Subgroup.inclusion hPleN
  let _ : MulDistribMulAction P V := MulDistribMulAction.compHom (A := V) act
  have hsm : ∀ (p : P) (v : V), ((p • v : V) : G) = (p : G) * (v : G) * (p : G)⁻¹ := by
    intro p v
    rfl
  ext v
  change v ∈ MulAction.fixedPoints P V ↔
    v ∈ (V ⊓ Subgroup.centralizer ({a} : Set G)).comap V.subtype
  rw [MulAction.mem_fixedPoints, Subgroup.mem_comap, Subgroup.mem_inf]
  constructor
  · intro hv
    refine ⟨v.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hv ⟨a, Subgroup.mem_zpowers a⟩
    have hcoe := congrArg (fun x : V => (x : G)) h
    rw [hsm] at hcoe
    calc (v : G) * a = (a * (v : G) * a⁻¹) * a := by rw [hcoe]
      _ = a * (v : G) := by group
  · rintro ⟨-, hC⟩ p
    have hv : (v : G) * a = a * (v : G) := Subgroup.mem_centralizer_singleton_iff.mp hC
    have hmem : (v : G) ∈ Subgroup.centralizer (Subgroup.zpowers a) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hC
    apply Subtype.ext
    rw [hsm]
    have hcomm : (p : G) * (v : G) = (v : G) * (p : G) := by
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact hmem (p : G) p.2
    calc ((p : G) * (v : G) * (p : G)⁻¹) = ((v : G) * (p : G) * (p : G)⁻¹) := by rw [hcomm]
      _ = (v : G) := by group

private lemma eq_zero_or_eq_three_of_pow_modEq {p d w : ℕ} (hp : p.Prime) (hd : d.Prime)
    (hne : d ≠ p) (hdgl : ¬ d ∣ (p ^ 2 - 1) * (p ^ 2 - p)) (hw : w ≤ 3)
    (hmod : p ^ 3 ≡ p ^ w [MOD d]) : w = 0 ∨ w = 3 := by
  rcases Nat.eq_zero_or_pos w with hw0 | hw0
  · exact Or.inl hw0
  rcases Nat.lt_or_ge w 3 with hw3 | hw3
  · exact absurd (dvd_gl2_of_dvd_sub_pow hp hd hne (by omega) (by omega) hmod.symm.dvd') hdgl
  · exact Or.inr (by omega)

private lemma orderOf_dvd_card_centralizer_of_le {G : Type*} [Group G] {V : Subgroup G}
    {a z : G} (hV : V ≤ Subgroup.centralizer ({a} : Set G)) (hzV : z ∈ V) :
    orderOf a ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  refine Subgroup.orderOf_dvd_natCard _ ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hV hzV)).symm

private lemma inf_centralizer_eq_bot_of_card_eq_cube (h : SporOvergroupData L p d Y)
    {V : Subgroup L} (hVcard : Nat.card V = p ^ 3)
    {a : L} (ha : orderOf a = d) (ha_N : a ∈ Subgroup.normalizer (V : Set L))
    {z : L} (hzV : z ∈ V)
    (hCz : ¬ d ∣ (p ^ 2 - 1) * (p ^ 2 - p) * Nat.card (Subgroup.centralizer ({z} : Set L))) :
    V ⊓ Subgroup.centralizer ({a} : Set L) = ⊥ := by
  have : Fact d.Prime := ⟨h.d_prime⟩
  let P := Subgroup.zpowers a
  have hPleN : P ≤ Subgroup.normalizer (V : Set L) := Subgroup.zpowers_le.mpr ha_N
  let act : P →* Subgroup.normalizer (V : Set L) := Subgroup.inclusion hPleN
  let _ : MulDistribMulAction P V := MulDistribMulAction.compHom (A := V) act
  have hP : IsPGroup d P :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, ha, pow_one]⟩
  let C' : Subgroup ↥V := (V ⊓ Subgroup.centralizer ({a} : Set L)).comap V.subtype
  have hfix_eq : MulAction.fixedPoints P V = (C' : Set V) := fixedPoints_zpowers_eq_comap ha_N
  have hmod := hP.card_modEq_card_fixedPoints (α := V)
  have hmodC : Nat.card V ≡ Nat.card ↥C' [MOD d] := by
    simpa [hfix_eq] using hmod
  have : Fact p.Prime := ⟨h.prime⟩
  have hVpgroup : IsPGroup p V := IsPGroup.iff_card.mpr ⟨3, hVcard⟩
  obtain ⟨w, hw⟩ := (IsPGroup.iff_card).mp (hVpgroup.to_subgroup C')
  have hw3 : w ≤ 3 := by
    have hdvd : p ^ w ∣ p ^ 3 := by
      rw [← hw, ← hVcard]
      have h : Nat.card ↥C' ∣ Nat.card (⊤ : Subgroup ↥V) := Subgroup.card_dvd_of_le le_top
      simpa [Subgroup.card_top] using h
    exact (Nat.pow_dvd_pow_iff_le_right h.prime.one_lt).mp hdvd
  rw [hVcard, hw] at hmodC
  have hdgl : ¬ d ∣ (p ^ 2 - 1) * (p ^ 2 - p) := fun hd => hCz (hd.mul_right _)
  rcases eq_zero_or_eq_three_of_pow_modEq h.prime h.d_prime h.d_ne hdgl hw3 hmodC with hw0 | hw3'
  · have hC'bot : C' = ⊥ := Subgroup.card_eq_one.mp (by rw [hw, hw0, pow_zero])
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : V) ∈ C' := by
      rw [Subgroup.mem_comap]
      exact ⟨hx.1, hx.2⟩
    rw [hC'bot] at hx'
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hx')
  · exfalso
    have hC'top : C' = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hw, hw3', hVcard]
    have hVleC : V ≤ Subgroup.centralizer ({a} : Set L) := by
      intro x hx
      have hx' : (⟨x, hx⟩ : V) ∈ C' := by
        rw [hC'top]
        exact Subgroup.mem_top _
      rw [Subgroup.mem_comap] at hx'
      exact hx'.2
    have hdC : d ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) :=
      ha ▸ orderOf_dvd_card_centralizer_of_le hVleC hzV
    exact hCz (hdC.mul_left _)

private lemma false_of_conj_pow_rank_three (h : SporOvergroupData L p d Y)
    {V : Subgroup L} (hVle : V ≤ Y) (hVsub : (V.subgroupOf Y).Normal)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hVp : ∀ v ∈ V, v ^ p = 1) (hVcard : Nat.card V = p ^ 3)
    {a b : L} {k : ℕ} (ha : orderOf a = d) (hk : b * a * b⁻¹ = a ^ k)
    (hkp : ∀ j < 3, ¬ k ≡ p ^ j [MOD d])
    {z : L} (hzV : z ∈ V)
    (hCz : ¬ d ∣ (p ^ 2 - 1) * (p ^ 2 - p) * Nat.card (Subgroup.centralizer ({z} : Set L))) :
    False := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨a', b', ha'_order, hb'_eq, ha'_Y, hb'_Y⟩ := conj_pow_core h ha hk
  have hYleV : Y ≤ Subgroup.normalizer (V : Set L) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVle).mp hVsub
  have ha'_N : a' ∈ Subgroup.normalizer (V : Set L) := hYleV ha'_Y
  have hb'_N : b' ∈ Subgroup.normalizer (V : Set L) := hYleV hb'_Y
  have hd : ¬ d ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
    intro hd
    exact hCz (hd.mul_right _)
  have hCbot := inf_centralizer_eq_bot_of_card_eq_cube h hVcard ha'_order ha'_N hzV hCz
  have hfix : ∀ v ∈ V, a' * v * a'⁻¹ = v → v = 1 := by
    intro v hv hfix_eq
    have hvC : v ∈ V ⊓ Subgroup.centralizer ({a'} : Set L) := by
      refine Subgroup.mem_inf.mpr ⟨hv, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : a' * v = v * a' := by
        have := congrArg (· * a') hfix_eq
        simpa [mul_assoc] using this
      exact h2.symm
    rw [hCbot] at hvC
    exact Subgroup.mem_bot.mp hvC
  exact false_of_conj_pow_of_card_eq_cube h.d_prime hVab hVp hVcard ha'_N hb'_N hfix
    ha'_order hd hb'_eq hkp

theorem op_eq_bot_of_data_of_conj_pow (h : SporOvergroupData L p d Y)
    (hCz : ∀ z : L, orderOf z = p →
      p ^ (Nat.card L).factorization p ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
      ¬ d ∣ (p ^ 2 - 1) * (p ^ 2 - p) * Nat.card (Subgroup.centralizer ({z} : Set L)))
    (hconj : ∃ (a b : L) (k : ℕ), orderOf a = d ∧ b * a * b⁻¹ = a ^ k ∧
      ∀ j < 3, ¬ k ≡ p ^ j [MOD d]) :
    ∀ R : Subgroup L, IsPGroup p R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥ := by
  intro R hRp hRY hRn
  by_contra hR
  obtain ⟨V, k', z, hVle, hVsub, hVab, hVp, hk', hk1, hk3, hzV, hz_order, hzdvd, hYdvd⟩ :=
    exists_elem_central_of_normal_pGroup h hRp hRY hRn hR
  have : Fact d.Prime := ⟨h.d_prime⟩
  have hdvdY : d ∣ Nat.card Y := by
    obtain ⟨D, hDsyl, hDne, hnorm⟩ := h.sylowD
    have hDY : D ≤ Y := Subgroup.le_normalizer.trans (hnorm D le_rfl hDne)
    have hdvdD : d ∣ Nat.card D := by
      have hP : IsPGroup d D := hDsyl.isPGroup
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
      have hn0 : n ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hn
        exact hDne (Subgroup.card_eq_one.mp hn)
      have : d ∣ d ^ n := dvd_pow_self d hn0
      rwa [hn]
    exact hdvdD.trans (Subgroup.card_dvd_of_le hDY)
  by_cases hk3' : k' = 3
  · have hVcard : Nat.card V = p ^ 3 := by rw [hk', hk3']
    obtain ⟨a, b, k, ha, hk, hkp⟩ := hconj
    exact false_of_conj_pow_rank_three h hVle hVsub hVab hVp hVcard ha hk hkp hzV
      (hCz z hz_order hzdvd)
  · have hk2 : k' ≤ 2 := by omega
    have hprod_dvd : (∏ i : Fin k', (p ^ k' - p ^ (i : ℕ))) ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
      interval_cases k'
      · simp only [Fin.prod_univ_one, Fin.val_zero, pow_one, pow_zero]
        have h1 : p - 1 ∣ p ^ 2 - 1 := by
          simpa using Nat.sub_dvd_pow_sub_pow p 1 2
        exact h1.trans (dvd_mul_right _ _)
      · simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_one, pow_zero]
        exact dvd_refl _
    have hdvd' : d ∣ (∏ i : Fin k', (p ^ k' - p ^ (i : ℕ))) *
        Nat.card (Subgroup.centralizer ({z} : Set L)) :=
      hdvdY.trans hYdvd
    have hdvdP2 : d ∣ (p ^ 2 - 1) * (p ^ 2 - p) * Nat.card (Subgroup.centralizer ({z} : Set L)) :=
      hdvd'.trans (Nat.mul_dvd_mul_right hprod_dvd _)
    exact hCz z hz_order hzdvd hdvdP2

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
