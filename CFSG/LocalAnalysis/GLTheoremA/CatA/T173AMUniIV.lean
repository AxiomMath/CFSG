module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMCfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMGhat
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped commutatorElement MatrixGroups

private theorem charP_two_of_card_sq {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p', hp'⟩ := CharP.exists F
  have hp'prime : p'.Prime := CharP.char_is_prime F p'
  obtain ⟨m, -, hcard⟩ := FiniteField.card F p'
  have hF' : Nat.card F = 2 ^ (2 * n) := by
    rw [hF, ← pow_mul, Nat.mul_comm]
  have hdvd : p' ∣ 2 ^ (2 * n) := by
    have h : 2 ^ (2 * n) = p' ^ (m : ℕ) := by
      rw [← hF', Nat.card_eq_fintype_card, hcard]
    rw [h]
    exact dvd_pow_self p' m.pos.ne'
  have h2 : p' ∣ 2 := hp'prime.dvd_of_dvd_pow hdvd
  have : p' = 2 := (Nat.prime_dvd_prime_iff_eq hp'prime Nat.prime_two).mp h2
  subst this
  exact hp'

private def permGL' {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d)) : GL (Fin d) F :=
  ⟨σ.permMatrix F, (σ⁻¹).permMatrix F,
    by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
    by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

@[simp] private theorem coe_permGL' {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d)) :
    ((permGL' σ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = σ.permMatrix F := rfl

private theorem permMatrix_apply' {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d))
    (i j : Fin d) : σ.permMatrix F i j = if σ i = j then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]

private theorem permMatrix_map_pow {n d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d))
    (hq0 : 2 ^ n ≠ 0) : (σ.permMatrix F).map (· ^ (2 ^ n)) = σ.permMatrix F := by
  ext i j
  rw [Matrix.map_apply, permMatrix_apply']
  by_cases h : σ i = j
  · simp [h]
  · rw [if_neg h]
    exact zero_pow hq0

private theorem swap_permGL'_mem_UniSU {n d : ℕ} {F : Type} [Field F] [CharP F 2]
    (hq0 : 2 ^ n ≠ 0) {b b' : Fin d} (hbb' : b ≠ b') :
    permGL' (Equiv.swap b b') ∈ UniSU n d F := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [coe_permGL', Matrix.det_permutation, Equiv.Perm.sign_swap hbb']
    have : ((-1 : ℤˣ) : F) = (-1 : F) := by simp
    rw [this]
    exact CharTwo.neg_eq 1
  · rw [coe_permGL', permMatrix_map_pow (Equiv.swap b b') hq0,
      Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

private theorem block_mul {d : ℕ} {F : Type} [Field F] {I : Finset (Fin d)} {g h : GL (Fin d) F}
    (hg : ∀ i j, (i ∉ I ∨ j ∉ I) →
      (g : Matrix (Fin d) (Fin d) F) i j = if i = j then 1 else 0)
    (hh : ∀ i j, (i ∉ I ∨ j ∉ I) →
      (h : Matrix (Fin d) (Fin d) F) i j = if i = j then 1 else 0) :
    ∀ i j, (i ∉ I ∨ j ∉ I) →
      ((g * h : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = if i = j then 1 else 0 := by
  intro i j hij
  rw [Units.val_mul, Matrix.mul_apply]
  by_cases hi : i ∈ I
  · have hj : j ∉ I := by rcases hij with h | h; exact absurd hi h; exact h
    rw [Finset.sum_eq_single j]
    · rw [hh j j (Or.inr hj), if_pos rfl, mul_one]
      exact hg i j (Or.inr hj)
    · intro b _ hbj
      rw [hh b j (Or.inr hj)]
      simp [hbj]
    · intro hnot
      exact absurd (Finset.mem_univ j) hnot
  · rw [Finset.sum_eq_single i]
    · rw [hg i i (Or.inl hi), if_pos rfl, one_mul]
      exact hh i j (Or.inl hi)
    · intro b _ hbi
      rw [hg i b (Or.inl hi)]
      simp [show i ≠ b from fun h => hbi h.symm]
    · intro hnot
      exact absurd (Finset.mem_univ i) hnot

private theorem block_pow {d : ℕ} {F : Type} [Field F] {I : Finset (Fin d)}
    {g : GL (Fin d) F}
    (hg : ∀ i j, (i ∉ I ∨ j ∉ I) →
      (g : Matrix (Fin d) (Fin d) F) i j = if i = j then 1 else 0) (k : ℕ) :
    ∀ i j, (i ∉ I ∨ j ∉ I) →
      ((g ^ k : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = if i = j then 1 else 0 := by
  induction k with
  | zero => intro i j _; simp [Matrix.one_apply]
  | succ k ih => intro i j hij; simpa [pow_succ] using block_mul ih hg i j hij

private theorem swap_permMatrix_block {d : ℕ} {F : Type} [Field F] {b b' : Fin d}
    {I : Finset (Fin d)} (hbI : b ∈ I) (hb'I : b' ∈ I) :
    ∀ i j, (i ∉ I ∨ j ∉ I) →
      ((permGL' (Equiv.swap b b') : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j =
        if i = j then 1 else 0 := by
  have hswap_mem : ∀ x, x ∈ I → Equiv.swap b b' x ∈ I := by
    intro x hx
    by_cases hxb : x = b
    · subst hxb; rwa [Equiv.swap_apply_left]
    · by_cases hxb' : x = b'
      · subst hxb'; rwa [Equiv.swap_apply_right]
      · rwa [Equiv.swap_apply_of_ne_of_ne hxb hxb']
  intro i j hij
  rw [coe_permGL', permMatrix_apply']
  by_cases h : i = j
  · subst h
    have hi : i ∉ I := hij.elim id id
    have hib : i ≠ b := fun hh => hi (hh ▸ hbI)
    have hib' : i ≠ b' := fun hh => hi (hh ▸ hb'I)
    rw [Equiv.swap_apply_of_ne_of_ne hib hib']
  · rw [if_neg h]
    have hsw_ne : Equiv.swap b b' i ≠ j := by
      intro hsw
      rcases hij with hi | hj
      · have hib : i ≠ b := fun hh => hi (hh ▸ hbI)
        have hib' : i ≠ b' := fun hh => hi (hh ▸ hb'I)
        rw [Equiv.swap_apply_of_ne_of_ne hib hib'] at hsw
        exact h hsw
      · by_cases hi : i ∈ I
        · have := hswap_mem i hi
          rw [hsw] at this
          exact hj this
        · have hib : i ≠ b := fun hh => hi (hh ▸ hbI)
          have hib' : i ≠ b' := fun hh => hi (hh ▸ hb'I)
          rw [Equiv.swap_apply_of_ne_of_ne hib hib'] at hsw
          exact h hsw
    rw [if_neg hsw_ne]

private theorem diagonal_comm_permMatrix_swap {d : ℕ} {F : Type} [Field F] {b b' : Fin d}
    {h : Fin d → F} (hh : h b = h b') :
    Matrix.diagonal h * (Equiv.swap b b').permMatrix F =
      (Equiv.swap b b').permMatrix F * Matrix.diagonal h := by
  have hswap : ∀ i, h (Equiv.swap b b' i) = h i := by
    intro i
    by_cases hib : i = b
    · subst hib; rw [Equiv.swap_apply_left, hh]
    · by_cases hib' : i = b'
      · subst hib'; rw [Equiv.swap_apply_right, hh]
      · rw [Equiv.swap_apply_of_ne_of_ne hib hib']
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, permMatrix_apply']
  by_cases hij : Equiv.swap b b' i = j
  · rw [if_pos hij, mul_one, one_mul]
    rw [← hij, hswap i]
  · rw [if_neg hij, mul_zero, zero_mul]

private theorem conj_pow_eq {d : ℕ} {F : Type} [Field F] (P g : GL (Fin d) F) (k : ℕ) :
    (P⁻¹ * g * P) ^ k = P⁻¹ * g ^ k * P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, pow_succ]; group

private def diagGL {d : ℕ} {F : Type} [Field F] (f : Fin d → Fˣ) : GL (Fin d) F where
  val := Matrix.diagonal fun i => (f i : F)
  inv := Matrix.diagonal fun i => ((f i)⁻¹ : F)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one,
      Matrix.diagonal_injective.eq_iff]
    funext i
    simpa using (f i).mul_inv
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one,
      Matrix.diagonal_injective.eq_iff]
    funext i
    simpa using (f i).inv_mul

@[simp] private theorem coe_diagGL {d : ℕ} {F : Type} [Field F] (f : Fin d → Fˣ) :
    ((diagGL f : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal fun i => (f i : F) := rfl

private def pairUnit {d : ℕ} {F : Type} [Field F] (i j : Fin d) (u v : Fˣ) : Fin d → Fˣ :=
  fun k => if k = i then u else if k = j then v else 1

private theorem pairUnit_self {d : ℕ} {F : Type} [Field F] {i j : Fin d} (u v : Fˣ) :
    pairUnit i j u v i = u := by simp [pairUnit]

private theorem pairUnit_other {d : ℕ} {F : Type} [Field F] {i j : Fin d} (hij : i ≠ j)
    (u v : Fˣ) : pairUnit i j u v j = v := by
  have hji : j ≠ i := fun h => hij h.symm
  simp [pairUnit, hji]

private theorem pairUnit_ne {d : ℕ} {F : Type} [Field F] {i j k : Fin d} (hki : k ≠ i)
    (hkj : k ≠ j) (u v : Fˣ) : pairUnit i j u v k = 1 := by simp [pairUnit, hki, hkj]

private theorem diagGL_mem_UniSU {n d : ℕ} {F : Type} [Field F] {f : Fin d → Fˣ}
    (hpow : ∀ i, (f i : F) ^ (2 ^ n + 1) = 1)
    (hdet : (∏ i, (f i : F)) = 1) :
    diagGL f ∈ UniSU n d F := by
  have hq0 : 2 ^ n ≠ 0 := by positivity
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [coe_diagGL, Matrix.det_diagonal]
    exact hdet
  · rw [coe_diagGL, Matrix.diagonal_map (by simp [hq0]), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_injective.eq_iff]
    funext i
    rw [← pow_succ]
    exact hpow i

private theorem prod_pairUnit {d : ℕ} {F : Type} [Field F] {i j : Fin d} (hij : i ≠ j)
    (u v : Fˣ) : (∏ k, (pairUnit i j u v k : F)) = (u : F) * (v : F) := by
  let s : Finset (Fin d) := {i, j}
  have h1 : (s.prod (fun k => (pairUnit i j u v k : F))) = (u : F) * (v : F) := by
    dsimp [s]
    rw [Finset.prod_insert (by simp [hij]), Finset.prod_singleton]
    simp [pairUnit_self, pairUnit_other hij]
  rw [← Finset.prod_subset (s₁ := s) (s₂ := Finset.univ)
    (f := fun k => (pairUnit i j u v k : F)) (Finset.subset_univ s) (fun k _ hk => ?_), h1]
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  simp [pairUnit_ne hk.1 hk.2]

private theorem pairUnit_pow_card {n d : ℕ} {F : Type} [Field F] {i j : Fin d} (hij : i ≠ j)
    {u v : Fˣ} (hu : (u : F) ^ (2 ^ n + 1) = 1) (hv : (v : F) ^ (2 ^ n + 1) = 1) :
    ∀ k, ((pairUnit i j u v k : Fˣ) : F) ^ (2 ^ n + 1) = 1 := by
  intro k
  by_cases hki : k = i
  · subst hki; simpa [pairUnit_self] using hu
  · by_cases hkj : k = j
    · subst hkj; simpa [pairUnit_other hij] using hv
    · simp [pairUnit_ne hki hkj]

private theorem exists_pair_element {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (hp : p.Prime) (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n + 1)
    (P : GL (Fin d) F) (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    {a a' : Fin d} (haa : a ≠ a') (ω : Fˣ) (hωorder : orderOf ω = p) :
    ∃ X' : GL (Fin d) F,
      X' ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) ∧ X' ^ p = 1 ∧
      ((P * X' * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        Matrix.diagonal (fun i => (pairUnit a a' ω ω⁻¹ i : F)) ∧
      MWt P X' a = (ω : F) ∧ MWt P X' a' = ((ω⁻¹ : Fˣ) : F) ∧
      X' ∉ LargeEvenScalars (Fin d) F := by
  classical
  haveI hchar : CharP F 2 := charP_two_of_card_sq hn hF
  haveI hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    { prime := Nat.prime_two, one_le := hn,
      card := by rw [hF, ← pow_mul, Nat.mul_comm n 2] }
  have hpodd : p ≠ 2 := by
    intro hp2
    have hodd : Odd (2 ^ n + 1) := by
      have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega]
        rw [pow_succ]; ring
      rw [h2]; exact ⟨2 ^ (n - 1), by ring⟩
    exact hodd.not_two_dvd_nat (hp2 ▸ hpq)
  have hωp : ω ^ p = 1 := by simpa [hωorder] using pow_orderOf_eq_one ω
  have hωF : (ω : F) ^ p = 1 := by
    simpa using congrArg (fun u : Fˣ => (u : F)) hωp
  have hωinvF : ((ω⁻¹ : Fˣ) : F) ^ p = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hωF, inv_one]
  have hωq1 : (ω : F) ^ (2 ^ n + 1) = 1 := by
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, hωF, one_pow]
  have hωinvq1 : ((ω⁻¹ : Fˣ) : F) ^ (2 ^ n + 1) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hωq1, inv_one]
  have hωne_inv : ω ≠ ω⁻¹ := by
    intro h
    have h2 : ω ^ 2 = 1 := by
      calc ω ^ 2 = ω * ω := sq ω
        _ = ω * ω⁻¹ := congrArg (fun z => ω * z) h
        _ = 1 := mul_inv_cancel ω
    have hdvd : p ∣ 2 := by
      rw [← hωorder]
      exact orderOf_dvd_iff_pow_eq_one.mpr h2
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd
    exact hpodd hp2
  let f : Fin d → Fˣ := pairUnit a a' ω ω⁻¹
  have hdet : (∏ i, (f i : F)) = 1 := by
    rw [show f = pairUnit a a' ω ω⁻¹ from rfl, prod_pairUnit haa]
    have : ((ω * ω⁻¹ : Fˣ) : F) = 1 := by rw [mul_inv_cancel, Units.val_one]
    simpa [Units.val_mul] using this
  have hD : diagGL f ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) := by
    rw [show LargeEvenSUGroup (Fin d) F (2 ^ n) = UniSU n d F from rfl]
    exact diagGL_mem_UniSU (pairUnit_pow_card haa hωq1 hωinvq1) hdet
  have hDp : (diagGL f) ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_diagGL]
    have hdiag : ∀ k : ℕ, (Matrix.diagonal (fun i => (f i : F))) ^ k =
        Matrix.diagonal (fun i => (f i : F) ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ, ih, Matrix.diagonal_mul_diagonal]
          refine congrArg Matrix.diagonal ?_
          funext i
          rw [pow_succ]
    rw [hdiag, Units.val_one, ← Matrix.diagonal_one, Matrix.diagonal_injective.eq_iff]
    funext i
    by_cases hia : i = a
    · subst hia; simpa [f, pairUnit_self] using hωF
    · by_cases hia' : i = a'
      · subst hia'; simpa [f, pairUnit_other haa] using hωinvF
      · simp [f, pairUnit_ne hia hia']
  set D : GL (Fin d) F := diagGL f with hDdef
  let X' : GL (Fin d) F := P⁻¹ * D * P
  have hPnorm : P ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) :=
    CFSG.StandardType.TableBUE.gu_subset_normalizer (d := d) (n := n) hUFD hP
  have hX'SU : X' ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) := by
    have hiff := (Subgroup.mem_normalizer_iff''.mp hPnorm) D
    exact hiff.mp hD
  have hXD : ((P * X' * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun i => (pairUnit a a' ω ω⁻¹ i : F)) := by
    have h1 : P * X' * P⁻¹ = D := by dsimp [X']; group
    rw [h1, hDdef, coe_diagGL]
  have hnotscal : X' ∉ LargeEvenScalars (Fin d) F := by
    intro hscal
    have hrange : X' ∈ (Matrix.GeneralLinearGroup.scalar (Fin d)).range := by
      rwa [← largeEvenScalars_def]
    obtain ⟨c, hc⟩ := hrange
    have hXeq : X' = Matrix.GeneralLinearGroup.scalar (Fin d) c := hc.symm
    have hcentral : P * Matrix.GeneralLinearGroup.scalar (Fin d) c * P⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin d) c := by
      calc P * Matrix.GeneralLinearGroup.scalar (Fin d) c * P⁻¹
          = Matrix.GeneralLinearGroup.scalar (Fin d) c * P * P⁻¹ := by
            rw [← Matrix.GeneralLinearGroup.scalar_commute c P]
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
            rw [mul_assoc, mul_inv_cancel, mul_one]
    have hconj : ((P * Matrix.GeneralLinearGroup.scalar (Fin d) c * P⁻¹ : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) = (c : F) • (1 : Matrix (Fin d) (Fin d) F) := by
      rw [hcentral, Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, h]
    have hdiag_eq : Matrix.diagonal (fun i => (pairUnit a a' ω ω⁻¹ i : F)) =
        (c : F) • (1 : Matrix (Fin d) (Fin d) F) := by
      rw [← hXD, hXeq, hconj]
    have h1 : (pairUnit a a' ω ω⁻¹ a : F) = (c : F) := by
      have := congrFun (congrFun hdiag_eq a) a
      simpa [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq] using this
    have h2 : (pairUnit a a' ω ω⁻¹ a' : F) = (c : F) := by
      have := congrFun (congrFun hdiag_eq a') a'
      simpa [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq] using this
    have h1' : (ω : F) = (c : F) := by simpa [f, pairUnit_self] using h1
    have h2' : ((ω⁻¹ : Fˣ) : F) = (c : F) := by
      simpa [f, pairUnit_other haa] using h2
    exact hωne_inv (Units.ext (h1'.trans h2'.symm))
  have hwta : MWt P X' a = (ω : F) := by
    change ((P * X' * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) a a = (ω : F)
    rw [hXD, Matrix.diagonal_apply_eq]
    simp [f, pairUnit_self]
  have hwta' : MWt P X' a' = ((ω⁻¹ : Fˣ) : F) := by
    change ((P * X' * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) a' a' = ((ω⁻¹ : Fˣ) : F)
    rw [hXD, Matrix.diagonal_apply_eq]
    simp [f, pairUnit_other haa]
  exact ⟨X', hX'SU, by dsimp [X']; rw [conj_pow_eq P D p, hDp]; group, hXD, hwta, hwta', hnotscal⟩

private theorem conj_mem_scalars {d : ℕ} {F : Type} [Field F] (A : GL (Fin d) F)
    {z : GL (Fin d) F} (hz : z ∈ LargeEvenScalars (Fin d) F) :
    A * z * A⁻¹ ∈ LargeEvenScalars (Fin d) F := by
  rw [largeEvenScalars_def] at hz ⊢
  obtain ⟨c, rfl⟩ := hz
  refine ⟨c, ?_⟩
  rw [← Matrix.GeneralLinearGroup.scalar_commute c A]
  group

private theorem ker_psi_le_scalars {n d : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω}
    {F : Type} [Field F]
    {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))}
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S} (hψ : GLifts θ ψ)
    {u : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n))} (hu : ψ u = 1) :
    (u : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
  have h1 : LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)) u = 1 := by
    simpa [hu] using (hψ u).symm
  have h2 : u ∈ (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n))).ker := h1
  rw [QuotientGroup.ker_mk'] at h2
  exact Subgroup.mem_subgroupOf.mp h2

private theorem diagonal_pow {d : ℕ} {F : Type} [Field F] (v : Fin d → F) (k : ℕ) :
    (Matrix.diagonal v) ^ k = Matrix.diagonal (fun i => v i ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, Matrix.diagonal_mul_diagonal]
      refine congrArg Matrix.diagonal ?_
      funext i
      rw [pow_succ]

private theorem mem_GU_of_diag_pow_scalar {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hF : Nat.card F = (2 ^ n) ^ 2) (hd : 1 ≤ d)
    {P A : GL (Fin d) F} (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) {Dfun : Fin d → F}
    (hdiag : ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.diagonal Dfun)
    (hAp : A ^ p ∈ LargeEvenScalars (Fin d) F) :
    A ∈ MGU n d F := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  set M : GL (Fin d) F := P * A * P⁻¹ with hM
  have hMp : M ^ p ∈ LargeEvenScalars (Fin d) F := by
    have h1 : M ^ p = P * A ^ p * P⁻¹ := by
      dsimp [M]
      rw [show P * A * P⁻¹ = (P⁻¹)⁻¹ * A * P⁻¹ from by group, conj_pow_eq]
      group
    rw [h1]
    exact conj_mem_scalars P hAp
  rw [largeEvenScalars_def] at hMp
  obtain ⟨lam, hlam⟩ := hMp
  have hMmat : ((M : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.diagonal Dfun := hdiag
  have hpow_eq : (Matrix.diagonal (fun i => Dfun i ^ p)) =
      Matrix.diagonal (fun _ => (lam : F)) := by
    have h1 : ((M ^ p : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        Matrix.scalar (Fin d) (lam : F) := by
      rw [← hlam, Matrix.GeneralLinearGroup.coe_scalar]
    calc Matrix.diagonal (fun i => Dfun i ^ p)
        = ((M : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) ^ p := by
          rw [hMmat, diagonal_pow]
      _ = ((M ^ p : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
          rw [Units.val_pow_eq_pow_val]
      _ = Matrix.scalar (Fin d) (lam : F) := h1
      _ = Matrix.diagonal (fun _ => (lam : F)) := Matrix.scalar_apply _
  have hDpow : ∀ i, Dfun i ^ p = (lam : F) := by
    intro i
    exact congrFun (Matrix.diagonal_injective.eq_iff.mp hpow_eq) i
  have hDne : ∀ i, Dfun i ≠ 0 := by
    intro i hi
    have hdetM : ((M : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det ≠ 0 := M.det_ne_zero
    apply hdetM
    rw [hMmat, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  let i0 : Fin d := ⟨0, by omega⟩
  have hD0ne : Dfun i0 ≠ 0 := hDne i0
  have hD0pow : Dfun i0 ^ p = (lam : F) := hDpow i0
  have hpowq1 : ∀ i, Dfun i ^ (2 ^ n + 1) = Dfun i0 ^ (2 ^ n + 1) := by
    intro i
    have hx : (Dfun i * (Dfun i0)⁻¹) ^ p = 1 := by
      rw [mul_pow, inv_pow, hDpow i, hD0pow]
      exact mul_inv_cancel₀ (by simpa using lam.ne_zero)
    have hxq : (Dfun i * (Dfun i0)⁻¹) ^ (2 ^ n + 1) = 1 := by
      obtain ⟨m, hm⟩ := hpq
      rw [hm, pow_mul, hx, one_pow]
    have hmul : Dfun i ^ (2 ^ n + 1) * ((Dfun i0 ^ (2 ^ n + 1)))⁻¹ = 1 := by
      rw [← inv_pow, ← mul_pow]
      exact hxq
    have hbne : Dfun i0 ^ (2 ^ n + 1) ≠ 0 := pow_ne_zero _ hD0ne
    have h := congrArg (fun z => z * Dfun i0 ^ (2 ^ n + 1)) hmul
    rw [one_mul, mul_assoc, inv_mul_cancel₀ hbne, mul_one] at h
    exact h
  have hMU : M ∈ LargeEvenGUSet (Fin d) F (2 ^ n) := by
    refine ⟨Dfun i0 ^ (2 ^ n + 1), pow_ne_zero _ hD0ne, ?_, ?_⟩
    · have hcard : Dfun i0 ^ (2 ^ n * 2 ^ n) = Dfun i0 := by
        have h2 : Fintype.card F = (2 ^ n) ^ 2 := by
          rw [← Nat.card_eq_fintype_card, hF]
        rw [show 2 ^ n * 2 ^ n = (2 ^ n) ^ 2 by ring, ← h2]
        exact FiniteField.pow_card (Dfun i0)
      calc (Dfun i0 ^ (2 ^ n + 1)) ^ 2 ^ n
          = Dfun i0 ^ ((2 ^ n + 1) * 2 ^ n) := by rw [pow_mul]
        _ = Dfun i0 ^ (2 ^ n * 2 ^ n + 2 ^ n) := by rw [add_mul, one_mul]
        _ = Dfun i0 ^ (2 ^ n * 2 ^ n) * Dfun i0 ^ (2 ^ n) := by rw [pow_add]
        _ = Dfun i0 * Dfun i0 ^ (2 ^ n) := by rw [hcard]
        _ = Dfun i0 ^ (2 ^ n) * Dfun i0 := mul_comm _ _
        _ = Dfun i0 ^ (2 ^ n + 1) := by rw [pow_succ]
    · rw [hMmat, Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal,
        Matrix.diagonal_injective.eq_iff]
      funext i
      rw [← pow_succ]
      exact hpowq1 i
  have hMMGU : M ∈ MGU n d F := Subgroup.subset_closure hMU
  have hPMGU : P ∈ MGU n d F := Subgroup.subset_closure hP
  have hPinvMGU : P⁻¹ ∈ MGU n d F := (MGU n d F).inv_mem hPMGU
  have hAeq : A = P⁻¹ * M * P := by dsimp [M]; group
  rw [hAeq]
  exact (MGU n d F).mul_mem ((MGU n d F).mul_mem hPinvMGU hMMGU) hPMGU

private theorem ginduced_of_gacts {n d : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω}
    {F : Type} [Field F]
    {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))}
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S} (hψ : GLifts θ ψ)
    (hψS : Function.Surjective ψ) {b : Ω} {A : GL (Fin d) F}
    (hAn : A ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)))
    (hActs : GActs ψ b A) :
    GInduced θ b A := by
  classical
  let U := LargeEvenSUGroup (Fin d) F (2 ^ n)
  let Z : Subgroup ↥U := (LargeEvenScalars (Fin d) F).subgroupOf U
  have hmem : ∀ u : ↥U, A * (u : GL (Fin d) F) * A⁻¹ ∈ U := by
    intro u
    exact ((Subgroup.mem_normalizer_iff.mp hAn) (u : GL (Fin d) F)).mp u.2
  let f : ↥U →* ↥U :=
    { toFun := fun u => ⟨A * (u : GL (Fin d) F) * A⁻¹, hmem u⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun u v => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hAninv : A⁻¹ ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)) := Subgroup.inv_mem _ hAn
  have hmeminv : ∀ u : ↥U, A⁻¹ * (u : GL (Fin d) F) * (A⁻¹)⁻¹ ∈ U := by
    intro u
    exact ((Subgroup.mem_normalizer_iff.mp hAninv) (u : GL (Fin d) F)).mp u.2
  let finv : ↥U →* ↥U :=
    { toFun := fun u => ⟨A⁻¹ * (u : GL (Fin d) F) * (A⁻¹)⁻¹, hmeminv u⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun u v => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hleftU : Function.LeftInverse finv f := by
    intro u
    apply Subtype.ext
    simp only [f, finv, MonoidHom.coe_mk, OneHom.coe_mk]
    group
  have hrightU : Function.RightInverse finv f := by
    intro u
    apply Subtype.ext
    simp only [f, finv, MonoidHom.coe_mk, OneHom.coe_mk]
    group
  have hZmap : Z ≤ Z.comap f := by
    intro z hz
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_subgroupOf.mpr
      (conj_mem_scalars A (Subgroup.mem_subgroupOf.mp hz))
  have hZmapinv : Z ≤ Z.comap finv := by
    intro z hz
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_subgroupOf.mpr
      (conj_mem_scalars A⁻¹ (Subgroup.mem_subgroupOf.mp hz))
  let φhom : LargeEvenProj U →* LargeEvenProj U :=
    QuotientGroup.map (N := Z) (M := Z) f hZmap
  let φinv : LargeEvenProj U →* LargeEvenProj U :=
    QuotientGroup.map (N := Z) (M := Z) finv hZmapinv
  have hφleft : Function.LeftInverse φinv φhom := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective Z x
    rw [show QuotientGroup.mk' Z u = (↑u : LargeEvenProj U) from QuotientGroup.mk'_apply (N := Z) u]
    change φinv (φhom (↑u)) = (↑u : LargeEvenProj U)
    dsimp only [φhom, φinv]
    rw [QuotientGroup.map_mk (N := Z) (M := Z) f hZmap u,
      QuotientGroup.map_mk (N := Z) (M := Z) finv hZmapinv (f u), hleftU u]
  have hφright : Function.RightInverse φinv φhom := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective Z x
    rw [show QuotientGroup.mk' Z u = (↑u : LargeEvenProj U) from QuotientGroup.mk'_apply (N := Z) u]
    change φhom (φinv (↑u)) = (↑u : LargeEvenProj U)
    dsimp only [φhom, φinv]
    rw [QuotientGroup.map_mk (N := Z) (M := Z) finv hZmapinv u,
      QuotientGroup.map_mk (N := Z) (M := Z) f hZmap (finv u), hrightU u]
  have hbij : Function.Bijective φhom :=
    ⟨fun x y h => by rw [← hφleft x, ← hφleft y, h],
     fun y => ⟨φinv y, hφright y⟩⟩
  let φ : MulAut (LargeEvenProj U) := MulEquiv.ofBijective φhom hbij
  have hφu : ∀ u : ↥U, φ (LargeEvenProjMk U u) =
      LargeEvenProjMk U ⟨A * (u : GL (Fin d) F) * A⁻¹, hmem u⟩ := by
    intro u
    change φhom (QuotientGroup.mk' Z u) =
      QuotientGroup.mk' Z ⟨A * (u : GL (Fin d) F) * A⁻¹, hmem u⟩
    rw [show QuotientGroup.mk' Z u = (↑u : LargeEvenProj U) from QuotientGroup.mk'_apply (N := Z) u]
    dsimp only [φhom]
    rw [QuotientGroup.map_mk (N := Z) (M := Z) f hZmap u]
    rfl
  refine ⟨φ, ?_, ?_⟩
  · intro u u' hrel
    have hu' : (⟨A * (u : GL (Fin d) F) * A⁻¹, hmem u⟩ : ↥U) = u' := Subtype.ext hrel.symm
    rw [hφu u, hu']
  · intro l l' hrel
    obtain ⟨u, hu⟩ := hψS l
    have hAu : (ψ ⟨A * (u : GL (Fin d) F) * A⁻¹, hmem u⟩ : ↥S) = l' := by
      apply Subtype.ext
      rw [hrel, ← hu]
      exact hActs u ⟨A * (u : GL (Fin d) F) * A⁻¹, hmem u⟩ rfl
    have hθl : θ (QuotientGroup.mk l) = LargeEvenProjMk U u := by
      rw [← hu]
      exact hψ u
    have hθl' : θ (QuotientGroup.mk l') =
        LargeEvenProjMk U ⟨A * (u : GL (Fin d) F) * A⁻¹, hmem u⟩ := by
      rw [← hAu]
      exact hψ ⟨A * (u : GL (Fin d) F) * A⁻¹, hmem u⟩
    rw [hθl, hθl', hφu u]

private theorem conj_eq_of_diag {d : ℕ} {F : Type} [Field F] (P A X : GL (Fin d) F)
    (hA : ∃ DA : Fin d → F, ((P * A * P⁻¹ : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = Matrix.diagonal DA)
    (hX : ∃ DX : Fin d → F, ((P * X * P⁻¹ : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = Matrix.diagonal DX) :
    A * X * A⁻¹ = X := by
  obtain ⟨DA, hA⟩ := hA
  obtain ⟨DX, hX⟩ := hX
  have hcomm_mat : ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
      ((P * X * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      ((P * X * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
    rw [hA, hX, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_injective.eq_iff]
    funext i
    exact mul_comm _ _
  have hcomm : (P * A * P⁻¹) * (P * X * P⁻¹) = (P * X * P⁻¹) * (P * A * P⁻¹) := by
    apply Units.ext
    simpa only [Units.val_mul] using hcomm_mat
  calc A * X * A⁻¹
      = P⁻¹ * (P * A * P⁻¹) * (P * X * P⁻¹) * (P * A * P⁻¹)⁻¹ * P := by group
    _ = P⁻¹ * ((P * A * P⁻¹) * (P * X * P⁻¹)) * (P * A * P⁻¹)⁻¹ * P := by group
    _ = P⁻¹ * ((P * X * P⁻¹) * (P * A * P⁻¹)) * (P * A * P⁻¹)⁻¹ * P := by rw [hcomm]
    _ = P⁻¹ * (P * X * P⁻¹) * P := by group
    _ = X := by group

private theorem pair_element_props {p n d : ℕ} {Ω : Type} [Group Ω]
    {S B : Subgroup Ω} {F : Type} [Field F]
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S}
    {P : GL (Fin d) F}
    (hB : ∀ b ∈ B, GDiagAct p ψ P b)
    (X' : GL (Fin d) F) (hX'SU : X' ∈ LargeEvenSUGroup (Fin d) F (2 ^ n))
    (hX'p : X' ^ p = 1)
    (hX'diag : ∃ DX : Fin d → F, ((P * X' * P⁻¹ : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = Matrix.diagonal DX) :
    (ψ ⟨X', hX'SU⟩ : Ω) ^ p = 1 ∧
      ∀ b ∈ B, b * (ψ ⟨X', hX'SU⟩ : Ω) = (ψ ⟨X', hX'SU⟩ : Ω) * b := by
  constructor
  · have h1 : (ψ ⟨X', hX'SU⟩ : ↥S) ^ p = 1 := by
      rw [← map_pow]
      have hu : (⟨X', hX'SU⟩ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n))) ^ p = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hX'p
      rw [hu, map_one]
    exact (congrArg (fun z : ↥S => (z : Ω)) h1).trans (by rw [Subgroup.coe_one])
  · intro b hb
    obtain ⟨A, hActs, -, hAdiag⟩ := hB b hb
    have hAX : A * X' * A⁻¹ = X' := conj_eq_of_diag P A X' hAdiag hX'diag
    have hmem : ((⟨X', hX'SU⟩ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n))) : GL (Fin d) F) =
        A * ((⟨X', hX'SU⟩ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n))) : GL (Fin d) F) * A⁻¹ := by
      simpa using hAX.symm
    have h := hActs ⟨X', hX'SU⟩ ⟨X', hX'SU⟩ hmem
    calc b * (ψ ⟨X', hX'SU⟩ : Ω)
        = b * (b⁻¹ * (ψ ⟨X', hX'SU⟩ : Ω) * b) := congrArg (fun z => b * z) h
      _ = (ψ ⟨X', hX'SU⟩ : Ω) * b := by group

private theorem pair_element_not_mem {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B N D K : Subgroup Ω} {x : Ω} (hcfg : MCfg p S B N D K x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hpq : p ∣ 2 ^ n + 1)
    {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))}
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S} (hψ : GLifts θ ψ)
    (hψS : Function.Surjective ψ)
    (hcen : ∀ A : GL (Fin d) F, (∀ u ∈ LargeEvenSUGroup (Fin d) F (2 ^ n),
      ⁅A, u⁆ ∈ LargeEvenScalars (Fin d) F) → A ∈ LargeEvenScalars (Fin d) F)
    {P : GL (Fin d) F} (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    (hB : ∀ b ∈ B, GDiagAct p ψ P b) {Gh : Subgroup (GL (Fin d) F)}
    (hGh : ∀ A, A ∈ Gh ↔ A ∈ MGU n d F ∧ ∃ b ∈ B, GInduced θ b A)
    {a a' : Fin d} (hpair : ∀ A ∈ Gh, MWt P A a = MWt P A a')
    (X' : GL (Fin d) F) (hX'SU : X' ∈ LargeEvenSUGroup (Fin d) F (2 ^ n))
    (DX : Fin d → F) (ω : Fˣ) (hDX : ((P * X' * P⁻¹ : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = Matrix.diagonal DX)
    (hDXa : DX a = (ω : F)) (hDXa' : DX a' = ((ω⁻¹ : Fˣ) : F)) (hωne : ω ≠ ω⁻¹) :
    (ψ ⟨X', hX'SU⟩ : Ω) ∉ B := by
  classical
  haveI hchar : CharP F 2 := charP_two_of_card_sq hn hF
  haveI hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    { prime := Nat.prime_two, one_le := hn,
      card := by rw [hF, ← pow_mul, Nat.mul_comm n 2] }
  let U := LargeEvenSUGroup (Fin d) F (2 ^ n)
  let cS : ↥S := ψ ⟨X', hX'SU⟩
  let c : Ω := cS
  intro hcB
  obtain ⟨Ac, hActs, hAcp, hAcdiag⟩ := hB c hcB
  obtain ⟨Dc, hDc⟩ := hAcdiag
  have hAcMGU : Ac ∈ MGU n d F :=
    mem_GU_of_diag_pow_scalar hcfg.prime hpq hF (by omega) hP hDc hAcp
  have hMGUN : MGU n d F ≤ Subgroup.normalizer (U : Set (GL (Fin d) F)) := by
    rw [MGU]
    exact (Subgroup.closure_le _).mpr fun A hA =>
      CFSG.StandardType.TableBUE.gu_subset_normalizer (d := d) (n := n) hUFD hA
  have hAcN : Ac ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)) := hMGUN hAcMGU
  have hG : GInduced θ c Ac := ginduced_of_gacts hψ hψS hAcN hActs
  have hAcGh : Ac ∈ Gh := (hGh Ac).mpr ⟨hAcMGU, c, hcB, hG⟩
  have hweq : MWt P Ac a = MWt P Ac a' := hpair Ac hAcGh
  have hZscal : X' * Ac ∈ LargeEvenScalars (Fin d) F := by
    apply hcen
    intro u hu
    have hw : Ac * (u : GL (Fin d) F) * Ac⁻¹ ∈ U :=
      ((Subgroup.mem_normalizer_iff.mp hAcN) (u : GL (Fin d) F)).mp hu
    have hmemZ : X' * Ac * (u : GL (Fin d) F) * (X' * Ac)⁻¹ * (u : GL (Fin d) F)⁻¹ ∈ U := by
      have h1 : X' * (Ac * (u : GL (Fin d) F) * Ac⁻¹) * X'⁻¹ ∈ U :=
        U.mul_mem (U.mul_mem hX'SU hw) (U.inv_mem hX'SU)
      have h2 : X' * Ac * (u : GL (Fin d) F) * (X' * Ac)⁻¹ * (u : GL (Fin d) F)⁻¹ =
          X' * (Ac * (u : GL (Fin d) F) * Ac⁻¹) * X'⁻¹ * (u : GL (Fin d) F)⁻¹ := by group
      rw [h2]
      exact U.mul_mem h1 (U.inv_mem hu)
    have hψ1 : ψ ⟨X' * Ac * (u : GL (Fin d) F) * (X' * Ac)⁻¹ *
        (u : GL (Fin d) F)⁻¹, hmemZ⟩ = 1 := by
      have hw_eq : (⟨X' * Ac * (u : GL (Fin d) F) * (X' * Ac)⁻¹ *
          (u : GL (Fin d) F)⁻¹, hmemZ⟩ : ↥U) =
          ⟨X', hX'SU⟩ * ⟨Ac * (u : GL (Fin d) F) * Ac⁻¹, hw⟩ *
            ⟨X', hX'SU⟩⁻¹ * ⟨u, hu⟩⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hAc' : ψ ⟨Ac * (u : GL (Fin d) F) * Ac⁻¹, hw⟩ = cS⁻¹ * ψ ⟨u, hu⟩ * cS := by
        apply Subtype.ext
        simpa [cS, c] using hActs ⟨u, hu⟩ ⟨Ac * (u : GL (Fin d) F) * Ac⁻¹, hw⟩ rfl
      rw [hw_eq, map_mul, map_mul, map_mul, map_inv, map_inv, hAc']
      change cS * (cS⁻¹ * ψ ⟨u, hu⟩ * cS) * cS⁻¹ * (ψ ⟨u, hu⟩)⁻¹ = 1
      group
    have := ker_psi_le_scalars hψ hψ1
    simpa [commutatorElement_def] using this
  obtain ⟨lam, hlam⟩ := hZscal
  have hAcmat : ((P * Ac * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal Dc := hDc
  have hZfact : (P * (X' * Ac) * P⁻¹ : GL (Fin d) F) =
      (P * X' * P⁻¹) * (P * Ac * P⁻¹) := by group
  have hprodmat : ((P * (X' * Ac) * P⁻¹ : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = Matrix.diagonal (fun i => DX i * Dc i) := by
    rw [hZfact, Units.val_mul, hDX, hAcmat, Matrix.diagonal_mul_diagonal]
  have hZmat : ((P * (X' * Ac) * P⁻¹ : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = Matrix.diagonal (fun _ => (lam : F)) := by
    have hcentral : P * (X' * Ac) * P⁻¹ = X' * Ac := by
      rw [← hlam]
      calc P * Matrix.GeneralLinearGroup.scalar (Fin d) lam * P⁻¹
          = Matrix.GeneralLinearGroup.scalar (Fin d) lam * P * P⁻¹ := by
            rw [← Matrix.GeneralLinearGroup.scalar_commute lam P]
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) lam := by
            rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [hcentral, ← hlam, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hpoint : ∀ i, DX i * Dc i = (lam : F) := by
    intro i
    exact congrFun (Matrix.diagonal_injective.eq_iff.mp (hprodmat.symm.trans hZmat)) i
  have hAcwta : MWt P Ac a = Dc a := by
    change ((P * Ac * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) a a = Dc a
    rw [hAcmat, Matrix.diagonal_apply_eq]
  have hAcwta' : MWt P Ac a' = Dc a' := by
    change ((P * Ac * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) a' a' = Dc a'
    rw [hAcmat, Matrix.diagonal_apply_eq]
  have hDa : Dc a = Dc a' := by rw [← hAcwta, ← hAcwta']; exact hweq
  have hDcane : Dc a ≠ 0 := by
    intro h0
    have hdet : ((P * Ac * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det ≠ 0 :=
      (P * Ac * P⁻¹).det_ne_zero
    apply hdet
    rw [hAcmat, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ a) h0
  have h1 : (ω : F) * Dc a = (lam : F) := by rw [← hDXa]; exact hpoint a
  have h2 : ((ω⁻¹ : Fˣ) : F) * Dc a' = (lam : F) := by rw [← hDXa']; exact hpoint a'
  rw [← hDa] at h2
  have h3 : (ω : F) * Dc a = ((ω⁻¹ : Fˣ) : F) * Dc a := h1.trans h2.symm
  exact hωne (Units.ext (mul_right_cancel₀ hDcane h3))

private theorem pair_element_sup {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B N D K : Subgroup Ω} {x : Ω} (hcfg : MCfg p S B N D K x)
    {F : Type} [Field F]
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S}
    {P : GL (Fin d) F}
    (hB : ∀ b ∈ B, GDiagAct p ψ P b)
    (X' : GL (Fin d) F) (hX'SU : X' ∈ LargeEvenSUGroup (Fin d) F (2 ^ n))
    (hX'p : X' ^ p = 1)
    (hX'diag : ∃ DX : Fin d → F, ((P * X' * P⁻¹ : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = Matrix.diagonal DX)
    (hcB : (ψ ⟨X', hX'SU⟩ : Ω) ∉ B) :
    let B' : Subgroup Ω := B ⊔ Subgroup.zpowers (ψ ⟨X', hX'SU⟩ : Ω)
    IsElemAbelian p B' ∧ B ≤ B' ∧ B ≠ B' ∧ B' ≤ S ⊔ B := by
  classical
  obtain ⟨hcp, hcomm⟩ := pair_element_props hB X' hX'SU hX'p hX'diag
  let c : Ω := (ψ ⟨X', hX'SU⟩ : Ω)
  let B' : Subgroup Ω := B ⊔ Subgroup.zpowers c
  have hB'elem : IsElemAbelian p B' := by
    refine IsElemAbelian.sup_of_commute hcfg.elem (isElemAbelian_zpowers hcp) ?_
    intro a ha b' hb'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    have hcommac : Commute a c := hcomm a ha
    exact (hcommac.zpow_right n).eq
  have hBle : B ≤ B' := le_sup_left
  have hcS : c ∈ S := (ψ ⟨X', hX'SU⟩).2
  have hSle : Subgroup.zpowers c ≤ S ⊔ B := Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hcS)
  have hB'le : B' ≤ S ⊔ B := sup_le le_sup_right hSle
  have hne : B ≠ B' := by
    intro heq
    apply hcB
    have hcB' : c ∈ B' := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    rwa [← heq] at hcB'
  exact ⟨hB'elem, hBle, hne, hB'le⟩

private theorem diag_conj_of_block {d : ℕ} {F : Type} [Field F] {I : Finset (Fin d)}
    {D g : GL (Fin d) F} {Dfun : Fin d → F}
    (hD : ((D : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.diagonal Dfun)
    (hDunit : ∀ i, i ∈ I → Dfun i = 1)
    (hg : ∀ i j, (i ∉ I ∨ j ∉ I) →
      ((g : Matrix (Fin d) (Fin d) F) i j = if i = j then 1 else 0)) :
    D * g * D⁻¹ = g := by
  have hDg : D * g = g * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : i = j
    · subst hij; exact mul_comm _ _
    · by_cases hg0 : ((g : Matrix (Fin d) (Fin d) F) i j) = 0
      · rw [hg0, mul_zero, zero_mul]
      · have hiI : i ∈ I := by
          by_contra hi
          exact hg0 (by rw [hg i j (Or.inl hi), if_neg hij])
        have hjI : j ∈ I := by
          by_contra hj
          exact hg0 (by rw [hg i j (Or.inr hj), if_neg hij])
        rw [hDunit i hiI, hDunit j hjI, one_mul, mul_one]
  calc D * g * D⁻¹ = g * D * D⁻¹ := by rw [hDg]
    _ = g := by group

private theorem diag_conj_mem_block {n d : ℕ} {F : Type} [Field F] {I : Finset (Fin d)}
    {D g : GL (Fin d) F} {Dfun : Fin d → F}
    (hD : ((D : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.diagonal Dfun)
    (hDne : ∀ i, Dfun i ≠ 0)
    (hDN : D ∈ Subgroup.normalizer (UniSU n d F : Set (GL (Fin d) F)))
    (hg : g ∈ UniBlockSet n d F I) :
    D * g * D⁻¹ ∈ UniBlockSet n d F I := by
  have hDinv : ((D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun i => (Dfun i)⁻¹) := by
    rw [Matrix.GeneralLinearGroup.coe_inv]
    apply Matrix.inv_eq_right_inv
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun i => mul_inv_cancel₀ (hDne i))
  refine ⟨?_, ?_⟩
  · exact ((Subgroup.mem_normalizer_iff.mp hDN) g).mp hg.1
  · intro i j hij
    rw [Units.val_mul, Units.val_mul, hD, hDinv, Matrix.mul_assoc, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    have hgij : ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j =
        if i = j then 1 else 0 := hg.2 i j hij
    rw [hgij]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, one_mul, mul_inv_cancel₀ (hDne i)]
    · rw [if_neg h, zero_mul, mul_zero]

private theorem B_le_normalizer_K {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B N D K : Subgroup Ω} {x : Ω} (hcfg : MCfg p S B N D K x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hpq : p ∣ 2 ^ n + 1)
    {P : GL (Fin d) F} (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    (I : Finset (Fin d))
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S}
    (hK : ∀ k : Ω, k ∈ K ↔ ∃ u : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)),
      (P * (u : GL (Fin d) F) * P⁻¹) ∈ UniBlockSet n d F I ∧ (ψ u : Ω) = k)
    (hB : ∀ b ∈ B, GDiagAct p ψ P b) :
    B ≤ Subgroup.normalizer (K : Set Ω) := by
  classical
  haveI hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    { prime := Nat.prime_two, one_le := hn,
      card := by rw [hF, ← pow_mul, Nat.mul_comm n 2] }
  let U := LargeEvenSUGroup (Fin d) F (2 ^ n)
  have hPN : P ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)) :=
    CFSG.StandardType.TableBUE.gu_subset_normalizer (d := d) (n := n) hUFD hP
  have hMGUN : MGU n d F ≤ Subgroup.normalizer (U : Set (GL (Fin d) F)) := by
    rw [MGU]
    exact (Subgroup.closure_le _).mpr fun A hA =>
      CFSG.StandardType.TableBUE.gu_subset_normalizer (d := d) (n := n) hUFD hA
  have hstep : ∀ c ∈ B, ∀ u : ↥U, (P * (u : GL (Fin d) F) * P⁻¹) ∈ UniBlockSet n d F I →
      c⁻¹ * (ψ u : Ω) * c ∈ K := by
    intro c hc u huBlk
    obtain ⟨A, hActs, hAp, hAdiag⟩ := hB c hc
    obtain ⟨Dfun, hD⟩ := hAdiag
    have hAMGU : A ∈ MGU n d F :=
      mem_GU_of_diag_pow_scalar hcfg.prime hpq hF (by omega) hP hD hAp
    have hAN : A ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)) := hMGUN hAMGU
    let D : GL (Fin d) F := P * A * P⁻¹
    have hDN : D ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)) :=
      (Subgroup.normalizer (U : Set (GL (Fin d) F))).mul_mem
        ((Subgroup.normalizer (U : Set (GL (Fin d) F))).mul_mem hPN hAN)
        ((Subgroup.normalizer (U : Set (GL (Fin d) F))).inv_mem hPN)
    have hDne : ∀ i, Dfun i ≠ 0 := by
      intro i hi
      have hdet : ((D : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det ≠ 0 := D.det_ne_zero
      apply hdet
      rw [show ((D : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.diagonal Dfun from hD,
        Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hblock : D * (P * (u : GL (Fin d) F) * P⁻¹) * D⁻¹ ∈ UniBlockSet n d F I :=
      diag_conj_mem_block hD hDne hDN huBlk
    have hsame : P * (A * (u : GL (Fin d) F) * A⁻¹) * P⁻¹ =
        D * (P * (u : GL (Fin d) F) * P⁻¹) * D⁻¹ := by dsimp [D]; group
    have hAu : A * (u : GL (Fin d) F) * A⁻¹ ∈ U :=
      ((Subgroup.mem_normalizer_iff.mp hAN) (u : GL (Fin d) F)).mp u.2
    have hKmem : (ψ ⟨A * (u : GL (Fin d) F) * A⁻¹, hAu⟩ : Ω) ∈ K :=
      (hK _).mpr ⟨⟨A * (u : GL (Fin d) F) * A⁻¹, hAu⟩, by rwa [hsame], rfl⟩
    have hg := hActs u ⟨A * (u : GL (Fin d) F) * A⁻¹, hAu⟩ rfl
    rw [← hg]
    exact hKmem
  intro b hb
  rw [Subgroup.mem_normalizer_iff'']
  intro k
  constructor
  · intro hkK
    obtain ⟨u, huBlk, rfl⟩ := (hK k).mp hkK
    exact hstep b hb u huBlk
  · intro hkK
    obtain ⟨u, huBlk, hu⟩ := (hK _).mp hkK
    have hb' : b⁻¹ ∈ B := B.inv_mem hb
    have hmem := hstep b⁻¹ hb' u huBlk
    have hk_eq : k = b * (ψ u : Ω) * b⁻¹ := by
      calc k = b * (b⁻¹ * k * b) * b⁻¹ := by group
        _ = b * (ψ u : Ω) * b⁻¹ := by rw [← hu]
    rw [hk_eq]
    simpa [inv_inv] using hmem

private theorem pair_element_mem_K {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B N D K : Subgroup Ω} {x : Ω} (hcfg : MCfg p S B N D K x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    {P : GL (Fin d) F} (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    (I : Finset (Fin d))
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S}
    (hK : ∀ k : Ω, k ∈ K ↔ ∃ u : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)),
      (P * (u : GL (Fin d) F) * P⁻¹) ∈ UniBlockSet n d F I ∧ (ψ u : Ω) = k)
    (X' : GL (Fin d) F) (hX'SU : X' ∈ LargeEvenSUGroup (Fin d) F (2 ^ n))
    {a a' : Fin d} (haI : a ∈ I) (ha'I : a' ∈ I) (ω : Fˣ)
    (hDX : ((P * X' * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun i => (pairUnit a a' ω ω⁻¹ i : F))) :
    (ψ ⟨X', hX'SU⟩ : Ω) ∈ K := by
  haveI hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    { prime := Nat.prime_two, one_le := hn,
      card := by rw [hF, ← pow_mul, Nat.mul_comm n 2] }
  have hPnorm : P ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) :=
    CFSG.StandardType.TableBUE.gu_subset_normalizer (d := d) (n := n) hUFD hP
  have hX'N : P * X' * P⁻¹ ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) :=
    ((Subgroup.mem_normalizer_iff.mp hPnorm) X').mp hX'SU
  have hX'block : (P * X' * P⁻¹) ∈ UniBlockSet n d F I := by
    refine ⟨hX'N, ?_⟩
    intro i j hij
    rw [hDX, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      have hi : i ∉ I := hij.elim id id
      have hia : i ≠ a := fun hh => hi (hh ▸ haI)
      have hia' : i ≠ a' := fun hh => hi (hh ▸ ha'I)
      simp [pairUnit, hia, hia']
    · rw [if_neg h, if_neg h]
  exact (hK _).mpr ⟨⟨X', hX'SU⟩, hX'block, rfl⟩

private theorem pair_element_centralizes_K {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B N D K : Subgroup Ω} {x : Ω} (hcfg : MCfg p S B N D K x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    {P : GL (Fin d) F} (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    (I : Finset (Fin d))
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S}
    (hK : ∀ k : Ω, k ∈ K ↔ ∃ u : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)),
      (P * (u : GL (Fin d) F) * P⁻¹) ∈ UniBlockSet n d F I ∧ (ψ u : Ω) = k)
    (X' : GL (Fin d) F) (hX'SU : X' ∈ LargeEvenSUGroup (Fin d) F (2 ^ n))
    {a a' : Fin d} (haI : a ∉ I) (ha'I : a' ∉ I) (ω : Fˣ)
    (hDX : ((P * X' * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun i => (pairUnit a a' ω ω⁻¹ i : F))) :
    (ψ ⟨X', hX'SU⟩ : Ω) ∈ Subgroup.centralizer (K : Set Ω) := by
  classical
  let U := LargeEvenSUGroup (Fin d) F (2 ^ n)
  let c : Ω := (ψ ⟨X', hX'SU⟩ : Ω)
  let Dfun : Fin d → F := fun i => (pairUnit a a' ω ω⁻¹ i : F)
  let D : GL (Fin d) F := P * X' * P⁻¹
  have hD : ((D : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.diagonal Dfun := hDX
  have hDunit : ∀ i, i ∈ I → Dfun i = 1 := by
    intro i hi
    have hia : i ≠ a := fun hh => haI (hh ▸ hi)
    have hia' : i ≠ a' := fun hh => ha'I (hh ▸ hi)
    simp [Dfun, pairUnit, hia, hia']
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨u, huBlk, rfl⟩ := (hK k).mp hk
  have hg : D * (P * (u : GL (Fin d) F) * P⁻¹) * D⁻¹ = P * (u : GL (Fin d) F) * P⁻¹ :=
    diag_conj_of_block hD hDunit huBlk.2
  have hXu : X' * (u : GL (Fin d) F) * X'⁻¹ = (u : GL (Fin d) F) := by
    have hX'eq : X' = P⁻¹ * D * P := by dsimp [D]; group
    have hueq : (u : GL (Fin d) F) = P⁻¹ * (P * (u : GL (Fin d) F) * P⁻¹) * P := by group
    rw [hX'eq, hueq]
    calc P⁻¹ * D * P * (P⁻¹ * (P * ↑u * P⁻¹) * P) * (P⁻¹ * D * P)⁻¹
        = P⁻¹ * (D * (P * ↑u * P⁻¹) * D⁻¹) * P := by group
      _ = P⁻¹ * (P * ↑u * P⁻¹) * P := by rw [hg]
  have hmemX : X' * (u : GL (Fin d) F) * X'⁻¹ ∈ U :=
    U.mul_mem (U.mul_mem hX'SU u.2) (U.inv_mem hX'SU)
  have hsub : (⟨X', hX'SU⟩ * u * ⟨X', hX'SU⟩⁻¹ : ↥U) = u :=
    Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hXu)
  have h2 : c * (ψ u : Ω) * c⁻¹ = (ψ u : Ω) := by
    have h1 : c * (ψ u : Ω) * c⁻¹ =
        (ψ (⟨X', hX'SU⟩ * u * ⟨X', hX'SU⟩⁻¹) : Ω) := by
      simp only [c, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1, hsub]
  have key : c * (ψ u : Ω) * c⁻¹ * c = c * (ψ u : Ω) := by
    rw [mul_assoc (c * (ψ u : Ω)) c⁻¹ c, inv_mul_cancel, mul_one]
  have h3 : c * (ψ u : Ω) = (ψ u : Ω) * c := by
    rw [← key, h2]
  exact h3.symm

theorem gen_lift_mem_B {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : MCfg p S B N D K x) {d : ℕ} {F : Type} [Field F] [Finite F]
    {U : Subgroup (GL (Fin d) F)} (ψ : ↥U →* ↥S) (hψ : Function.Surjective ψ) {b : Ω}
    (hb : b ∈ B) (u : ↥U) (hact : GActs ψ b (u : GL (Fin d) F)) (hup : u ^ p = 1) :
    (ψ u : Ω) ∈ B := by
  classical
  have hxcent : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).mpr (Subgroup.mem_zpowers x)
  have hbu : b * (ψ u : Ω) = (ψ u : Ω) * b := by
    have h := hact u u (by group)
    nth_rewrite 1 [h]
    group
  let c : Ω := b * (ψ u : Ω)
  have hc_eq : c = b * (ψ u : Ω) := rfl
  have hcS : c ∈ Subgroup.centralizer (S : Set Ω) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨v, hv⟩ := hψ ⟨s, hs⟩
    have hvs : (ψ v : Ω) = s := congrArg Subtype.val hv
    rw [← hvs]
    have hv : ((u * v * u⁻¹ : ↥U) : GL (Fin d) F) =
        (u : GL (Fin d) F) * (v : GL (Fin d) F) * (u : GL (Fin d) F)⁻¹ := by
      simp [Subgroup.coe_mul, Subgroup.coe_inv]
    have hg := hact v (u * v * u⁻¹) hv
    have h1 : (ψ v : Ω) * b = b * (ψ (u * v * u⁻¹) : Ω) := by
      rw [hg]; group
    have hψmul : ∀ a b : ↥U, ((ψ (a * b) : ↥S) : Ω) = (ψ a : Ω) * (ψ b : Ω) := by
      intro a b
      rw [map_mul, Subgroup.coe_mul]
    calc (ψ v : Ω) * c = (ψ v : Ω) * b * (ψ u : Ω) := by rw [hc_eq]; group
      _ = b * (ψ (u * v * u⁻¹) : Ω) * (ψ u : Ω) := by rw [h1]
      _ = b * ((ψ (u * v * u⁻¹) : Ω) * (ψ u : Ω)) := by group
      _ = b * ((ψ ((u * v * u⁻¹) * u) : ↥S) : Ω) := by
            conv_rhs => rw [hψmul]
      _ = b * ((ψ (u * v) : ↥S) : Ω) := by
            rw [show (u * v * u⁻¹) * u = u * v from by group]
      _ = b * ((ψ u * ψ v : ↥S) : Ω) := by rw [map_mul]
      _ = b * ((ψ u : Ω) * (ψ v : Ω)) := by rw [Subgroup.coe_mul]
      _ = c * (ψ v : Ω) := by rw [hc_eq]; group
  have hcx : c * x = x * c := by
    have hxψu : (ψ u : Ω) * x = x * (ψ u : Ω) :=
      (Subgroup.mem_centralizer_iff.mp hxcent) _ (ψ u).2
    have hbx : b * x = x * b := hcfg.elem.comm hb hcfg.mem
    calc c * x = b * (ψ u : Ω) * x := by rw [hc_eq]
      _ = b * ((ψ u : Ω) * x) := by group
      _ = b * (x * (ψ u : Ω)) := by rw [hxψu]
      _ = b * x * (ψ u : Ω) := by group
      _ = x * b * (ψ u : Ω) := by rw [hbx]
      _ = x * (b * (ψ u : Ω)) := by group
      _ = x * c := by rw [hc_eq]
  have hcp : c ^ p = 1 := by
    have hbp : b ^ p = 1 := hcfg.elem.2 b hb
    have h1 : (ψ u : ↥S) ^ p = 1 := by rw [← map_pow, hup, map_one]
    have hupS : (ψ u : Ω) ^ p = 1 := by
      simpa using congrArg (fun z : ↥S => (z : Ω)) h1
    rw [hc_eq, Commute.mul_pow (show Commute b (ψ u : Ω) from hbu), hbp, hupS, one_mul]
  have hxp : x ^ p = 1 := hcfg.elem.2 x hcfg.mem
  let E : Subgroup Ω := Subgroup.zpowers x ⊔ Subgroup.zpowers c
  have hEelem : IsElemAbelian p E := by
    refine IsElemAbelian.sup_of_commute (isElemAbelian_zpowers hxp) (isElemAbelian_zpowers hcp) ?_
    intro a ha b' hb'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    exact (show Commute c x from hcx).symm |>.zpow_zpow m n |>.eq
  have hEcent : E ≤ Subgroup.centralizer (S : Set Ω) :=
    sup_le (Subgroup.zpowers_le.mpr hxcent) (Subgroup.zpowers_le.mpr hcS)
  have hcyc' : ∀ T : Subgroup Ω, T ≤ Subgroup.centralizer (S : Set Ω) →
      IsPGroup p T → IsCyclic T :=
    fun T hT hTp => hcfg.cyc T
      (fun g hg => centMod_of_mem_centralizer (Subgroup.mem_centralizer_iff.mp (hT hg))) hTp
  have hcx_zp : c ∈ Subgroup.zpowers x :=
    (S171.cent_of_cyc hcfg.prime hEelem (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
      hcfg.ne_one hxcent hcyc' c (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))).mp hcS
  have hcB : c ∈ B := Subgroup.zpowers_le.mpr hcfg.mem hcx_zp
  have heq : (ψ u : Ω) = b⁻¹ * c := by
    rw [hc_eq]; group
  rw [heq]
  exact B.mul_mem (B.inv_mem hb) hcB

theorem uni_transvection {n d : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (P : GL (Fin d) F)
    (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) (I : Finset (Fin d)) {s t : Fin d} (hs : s ∈ I)
    (ht : t ∈ I) (hst : s ≠ t) :
    ∃ U₀ : Subgroup (GL (Fin d) F), U₀ ≠ ⊥ ∧ IsPGroup 2 U₀ ∧
      (∀ u ∈ U₀, (P * u * P⁻¹) ∈ UniBlockSet n d F I) ∧
      ∀ A ∈ MGU n d F, MWt P A s = MWt P A t →
        (∀ i j : Fin d, i ≠ j → ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = 0) →
        A ∈ Subgroup.normalizer (U₀ : Set (GL (Fin d) F)) := by
  classical
  haveI hchar : CharP F 2 := charP_two_of_card_sq hn hF
  let σ : Equiv.Perm (Fin d) := Equiv.swap s t
  let τ : GL (Fin d) F := permGL' σ
  have hτSU : τ ∈ UniSU n d F := by
    dsimp [τ, σ]
    exact swap_permGL'_mem_UniSU (n := n) (by positivity) hst
  have hτmat : ((τ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = σ.permMatrix F := rfl
  have hτ2 : τ ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, sq, hτmat]
    dsimp [σ]
    rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
  have hτne : τ ≠ 1 := by
    intro h
    have hmat := congrArg (fun g : GL (Fin d) F =>
      ((g : Matrix (Fin d) (Fin d) F) s t)) h
    have hτst : ((τ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) s t = 1 := by
      rw [hτmat]
      change (σ.permMatrix F) s t = 1
      rw [permMatrix_apply', Equiv.swap_apply_left, if_pos rfl]
    have h1st : ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) s t = 0 := by
      rw [Units.val_one, Matrix.one_apply_ne hst]
    rw [hτst, h1st] at hmat
    exact one_ne_zero hmat
  have hτblock : ∀ i j : Fin d, (i ∉ I ∨ j ∉ I) →
      ((τ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = if i = j then 1 else 0 := by
    rw [hτmat]
    simpa [σ] using swap_permMatrix_block (b := s) (b' := t) hs ht
  let g : GL (Fin d) F := P⁻¹ * τ * P
  let U₀ : Subgroup (GL (Fin d) F) := Subgroup.zpowers g
  have hg2 : g ^ 2 = 1 := by
    dsimp [g]
    rw [conj_pow_eq P τ 2, hτ2]
    group
  have hgne : g ≠ 1 := by
    intro h
    apply hτne
    have := congrArg (fun z : GL (Fin d) F => P * z * P⁻¹) h
    simpa [g, mul_assoc] using this
  have hu_pow : ∀ u : GL (Fin d) F, u ∈ U₀ → ∃ k : ℕ, g ^ k = u := by
    intro u hu
    have hmem : u ∈ Submonoid.powers g := by
      rw [mem_powers_iff_mem_zpowers]
      exact hu
    exact (Submonoid.mem_powers_iff u g).mp hmem
  refine ⟨U₀, ?_, ?_, ?_, ?_⟩
  · simpa [U₀] using (Subgroup.zpowers_ne_bot (g := g)).mpr hgne
  · intro u
    obtain ⟨k, hk⟩ := hu_pow (u : GL (Fin d) F) u.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, show (2 : ℕ) ^ 1 = 2 from rfl, ← hk]
    calc (g ^ k) ^ 2 = g ^ (k * 2) := by rw [pow_mul]
      _ = g ^ (2 * k) := by rw [Nat.mul_comm k 2]
      _ = (g ^ 2) ^ k := by rw [pow_mul]
      _ = 1 := by rw [hg2, one_pow]
  · intro u hu
    obtain ⟨k, hk⟩ := hu_pow (u : GL (Fin d) F) hu
    have hconj : P * (u : GL (Fin d) F) * P⁻¹ = τ ^ k := by
      rw [← hk]
      dsimp [g]
      rw [conj_pow_eq]
      group
    rw [UniBlockSet]
    refine ⟨?_, ?_⟩
    · rw [hconj]
      exact Subgroup.pow_mem (K := UniSU n d F) hτSU k
    · rw [hconj]
      exact block_pow hτblock k
  · intro A hA hwt hdiag
    let B' : GL (Fin d) F := P * A * P⁻¹
    have hBdiag : ((B' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        Matrix.diagonal (fun i => ((B' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i) := by
      ext i j
      by_cases h : i = j
      · subst h; rw [Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ h]
        exact hdiag i j h
    have hB'τ : ((B' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        ((τ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        ((τ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
          ((B' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
      rw [hBdiag, hτmat]
      dsimp [σ]
      exact diagonal_comm_permMatrix_swap (b := s) (b' := t) (h := fun i =>
        ((B' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i) (by simpa [MWt, B'] using hwt)
    have hBτ : B' * τ = τ * B' := Units.ext hB'τ
    have hAg : A * g = g * A := by
      have h := congrArg (fun z : GL (Fin d) F => P⁻¹ * z * P) hBτ
      simpa [B', g, mul_assoc] using h
    have hcent : A ∈ Subgroup.centralizer ({g} : Set (GL (Fin d) F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hAg
    have hcentU : A ∈ Subgroup.centralizer (U₀ : Set (GL (Fin d) F)) := by
      rw [show (U₀ : Set (GL (Fin d) F)) = (Subgroup.zpowers g : Set _) from rfl,
        Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hcent
    exact Subgroup.centralizer_le_normalizer (U₀ : Set (GL (Fin d) F)) hcentU

private theorem MGU_le_normalizer {n d : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) :
    MGU n d F ≤ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) := by
  haveI hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    { prime := Nat.prime_two, one_le := hn,
      card := by rw [hF, ← pow_mul, Nat.mul_comm n 2] }
  rw [MGU]
  exact (Subgroup.closure_le _).mpr fun A hA =>
    CFSG.StandardType.TableBUE.gu_subset_normalizer (d := d) (n := n) hUFD hA

private theorem GActs_mul {n d : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω}
    {F : Type} [Field F]
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S}
    {c c' : Ω} {X Y : GL (Fin d) F}
    (hX : GActs ψ c X) (hY : GActs ψ c' Y)
    (hYN : Y ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) :
    GActs ψ (c' * c) (X * Y) := by
  intro u u' hu'
  have hYu : Y * (u : GL (Fin d) F) * Y⁻¹ ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) :=
    ((Subgroup.mem_normalizer_iff.mp hYN) (u : GL (Fin d) F)).mp u.2
  have hv : (u' : GL (Fin d) F) =
      X * ((⟨Y * (u : GL (Fin d) F) * Y⁻¹, hYu⟩ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n))) :
        GL (Fin d) F) * X⁻¹ := by
    rw [Subgroup.coe_mk, hu']
    group
  have h1 := hX ⟨Y * (u : GL (Fin d) F) * Y⁻¹, hYu⟩ u' hv
  have h2 := hY u ⟨Y * (u : GL (Fin d) F) * Y⁻¹, hYu⟩ rfl
  rw [h1, h2]
  group

private theorem GActs_pow_self {n d : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω}
    {F : Type} [Field F]
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S}
    (w : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n))) (j : ℕ) :
    GActs ψ (((ψ w : Ω) ^ j)⁻¹) ((w : GL (Fin d) F) ^ j) := by
  intro u u' hu'
  have hwj : ((w : GL (Fin d) F) ^ j) ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) :=
    Subgroup.pow_mem (K := LargeEvenSUGroup (Fin d) F (2 ^ n)) w.2 j
  have heq : u' = w ^ j * u * (w ^ j)⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    exact hu'
  rw [heq, map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [map_pow]
  simp only [Subgroup.coe_pow]
  group

private theorem exists_uni_U {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B N D K : Subgroup Ω} {x : Ω} (hcfg : MCfg p S B N D K x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d)
    {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))}
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S} (hψ : GLifts θ ψ)
    {P : GL (Fin d) F} (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    (I : Finset (Fin d)) {s t : Fin d} (hs : s ∈ I) (ht : t ∈ I) (hst : s ≠ t)
    (hK : ∀ k : Ω, k ∈ K ↔ ∃ u : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)),
      (P * (u : GL (Fin d) F) * P⁻¹) ∈ UniBlockSet n d F I ∧ (ψ u : Ω) = k) :
    ∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ K ∧
      (∀ (b : Ω) (A : GL (Fin d) F), b ∈ B → A ∈ MGU n d F →
        MWt P A s = MWt P A t →
        (∀ i j : Fin d, i ≠ j → ((P * A * P⁻¹ : GL (Fin d) F) :
          Matrix (Fin d) (Fin d) F) i j = 0) →
        GActs ψ b A → b ∈ Subgroup.normalizer (U : Set Ω)) := by
  classical
  haveI hchar : CharP F 2 := charP_two_of_card_sq hn hF
  haveI hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    { prime := Nat.prime_two, one_le := hn,
      card := by rw [hF, ← pow_mul, Nat.mul_comm n 2] }
  let SU := LargeEvenSUGroup (Fin d) F (2 ^ n)
  obtain ⟨U₀, hU₀ne, hU₀2, hU₀block, hU₀norm⟩ :=
    uni_transvection (n := n) (d := d) hF hn P hP I hs ht hst
  have hPnorm : P ∈ Subgroup.normalizer (SU : Set (GL (Fin d) F)) :=
    CFSG.StandardType.TableBUE.gu_subset_normalizer (d := d) (n := n) hUFD hP
  have hU₀le : U₀ ≤ SU := by
    intro u hu
    have hmem : P * u * P⁻¹ ∈ SU := (hU₀block u hu).1
    exact ((Subgroup.mem_normalizer_iff.mp hPnorm) u).mpr hmem
  let φ : ↥U₀ →* ↥S :=
    { toFun := fun u => ψ ⟨(u : GL (Fin d) F), hU₀le u.2⟩
      map_one' := map_one ψ
      map_mul' := fun u v => by
        apply Subtype.ext
        change ((ψ (⟨(u : GL (Fin d) F), hU₀le u.2⟩ * ⟨(v : GL (Fin d) F), hU₀le v.2⟩) : ↥S) : Ω) =
          ((ψ ⟨(u : GL (Fin d) F), hU₀le u.2⟩ : ↥S) : Ω) *
            ((ψ ⟨(v : GL (Fin d) F), hU₀le v.2⟩ : ↥S) : Ω)
        rw [map_mul, Subgroup.coe_mul] }
  have hinj : ∀ u : ↥U₀, φ u = 1 → u = 1 := by
    intro u hu
    have hscal : (u : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
      apply ker_psi_le_scalars hψ (u := ⟨(u : GL (Fin d) F), hU₀le u.2⟩)
      exact hu
    obtain ⟨lam, hlam⟩ := hscal
    obtain ⟨k, hk⟩ := hU₀2 u
    have hk' : (u : GL (Fin d) F) ^ (2 ^ k) = 1 := by
      have h := congrArg (fun z : ↥U₀ => (z : GL (Fin d) F)) hk
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h
    have hlam_pow : ((lam : F) ^ (2 ^ k)) = 1 := by
      have h1 : (Matrix.GeneralLinearGroup.scalar (Fin d) lam ^ (2 ^ k)) = 1 := by
        rw [hlam]; exact hk'
      have h2 : Matrix.GeneralLinearGroup.scalar (Fin d) (lam ^ (2 ^ k)) = 1 := by
        rw [map_pow]; exact h1
      have h3 := congrArg (fun z : GL (Fin d) F =>
        ((z : Matrix (Fin d) (Fin d) F) ⟨0, by omega⟩ ⟨0, by omega⟩)) h2
      simpa [Matrix.GeneralLinearGroup.coe_scalar, diagonal_pow, Matrix.diagonal_apply_eq] using h3
    have hzero : ((lam : F) - 1) ^ (2 ^ k) = 0 := by
      rw [sub_pow_char_pow, hlam_pow, one_pow, sub_self]
    have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
    have hsub : (lam : F) - 1 = 0 :=
      (pow_eq_zero_iff (by positivity : (2 : ℕ) ^ k ≠ 0)).mp hzero
    have hlam1 : (lam : F) = 1 := sub_eq_zero.mp hsub
    apply Subtype.ext
    have hu1 : (u : GL (Fin d) F) = 1 := by
      apply Units.ext
      rw [← hlam, Matrix.GeneralLinearGroup.coe_scalar, Units.val_one, ← Matrix.diagonal_one]
      exact congrArg Matrix.diagonal (funext fun i => by simp [hlam1])
    simpa using hu1
  have hU₀'ne : U₀ ≠ ⊥ := hU₀ne
  have hmapne : φ.range ≠ ⊥ := by
    obtain ⟨u, hu_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU₀ne
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨φ u, MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩, ?_⟩
    intro h
    exact hu_ne (hinj u (Subtype.ext_iff.mp h))
  have hUne : (φ.range).map S.subtype ≠ ⊥ := by
    intro hbot
    apply hmapne
    have := (Subgroup.map_eq_bot_iff_of_injective (H := φ.range) (f := S.subtype)
      S.subtype_injective).mp hbot
    exact this
  let U : Subgroup Ω := (φ.range).map S.subtype
  have hφrange2 : IsPGroup 2 φ.range :=
    hU₀2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hU2 : IsPGroup 2 U := hφrange2.map S.subtype
  have hUle : U ≤ K := by
    intro y hy
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hs'
    exact (hK _).mpr ⟨⟨(u : GL (Fin d) F), hU₀le u.2⟩, hU₀block u u.2, rfl⟩
  refine ⟨U, hUne, hU2, hUle, ?_⟩
  intro b A hb hA hwt hdiag hActs
  have hAN : A ∈ Subgroup.normalizer (U₀ : Set (GL (Fin d) F)) := hU₀norm A hA hwt hdiag
  have hAinvN : A⁻¹ ∈ Subgroup.normalizer (U₀ : Set (GL (Fin d) F)) := Subgroup.inv_mem _ hAN
  have hfw : ∀ u : ↥U₀, b⁻¹ * ((φ u : ↥S) : Ω) * b =
      ((φ ⟨A * (u : GL (Fin d) F) * A⁻¹, ((Subgroup.mem_normalizer_iff.mp hAN) u).mp u.2⟩ :
        ↥S) : Ω) := by
    intro u
    have hAu : A * (u : GL (Fin d) F) * A⁻¹ ∈ U₀ :=
      ((Subgroup.mem_normalizer_iff.mp hAN) u).mp u.2
    have hg := hActs ⟨(u : GL (Fin d) F), hU₀le u.2⟩
      ⟨A * (u : GL (Fin d) F) * A⁻¹, hU₀le hAu⟩ rfl
    have h1 : (φ ⟨A * (u : GL (Fin d) F) * A⁻¹, hAu⟩ : ↥S) =
        ψ ⟨A * (u : GL (Fin d) F) * A⁻¹, hU₀le hAu⟩ := rfl
    have h2 : (φ u : ↥S) = ψ ⟨(u : GL (Fin d) F), hU₀le u.2⟩ := rfl
    rw [h1, h2]
    exact hg.symm
  have hbw : ∀ u : ↥U₀, b * ((φ u : ↥S) : Ω) * b⁻¹ =
      ((φ ⟨A⁻¹ * (u : GL (Fin d) F) * A, ((Subgroup.mem_normalizer_iff.mp hAinvN) u).mp u.2⟩ :
        ↥S) : Ω) := by
    intro u
    have hAiu : A⁻¹ * (u : GL (Fin d) F) * A ∈ U₀ :=
      ((Subgroup.mem_normalizer_iff.mp hAinvN) u).mp u.2
    have hg := hActs ⟨A⁻¹ * (u : GL (Fin d) F) * A, hU₀le hAiu⟩
      ⟨(u : GL (Fin d) F), hU₀le u.2⟩ (by group)
    have h1 : (φ ⟨A⁻¹ * (u : GL (Fin d) F) * A, hAiu⟩ : ↥S) =
        ψ ⟨A⁻¹ * (u : GL (Fin d) F) * A, hU₀le hAiu⟩ := rfl
    have h2 : (φ u : ↥S) = ψ ⟨(u : GL (Fin d) F), hU₀le u.2⟩ := rfl
    rw [h1, h2]
    calc b * ψ ⟨(u : GL (Fin d) F), hU₀le u.2⟩ * b⁻¹
        = b * (b⁻¹ * ψ ⟨A⁻¹ * (u : GL (Fin d) F) * A, hU₀le hAiu⟩ * b) * b⁻¹ := by rw [hg]
      _ = ψ ⟨A⁻¹ * (u : GL (Fin d) F) * A, hU₀le hAiu⟩ := by group
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  constructor
  · intro hy
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hs'
    change b⁻¹ * ((φ u : ↥S) : Ω) * b ∈ U
    rw [hfw u]
    exact Subgroup.mem_map_of_mem S.subtype (MonoidHom.mem_range.mpr ⟨
      ⟨A * (u : GL (Fin d) F) * A⁻¹, ((Subgroup.mem_normalizer_iff.mp hAN) u).mp u.2⟩, rfl⟩)
  · intro hy
    obtain ⟨s', hs', hs'eq⟩ := Subgroup.mem_map.mp hy
    obtain ⟨u, hueq⟩ := MonoidHom.mem_range.mp hs'
    have hy_eq : y = b * ((φ u : ↥S) : Ω) * b⁻¹ := by
      calc y = b * (b⁻¹ * y * b) * b⁻¹ := by group
        _ = b * (S.subtype s') * b⁻¹ := by rw [hs'eq]
        _ = b * ((φ u : ↥S) : Ω) * b⁻¹ := by rw [← hueq]; rfl
    rw [hy_eq, hbw u]
    exact Subgroup.mem_map_of_mem S.subtype (MonoidHom.mem_range.mpr ⟨
      ⟨A⁻¹ * (u : GL (Fin d) F) * A, ((Subgroup.mem_normalizer_iff.mp hAinvN) u).mp u.2⟩, rfl⟩)

private theorem B_decomp_equal {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B N D K : Subgroup Ω} {x : Ω} (hcfg : MCfg p S B N D K x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hpq : p ∣ 2 ^ n + 1)
    {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))}
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S} (hψ : GLifts θ ψ)
    (hψS : Function.Surjective ψ)
    {P : GL (Fin d) F} (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    (hB : ∀ b ∈ B, GDiagAct p ψ P b) {Gh : Subgroup (GL (Fin d) F)}
    (hGh : ∀ A, A ∈ Gh ↔ A ∈ MGU n d F ∧ ∃ b ∈ B, GInduced θ b A)
    {s t : Fin d}
    (hsep : ∀ A ∈ Gh, MWt P A s = MWt P A t)
    (U : Subgroup Ω)
    (hU : U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ K ∧
      (∀ (b : Ω) (A : GL (Fin d) F), b ∈ B → A ∈ MGU n d F →
        MWt P A s = MWt P A t →
        (∀ i j : Fin d, i ≠ j → ((P * A * P⁻¹ : GL (Fin d) F) :
          Matrix (Fin d) (Fin d) F) i j = 0) →
        GActs ψ b A → b ∈ Subgroup.normalizer (U : Set Ω))) :
    B = (B ⊓ K) ⊔ (B ⊓ Subgroup.normalizer (U : Set Ω)) := by
  have hUN := U
  have hMGUN := MGU_le_normalizer (n := n) (d := d) hF hn
  have hBle : B ≤ Subgroup.normalizer (U : Set Ω) := by
    intro b hb
    obtain ⟨A, hActs, hAp, hAdiag⟩ := hB b hb
    obtain ⟨D, hD⟩ := hAdiag
    have hAMGU : A ∈ MGU n d F :=
      mem_GU_of_diag_pow_scalar hcfg.prime hpq hF (by omega) hP hD hAp
    have hAN : A ∈ Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) := hMGUN hAMGU
    have hGInd : GInduced θ b A := ginduced_of_gacts hψ hψS hAN hActs
    have hAGh : A ∈ Gh := (hGh A).mpr ⟨hAMGU, b, hb, hGInd⟩
    have hwt : MWt P A s = MWt P A t := hsep A hAGh
    have hoff : ∀ i j : Fin d, i ≠ j → ((P * A * P⁻¹ : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) i j = 0 := by
      intro i j hij
      rw [hD, Matrix.diagonal_apply_ne _ hij]
    exact hU.2.2.2 b A hb hAMGU hwt hoff hActs
  apply le_antisymm
  · intro b hb
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hb, hBle hb⟩)
  · exact sup_le inf_le_left inf_le_left

private theorem B_decomp_sep {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B N D K : Subgroup Ω} {x : Ω} (hcfg : MCfg p S B N D K x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hpq : p ∣ 2 ^ n + 1)
    (hBN : B ≤ Subgroup.normalizer (S : Set Ω))
    {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))}
    {ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S} (hψ : GLifts θ ψ)
    (hψS : Function.Surjective ψ)
    (hperf : Group.IsPerfect ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)))
    (hcen : ∀ A : GL (Fin d) F, (∀ u ∈ LargeEvenSUGroup (Fin d) F (2 ^ n),
      ⁅A, u⁆ ∈ LargeEvenScalars (Fin d) F) → A ∈ LargeEvenScalars (Fin d) F)
    {P : GL (Fin d) F} (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    (hB : ∀ b ∈ B, GDiagAct p ψ P b) {Gh : Subgroup (GL (Fin d) F)}
    (hGh : ∀ A, A ∈ Gh ↔ A ∈ MGU n d F ∧ ∃ b ∈ B, GInduced θ b A)
    (hdiag : MDiagAt d F P Gh)
    (I : Finset (Fin d))
    (hK : ∀ k : Ω, k ∈ K ↔ ∃ u : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)),
      (P * (u : GL (Fin d) F) * P⁻¹) ∈ UniBlockSet n d F I ∧ (ψ u : Ω) = k)
    {s t : Fin d} (hs : s ∈ I) (ht : t ∈ I) (hst : s ≠ t)
    (hsep : ∃ A ∈ Gh, (P * A * P⁻¹) ∈ UniBlockSet n d F I ∧ A ^ p = 1 ∧
      MWt P A s ≠ MWt P A t)
    (U : Subgroup Ω) (hUne : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hUK : U ≤ K)
    (hUtrans : ∀ (b : Ω) (A : GL (Fin d) F), b ∈ B → A ∈ MGU n d F →
        MWt P A s = MWt P A t →
        (∀ i j : Fin d, i ≠ j → ((P * A * P⁻¹ : GL (Fin d) F) :
          Matrix (Fin d) (Fin d) F) i j = 0) →
        GActs ψ b A → b ∈ Subgroup.normalizer (U : Set Ω)) :
    B ≤ (B ⊓ K) ⊔ (B ⊓ Subgroup.normalizer (U : Set Ω)) := by
  classical
  obtain ⟨A, hAGh, hAblk, hAp, hAne⟩ := hsep
  obtain ⟨hAMGU, b₀, hb₀, hind⟩ := (hGh A).mp hAGh
  have hMGUN := MGU_le_normalizer (n := n) (d := d) hF hn
  have hAN : A ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) := hMGUN hAMGU
  have hb₀S : b₀ ∈ Subgroup.normalizer (S : Set Ω) := hBN hb₀
  have hActsA : GActs ψ b₀ A :=
    gen_equivariance hperf θ ψ hψ hb₀S hAN hind
  have hPnorm : P ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) :=
    hMGUN (Subgroup.subset_closure hP)
  have hPinvN : P⁻¹ ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) := Subgroup.inv_mem _ hPnorm
  have hASU : A ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) := by
    have h := ((Subgroup.mem_normalizer_iff.mp hPinvN) (P * A * P⁻¹)).mp hAblk.1
    convert h using 1
    group
  let w : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) := ⟨A, hASU⟩
  have hwp : w ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hAp
  let b₁ : Ω := (ψ w : Ω)
  have hb₁B : b₁ ∈ B :=
    gen_lift_mem_B hcfg ψ hψS hb₀ w hActsA hwp
  have hb₁K : b₁ ∈ K :=
    (hK b₁).mpr ⟨w, by simpa [w, b₁] using hAblk, rfl⟩
  obtain ⟨lam, hlam⟩ := hdiag A hAGh
  have hAmat : ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal lam := hlam
  have hLamp : ∀ i, lam i ^ p = 1 := by
    intro i
    have h2 : ((P * A * P⁻¹ : GL (Fin d) F) ^ p : Matrix (Fin d) (Fin d) F) =
        Matrix.diagonal (fun i => lam i ^ p) := by
      change ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) ^ p =
        Matrix.diagonal (fun i => lam i ^ p)
      rw [hAmat, diagonal_pow]
    have h3 : ((P * A * P⁻¹ : GL (Fin d) F) ^ p : Matrix (Fin d) (Fin d) F) = 1 := by
      change ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) ^ p = 1
      rw [← Units.val_pow_eq_pow_val]
      rw [show (P * A * P⁻¹ : GL (Fin d) F) ^ p = 1 from by
        rw [show P * A * P⁻¹ = (P⁻¹)⁻¹ * A * P⁻¹ from by group, conj_pow_eq, hAp]
        group, Units.val_one]
    have h4 := h2.symm.trans h3
    rw [← Matrix.diagonal_one] at h4
    exact congrFun (Matrix.diagonal_injective h4) i
  have hLamt : lam t ≠ 0 := by
    intro h0
    have hdet : ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det ≠ 0 :=
      (P * A * P⁻¹).det_ne_zero
    apply hdet
    rw [hAmat, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ t) h0
  have hLams : lam s ≠ 0 := by
    intro h0
    have hdet : ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det ≠ 0 :=
      (P * A * P⁻¹).det_ne_zero
    apply hdet
    rw [hAmat, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ s) h0
  let ρ : Fˣ := Units.mk0 (lam s) hLams * (Units.mk0 (lam t) hLamt)⁻¹
  have hρval : (ρ : F) = lam s * (lam t)⁻¹ := rfl
  have hρp : ρ ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hρval, mul_pow, inv_pow, hLamp s, hLamp t,
      inv_one, mul_one]
  have hρne : ρ ≠ 1 := by
    intro h
    apply hAne
    have h1 : (ρ : F) = 1 := by rw [h, Units.val_one]
    rw [hρval] at h1
    have h2 : lam s = lam t := by
      have := congrArg (fun z => z * lam t) h1
      simpa [mul_assoc, inv_mul_cancel₀ hLamt] using this
    change ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) s s =
      ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) t t
    rw [hAmat, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    exact h2
  haveI : NeZero p := ⟨hcfg.prime.ne_zero⟩
  have hρprim : IsPrimitiveRoot ρ p := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    have hdvd : orderOf ρ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hρp
    have hne1 : orderOf ρ ≠ 1 := by
      intro h
      exact hρne (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime hcfg.prime).mp hdvd with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  have hstep : ∀ b ∈ B, ∃ j : ℕ, j < p ∧ b₁ ^ j ∈ B ⊓ K ∧
      ((b₁ ^ j)⁻¹ * b) ∈ B ⊓ Subgroup.normalizer (U : Set Ω) := by
    intro b hb
    obtain ⟨Ab, hActs, hAbscal, hAbdiag⟩ := hB b hb
    obtain ⟨D, hD⟩ := hAbdiag
    obtain ⟨c, hc⟩ := hAbscal
    have hAbMGU : Ab ∈ MGU n d F :=
      mem_GU_of_diag_pow_scalar hcfg.prime hpq hF (by omega) hP hD ⟨c, hc⟩
    have hAbN : Ab ∈ Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) := hMGUN hAbMGU
    have hDp : ∀ i, D i ^ p = (c : F) := by
      intro i
      have hdiagp : ((P * Ab * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) ^ p =
          Matrix.diagonal (fun i => D i ^ p) := by
        rw [hD, diagonal_pow]
      have hscal : ((P * Ab * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) ^ p =
          (c : F) • (1 : Matrix (Fin d) (Fin d) F) := by
        rw [← Units.val_pow_eq_pow_val]
        rw [show (P * Ab * P⁻¹ : GL (Fin d) F) ^ p = P * Ab ^ p * P⁻¹ from by
          rw [show P * Ab * P⁻¹ = (P⁻¹)⁻¹ * Ab * P⁻¹ from by group, conj_pow_eq]
          group]
        rw [← hc]
        have hcen : P * Matrix.GeneralLinearGroup.scalar (Fin d) c * P⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin d) c := by
          calc P * Matrix.GeneralLinearGroup.scalar (Fin d) c * P⁻¹
              = Matrix.GeneralLinearGroup.scalar (Fin d) c * P * P⁻¹ := by
                rw [← Matrix.GeneralLinearGroup.scalar_commute c P]
            _ = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
                rw [mul_assoc, mul_inv_cancel, mul_one]
        rw [hcen, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal]
      have h3 := hdiagp.symm.trans hscal
      rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_injective.eq_iff] at h3
      exact congrFun h3 i
    have hDt : D t ≠ 0 := by
      intro h0
      have hdet : ((P * Ab * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det ≠ 0 :=
        (P * Ab * P⁻¹).det_ne_zero
      apply hdet
      rw [hD, Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ t) h0
    let α : Fˣ := Units.mk0 (D s) (by
      intro h0
      have hdet : ((P * Ab * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det ≠ 0 :=
        (P * Ab * P⁻¹).det_ne_zero
      apply hdet
      rw [hD, Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ s) h0) * (Units.mk0 (D t) hDt)⁻¹
    have hαval : (α : F) = D s * (D t)⁻¹ := rfl
    have hαp : α ^ p = 1 := by
      apply Units.ext
      change (α : F) ^ p = (1 : F)
      rw [hαval, mul_pow, inv_pow, hDp s, hDp t]
      exact mul_inv_cancel₀ (by simpa using c.ne_zero)
    have hαpF : (α : F) ^ p = 1 := by
      have := congrArg (fun z : Fˣ => (z : F)) hαp
      simpa [Units.val_one, Units.val_pow_eq_pow_val] using this
    obtain ⟨j, hjlt, hj⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one
      (IsPrimitiveRoot.coe_units_iff.mpr hρprim) (by rw [inv_pow, hαpF, inv_one])
    have hαj : (α : F) * (ρ : F) ^ j = 1 := by
      rw [hj]
      exact mul_inv_cancel₀ (by simpa using α.ne_zero)
    have hxj : D s * lam s ^ j = D t * lam t ^ j := by
      have hval : (α : F) * (ρ : F) ^ j = 1 := hαj
      rw [hαval, hρval, mul_pow, inv_pow] at hval
      have hDt' : D t ≠ 0 := hDt
      have hLamt' : lam t ≠ 0 := hLamt
      field_simp [hDt', hLamt'] at hval ⊢
      exact hval
    let X : GL (Fin d) F := Ab * A ^ j
    have hXMGU : X ∈ MGU n d F :=
      (MGU n d F).mul_mem hAbMGU (Subgroup.pow_mem (K := MGU n d F) hAMGU j)
    have hXmat : ((P * X * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        Matrix.diagonal (fun i => D i * lam i ^ j) := by
      have h1 : P * X * P⁻¹ = (P * Ab * P⁻¹) * ((P * A * P⁻¹) ^ j) := by
        dsimp [X]
        rw [show (P * A * P⁻¹ : GL (Fin d) F) ^ j = P * A ^ j * P⁻¹ from by
          rw [show P * A * P⁻¹ = (P⁻¹)⁻¹ * A * P⁻¹ from by group, conj_pow_eq]
          group]
        group
      rw [h1, Units.val_mul, hD, Units.val_pow_eq_pow_val, hAmat, diagonal_pow,
        Matrix.diagonal_mul_diagonal]
    have hoff : ∀ i jj : Fin d, i ≠ jj →
        ((P * X * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i jj = 0 := by
      intro i jj hij
      rw [hXmat, Matrix.diagonal_apply_ne _ hij]
    have hwt : MWt P X s = MWt P X t := by
      change ((P * X * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) s s =
        ((P * X * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) t t
      rw [hXmat, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      exact hxj
    have hb''B : (b₁ ^ j)⁻¹ * b ∈ B :=
      B.mul_mem (B.inv_mem (Subgroup.pow_mem (K := B) hb₁B j)) hb
    have hAjN : A ^ j ∈ Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)) :=
      Subgroup.pow_mem
        (K := Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F))) hAN j
    have hGActsX : GActs ψ ((b₁ ^ j)⁻¹ * b) X := by
      have hL2 : GActs ψ (((ψ w : Ω) ^ j)⁻¹) ((w : GL (Fin d) F) ^ j) :=
        GActs_pow_self (ψ := ψ) w j
      have hL2' : GActs ψ ((b₁ ^ j)⁻¹) (A ^ j) := by
        simpa [b₁, w] using hL2
      exact GActs_mul hActs hL2' hAjN
    have hb''N : (b₁ ^ j)⁻¹ * b ∈ Subgroup.normalizer (U : Set Ω) :=
      hUtrans ((b₁ ^ j)⁻¹ * b) X hb''B hXMGU hwt hoff hGActsX
    exact ⟨j, hjlt,
      Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem (K := B) hb₁B j, Subgroup.pow_mem (K := K) hb₁K j⟩,
      Subgroup.mem_inf.mpr ⟨hb''B, hb''N⟩⟩
  intro b hb
  obtain ⟨j, -, hKj, hNj⟩ := hstep b hb
  have hb_eq : b = b₁ ^ j * ((b₁ ^ j)⁻¹ * b) := by group
  rw [hb_eq]
  exact Subgroup.mul_mem_sup hKj hNj

theorem uni_iv_assembly {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} (hcfg : MCfg p S B N D K x) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hpq : p ∣ 2 ^ n + 1)
    (hBN : B ≤ Subgroup.normalizer (S : Set Ω))
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))
    (ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S) (hψ : GLifts θ ψ)
    (hψS : Function.Surjective ψ) (hperf : Group.IsPerfect ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)))
    (hcen : ∀ A : GL (Fin d) F, (∀ u ∈ LargeEvenSUGroup (Fin d) F (2 ^ n),
      ⁅A, u⁆ ∈ LargeEvenScalars (Fin d) F) → A ∈ LargeEvenScalars (Fin d) F)
    (P : GL (Fin d) F) (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    (hB : ∀ b ∈ B, GDiagAct p ψ P b) {Gh : Subgroup (GL (Fin d) F)}
    (hGh : ∀ A, A ∈ Gh ↔ A ∈ MGU n d F ∧ ∃ b ∈ B, GInduced θ b A) (hdiag : MDiagAt d F P Gh)
    (I : Finset (Fin d))
    (hK : ∀ k : Ω, k ∈ K ↔ ∃ u : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)),
      (P * (u : GL (Fin d) F) * P⁻¹) ∈ UniBlockSet n d F I ∧ (ψ u : Ω) = k)
    (a a' : Fin d) (haa : a ≠ a') (hpair : ∀ A ∈ Gh, MWt P A a = MWt P A a')
    (hIpair : (a ∈ I ∧ a' ∈ I) ∨ (a ∉ I ∧ a' ∉ I)) (s t : Fin d) (hs : s ∈ I) (ht : t ∈ I)
    (hst : s ≠ t)
    (hsep : (∀ A ∈ Gh, MWt P A s = MWt P A t) ∨
      ∃ A ∈ Gh, (P * A * P⁻¹) ∈ UniBlockSet n d F I ∧ A ^ p = 1 ∧ MWt P A s ≠ MWt P A t) :
    ∃ B' U : Subgroup Ω, IsElemAbelian p B' ∧ B' ≤ S ⊔ B ∧ B ≤ B' ∧ B ≠ B' ∧ U ≠ ⊥ ∧
      IsPGroup 2 U ∧ U ≤ K ∧ B' = (B' ⊓ K) ⊔ (B' ⊓ Subgroup.normalizer (U : Set Ω)) ∧
      B' ≤ Subgroup.normalizer (K : Set Ω) := by
  classical
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  have hpF : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ n) 1
    rw [hfac]
    exact dvd_mul_of_dvd_left hpq _
  obtain ⟨ω, hωorder⟩ := exists_prime_orderOf_dvd_card' p hpF
  have hpodd : p ≠ 2 := by
    intro hp2
    have hodd : Odd (2 ^ n + 1) := by
      have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega]
        rw [pow_succ]; ring
      rw [h2]; exact ⟨2 ^ (n - 1), by ring⟩
    exact hodd.not_two_dvd_nat (hp2 ▸ hpq)
  have hωp : ω ^ p = 1 := by simpa [hωorder] using pow_orderOf_eq_one ω
  have hωF : (ω : F) ^ p = 1 := by
    simpa using congrArg (fun u : Fˣ => (u : F)) hωp
  have hωne : ω ≠ ω⁻¹ := by
    intro h
    have h2 : ω ^ 2 = 1 := by
      calc ω ^ 2 = ω * ω := sq ω
        _ = ω * ω⁻¹ := congrArg (fun z => ω * z) h
        _ = 1 := mul_inv_cancel ω
    have hdvd : p ∣ 2 := by
      rw [← hωorder]
      exact orderOf_dvd_iff_pow_eq_one.mpr h2
    exact hpodd ((Nat.prime_dvd_prime_iff_eq hcfg.prime Nat.prime_two).mp hdvd)
  set DX : Fin d → F := fun i => (pairUnit a a' ω ω⁻¹ i : F) with hDXdef
  obtain ⟨X', hX'SU, hX'p, hXD, -, -, -⟩ :=
    exists_pair_element hcfg.prime hF hn hpq P hP haa ω hωorder
  have hXD' : ((P * X' * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal DX := hXD
  let c : Ω := (ψ ⟨X', hX'SU⟩ : Ω)
  have hcB : c ∉ B := by
    apply pair_element_not_mem hcfg hF hn hd hpq hψ hψS hcen hP hB hGh hpair
      X' hX'SU DX ω hXD'
    · simp [DX, pairUnit_self]
    · simp [DX, pairUnit_other haa]
    · exact hωne
  obtain ⟨hB'elem, hBle, hBne, hB'le⟩ :=
    pair_element_sup hcfg hB X' hX'SU hX'p ⟨DX, hXD'⟩ (by simpa [c] using hcB)
  obtain ⟨U, hUne, hU2, hUK, hUtrans⟩ := exists_uni_U hcfg hF hn hd hψ hP I hs ht hst hK
  have hBdec : B ≤ (B ⊓ K) ⊔ (B ⊓ Subgroup.normalizer (U : Set Ω)) := by
    rcases hsep with hw | hsep2
    · have h := B_decomp_equal hcfg hF hn hd hpq hψ hψS hP hB hGh hw U
        ⟨hUne, hU2, hUK, hUtrans⟩
      exact h.le
    · exact B_decomp_sep hcfg hF hn hd hpq hBN hψ hψS hperf hcen hP hB hGh hdiag I hK
        hs ht hst hsep2 U hUne hU2 hUK hUtrans
  have hcdec : c ∈ ((B ⊔ Subgroup.zpowers c) ⊓ K) ⊔
      ((B ⊔ Subgroup.zpowers c) ⊓ Subgroup.normalizer (U : Set Ω)) := by
    have hcB' : c ∈ B ⊔ Subgroup.zpowers c :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    rcases hIpair with ⟨haI, ha'I⟩ | ⟨haI, ha'I⟩
    · have hcK : c ∈ K := by
        have := pair_element_mem_K hcfg hF hn hP I hK X' hX'SU haI ha'I ω hXD'
        simpa [c] using this
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hcB', hcK⟩)
    · have hcC : c ∈ Subgroup.centralizer (K : Set Ω) := by
        have := pair_element_centralizes_K hcfg hF hn hP I hK X' hX'SU haI ha'I ω hXD'
        simpa [c] using this
      have hcN : c ∈ Subgroup.normalizer (U : Set Ω) :=
        Subgroup.centralizer_le_normalizer (U : Set Ω)
          (Subgroup.centralizer_le hUK hcC)
      exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hcB', hcN⟩)
  have hB'dec : B ⊔ Subgroup.zpowers c =
      ((B ⊔ Subgroup.zpowers c) ⊓ K) ⊔
        ((B ⊔ Subgroup.zpowers c) ⊓ Subgroup.normalizer (U : Set Ω)) := by
    apply le_antisymm
    · have hmono : (B ⊓ K) ⊔ (B ⊓ Subgroup.normalizer (U : Set Ω)) ≤
          ((B ⊔ Subgroup.zpowers c) ⊓ K) ⊔
            ((B ⊔ Subgroup.zpowers c) ⊓ Subgroup.normalizer (U : Set Ω)) :=
        sup_le ((inf_le_inf le_sup_left le_rfl).trans le_sup_left)
          ((inf_le_inf le_sup_left le_rfl).trans le_sup_right)
      exact sup_le (hBdec.trans hmono) (Subgroup.zpowers_le.mpr hcdec)
    · exact sup_le inf_le_left inf_le_left
  have hB'NK : B ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (K : Set Ω) := by
    refine sup_le (B_le_normalizer_K hcfg hF hn hd hpq hP I hK hB) (Subgroup.zpowers_le.mpr ?_)
    rcases hIpair with ⟨haI, ha'I⟩ | ⟨haI, ha'I⟩
    · have hcK : c ∈ K := by
        have := pair_element_mem_K hcfg hF hn hP I hK X' hX'SU haI ha'I ω hXD'
        simpa [c] using this
      exact Subgroup.le_normalizer (H := K) hcK
    · have hcC : c ∈ Subgroup.centralizer (K : Set Ω) := by
        have := pair_element_centralizes_K hcfg hF hn hP I hK X' hX'SU haI ha'I ω hXD'
        simpa [c] using this
      exact Subgroup.centralizer_le_normalizer (K : Set Ω) hcC
  exact ⟨B ⊔ Subgroup.zpowers c, U, hB'elem, hB'le, hBle, hBne, hUne, hU2, hUK, hB'dec, hB'NK⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
