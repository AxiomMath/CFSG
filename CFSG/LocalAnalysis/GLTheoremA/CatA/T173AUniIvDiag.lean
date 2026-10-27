module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly
open scoped MatrixGroups

@[expose] def diagHom (d : ℕ) (F : Type) [Field F] : (Fin d → Fˣ) →* GL (Fin d) F where
  toFun f :=
    ⟨Matrix.diagonal fun i => (f i : F), Matrix.diagonal fun i => ((f i)⁻¹ : F),
      by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one,
          Matrix.diagonal_injective.eq_iff]
        funext i
        simpa using (f i).mul_inv,
      by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one,
          Matrix.diagonal_injective.eq_iff]
        funext i
        simpa using (f i).inv_mul⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' f g := by
    apply Units.ext
    simp [Matrix.diagonal_mul_diagonal]

@[simp] private theorem coe_diagHom {d : ℕ} {F : Type} [Field F] (f : Fin d → Fˣ) :
    ((diagHom d F f : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal fun i => (f i : F) := rfl

@[expose] def prodUnits (d : ℕ) (F : Type) [Field F] : (Fin d → Fˣ) →* Fˣ where
  toFun f := ∏ i, f i
  map_one' := Finset.prod_const_one
  map_mul' f g := by
    simpa only [Pi.mul_apply] using
      (Finset.prod_mul_distrib (s := Finset.univ) (f := f) (g := g))

@[expose] def diagPTorsion (p d : ℕ) (F : Type) [Field F] : Subgroup (Fin d → Fˣ) :=
  (powMonoidHom p).ker ⊓ (prodUnits d F).ker

@[expose] def diagPGroup (p d : ℕ) (F : Type) [Field F] : Subgroup (GL (Fin d) F) :=
  (diagPTorsion p d F).map (diagHom d F)

private theorem diagHom_mem_UniSU {n d : ℕ} {F : Type} [Field F] {f : Fin d → Fˣ}
    (hq0 : 2 ^ n ≠ 0)
    (hpow : ∀ i, (f i : F) ^ (2 ^ n + 1) = 1)
    (hdet : ∏ i, (f i : F) = 1) :
    diagHom d F f ∈ UniSU n d F := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [coe_diagHom, Matrix.det_diagonal]
    exact hdet
  · rw [coe_diagHom, Matrix.diagonal_map (by simp [hq0]), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one,
      Matrix.diagonal_injective.eq_iff]
    funext i
    rw [← pow_succ]
    exact hpow i

private theorem diagPGroup_le_UniSU {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : UniArith p n d F) : diagPGroup p d F ≤ UniSU n d F := by
  intro x hx
  obtain ⟨f, hfT, rfl⟩ := Subgroup.mem_map.mp hx
  have hfp : f ^ p = 1 := (Subgroup.mem_inf.mp hfT).1
  have hfprod : ∏ i, f i = 1 := (Subgroup.mem_inf.mp hfT).2
  have hq0 : 2 ^ n ≠ 0 := by positivity
  have hpow : ∀ i, (f i : F) ^ (2 ^ n + 1) = 1 := by
    intro i
    have hfpi : (f i) ^ p = 1 := by
      have := congrFun hfp i
      simpa using this
    have hfpiF : (f i : F) ^ p = 1 := by
      simpa using congrArg (fun u : Fˣ => (u : F)) hfpi
    obtain ⟨m, hm⟩ := h.2.1
    rw [hm, pow_mul, hfpiF, one_pow]
  have hdet : ∏ i, (f i : F) = 1 := by
    simpa using congrArg (fun u : Fˣ => (u : F)) hfprod
  exact diagHom_mem_UniSU hq0 hpow hdet

private theorem diagPGroup_pow {p d : ℕ} {F : Type} [Field F] {x : GL (Fin d) F}
    (hx : x ∈ diagPGroup p d F) : x ^ p = 1 := by
  obtain ⟨f, hfT, rfl⟩ := Subgroup.mem_map.mp hx
  have hfp : f ^ p = 1 := (Subgroup.mem_inf.mp hfT).1
  rw [← map_pow, hfp, map_one]

private theorem diagPGroup_comm {p d : ℕ} {F : Type} [Field F] {x y : GL (Fin d) F}
    (hx : x ∈ diagPGroup p d F) (hy : y ∈ diagPGroup p d F) : x * y = y * x := by
  obtain ⟨f, hfT, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨g, hgT, rfl⟩ := Subgroup.mem_map.mp hy
  rw [← map_mul, ← map_mul, mul_comm f g]

private theorem diagPGroup_diag {p d : ℕ} {F : Type} [Field F] {x : GL (Fin d) F}
    (hx : x ∈ diagPGroup p d F) {i j : Fin d} (hij : i ≠ j) :
    (x : Matrix (Fin d) (Fin d) F) i j = 0 := by
  obtain ⟨f, _, rfl⟩ := Subgroup.mem_map.mp hx
  rw [coe_diagHom]
  exact Matrix.diagonal_apply_ne _ hij

def pairUnit {d : ℕ} {F : Type} [Field F] (i j : Fin d) (u v : Fˣ) : Fin d → Fˣ :=
  fun k => if k = i then u else if k = j then v else 1

theorem pairUnit_self {d : ℕ} {F : Type} [Field F] {i j : Fin d} (u v : Fˣ) :
    pairUnit i j u v i = u := by simp [pairUnit]

theorem pairUnit_other {d : ℕ} {F : Type} [Field F] {i j : Fin d} (hij : i ≠ j)
    (u v : Fˣ) : pairUnit i j u v j = v := by
  have hji : j ≠ i := fun h => hij h.symm
  simp [pairUnit, hji]

theorem pairUnit_ne {d : ℕ} {F : Type} [Field F] {i j k : Fin d} (hki : k ≠ i)
    (hkj : k ≠ j) (u v : Fˣ) : pairUnit i j u v k = 1 := by simp [pairUnit, hki, hkj]

theorem pairUnit_pow {d : ℕ} {F : Type} [Field F] {i j : Fin d} (u v : Fˣ) (k : ℕ) :
    pairUnit i j u v ^ k = pairUnit i j (u ^ k) (v ^ k) := by
  funext x
  simp only [Pi.pow_apply, pairUnit]
  split_ifs <;> simp_all

theorem pairUnit_mem_diagPTorsion {p d : ℕ} {F : Type} [Field F] {i j : Fin d}
    (hij : i ≠ j) {u v : Fˣ} (hu : u ^ p = 1) (hv : v ^ p = 1) (huv : u * v = 1) :
    pairUnit i j u v ∈ diagPTorsion p d F := by
  rw [diagPTorsion, Subgroup.mem_inf]
  constructor
  · rw [MonoidHom.mem_ker]
    funext k
    by_cases hki : k = i
    · simp [powMonoidHom_apply, pairUnit, hki, hu]
    · by_cases hkj : k = j
      · have hji : j ≠ i := fun h => hki (hkj.trans h)
        simp [powMonoidHom_apply, pairUnit, hki, hkj, hji, hv]
      · simp [powMonoidHom_apply, pairUnit, hki, hkj]
  · rw [MonoidHom.mem_ker]
    show Finset.univ.prod (pairUnit i j u v) = 1
    let s : Finset (Fin d) := {i, j}
    have h1 : s.prod (pairUnit i j u v) = u * v := by
      dsimp [s]
      rw [Finset.prod_insert (by simp [hij]), Finset.prod_singleton]
      rw [pairUnit_self, pairUnit_other hij]
    rw [← Finset.prod_subset (s₁ := s) (s₂ := Finset.univ)
      (f := pairUnit i j u v) (Finset.subset_univ s) (fun k _ hk => ?_), h1, huv]
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact pairUnit_ne hk.1 hk.2 u v

def permGL {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d)) : GL (Fin d) F :=
  ⟨σ.permMatrix F, (σ⁻¹).permMatrix F,
    by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
    by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

@[simp] private theorem coe_permGL {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d)) :
    ((permGL σ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = σ.permMatrix F := rfl

theorem permMatrix_apply' {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d))
    (i j : Fin d) : σ.permMatrix F i j = if σ i = j then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]

theorem permMatrix_map_pow {n d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d))
    (hq0 : 2 ^ n ≠ 0) : (σ.permMatrix F).map (· ^ (2 ^ n)) = σ.permMatrix F := by
  ext i j
  rw [Matrix.map_apply, permMatrix_apply']
  by_cases h : σ i = j
  · simp [h]
  · rw [if_neg h]
    exact zero_pow hq0

theorem swap_permGL_mem_UniSU {n d : ℕ} {F : Type} [Field F] [CharP F 2]
    (hq0 : 2 ^ n ≠ 0) {b b' : Fin d} (hbb' : b ≠ b') :
    permGL (Equiv.swap b b') ∈ UniSU n d F := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [coe_permGL, Matrix.det_permutation, Equiv.Perm.sign_swap hbb']
    have : ((-1 : ℤˣ) : F) = (-1 : F) := by simp
    rw [this]
    exact CharTwo.neg_eq 1
  · rw [coe_permGL, permMatrix_map_pow (Equiv.swap b b') hq0,
      Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

theorem block_mul {d : ℕ} {F : Type} [Field F] {I : Finset (Fin d)} {g h : GL (Fin d) F}
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

theorem swap_permMatrix_block {d : ℕ} {F : Type} [Field F] {b b' : Fin d}
    {I : Finset (Fin d)} (hbI : b ∈ I) (hb'I : b' ∈ I) :
    ∀ i j, (i ∉ I ∨ j ∉ I) →
      ((permGL (Equiv.swap b b') : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j =
        if i = j then 1 else 0 := by
  have hswap_mem : ∀ x, x ∈ I → Equiv.swap b b' x ∈ I := by
    intro x hx
    by_cases hxb : x = b
    · subst hxb; rwa [Equiv.swap_apply_left]
    · by_cases hxb' : x = b'
      · subst hxb'; rwa [Equiv.swap_apply_right]
      · rwa [Equiv.swap_apply_of_ne_of_ne hxb hxb']
  intro i j hij
  rw [coe_permGL, permMatrix_apply']
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

theorem diagonal_comm_permMatrix_swap {d : ℕ} {F : Type} [Field F] {b b' : Fin d}
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

theorem det_eq_one_of_mem_UniSU {n d : ℕ} {F : Type} [Field F] {g : GL (Fin d) F}
    (hg : g ∈ UniSU n d F) : (g : Matrix (Fin d) (Fin d) F).det = 1 := by
  have hle : UniSU n d F ≤ (Matrix.GeneralLinearGroup.det : GL (Fin d) F →* Fˣ).ker := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simpa [MonoidHom.mem_ker, Units.ext_iff] using hx.1
  have hmem := hle hg
  rw [MonoidHom.mem_ker, Units.ext_iff] at hmem
  simpa using hmem

private theorem uniArith_charP_two {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : UniArith p n d F) : CharP F 2 := by
  have hn : 1 ≤ n := h.2.2.2.2.1
  have hcard : Nat.card F = (2 ^ n) ^ 2 := h.2.2.2.1
  have hring : ringChar F = 2 := by
    have h2dvd : 2 ∣ Nat.card F := by
      rw [hcard, sq]
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega : n ≠ 0)) _
    haveI := Fintype.ofFinite F
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
    exact Nat.dvd_iff_mod_eq_zero.mp h2dvd
  rw [← hring]
  exact ringChar.charP F

private theorem uniArith_p_ne_two {p n d : ℕ} {F : Type} [Field F]
    (h : UniArith p n d F) : p ≠ 2 := by
  intro hp2
  have hdvd : p ∣ 2 ^ n + 1 := h.2.1
  rw [hp2] at hdvd
  have hodd : Odd (2 ^ n + 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by
      have := h.2.2.2.2.1
      omega)
    rw [pow_succ]
    exact ⟨2 ^ m, by ring⟩
  exact hodd.not_two_dvd_nat hdvd

private theorem permGL_swap_sq {d : ℕ} {F : Type} [Field F] {b b' : Fin d} :
    permGL (F := F) (Equiv.swap b b') ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, sq, coe_permGL, ← Matrix.permMatrix_mul,
    Equiv.swap_mul_self, Matrix.permMatrix_one, Units.val_one]

private theorem permGL_swap_ne_one {d : ℕ} {F : Type} [Field F] {b b' : Fin d}
    (hbb' : b ≠ b') : permGL (F := F) (Equiv.swap b b') ≠ 1 := by
  intro h
  have hmat := congrArg (fun g : GL (Fin d) F =>
    ((g : Matrix (Fin d) (Fin d) F) b b')) h
  have hPb : ((permGL (Equiv.swap b b') : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) b b' = 1 := by
    change ((Equiv.swap b b').permMatrix F) b b' = 1
    rw [permMatrix_apply', Equiv.swap_apply_left, if_pos rfl]
  have h1b : ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) b b' = 0 := by
    rw [Units.val_one, Matrix.one_apply_ne hbb']
  rw [hPb, h1b] at hmat
  exact one_ne_zero hmat

private theorem permGL_swap_pow_mem_block {d : ℕ} {F : Type} [Field F]
    {b b' : Fin d} {I : Finset (Fin d)} (hbI : b ∈ I) (hb'I : b' ∈ I) (k : ℕ) :
    ∀ i j, (i ∉ I ∨ j ∉ I) →
      (((permGL (Equiv.swap b b')) ^ k : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) i j = if i = j then 1 else 0 := by
  have hP_block : ∀ i j, (i ∉ I ∨ j ∉ I) →
      ((permGL (Equiv.swap b b') : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) i j = if i = j then 1 else 0 :=
    swap_permMatrix_block hbI hb'I
  induction k with
  | zero =>
      intro i j _
      simp [Matrix.one_apply]
  | succ k ih =>
      intro i j hij
      have h1 := block_mul ih hP_block i j hij
      simpa [pow_succ] using h1

private theorem permGL_swap_zpowers_isPGroup {d : ℕ} {F : Type} [Field F] [Finite F]
    {b b' : Fin d} :
    IsPGroup 2 (Subgroup.zpowers (permGL (F := F) (Equiv.swap b b'))) := by
  intro g
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (g : GL (Fin d) F)
    (permGL (Equiv.swap b b'))).mp (by
      rw [mem_powers_iff_mem_zpowers]
      exact g.2)
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, show (2 : ℕ) ^ 1 = 2 from rfl, ← hk]
  calc (permGL (Equiv.swap b b') ^ k) ^ 2
      = permGL (Equiv.swap b b') ^ (k * 2) := by rw [pow_mul]
    _ = permGL (Equiv.swap b b') ^ (2 * k) := by rw [Nat.mul_comm k 2]
    _ = (permGL (Equiv.swap b b') ^ 2) ^ k := by rw [pow_mul]
    _ = 1 := by rw [permGL_swap_sq, one_pow]

private theorem permGL_swap_zpowers_mem_block {n d : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {b b' : Fin d} {I : Finset (Fin d)} (hq0 : 2 ^ n ≠ 0) (hbI : b ∈ I)
    (hb'I : b' ∈ I) (hbb' : b ≠ b')
    {u : GL (Fin d) F} (hu : u ∈ Subgroup.zpowers (permGL (F := F) (Equiv.swap b b'))) :
    u ∈ UniBlockSet n d F I := by
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff u
    (permGL (Equiv.swap b b'))).mp (by
      rw [mem_powers_iff_mem_zpowers]
      exact hu)
  refine ⟨?_, ?_⟩
  · rw [← hk]
    exact Subgroup.pow_mem _ (swap_permGL_mem_UniSU hq0 hbb') k
  · rw [← hk]
    exact permGL_swap_pow_mem_block hbI hb'I k

private theorem exists_pair_pow_eq {p d : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hp_ne_two : p ≠ 2) {ω : Fˣ} (hωorder : orderOf ω = p)
    {f : Fin d → Fˣ} (hfp : f ^ p = 1) (b b' : Fin d) :
    ∃ k : ℕ, ω ^ k * ω ^ k = f b * (f b')⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hωp : ω ^ p = 1 := by simpa [hωorder] using pow_orderOf_eq_one ω
  have hωprim : IsPrimitiveRoot ω p := IsPrimitiveRoot.iff_orderOf.mpr hωorder
  have hgen : Subgroup.zpowers ω = rootsOfUnity p F := IsPrimitiveRoot.zpowers_eq hωprim
  have hfb : (f b) ^ p = 1 := by
    have := congrFun hfp b
    simpa using this
  have hfb' : (f b') ^ p = 1 := by
    have := congrFun hfp b'
    simpa using this
  let r : Fˣ := f b * (f b')⁻¹
  have hr_root : r ∈ rootsOfUnity p F := by
    rw [mem_rootsOfUnity]
    dsimp [r]
    rw [mul_pow, inv_pow, hfb, hfb', inv_one, mul_one]
  have hr_mem : r ∈ Subgroup.zpowers ω := by rw [hgen]; exact hr_root
  have hr_pow : r ∈ Submonoid.powers ω := by
    rwa [mem_powers_iff_mem_zpowers]
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff r ω).mp hr_pow
  have hodd : Odd p := hp.odd_of_ne_two hp_ne_two
  obtain ⟨t, ht⟩ := hodd
  let k : ℕ := m * ((p + 1) / 2)
  have hk2 : k * 2 = m * (p + 1) := by
    dsimp [k]
    have hdiv : (p + 1) / 2 = t + 1 := by omega
    rw [hdiv, ht]
    ring
  have hωp1 : ω ^ (p + 1) = ω := by rw [pow_succ, hωp, one_mul]
  refine ⟨k, ?_⟩
  rw [← pow_two, ← pow_mul, hk2, Nat.mul_comm m (p + 1), pow_mul, hωp1, hm]

private theorem pair_pow_inv_mul_apply_eq {d : ℕ} {F : Type} [Field F]
    {b b' : Fin d} (hbb' : b ≠ b') {ω : Fˣ} {k : ℕ} {f : Fin d → Fˣ}
    (hα2 : ω ^ k * ω ^ k = f b * (f b')⁻¹) :
    ((pairUnit b b' ω ω⁻¹ ^ k)⁻¹ * f) b =
      ((pairUnit b b' ω ω⁻¹ ^ k)⁻¹ * f) b' := by
  have hα2' : ω ^ k * ω ^ k * f b' = f b := by
    rw [hα2]
    group
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [show (pairUnit b b' ω ω⁻¹ ^ k) b = ω ^ k by
        rw [pairUnit_pow, pairUnit_self],
      show (pairUnit b b' ω ω⁻¹ ^ k) b' = (ω⁻¹) ^ k by
        rw [pairUnit_pow, pairUnit_other hbb']]
  rw [inv_pow, inv_inv]
  calc (ω ^ k)⁻¹ * f b = (ω ^ k)⁻¹ * (ω ^ k * ω ^ k * f b') := by rw [hα2']
    _ = ω ^ k * f b' := by group

private theorem diagHom_mul_permGL_swap_comm {d : ℕ} {F : Type} [Field F]
    {b b' : Fin d} {f : Fin d → Fˣ} (hfb : f b = f b') :
    diagHom d F f * permGL (Equiv.swap b b') =
      permGL (Equiv.swap b b') * diagHom d F f := by
  apply Units.ext
  change (Matrix.diagonal fun i => (f i : F)) * (Equiv.swap b b').permMatrix F =
    (Equiv.swap b b').permMatrix F * Matrix.diagonal fun i => (f i : F)
  exact diagonal_comm_permMatrix_swap (h := fun i => (f i : F)) (congrArg Units.val hfb)

private theorem diag_pair_pow_mem_block {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : UniArith p n d F) {A' : Subgroup (GL (Fin d) F)} (hA'le_D : A' ≤ diagPGroup p d F)
    {I : Finset (Fin d)} {b b' : Fin d} (hbI : b ∈ I) (hb'I : b' ∈ I)
    {ω : Fˣ} (hvbb : diagHom d F (pairUnit b b' ω ω⁻¹) ∈ A') (k : ℕ) :
    (diagHom d F (pairUnit b b' ω ω⁻¹)) ^ k ∈ A' ∧
      (diagHom d F (pairUnit b b' ω ω⁻¹)) ^ k ∈ UniBlockSet n d F I := by
  have hmmA' : (diagHom d F (pairUnit b b' ω ω⁻¹)) ^ k ∈ A' :=
    Subgroup.pow_mem A' hvbb k
  refine ⟨hmmA', ?_⟩
  have hmm_eq : (diagHom d F (pairUnit b b' ω ω⁻¹)) ^ k =
      diagHom d F (pairUnit b b' (ω ^ k) ((ω⁻¹) ^ k)) := by
    rw [← map_pow, pairUnit_pow]
  refine ⟨diagPGroup_le_UniSU h (hA'le_D hmmA'), ?_⟩
  intro i j hij
  rw [hmm_eq, coe_diagHom, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp only [if_pos rfl]
    have hi : i ∉ I := hij.elim id id
    have hib : i ≠ b := fun hh => hi (hh ▸ hbI)
    have hib' : i ≠ b' := fun hh => hi (hh ▸ hb'I)
    rw [show pairUnit b b' (ω ^ k) ((ω⁻¹) ^ k) i = 1 by
      simp [pairUnit, hib, hib']]
    simp
  · rw [if_neg h, if_neg h]

private theorem exists_diag_split_of_mem {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : UniArith p n d F) {A' : Subgroup (GL (Fin d) F)} (hA'le_D : A' ≤ diagPGroup p d F)
    {I : Finset (Fin d)} {b b' : Fin d} (hbI : b ∈ I) (hb'I : b' ∈ I) (hbb' : b ≠ b')
    {ω : Fˣ} (hωorder : orderOf ω = p)
    (hvbb : diagHom d F (pairUnit b b' ω ω⁻¹) ∈ A')
    {a : GL (Fin d) F} (ha : a ∈ A') :
    ∃ m ∈ A', m ∈ UniBlockSet n d F I ∧
      ∃ c ∈ A', c ∈ Subgroup.normalizer
        (Subgroup.zpowers (permGL (F := F) (Equiv.swap b b')) : Set (GL (Fin d) F)) ∧
        a = m * c := by
  obtain ⟨f, hfT, hf_eq⟩ := Subgroup.mem_map.mp (hA'le_D ha)
  have hfp : f ^ p = 1 := (Subgroup.mem_inf.mp hfT).1
  obtain ⟨k, hk2⟩ := exists_pair_pow_eq h.1 (uniArith_p_ne_two h) hωorder hfp b b'
  let mm : GL (Fin d) F := (diagHom d F (pairUnit b b' ω ω⁻¹)) ^ k
  obtain ⟨hmmA', hmm_block⟩ := diag_pair_pow_mem_block h hA'le_D hbI hb'I hvbb k
  let cc : GL (Fin d) F := mm⁻¹ * a
  have hccA' : cc ∈ A' := by
    dsimp [cc]
    exact Subgroup.mul_mem A' (Subgroup.inv_mem A' hmmA') ha
  have hcc_eq : cc = diagHom d F ((pairUnit b b' ω ω⁻¹ ^ k)⁻¹ * f) := by
    dsimp [cc, mm]
    rw [← hf_eq, ← map_pow, ← map_inv, ← map_mul]
  have hEq_unit : ((pairUnit b b' ω ω⁻¹ ^ k)⁻¹ * f) b =
      ((pairUnit b b' ω ω⁻¹ ^ k)⁻¹ * f) b' :=
    pair_pow_inv_mul_apply_eq hbb' hk2
  have hcomm : cc * permGL (Equiv.swap b b') = permGL (Equiv.swap b b') * cc := by
    rw [hcc_eq]
    exact diagHom_mul_permGL_swap_comm hEq_unit
  have hccN : cc ∈ Subgroup.normalizer
      (Subgroup.zpowers (permGL (F := F) (Equiv.swap b b')) : Set (GL (Fin d) F)) := by
    have hcent : cc ∈ Subgroup.centralizer
        ({permGL (Equiv.swap b b')} : Set (GL (Fin d) F)) := by
      rwa [Subgroup.mem_centralizer_singleton_iff]
    have hcentU : cc ∈ Subgroup.centralizer
        (Subgroup.zpowers (permGL (F := F) (Equiv.swap b b')) : Set (GL (Fin d) F)) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hcent
    exact (Subgroup.centralizer_le_normalizer _) hcentU
  exact ⟨mm, hmmA', hmm_block, cc, hccA', hccN, by dsimp [cc]; group⟩

theorem uni_diag_decomp {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : UniArith p n d F) {A' : Subgroup (GL (Fin d) F)} (hA'le_D : A' ≤ diagPGroup p d F)
    (I : Finset (Fin d)) (hI : 2 ≤ I.card)
    (b b' : Fin d) (hbI : b ∈ I) (hb'I : b' ∈ I) (hbb' : b ≠ b')
    (ω : Fˣ) (hωorder : orderOf ω = p)
    (hvbb : diagHom d F (pairUnit b b' ω ω⁻¹) ∈ A') :
    ∃ U : Subgroup (GL (Fin d) F), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      (∀ u ∈ U, u ∈ UniBlockSet n d F I) ∧
      ∀ a ∈ A', ∃ m ∈ A', m ∈ UniBlockSet n d F I ∧
        ∃ c ∈ A', c ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)) ∧ a = m * c := by
  have hp : p.Prime := h.1
  have hn : 1 ≤ n := h.2.2.2.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F 2 := uniArith_charP_two h
  have hq0 : 2 ^ n ≠ 0 := by positivity
  let P : GL (Fin d) F := permGL (Equiv.swap b b')
  let U : Subgroup (GL (Fin d) F) := Subgroup.zpowers P
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · simpa [U, P] using (Subgroup.zpowers_ne_bot (g := P)).mpr (permGL_swap_ne_one hbb')
  · simpa [U, P] using permGL_swap_zpowers_isPGroup (b := b) (b' := b')
  · intro u hu
    exact permGL_swap_zpowers_mem_block hq0 hbI hb'I hbb' (by simpa [U, P] using hu)
  · intro a ha
    obtain ⟨m, hmA, hmblk, c, hcA, hcN, hamc⟩ :=
      exists_diag_split_of_mem h hA'le_D hbI hb'I hbb' hωorder hvbb ha
    exact ⟨m, hmA, hmblk, c, hcA, by simpa [U, P] using hcN, hamc⟩

private theorem uni_iv_diag_core {p n d : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (h : UniArith p n d F) {A : Subgroup (GL (Fin d) F)} (hA : A ≤ UniSU n d F)
    (hAe : IsElemAbelian p A)
    (hAd : ∀ a ∈ A, ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0)
    (I : Finset (Fin d)) (hI : 2 ≤ I.card)
    (b b' : Fin d) (hbI : b ∈ I) (hb'I : b' ∈ I) (hbb' : b ≠ b')
    (ω : Fˣ) (hωorder : orderOf ω = p)
    (v : GL (Fin d) F) (hvD : v ∈ diagPGroup p d F) (hvnotA : v ∉ A)
    (hvbb : diagHom d F (pairUnit b b' ω ω⁻¹) ∈ A ⊔ Subgroup.zpowers v) :
    ∃ A' U : Subgroup (GL (Fin d) F), A ≤ A' ∧ A ≠ A' ∧ A' ≤ UniSU n d F ∧
      IsElemAbelian p A' ∧
      (∀ a ∈ A', ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0) ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ u ∈ U, u ∈ UniBlockSet n d F I) ∧
      ∀ a ∈ A', ∃ m ∈ A', m ∈ UniBlockSet n d F I ∧
        ∃ c ∈ A', c ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)) ∧ a = m * c := by
  have hp : p.Prime := h.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hA_le_D : A ≤ diagPGroup p d F := by
    intro a ha
    have hdiag : (a : Matrix (Fin d) (Fin d) F) = Matrix.diagonal (fun i => a i i) := by
      ext i j
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ hij]; exact hAd a ha i j hij
    have hdet_ne : (a : Matrix (Fin d) (Fin d) F).det ≠ 0 := by
      simpa using (Matrix.GeneralLinearGroup.det a).ne_zero
    have hne : ∀ i, (a : Matrix (Fin d) (Fin d) F) i i ≠ 0 := by
      intro i hi0
      apply hdet_ne
      rw [hdiag, Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi0
    let f : Fin d → Fˣ :=
      fun i => Units.mk0 ((a : Matrix (Fin d) (Fin d) F) i i) (hne i)
    have hf_eq : diagHom d F f = a := by
      apply Units.ext
      rw [coe_diagHom, hdiag]
      rfl
    have hfT : f ∈ diagPTorsion p d F := by
      rw [diagPTorsion, Subgroup.mem_inf]
      constructor
      · rw [MonoidHom.mem_ker]
        have hap : a ^ p = 1 := hAe.2 a ha
        have h1 : diagHom d F (f ^ p) = 1 := by
          rw [map_pow, hf_eq, hap]
        funext i
        have h2 := congrArg (fun g : GL (Fin d) F =>
          ((g : Matrix (Fin d) (Fin d) F) i i)) h1
        rw [coe_diagHom, Matrix.diagonal_apply_eq, Units.val_one,
          Matrix.one_apply_eq] at h2
        exact Units.ext (by simpa using h2)
      · rw [MonoidHom.mem_ker]
        show (∏ i, f i) = 1
        have hdet_a : (a : Matrix (Fin d) (Fin d) F).det = 1 :=
          det_eq_one_of_mem_UniSU (hA ha)
        have hprodF : ∏ i, (f i : F) = 1 := by
          have hdet_diag : ((diagHom d F f : GL (Fin d) F) :
              Matrix (Fin d) (Fin d) F).det = ∏ i, (f i : F) := by
            rw [coe_diagHom, Matrix.det_diagonal]
          rw [← hf_eq] at hdet_a
          rwa [hdet_diag] at hdet_a
        apply Units.ext
        simpa using hprodF
    rw [diagPGroup]
    exact Subgroup.mem_map.mpr ⟨f, hfT, hf_eq⟩
  let A' : Subgroup (GL (Fin d) F) := A ⊔ Subgroup.zpowers v
  have hA'le_D : A' ≤ diagPGroup p d F := by
    dsimp [A']
    exact sup_le hA_le_D (Subgroup.zpowers_le_of_mem hvD)
  obtain ⟨U, hUbot, hU2, hUblk, hdec⟩ :=
    uni_diag_decomp h hA'le_D I hI b b' hbI hb'I hbb' ω hωorder hvbb
  refine ⟨A', U, le_sup_left, ?_, ?_, ?_, ?_, hUbot, hU2, hUblk, hdec⟩
  · intro hEq
    apply hvnotA
    rw [hEq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  · exact hA'le_D.trans (diagPGroup_le_UniSU h)
  · constructor
    · rw [isMulCommutative_iff]
      intro x y
      apply Subtype.ext
      exact diagPGroup_comm (hA'le_D x.2) (hA'le_D y.2)
    · intro x hx
      exact diagPGroup_pow (hA'le_D hx)
  · intro a ha i j hij
    exact diagPGroup_diag (hA'le_D ha) hij

theorem uni_iv_diag {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : UniArith p n d F)
    {A : Subgroup (GL (Fin d) F)} (hA : A ≤ UniSU n d F) (hAe : IsElemAbelian p A)
    (hAd : ∀ a ∈ A, ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0)
    (hrep : ∃ i j : Fin d, i ≠ j ∧ ∀ a ∈ A,
      (a : Matrix (Fin d) (Fin d) F) i i = (a : Matrix (Fin d) (Fin d) F) j j)
    (I : Finset (Fin d)) (hI : 2 ≤ I.card) :
    ∃ A' U : Subgroup (GL (Fin d) F), A ≤ A' ∧ A ≠ A' ∧ A' ≤ UniSU n d F ∧
      IsElemAbelian p A' ∧
      (∀ a ∈ A', ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0) ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ u ∈ U, u ∈ UniBlockSet n d F I) ∧
      ∀ a ∈ A', ∃ m ∈ A', m ∈ UniBlockSet n d F I ∧
        ∃ c ∈ A', c ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)) ∧ a = m * c := by
  have hp : p.Prime := h.1
  have hn : 1 ≤ n := h.2.2.2.2.1
  have hchar : ringChar F = 2 := by
    have h2dvd : 2 ∣ Nat.card F := by
      rw [h.2.2.2.1, sq]
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega : n ≠ 0)) _
    haveI := Fintype.ofFinite F
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
    exact Nat.dvd_iff_mod_eq_zero.mp h2dvd
  haveI : CharP F 2 := ringChar.of_eq hchar
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have hdvd : p ∣ 2 ^ n + 1 := h.2.1
    rw [hp2] at hdvd
    have hodd : Odd (2 ^ n + 1) := by
      have hpow2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega]
        rw [pow_succ]
        ring
      rw [hpow2]
      exact ⟨2 ^ (n - 1), by ring⟩
    exact hodd.not_two_dvd_nat hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_dvd_card : p ∣ Nat.card Fˣ := by
    have h2dvd_sq : p ∣ (2 ^ n) ^ 2 - 1 := by
      have hmod : ((2 ^ n) ^ 2 : ℕ) ≡ 1 [MOD p] := by
        rw [← ZMod.natCast_eq_natCast_iff]
        have h1 : ((2 ^ n + 1 : ℕ) : ZMod p) = 0 := by
          obtain ⟨k, hk⟩ := h.2.1
          rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
        have hx : ((2 ^ n : ℕ) : ZMod p) = -1 := by
          have h := congrArg (fun z : ZMod p => z - 1) h1
          rw [Nat.cast_add, Nat.cast_one] at h
          rwa [add_sub_cancel_right, zero_sub] at h
        have hsq : (((2 ^ n) ^ 2 : ℕ) : ZMod p) = ((2 ^ n : ℕ) : ZMod p) ^ 2 := by
          push_cast
          ring
        rw [hsq, hx]
        rw [show ((1 : ℕ) : ZMod p) = 1 by norm_num]
        exact neg_one_sq (R := ZMod p)
      have hmod' : 1 ≡ (2 ^ n) ^ 2 [MOD p] := hmod.symm
      rwa [Nat.modEq_iff_dvd' (Nat.one_le_pow 2 (2 ^ n) (by positivity))] at hmod'
    rw [Nat.card_units, h.2.2.2.1]
    exact h2dvd_sq
  obtain ⟨ω, hωorder⟩ := exists_prime_orderOf_dvd_card' p hp_dvd_card
  obtain ⟨b, hbI, b', hb'I, hbb'⟩ :=
    Finset.one_lt_card.mp (lt_of_lt_of_le (by norm_num : 1 < 2) hI)
  have hωp : ω ^ p = 1 := by simpa [hωorder] using pow_orderOf_eq_one ω
  have hωip : (ω⁻¹) ^ p = 1 := by rw [inv_pow, hωp, inv_one]
  have hvbbD : diagHom d F (pairUnit b b' ω ω⁻¹) ∈ diagPGroup p d F := by
    rw [diagPGroup]
    exact Subgroup.mem_map.mpr
      ⟨pairUnit b b' ω ω⁻¹, pairUnit_mem_diagPTorsion hbb' hωp hωip (mul_inv_cancel ω), rfl⟩
  by_cases hv : diagHom d F (pairUnit b b' ω ω⁻¹) ∈ A
  · obtain ⟨i, j, hij, hrepij⟩ := hrep
    have hvijD : diagHom d F (pairUnit i j ω ω⁻¹) ∈ diagPGroup p d F := by
      rw [diagPGroup]
      exact Subgroup.mem_map.mpr
        ⟨pairUnit i j ω ω⁻¹, pairUnit_mem_diagPTorsion hij hωp hωip (mul_inv_cancel ω), rfl⟩
    have hvij_notA : diagHom d F (pairUnit i j ω ω⁻¹) ∉ A := by
      intro hmem
      have hEq := hrepij (diagHom d F (pairUnit i j ω ω⁻¹)) hmem
      have hvii : ((diagHom d F (pairUnit i j ω ω⁻¹) : GL (Fin d) F) :
          Matrix (Fin d) (Fin d) F) i i = (ω : F) := by
        rw [coe_diagHom, Matrix.diagonal_apply_eq, pairUnit_self]
      have hvjj : ((diagHom d F (pairUnit i j ω ω⁻¹) : GL (Fin d) F) :
          Matrix (Fin d) (Fin d) F) j j = ((ω⁻¹ : Fˣ) : F) := by
        rw [coe_diagHom, Matrix.diagonal_apply_eq, pairUnit_other hij]
      rw [hvii, hvjj] at hEq
      have hω_ne_inv : ω ≠ ω⁻¹ := by
        intro hinv
        have h2 : ω ^ 2 = 1 := by
          rw [sq]
          nth_rewrite 1 [hinv]
          exact inv_mul_cancel ω
        have hdvd : orderOf ω ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
        rw [hωorder] at hdvd
        have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
        exact hp_ne_two (le_antisymm hle hp.two_le)
      exact (fun h => hω_ne_inv (Units.ext h)) hEq
    exact uni_iv_diag_core h hA hAe hAd I hI b b' hbI hb'I hbb' ω hωorder _
      hvijD hvij_notA (Subgroup.mem_sup_left hv)
  · exact uni_iv_diag_core h hA hAe hAd I hI b b' hbI hb'I hbb' ω hωorder _
      hvbbD hv (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
