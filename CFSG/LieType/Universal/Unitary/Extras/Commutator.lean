module

public import CFSG.LieType.Universal.Unitary.Extras.RankOneLast
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.LieType.Universal.Unitary.SUExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open scoped commutatorElement

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

@[expose] def cone {m : ℕ} (e f : Fin m → ℤ) : Set (Fin m → ℤ) :=
  {w | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ w = a • e + b • f}

section Cone

variable {m : ℕ} {e f u v : Fin m → ℤ}

theorem cone_add (hu : u ∈ cone e f) (hv : v ∈ cone e f) : u + v ∈ cone e f := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hu
  obtain ⟨a', b', ha', hb', rfl⟩ := hv
  exact ⟨a + a', b + b', by omega, by omega, by rw [add_nsmul, add_nsmul]; abel⟩

theorem cone_add_e (hu : u ∈ cone e f) : u + e ∈ cone e f := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hu
  exact ⟨a + 1, b, by omega, hb, by rw [add_nsmul, one_nsmul]; abel⟩

theorem cone_add_f (hu : u ∈ cone e f) : u + f ∈ cone e f := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hu
  exact ⟨a, b + 1, ha, by omega, by rw [add_nsmul, one_nsmul]; abel⟩

theorem two_nsmul_mem_cone (hu : u ∈ cone e f) : 2 • u ∈ cone e f := by
  rw [two_nsmul]
  exact cone_add hu hu

theorem mem_cone_of_wt2 {u v : Fin m → ℤ} (hu : u = e ∨ u = 2 • e) (hv : v = f ∨ v = 2 • f) :
    u + v ∈ cone e f := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact ⟨1, 1, one_pos, one_pos, by simp⟩
  · exact ⟨1, 2, one_pos, two_pos, by simp⟩
  · exact ⟨2, 1, two_pos, one_pos, by simp⟩
  · exact ⟨2, 2, two_pos, two_pos, rfl⟩

end Cone

variable (hσ : ∀ c, σ (σ c) = c)

theorem hasWt_mat_of_mem_rootGroup {γ : Fin (n / 2) → ℤ} {x : SU σ n}
    (hx : x ∈ rootGroup σ hσ n γ) :
    HasWt {w | w = 0 ∨ w = toStd n γ ∨ w = 2 • toStd n γ} (mat σ n x) := by
  have h1 : HasWt {w | w = 0 ∨ w = toStd n γ ∨ w = 2 • toStd n γ}
      (1 : Matrix (Fin n) (Fin n) F) := by
    intro a b hab
    have : a = b := by
      by_contra h
      exact hab (one_apply_ne h)
    subst this
    left
    exact sub_self _
  have h2 := (hasWt_of_mem_rootGroup hσ hx).mono (D := {w | w = 0 ∨ w = toStd n γ ∨
    w = 2 • toStd n γ}) fun w hw => Or.inr (mem_wt2.1 hw)
  have := h1.add h2
  rwa [add_sub_cancel] at this

theorem cone_add_zero_wt2 {m : ℕ} {e f u v : Fin m → ℤ} (hu : u ∈ cone e f)
    (hv : v = 0 ∨ v = e ∨ v = 2 • e) : u + v ∈ cone e f := by
  rcases hv with rfl | rfl | rfl
  · rwa [add_zero]
  · exact cone_add_e hu
  · rw [two_nsmul, ← add_assoc]
    exact cone_add_e (cone_add_e hu)

theorem cone_add_zero_wt2' {m : ℕ} {e f u v : Fin m → ℤ} (hu : u ∈ cone e f)
    (hv : v = 0 ∨ v = f ∨ v = 2 • f) : u + v ∈ cone e f := by
  rcases hv with rfl | rfl | rfl
  · rwa [add_zero]
  · exact cone_add_f hu
  · rw [two_nsmul, ← add_assoc]
    exact cone_add_f (cone_add_f hu)

theorem hasWt_commutator {γ δ : Fin (n / 2) → ℤ} {x y : SU σ n} (hx : x ∈ rootGroup σ hσ n γ)
    (hy : y ∈ rootGroup σ hσ n δ) :
    HasWt (cone (toStd n γ) (toStd n δ)) (mat σ n ⁅x, y⁆ - 1) := by
  set X := mat σ n x
  set Y := mat σ n y
  set X' := mat σ n x⁻¹
  set Y' := mat σ n y⁻¹
  have hXX : X * X' = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hYY : Y * Y' = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hc : mat σ n ⁅x, y⁆ - 1 = ((X - 1) * (Y - 1) - (Y - 1) * (X - 1)) * X' * Y' := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul]
    have e1 : ((X - 1) * (Y - 1) - (Y - 1) * (X - 1)) * X' * Y' =
        X * Y * X' * Y' - Y * (X * X') * Y' := by noncomm_ring
    rw [e1, hXX, Matrix.mul_one, hYY]
  rw [hc]
  have hA := hasWt_of_mem_rootGroup hσ hx
  have hB := hasWt_of_mem_rootGroup hσ hy
  have hAB : HasWt (cone (toStd n γ) (toStd n δ)) ((X - 1) * (Y - 1)) :=
    hA.mul hB fun a c b h1 h2 => by
      rw [show weight n a - weight n b = (weight n a - weight n c) + (weight n c - weight n b) by
        abel]
      exact mem_cone_of_wt2 (mem_wt2.1 h1) (mem_wt2.1 h2)
  have hBA : HasWt (cone (toStd n γ) (toStd n δ)) ((Y - 1) * (X - 1)) :=
    hB.mul hA fun a c b h1 h2 => by
      rw [show weight n a - weight n b = (weight n c - weight n b) + (weight n a - weight n c) by
        abel]
      exact mem_cone_of_wt2 (mem_wt2.1 h2) (mem_wt2.1 h1)
  have h1 : HasWt (cone (toStd n γ) (toStd n δ))
      (((X - 1) * (Y - 1) - (Y - 1) * (X - 1)) * X') :=
    (hAB.sub hBA).mul (hasWt_mat_of_mem_rootGroup hσ (inv_mem hx)) fun a c b h1 h2 => by
      rw [show weight n a - weight n b = (weight n a - weight n c) + (weight n c - weight n b) by
        abel]
      exact cone_add_zero_wt2 h1 h2
  exact h1.mul (hasWt_mat_of_mem_rootGroup hσ (inv_mem hy)) fun a c b h1 h2 => by
    rw [show weight n a - weight n b = (weight n a - weight n c) + (weight n c - weight n b) by
      abel]
    exact cone_add_zero_wt2' h1 h2

theorem exists_minor_ne_zero {m : ℕ} {e f : Fin m → ℤ}
    (hind : ∀ a b : ℤ, a • e + b • f = 0 → a = 0 ∧ b = 0) :
    ∃ s t, e s * f t - e t * f s ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨s0, hs0⟩ : ∃ s, e s ≠ 0 := by
    by_contra h'
    push Not at h'
    have := hind 1 0 (by funext c; simp [h' c])
    exact one_ne_zero this.1
  have := hind (f s0) (-e s0) (by
    funext t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination (-1 : ℤ) * h s0 t)
  exact hs0 (neg_eq_zero.mp this.2)

@[expose] def coneForm {m : ℕ} (e f : Fin m → ℤ) (s t : Fin m) : (Fin m → ℤ) →+ ℤ where
  toFun v := (e s * f t - e t * f s) * (v s * (f t - e t) + v t * (e s - f s))
  map_zero' := by simp
  map_add' v w := by
    simp only [Pi.add_apply]
    ring

theorem coneForm_pos {m : ℕ} {e f : Fin m → ℤ} {s t : Fin m}
    (hD : e s * f t - e t * f s ≠ 0) {w : Fin m → ℤ} (hw : w ∈ cone e f) :
    1 ≤ coneForm e f s t w := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hw
  have h1 : coneForm e f s t (a • e + b • f) =
      ((a : ℤ) + b) * ((e s * f t - e t * f s) * (e s * f t - e t * f s)) := by
    simp only [coneForm, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul]
    ring
  rw [h1]
  have h2 : 0 < (e s * f t - e t * f s) * (e s * f t - e t * f s) := mul_self_pos.mpr hD
  have h3 : (1 : ℤ) ≤ (a : ℤ) + b := by omega
  nlinarith

theorem mat_add_map_eq_zero_of_idBelow {s : Fin n → ℤ} (hs : ∀ i, s (Fin.rev i) = -s i)
    {d : ℤ} (hd : 1 ≤ d) {g : SU σ n} (hg : IdBelow s d (mat σ n g)) {p q : Fin n}
    (hpq : s q - s p = d) : mat σ n g p q + σ (mat σ n g (Fin.rev q) (Fin.rev p)) = 0 := by
  have hne : p ≠ q := by
    rintro rfl
    omega
  have hne' : Fin.rev p ≠ Fin.rev q := fun h => hne (Fin.rev_injective h)
  have h := sum_mat_mul_mat g (Fin.rev p) q
  rw [Fin.rev_rev, ite_eq_right (Ne.symm hne), sum_eq_two (Fin.rev p) (Fin.rev q) hne' (fun t h1 h2 =>
    by
      by_cases h3 : s (Fin.rev p) - s t < d
      · rw [hg t (Fin.rev p) h3, one_apply_ne h1, map_zero, zero_mul]
      · have h4 : s q - s (Fin.rev t) < d := by
          rw [hs] at h3 ⊢
          omega
        have h5 : Fin.rev t ≠ q := fun h => h2 (by rw [← h, Fin.rev_rev])
        rw [hg (Fin.rev t) q h4, one_apply_ne h5, mul_zero]),
    Fin.rev_rev, Fin.rev_rev, hg (Fin.rev p) (Fin.rev p) (by simp; omega), one_apply_eq,
    hg q q (by simp; omega), one_apply_eq, map_one, one_mul, mul_one] at h
  linear_combination h

theorem rootMatrix_apply_rev {p q : Fin n} (hpq : p ≠ q) (hqp : q ≠ Fin.rev p) (c : F) :
    rootMatrix σ p q c (Fin.rev q) (Fin.rev p) = -σ c := by
  have h1 : Fin.rev q ≠ Fin.rev p := fun h => hpq (Fin.rev_injective h).symm
  have h2 : ¬(p = Fin.rev q ∧ q = Fin.rev p) := fun h => hqp h.2
  simp [rootMatrix, one_apply_ne h1, h2]

theorem longRootMatrix_apply {i : Fin n} (hi : i ≠ Fin.rev i) (c : F) :
    longRootMatrix i c i (Fin.rev i) = c := by
  simp [longRootMatrix, one_apply_ne hi]

theorem heisenbergMatrix_apply_ik {i k : Fin n} (hik : i ≠ k) (hk : Fin.rev k = k)
    (a b : F) : heisenbergMatrix σ i k a b i k = a := by
  have h1 : Fin.rev i ≠ k := fun h => hik (by rw [← Fin.rev_rev i, h, hk])
  simp [heisenbergMatrix, one_apply_ne hik, Ne.symm hik, h1]

theorem heisenbergMatrix_apply_ki {i k : Fin n} (hik : i ≠ k) (hk : Fin.rev k = k)
    (a b : F) : heisenbergMatrix σ i k a b k (Fin.rev i) = -σ a := by
  have h1 : k ≠ Fin.rev i := fun h => hik (by rw [← Fin.rev_rev i, ← h, hk])
  simp [heisenbergMatrix, one_apply_ne h1, hik]

section Peel

variable {γ δ : Fin (n / 2) → ℤ}

theorem toStd_add' (v w : Fin (n / 2) → ℤ) : toStd n (v + w) = toStd n v + toStd n w :=
  (toStdLin n).map_add v w

theorem toStd_zero' : toStd n (0 : Fin (n / 2) → ℤ) = 0 := (toStdLin n).map_zero

theorem linIndep_toStd (hind : LinIndepPair γ δ) :
    ∀ a b : ℤ, a • toStd n γ + b • toStd n δ = 0 → a = 0 ∧ b = 0 := by
  intro a b h
  apply hind a b
  apply toStd_injective n
  rw [toStd_add', toStd_zsmul, toStd_zsmul, h, toStd_zero']

theorem exists_peel (htr : ∀ x, σ x = x → ∃ c, c + σ c = x) (φ : (Fin (n / 2) → ℤ) →+ ℤ)
    {d : ℤ} (hd : 1 ≤ d) {g : SU σ n}
    (hg : IdBelow (fun i => -φ (weight n i)) d (mat σ n g))
    (hgc : HasWt (cone (toStd n γ) (toStd n δ)) (mat σ n g - 1)) {a₀ b₀ : Fin n}
    (hlev : φ (weight n a₀ - weight n b₀) = d) (hne : mat σ n g a₀ b₀ ≠ 0) :
    ∃ ε ∈ openCone (roots (isFiniteType_cartan n) (divisible n)) γ δ, ∃ x ∈ rootGroup σ hσ n ε,
      toStd n ε = weight n a₀ - weight n b₀ ∧ ∀ a b, weight n a - weight n b =
        weight n a₀ - weight n b₀ → mat σ n x a b = mat σ n g a b := by
  set s : Fin n → ℤ := fun i => -φ (weight n i) with hsdef
  have hs : ∀ i, s (Fin.rev i) = -s i := fun i => by
    simp only [hsdef, weight_rev', map_neg, neg_neg]
  have hlv : ∀ a b, s b - s a = φ (weight n a - weight n b) := fun a b => by
    simp only [hsdef, map_sub]
    ring
  have hab₀ : a₀ ≠ b₀ := by
    rintro rfl
    rw [sub_self, map_zero] at hlev
    omega
  have hw₀ : weight n a₀ - weight n b₀ ∈ cone (toStd n γ) (toStd n δ) :=
    hgc a₀ b₀ (by rwa [Matrix.sub_apply, one_apply_ne hab₀, sub_zero])
  obtain ⟨ka, kb, hka, hkb, hkw⟩ := hw₀
  set ε : Fin (n / 2) → ℤ := ka • γ + kb • δ with hεdef
  have hε : toStd n ε = weight n a₀ - weight n b₀ := by
    rw [hεdef, toStd_add', toStd_nsmul, toStd_nsmul, hkw]
  have hεr : ε ∈ roots (isFiniteType_cartan n) (divisible n) :=
    mem_roots_of_weight_sub hab₀ hε.symm
  have hεc : ε ∈ openCone (roots (isFiniteType_cartan n) (divisible n)) γ δ :=
    ⟨hεr, ka, kb, hka, hkb, rfl⟩
  have hlead : ∀ p q, weight n p - weight n q = weight n a₀ - weight n b₀ →
      mat σ n g p q + σ (mat σ n g (Fin.rev q) (Fin.rev p)) = 0 := fun p q hpq =>
    mat_add_map_eq_zero_of_idBelow hs hd hg (by rw [hlv, hpq, hlev])
  refine ⟨ε, hεc, ?_⟩
  have hheis : ∀ {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k),
      weight n i = weight n a₀ - weight n b₀ →
      (∀ a b, weight n a - weight n b = weight n i → (a = i ∧ b = k) ∨ (a = k ∧ b = Fin.rev i)) →
      mat σ n g k (Fin.rev i) = -σ (mat σ n g i k) →
      ∃ x ∈ rootGroup σ hσ n ε, toStd n ε = weight n a₀ - weight n b₀ ∧ ∀ a b,
        weight n a - weight n b = weight n a₀ - weight n b₀ → mat σ n x a b = mat σ n g a b := by
    intro i k hi hik hk hwi hpos hki
    obtain ⟨β, hβ⟩ := htr (-(σ (mat σ n g i k) * mat σ n g i k)) (by
      rw [map_neg, map_mul, hσ, mul_comm])
    have hrel : β + σ β + σ (mat σ n g i k) * mat σ n g i k = 0 := by
      rw [hβ]
      ring
    refine ⟨heisRootElt hσ hi hik hk _ _ hrel, heisenberg_le hσ hi hik hk (by rw [hwi, hε])
      (heisRootElt_mem hσ hi hik hk _ _ hrel), hε, fun a b hab => ?_⟩
    rw [← hwi] at hab
    rcases hpos a b hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact heisenbergMatrix_apply_ik hik hk _ _
    · rw [hki]
      exact heisenbergMatrix_apply_ki hik hk _ _
  by_cases ha : Fin.rev a₀ = a₀
  ·
    have hb : b₀ ≠ Fin.rev b₀ := fun hb => hab₀ (middle_unique ha hb.symm)
    have hik : Fin.rev b₀ ≠ a₀ := fun h => hab₀ (show b₀ = a₀ by rw [← Fin.rev_rev b₀, h, ha]).symm
    refine hheis (rev_ne_rev_rev hb) hik ha ?_ (fun a b h => ?_) ?_
    · rw [weight_rev', weight_eq_zero_of_rev_eq ha, zero_sub]
    · rcases eq_of_weight_sub_eq_weight (rev_ne_rev_rev hb) ha h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · have h := hlead a₀ b₀ rfl
      rw [ha] at h
      rw [Fin.rev_rev]
      linear_combination h
  · have ha' : a₀ ≠ Fin.rev a₀ := fun h => ha h.symm
    by_cases hb : Fin.rev b₀ = b₀
    ·
      refine hheis ha' hab₀ hb ?_ (fun a b h => eq_of_weight_sub_eq_weight ha' hb h) ?_
      · rw [weight_eq_zero_of_rev_eq hb, sub_zero]
      · have h := hlead b₀ (Fin.rev a₀) (by
          rw [weight_eq_zero_of_rev_eq hb, weight_rev']
          abel)
        rw [Fin.rev_rev, hb] at h
        linear_combination h
    · have hb' : b₀ ≠ Fin.rev b₀ := fun h => hb h.symm
      by_cases hba : b₀ = Fin.rev a₀
      ·
        have hc : mat σ n g a₀ (Fin.rev a₀) + σ (mat σ n g a₀ (Fin.rev a₀)) = 0 := by
          have h := hlead a₀ (Fin.rev a₀) (by rw [hba])
          rwa [Fin.rev_rev] at h
        have hw2 : 2 • weight n a₀ = toStd n ε := by
          rw [hε, hba, weight_rev', sub_neg_eq_add, two_nsmul]
        refine ⟨longRootHom σ ha' (Multiplicative.ofAdd ⟨_, hc⟩),
          longRootHom_mem hσ ha' hw2 _, hε, fun a b hab => ?_⟩
        rw [hba, weight_rev', sub_neg_eq_add, ← two_nsmul] at hab
        obtain ⟨rfl, rfl⟩ := eq_of_weight_sub_eq_two_smul ha' hab
        rw [mat_apply (longRootHom _ _ _), coe_longRootHom, toAdd_ofAdd, longRootMatrix_apply ha']
      ·
        refine ⟨rootHom σ hσ hab₀ ha' hb' (Multiplicative.ofAdd (mat σ n g a₀ b₀)),
          rootHom_mem hσ hab₀ ha' hb' hba hε.symm _, hε, fun a b hab => ?_⟩
        rcases eq_of_weight_sub_eq_sub hab₀ ha' hb' hba hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [mat_apply (rootHom _ _ _ _ _ _), coe_rootHom, toAdd_ofAdd,
            rootMatrix_apply_pq hab₀ hba]
        · rw [mat_apply (rootHom _ _ _ _ _ _), coe_rootHom, toAdd_ofAdd,
            rootMatrix_apply_rev hab₀ hba]
          have h := hlead (Fin.rev b₀) (Fin.rev a₀) (by rw [weight_rev', weight_rev']; abel)
          rw [Fin.rev_rev, Fin.rev_rev] at h
          linear_combination -h

theorem mem_iSup_of_hasWt_cone (htr : ∀ x, σ x = x → ∃ c, c + σ c = x)
    (hind : LinIndepPair γ δ) {g : SU σ n}
    (hg : HasWt (cone (toStd n γ) (toStd n δ)) (mat σ n g - 1)) :
    g ∈ ⨆ ε ∈ openCone (roots (isFiniteType_cartan n) (divisible n)) γ δ,
      rootGroup σ hσ n ε := by
  set V := ⨆ ε ∈ openCone (roots (isFiniteType_cartan n) (divisible n)) γ δ,
    rootGroup σ hσ n ε with hVdef
  set C := cone (toStd n γ) (toStd n δ) with hCdef
  obtain ⟨s₀, t₀, hD⟩ := exists_minor_ne_zero (linIndep_toStd hind)
  set φ := coneForm (toStd n γ) (toStd n δ) s₀ t₀ with hφdef
  set s : Fin n → ℤ := fun i => -φ (weight n i) with hsdef
  have hlv : ∀ a b, s b - s a = φ (weight n a - weight n b) := fun a b => by
    simp only [hsdef, map_sub]
    ring
  have hpos : ∀ w ∈ C, 1 ≤ φ w := fun w hw => coneForm_pos hD hw
  have hmemV : ∀ ε ∈ openCone (roots (isFiniteType_cartan n) (divisible n)) γ δ,
      ∀ x ∈ rootGroup σ hσ n ε, x ∈ V := fun ε hε x hx =>
    (le_iSup₂ (f := fun ε (_ : ε ∈ openCone (roots (isFiniteType_cartan n) (divisible n)) γ δ) =>
      rootGroup σ hσ n ε) ε hε) hx
  have hbelow1 : ∀ g : SU σ n, HasWt C (mat σ n g - 1) → IdBelow s 1 (mat σ n g) := by
    intro g hg a b hab
    have := hg.eq_zero_apply (a := a) (b := b) (fun hw => by
      have := hpos _ hw
      rw [hlv] at hab
      omega)
    rwa [Matrix.sub_apply, sub_eq_zero] at this
  set B : ℤ := 1 + 2 * ∑ i, |s i| with hBdef
  have hB : ∀ a b : Fin n, s b - s a < B := by
    intro a b
    have h1 : |s a| ≤ ∑ i, |s i| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (s i)) (Finset.mem_univ a)
    have h2 : |s b| ≤ ∑ i, |s i| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (s i)) (Finset.mem_univ b)
    have h3 := le_abs_self (s b)
    have h4 := neg_abs_le (s a)
    omega
  have step : ∀ d : ℤ, 1 ≤ d → (∀ g : SU σ n, HasWt C (mat σ n g - 1) →
      IdBelow s (d + 1) (mat σ n g) → g ∈ V) →
      ∀ g : SU σ n, HasWt C (mat σ n g - 1) → IdBelow s d (mat σ n g) → g ∈ V := by
    intro d hd ih
    have key : ∀ S : Finset (Fin n × Fin n), ∀ g : SU σ n, HasWt C (mat σ n g - 1) →
        IdBelow s d (mat σ n g) →
        (∀ a b, s b - s a = d → mat σ n g a b ≠ 0 → (a, b) ∈ S) → g ∈ V := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro g hgc hgd hS
        refine ih g hgc fun a b hab => ?_
        by_cases hab' : s b - s a < d
        · exact hgd a b hab'
        · have hd' : s b - s a = d := by omega
          have hab'' : a ≠ b := by
            rintro rfl
            omega
          rw [one_apply_ne hab'']
          by_contra hne
          exact Finset.notMem_empty _ (hS a b hd' hne)
      | insert pq S hpq ihS =>
        intro g hgc hgd hS
        by_cases hpqd : s pq.2 - s pq.1 = d ∧ mat σ n g pq.1 pq.2 ≠ 0
        · obtain ⟨ε, hε, x, hx, hεw, hagree⟩ :=
            exists_peel hσ htr φ hd hgd hgc (by rw [← hlv]; exact hpqd.1) hpqd.2
          have hw₀ : φ (toStd n ε) = d := by rw [hεw, ← hlv]; exact hpqd.1
          have hidX : ∀ y ∈ rootGroup σ hσ n ε, IdBelow s d (mat σ n y) := by
            intro y hy a b hab
            apply mat_apply_of_mem_rootGroup hσ hy
            · intro h
              rw [hlv, h, hw₀] at hab
              omega
            · intro h
              rw [hlv, h, map_nsmul, hw₀] at hab
              simp only [nsmul_eq_mul, Nat.cast_ofNat] at hab
              omega
          have hxinv := inv_mem hx
          have hxd := hidX x hx
          have hxid := hidX _ hxinv
          have hxinvd : ∀ a b, s b - s a = d → mat σ n x⁻¹ a b = -mat σ n x a b := by
            intro a b hab
            have hab' : a ≠ b := by
              rintro rfl
              omega
            have h1 : (mat σ n x * mat σ n x⁻¹) a b = (1 : Matrix (Fin n) (Fin n) F) a b := by
              rw [← map_mul, mul_inv_cancel, map_one]
            rw [mul_apply_of_idBelow s (by omega) hxd hxid hab' hab.le, one_apply_ne hab'] at h1
            linear_combination h1
          rw [show g = x * (x⁻¹ * g) from (mul_inv_cancel_left x g).symm]
          refine mul_mem (hmemV ε hε x hx) (ihS _ ?_ ?_ ?_)
          ·
            have hw₀C : toStd n ε ∈ C := by
              rw [hεw]
              exact hgc pq.1 pq.2 (by
                rw [Matrix.sub_apply, one_apply_ne (fun h => by
                  rw [hlv, h, sub_self, map_zero] at hpqd
                  omega), sub_zero]
                exact hpqd.2)
            have hX : HasWt C (mat σ n x⁻¹ - 1) := (hasWt_of_mem_rootGroup hσ hxinv).mono
              fun w hw => by
                rcases mem_wt2.1 hw with rfl | rfl
                · exact hw₀C
                · exact two_nsmul_mem_cone hw₀C
            have h : mat σ n (x⁻¹ * g) - 1 = (mat σ n x⁻¹ - 1) + (mat σ n g - 1) +
                (mat σ n x⁻¹ - 1) * (mat σ n g - 1) := by
              rw [map_mul]
              noncomm_ring
            rw [h]
            exact (hX.add hgc).add (hX.mul hgc fun a c b h1 h2 => by
              rw [show weight n a - weight n b = (weight n a - weight n c) +
                (weight n c - weight n b) by abel]
              exact cone_add h1 h2)
          · rw [map_mul]
            exact idBelow_mul s (by omega) hxid hgd
          · intro a b hab hne
            have hab' : a ≠ b := by
              rintro rfl
              omega
            rw [map_mul, mul_apply_of_idBelow s (by omega) hxid hgd hab' hab.le] at hne
            by_cases hw : weight n a - weight n b = weight n pq.1 - weight n pq.2
            · exfalso
              rw [hxinvd a b hab, hagree a b hw] at hne
              exact hne (neg_add_cancel _)
            · have h0 : mat σ n x⁻¹ a b = 0 := by
                rw [mat_apply_of_mem_rootGroup hσ hxinv (by rw [hεw]; exact hw) (fun h => by
                  rw [hlv, h, map_nsmul, hw₀] at hab
                  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hab
                  omega), one_apply_ne hab']
              rw [h0, zero_add] at hne
              rcases Finset.mem_insert.mp (hS a b hab hne) with h | h
              · exfalso
                apply hw
                rw [← h]
              · exact h
        · refine ihS g hgc hgd fun a b hab hne => ?_
          rcases Finset.mem_insert.mp (hS a b hab hne) with h | h
          · exfalso
            apply hpqd
            subst h
            exact ⟨hab, hne⟩
          · exact h
    exact fun g hgc hgd => key Finset.univ g hgc hgd fun a b _ _ => Finset.mem_univ _
  have main : ∀ t : ℕ, ∀ d : ℤ, 1 ≤ d → B - d ≤ t → ∀ g : SU σ n, HasWt C (mat σ n g - 1) →
      IdBelow s d (mat σ n g) → g ∈ V := by
    intro t
    induction t with
    | zero =>
      intro d hd hBd g hgc hgd
      have : g = 1 := by
        apply mat_injective
        rw [map_one]
        ext a b
        exact hgd a b (by have := hB a b; omega)
      rw [this]
      exact one_mem _
    | succ t ih =>
      intro d hd hBd g hgc hgd
      by_cases h : B - d ≤ t
      · exact ih d hd h g hgc hgd
      · exact step d hd (fun g' hgc' hgd' => ih (d + 1) (by omega) (by omega) g' hgc' hgd') g
          hgc hgd
  exact main (B - 1).toNat 1 le_rfl (by omega) g hg (hbelow1 g hg)

end Peel

theorem commutator_mem (htr : ∀ x, σ x = x → ∃ c, c + σ c = x) {γ δ : Fin (n / 2) → ℤ}
    (hind : LinIndepPair γ δ) {x y : SU σ n} (hx : x ∈ rootGroup σ hσ n γ)
    (hy : y ∈ rootGroup σ hσ n δ) :
    ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (roots (isFiniteType_cartan n) (divisible n)) γ δ,
      rootGroup σ hσ n ε :=
  mem_iSup_of_hasWt_cone hσ htr hind (hasWt_commutator hσ hx hy)

end CFSG.LieType.Universal.Unitary.SUExtras
