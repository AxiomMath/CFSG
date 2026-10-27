module

public import CFSG.LieType.Steinberg.CentralExt.WeylLift
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.CentralExt.AdjointClosed CFSG.LieType.Steinberg.CentralExt.WeylLift

namespace CFSG.LieType.Steinberg.CentralExt.FieldThree

theorem exists_sep_of_parity {τ : Tag} {k : Type} [Field k] (h2 : (2 : k) ≠ 0)
    {γ δ : Fin τ.rank → ℤ} (hv : ∃ j, ¬2 ∣ cartanCoord δ j)
    (huv : ∃ i, ¬2 ∣ (cartanCoord γ i - cartanCoord δ i)) :
    ∃ t : Fin τ.rank → kˣ, rootChar k γ t = 1 ∧ rootChar k δ t ≠ 1 := by
  obtain ⟨m, hmu, hmv⟩ := exists_even_odd hv huv
  refine ⟨tvec (-1) m, ?_, ?_⟩
  · rw [rootChar_tvec]
    exact Even.neg_one_zpow (even_iff_two_dvd.2 hmu)
  · rw [rootChar_tvec, Odd.neg_one_zpow (Int.not_even_iff_odd.1 fun h => hmv
      (even_iff_two_dvd.1 h))]
    intro h
    apply h2
    have := congrArg (fun u : kˣ => (u : k)) h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this

section F4Roots

theorem f4_symm (i j : Fin 4) : Tag.symmetrizedCartan .F4 i j =
    (!![4, -2, 0, 0; -2, 4, -2, 0; 0, -2, 2, -1; 0, 0, -1, 2] : Matrix (Fin 4) (Fin 4) ℤ) i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem f4_iform_eq (v w : Fin 4 → ℤ) : iform (τ := .F4) v w =
    4 * v 0 * w 0 - 2 * v 0 * w 1 - 2 * v 1 * w 0 + 4 * v 1 * w 1 - 2 * v 1 * w 2 - 2 * v 2 * w 1
      + 2 * v 2 * w 2 - v 2 * w 3 - v 3 * w 2 + 2 * v 3 * w 3 := by
  change ∑ i : Fin 4, ∑ j : Fin 4, v i * Tag.symmetrizedCartan .F4 i j * w j = _
  simp only [f4_symm, Fin.sum_univ_four]
  simp
  ring

theorem iform_self_dvd {τ : Tag} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (δ : Fin τ.rank → ℤ) :
    iform γ γ ∣ 2 * iform γ δ := by
  induction hγ generalizing δ with
  | basis j =>
    rw [iform_single_single, iform_single_left]
    exact ⟨∑ l, τ.cartan j l * δ l, by ring⟩
  | reflect i hv ih =>
    have h := ih (reflect τ i δ)
    rw [← iform_reflect i _ (reflect τ i δ), reflect_reflect] at h
    rw [iform_reflect]
    exact h

theorem f4_iform_self {v : Fin (Tag.rank .F4) → ℤ} (hv : IsRoot .F4 v) :
    iform v v = 2 ∨ iform v v = 4 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hv
  rw [hj]
  fin_cases j <;> decide

theorem f4_even_of_cartanCoord {z : Fin (Tag.rank .F4) → ℤ} (hz : ∀ i, 2 ∣ cartanCoord z i)
    (a : Fin (Tag.rank .F4)) : 2 ∣ z a := by
  have hrow : ∀ i : Fin 4, 2 ∣ ∑ j : Fin 4, Tag.cartan .F4 i j * z j := hz
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  have h3 := hrow 3
  simp only [Fin.sum_univ_four, Tag.cartan] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  have key : ∀ a : Fin 4, 2 ∣ z a := by
    intro a
    fin_cases a <;> simp <;> omega
  exact key a

theorem f4_not_isRoot_of_orth {a b : Fin (Tag.rank .F4) → ℤ} (ha : iform a a = 4)
    (hb : iform b b = 4) (hab : iform a b = 0) (p : ℕ × ℕ) (hp1 : 0 < p.1) (hp2 : 0 < p.2) :
    ¬IsRoot .F4 (p.1 • a + p.2 • b) := by
  intro hr
  have hv := f4_iform_self hr
  have e : iform (p.1 • a + p.2 • b) (p.1 • a + p.2 • b) = 4 * (p.1 : ℤ) ^ 2 + 4 * (p.2 : ℤ) ^ 2 := by
    rw [← Nat.cast_smul_eq_nsmul ℤ p.1 a, ← Nat.cast_smul_eq_nsmul ℤ p.2 b, iform_add_left,
      iform_add_right, iform_add_right, iform_smul_left, iform_smul_left, iform_smul_left,
      iform_smul_left, iform_smul_right, iform_smul_right, iform_smul_right, iform_smul_right,
      iform_comm b a, ha, hb, hab]
    ring
  rw [e] at hv
  have h1 : (1 : ℤ) ≤ p.1 := by exact_mod_cast hp1
  have h2 : (1 : ℤ) ≤ p.2 := by exact_mod_cast hp2
  rcases hv with h | h <;> nlinarith

theorem f4_insep {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (hδ : IsRoot .F4 δ)
    (hli : LinIndepPair γ δ)
    (hpar : (∀ i, 2 ∣ cartanCoord δ i) ∨ ∀ i, 2 ∣ cartanCoord γ i - cartanCoord δ i) :
    iform γ γ = 4 ∧ iform δ δ = 4 ∧ iform γ δ = 0 ∧ ∀ i, 2 ∣ γ i - δ i := by
  have hdouble : ∀ z : Fin (Tag.rank .F4) → ℤ, (∀ a, 2 ∣ z a) → ∃ y, z = (2 : ℤ) • y := by
    intro z hz
    choose y hy using hz
    exact ⟨y, funext fun a => by simp [hy a]⟩
  have hne : γ ≠ δ := fun h => by
    have := hli 1 (-1) (by rw [h]; simp)
    omega
  have hne' : γ ≠ -δ := fun h => by
    have := hli 1 1 (by rw [h]; simp)
    omega
  rcases hpar with hδ2 | hγδ
  · exfalso
    obtain ⟨y, hy⟩ := hdouble δ (f4_even_of_cartanCoord hδ2)
    obtain ⟨c, hc⟩ := two_dvd_iform_self y
    have h := f4_iform_self hδ
    rw [hy, iform_smul_left, iform_smul_right, hc] at h
    omega
  · have hz : ∀ i, 2 ∣ cartanCoord (γ - δ) i := fun i => by
      rw [cartanCoord_sub]
      exact hγδ i
    have hpar' := f4_even_of_cartanCoord hz
    have hpar'' : ∀ i, 2 ∣ γ i - δ i := fun i => by simpa using hpar' i
    obtain ⟨y, hy⟩ := hdouble (γ - δ) hpar'
    obtain ⟨c, hc⟩ := two_dvd_iform_self y
    have hval : iform (γ - δ) (γ - δ) = iform γ γ + iform δ δ - 2 * iform γ δ := by
      rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm δ γ]
      ring
    rw [hy, iform_smul_left, iform_smul_right, hc] at hval
    have hcs := iform_sq_lt hγ hδ hne hne'
    have hd1 := iform_self_dvd hγ δ
    have hd2 := iform_self_dvd hδ γ
    rw [iform_comm δ γ] at hd2
    rcases f4_iform_self hγ with ha | ha <;> rcases f4_iform_self hδ with hb | hb <;>
      rw [ha, hb] at hval hcs <;> rw [ha] at hd1 <;> rw [hb] at hd2
    · exfalso
      have h1 : iform γ δ ≤ 1 := by nlinarith
      have h2 : -1 ≤ iform γ δ := by nlinarith
      omega
    · exfalso
      have h1 : iform γ δ ≤ 2 := by nlinarith
      have h2 : -2 ≤ iform γ δ := by nlinarith
      omega
    · exfalso
      have h1 : iform γ δ ≤ 2 := by nlinarith
      have h2 : -2 ≤ iform γ δ := by nlinarith
      omega
    · refine ⟨ha, hb, ?_, hpar''⟩
      have h1 : iform γ δ ≤ 3 := by nlinarith
      have h2 : -3 ≤ iform γ δ := by nlinarith
      omega

@[expose] def f4Q (a b c d : ℤ) : ℤ :=
  4 * a * a - 2 * a * b - 2 * b * a + 4 * b * b - 2 * b * c - 2 * c * b + 2 * c * c - c * d - d * c +
    2 * d * d

@[expose] def f4Cands0 : List (List ℤ) :=
  [[-1, -2, -4, -2], [-1, -2, -2, -2], [-1, -2, -2, 0], [1, 2, 2, 0], [1, 2, 2, 2], [1, 2, 4, 2]]

@[expose] def f4Cands1 : List (List ℤ) :=
  [[-2, -3, -4, -2], [0, -1, -2, -2], [0, -1, -2, 0], [0, 1, 2, 0], [0, 1, 2, 2], [2, 3, 4, 2]]


@[expose] def f4Cond0 : List ℤ → Bool
  | [a, b, c, d] => decide (4 * a - 2 * b = 0 ∧ f4Q a b c d = 4 ∧ (a - 1) % 2 = 0 ∧ b % 2 = 0 ∧
      c % 2 = 0 ∧ d % 2 = 0)
  | _ => false

@[expose] def f4Cond1 : List ℤ → Bool
  | [a, b, c, d] => decide (-2 * a + 4 * b - 2 * c = 0 ∧ f4Q a b c d = 4 ∧ a % 2 = 0 ∧
      (b - 1) % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0)
  | _ => false

theorem f4_enum0 : ∀ l ∈ Tag.F4.artifactRoots, f4Cond0 l = true → l ∈ f4Cands0 := by
  decide

theorem f4_enum1 : ∀ l ∈ Tag.F4.artifactRoots, f4Cond1 l = true → l ∈ f4Cands1 := by
  decide

theorem reach_base (g : Fin (Tag.rank .F4) → ℤ) (j : Fin (Tag.rank .F4))
    (l : List (Fin (Tag.rank .F4))) {a b : Fin (Tag.rank .F4) → ℤ}
    (hg : List.ofFn g ∈ Tag.F4.artifactRoots) (h1 : iform g g = 4)
    (h3 : iform g (reflect .F4 j g) = 0) (heven : cartanCoord g j % 2 = 0)
    (ha : ∀ i, reflectPath .F4 l g i = a i) (hb : ∀ i, reflectPath .F4 l (reflect .F4 j g) i = b i) :
    Reach .F4 a b := by
  have hgr : IsRoot .F4 g := isRoot_iff_mem_artifactRoots.2 hg
  have h2 : iform (reflect .F4 j g) (reflect .F4 j g) = 4 := by
    rw [iform_reflect]
    exact h1
  have hR := (Reach.single hgr j (Int.even_iff.2 heven) (f4_not_isRoot_of_orth h1 h2 h3)).path l
  rwa [funext ha, funext hb] at hR

theorem ofFn_four (δ : Fin 4 → ℤ) : List.ofFn δ = [δ 0, δ 1, δ 2, δ 3] := by
  simp [List.ofFn_succ]

theorem f4_base0 (δ : Fin 4 → ℤ) (hδ : List.ofFn δ ∈ Tag.F4.artifactRoots)
    (h2 : iform (τ := .F4) δ δ = 4)
    (h3 : iform (τ := .F4) (Pi.single (0 : Fin 4) 1 : Fin 4 → ℤ) δ = 0)
    (h4 : ∀ i, 2 ∣ (Pi.single (0 : Fin 4) 1 : Fin 4 → ℤ) i - δ i) :
    Reach .F4 (Pi.single (0 : Fin 4) 1 : Fin 4 → ℤ) δ := by
  rw [f4_iform_eq] at h2 h3
  have hc : f4Cond0 (List.ofFn δ) = true := by
    rw [ofFn_four]
    simp only [f4Cond0, decide_eq_true_eq]
    have e0 := h4 0
    have e1 := h4 1
    have e2 := h4 2
    have e3 := h4 3
    simp at h3 e0 e1 e2 e3
    refine ⟨by linarith, by unfold f4Q; linear_combination h2, by omega, by omega, by omega,
      by omega⟩
  have hm := f4_enum0 _ hδ hc
  simp only [f4Cands0, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h
  · have hδe : δ = ![-1, -2, -4, -2] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact reach_base ![-1, -1, -2, 0] (3 : Fin 4) ([2, 1, 0, 2] : List (Fin 4)) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  · have hδe : δ = ![-1, -2, -2, -2] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact reach_base ![-1, -1, -2, 0] (3 : Fin 4) ([2, 1, 0] : List (Fin 4)) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  · have hδe : δ = ![-1, -2, -2, 0] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact reach_base ![-1, -1, 0, 0] (2 : Fin 4) ([1, 0] : List (Fin 4)) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  · have hδe : δ = ![1, 2, 2, 0] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact reach_base ![1, 1, 0, 0] (2 : Fin 4) ([1] : List (Fin 4)) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  · have hδe : δ = ![1, 2, 2, 2] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact reach_base ![1, 1, 0, 0] (2 : Fin 4) ([1, 3] : List (Fin 4)) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  · have hδe : δ = ![1, 2, 4, 2] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact reach_base ![1, 1, 0, 0] (2 : Fin 4) ([1, 3, 2] : List (Fin 4)) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)

theorem f4_base1 (δ : Fin 4 → ℤ) (hδ : List.ofFn δ ∈ Tag.F4.artifactRoots)
    (h2 : iform (τ := .F4) δ δ = 4)
    (h3 : iform (τ := .F4) (Pi.single (1 : Fin 4) 1 : Fin 4 → ℤ) δ = 0)
    (h4 : ∀ i, 2 ∣ (Pi.single (1 : Fin 4) 1 : Fin 4 → ℤ) i - δ i) :
    Reach .F4 (Pi.single (1 : Fin 4) 1 : Fin 4 → ℤ) δ := by
  rw [f4_iform_eq] at h2 h3
  have hc : f4Cond1 (List.ofFn δ) = true := by
    rw [ofFn_four]
    simp only [f4Cond1, decide_eq_true_eq]
    have e0 := h4 0
    have e1 := h4 1
    have e2 := h4 2
    have e3 := h4 3
    simp at h3 e0 e1 e2 e3
    refine ⟨by linarith, by unfold f4Q; linear_combination h2, by omega, by omega, by omega,
      by omega⟩
  have hm := f4_enum1 _ hδ hc
  simp only [f4Cands1, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h
  · have hδe : δ = ![-2, -3, -4, -2] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact reach_base ![-1, -2, -2, -2] (2 : Fin 4) ([1, 0, 3, 2, 1] : List (Fin 4)) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  · have hδe : δ = ![0, -1, -2, -2] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact reach_base ![0, -1, -2, 0] (3 : Fin 4) ([2, 1] : List (Fin 4)) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  · have hδe : δ = ![0, -1, -2, 0] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact reach_base ![0, -1, 0, 0] (2 : Fin 4) ([1] : List (Fin 4)) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  · have hδe : δ = ![0, 1, 2, 0] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact reach_base ![0, 1, 0, 0] (2 : Fin 4) ([] : List (Fin 4)) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  · have hδe : δ = ![0, 1, 2, 2] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact reach_base ![0, 1, 0, 0] (2 : Fin 4) ([3] : List (Fin 4)) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  · have hδe : δ = ![2, 3, 4, 2] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact reach_base ![1, 2, 2, 0] (3 : Fin 4) ([2, 1, 0, 2] : List (Fin 4)) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)

theorem f4_reach : ∀ {γ : Fin (Tag.rank .F4) → ℤ}, IsRoot .F4 γ → ∀ δ, IsRoot .F4 δ →
    iform γ γ = 4 → iform δ δ = 4 → iform γ δ = 0 → (∀ i, 2 ∣ γ i - δ i) → Reach .F4 γ δ := by
  intro γ hγ
  induction hγ with
  | basis j =>
    intro δ hδ h1 h2 h3 h4
    have hδl := isRoot_iff_mem_artifactRoots.1 hδ
    fin_cases j
    · exact f4_base0 δ hδl h2 h3 h4
    · exact f4_base1 δ hδl h2 h3 h4
    · exfalso
      rw [iform_single_single] at h1
      revert h1
      decide
    · exfalso
      rw [iform_single_single] at h1
      revert h1
      decide
  | @reflect i v hv ih =>
    intro δ hδ h1 h2 h3 h4
    have key : ∀ w : Fin (Tag.rank .F4) → ℤ, (∀ a, 2 ∣ w a) → ∀ a, 2 ∣ reflect .F4 i w a :=
      fun w hw a => by
        simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact dvd_sub (hw a)
          (Dvd.dvd.mul_right (Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (hw j) _) _)
    have e : v - reflect .F4 i δ = reflect .F4 i (reflect .F4 i v - δ) := by
      rw [← reflectHom_apply .F4 i (reflect .F4 i v - δ), map_sub, reflectHom_apply,
        reflectHom_apply, reflect_reflect]
    have h4' : ∀ a, 2 ∣ v a - reflect .F4 i δ a := fun a => by
      have := key (reflect .F4 i v - δ) (fun a => by simpa using h4 a) a
      rw [← e] at this
      simpa using this
    have h := ih (reflect .F4 i δ) (.reflect i hδ) (by rwa [iform_reflect] at h1)
      (by rwa [iform_reflect]) (by rwa [← iform_reflect i v (reflect .F4 i δ), reflect_reflect])
      h4'
    have := h.step i
    rwa [reflect_reflect] at this

theorem f4_sep_or_reach {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hδ : IsRoot .F4 δ) (hli : LinIndepPair γ δ) :
    (∃ t : Fin (Tag.rank .F4) → Kˣ, rootChar K γ t = 1 ∧ rootChar K δ t ≠ 1) ∨ Reach .F4 γ δ := by
  by_cases h : (∃ j, ¬2 ∣ cartanCoord δ j) ∧ ∃ i, ¬2 ∣ (cartanCoord γ i - cartanCoord δ i)
  · exact Or.inl (exists_sep_of_parity (two_ne_zero_of_card_three hK) h.1 h.2)
  · right
    have hpar : (∀ i, 2 ∣ cartanCoord δ i) ∨ ∀ i, 2 ∣ cartanCoord γ i - cartanCoord δ i := by
      by_contra hcon
      push Not at hcon
      exact h hcon
    obtain ⟨h1, h2, h3, h4⟩ := f4_insep hγ hδ hli hpar
    exact f4_reach hγ δ hδ h1 h2 h3 h4

end F4Roots

section F4

variable {K : Type} [Field K] [Finite K]

theorem f4_three_exists_section_of_central (hK : Nat.card K = 3) {E : Type*} [Group E]
    {π : E →* adjointGroup .F4 K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : adjointGroup .F4 K →* E, ∀ g, π (σ g) = g := by
  obtain ⟨-, ⟨O⟩, hP, -⟩ := f4_conclusionB K
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  have hT : ∀ (t : Fin (Tag.rank .F4) → Kˣ) (γ : Fin (Tag.rank .F4) → ℤ), IsRoot .F4 γ → ∀ c,
      torusAdjHom t * xPar (rootOperatorFamily .F4) γ c * (torusAdjHom t)⁻¹ =
        xPar (rootOperatorFamily .F4) γ ((rootChar K γ t : K) * c) :=
    fun t γ _ c => torusAdj_conj_xPar t γ c
  exact exists_section_of_torus_three (isFiniteType_cartan .F4)
    (RG := rootGroup (rootOperatorFamily .F4) K) hK (adjDatum_roots _ K) hE hP torusAdjHom hT
    (fun _ hγ => exists_unitVec cartan_mul_cartanInvF4 hγ)
    (fun i t => weyl_conj_torus (adjDatum_roots _ K) hE hP torusAdjHom hT
      center_adjointGroup_eq_bot i t)
    (fun _ _ hγ hδ hli => f4_sep_or_reach hK hγ hδ hli) hπ hcen

theorem f4_three_hopfMultiplier (hK : Nat.card K = 3) :
    commutator (AdjointQuotient .F4 K) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) := by
  have : Group.IsPerfect ↥(adjointGroup .F4 K) := isPerfect_f4 K
  exact AdjointClosed.hopfMultiplier_subsingleton center_adjointGroup_eq_bot
    fun π hπ hcen => f4_three_exists_section_of_central hK hπ hcen

end F4

end CFSG.LieType.Steinberg.CentralExt.FieldThree
