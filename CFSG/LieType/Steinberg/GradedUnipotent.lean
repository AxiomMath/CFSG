module

public import Mathlib.Algebra.Group.Pi.Torsion
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LieType.Steinberg.Graded

open Matrix

section Level

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {R : Type*} [CommRing R] (σ : κ → ℤ)

@[expose] def IdBelow (h : ℤ) (M : Matrix κ κ R) : Prop :=
  ∀ a b, σ a - σ b < h → M a b = (1 : Matrix κ κ R) a b

variable {σ}

omit [Fintype κ] in
theorem idBelow_one (h : ℤ) : IdBelow σ h (1 : Matrix κ κ R) := fun _ _ _ => rfl

omit [Fintype κ] in
theorem IdBelow.apply_eq_zero {h : ℤ} {M : Matrix κ κ R} (hM : IdBelow σ h M) {a b : κ}
    (hab : a ≠ b) (hlev : σ a - σ b < h) : M a b = 0 := by
  rw [hM a b hlev, Matrix.one_apply_ne hab]

omit [Fintype κ] in
theorem IdBelow.apply_self {h : ℤ} (hh : 0 < h) {M : Matrix κ κ R} (hM : IdBelow σ h M) (a : κ) :
    M a a = 1 := by
  rw [hM a a (by simpa using hh), Matrix.one_apply_eq]

omit [Fintype κ] in
theorem IdBelow.mono {h h' : ℤ} (hle : h' ≤ h) {M : Matrix κ κ R} (hM : IdBelow σ h M) :
    IdBelow σ h' M := fun a b hab => hM a b (by omega)

theorem mul_apply_of_idBelow {h : ℤ} (hh : 0 < h) {M N : Matrix κ κ R} (hM : IdBelow σ h M)
    (hN : IdBelow σ h N) {a b : κ} (hab : a ≠ b) (hlev : σ a - σ b ≤ h) :
    (M * N) a b = M a b + N a b := by
  rw [Matrix.mul_apply, Finset.sum_eq_add a b hab]
  · rw [hM.apply_self hh, hN.apply_self hh, one_mul, mul_one, add_comm]
  · intro c _ hc
    by_cases h1 : σ a - σ c < h
    · rw [hM.apply_eq_zero (Ne.symm hc.1) h1, zero_mul]
    · rw [hN.apply_eq_zero hc.2 (by omega), mul_zero]
  · simp
  · simp

theorem idBelow_mul {h : ℤ} (hh : 0 < h) {M N : Matrix κ κ R} (hM : IdBelow σ h M)
    (hN : IdBelow σ h N) : IdBelow σ h (M * N) := by
  intro a b hab
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hM.apply_self hh, one_mul, hN a b hab]
  · intro c _ hca
    by_cases h1 : σ a - σ c < h
    · rw [hM.apply_eq_zero (Ne.symm hca) h1, zero_mul]
    · by_cases hcb : c = b
      · subst hcb
        exact absurd hab (by omega)
      · rw [hN.apply_eq_zero hcb (by omega), mul_zero]
  · simp

theorem idBelow_list_prod {h : ℤ} (hh : 0 < h) :
    ∀ {l : List (Matrix κ κ R)}, (∀ M ∈ l, IdBelow σ h M) → IdBelow σ h l.prod
  | [], _ => idBelow_one h
  | M :: l, hl => by
    rw [List.prod_cons]
    exact idBelow_mul hh (hl M (List.mem_cons_self ..))
      (idBelow_list_prod hh fun N hN => hl N (List.mem_cons_of_mem _ hN))

theorem list_prod_apply_of_idBelow {h : ℤ} (hh : 0 < h) {a b : κ} (hab : a ≠ b)
    (hlev : σ a - σ b ≤ h) :
    ∀ {l : List (Matrix κ κ R)}, (∀ M ∈ l, IdBelow σ h M) →
      l.prod a b = (l.map fun M => M a b).sum
  | [], _ => by simp [Matrix.one_apply_ne hab]
  | M :: l, hl => by
    rw [List.prod_cons, List.map_cons, List.sum_cons,
      mul_apply_of_idBelow hh (hl M (List.mem_cons_self ..))
        (idBelow_list_prod hh fun N hN => hl N (List.mem_cons_of_mem _ hN)) hab hlev,
      list_prod_apply_of_idBelow hh hab hlev fun N hN => hl N (List.mem_cons_of_mem _ hN)]

end Level

section Unipotent

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {F : Type*} [Field F] {ι : Type*}
  (wt : κ → ι → ℤ)

@[expose] def Shifts (M : Matrix κ κ F) (δ : ι → ℤ) : Prop :=
  ∀ a b, M a b ≠ 0 → wt a - wt b = δ

@[expose] def elt (K : ℕ) (D : ℕ → Matrix κ κ F) (c : F) : Matrix κ κ F :=
  1 + ∑ k ∈ Finset.Icc 1 K, c ^ k • D k

variable {wt}

omit [Fintype κ] in
theorem elt_apply_of_ne (K : ℕ) (D : ℕ → Matrix κ κ F) (c : F) {a b : κ} (hab : a ≠ b) :
    elt K D c a b = ∑ k ∈ Finset.Icc 1 K, c ^ k * D k a b := by
  simp [elt, Matrix.one_apply_ne hab, Matrix.sum_apply]

omit [Fintype κ] [DecidableEq κ] in
theorem Shifts.apply_eq_zero {M : Matrix κ κ F} {δ : ι → ℤ} (hM : Shifts wt M δ) {a b : κ}
    (h : wt a - wt b ≠ δ) : M a b = 0 := by
  by_contra h'
  exact h (hM a b h')

omit [Fintype κ] in
theorem idBelow_elt (f : (ι → ℤ) →+ ℤ) {K : ℕ} {D : ℕ → Matrix κ κ F} {δ : ι → ℤ}
    (hD : ∀ k, 1 ≤ k → Shifts wt (D k) (k • δ)) (hpos : 0 < f δ) (c : F) :
    IdBelow (fun a => f (wt a)) (f δ) (elt K D c) := by
  intro a b hab
  rw [elt, Matrix.add_apply, Matrix.sum_apply, add_eq_left]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  rw [Matrix.smul_apply, (hD k hk.1).apply_eq_zero, smul_zero]
  intro h
  have : f (wt a) - f (wt b) = k * f δ := by
    rw [← map_sub, h, map_nsmul, nsmul_eq_mul]
  have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast hk.1
  simp only at hab
  nlinarith

theorem eq_of_prod_eq {Λ : Type*} {K : ℕ} (hK : 1 ≤ K) (root : Λ → ι → ℤ)
    (D : Λ → ℕ → Matrix κ κ F) (f : (ι → ℤ) →+ ℤ)
    (hD : ∀ γ k, 1 ≤ k → Shifts wt (D γ k) (k • root γ)) :
    ∀ (L : List Λ), L.Nodup → (∀ γ ∈ L, ∀ δ ∈ L, root γ = root δ → γ = δ) →
      (∀ γ ∈ L, 0 < f (root γ)) → (∀ γ ∈ L, D γ 1 ≠ 0) →
      L.Pairwise (fun γ δ => f (root γ) ≤ f (root δ)) →
      (∀ γ ∈ L, ∀ c, IsUnit (elt K (D γ) c)) → ∀ c d : Λ → F,
      (L.map fun γ => elt K (D γ) (c γ)).prod = (L.map fun γ => elt K (D γ) (d γ)).prod →
      ∀ γ ∈ L, c γ = d γ
  | [], _, _, _, _, _, _, _, _, _ => by simp
  | γ₀ :: L, hnd, hinj, hpos, hne, hsort, hunit, c, d, h => by
    rw [List.pairwise_cons] at hsort
    rw [List.nodup_cons] at hnd
    have h₀ := hpos γ₀ (List.mem_cons_self ..)
    obtain ⟨a, b, hab⟩ : ∃ a b, D γ₀ 1 a b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne γ₀ (List.mem_cons_self ..) (Matrix.ext hcon)
    have hshift : wt a - wt b = root γ₀ := by
      have := hD γ₀ 1 le_rfl a b hab
      rwa [one_nsmul] at this
    have hlev : f (wt a) - f (wt b) = f (root γ₀) := by rw [← map_sub, hshift]
    have habne : a ≠ b := by
      rintro rfl
      rw [sub_self] at hlev
      omega
    have hall : ∀ e : Λ → F, ∀ M ∈ ((γ₀ :: L).map fun γ => elt K (D γ) (e γ)),
        IdBelow (fun a => f (wt a)) (f (root γ₀)) M := by
      intro e M hM
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hM
      refine (idBelow_elt f (hD γ) (hpos γ hγ) (e γ)).mono ?_
      rcases List.mem_cons.1 hγ with rfl | hγ
      · exact le_rfl
      · exact hsort.1 γ hγ
    have hhead : ∀ e : F, elt K (D γ₀) e a b = e * D γ₀ 1 a b := by
      intro e
      rw [elt_apply_of_ne K _ _ habne, Finset.sum_eq_single 1]
      · rw [pow_one]
      · intro k hk hk1
        rw [Finset.mem_Icc] at hk
        rw [(hD γ₀ k hk.1).apply_eq_zero, mul_zero]
        rw [hshift]
        intro h'
        have h2 : ((k : ℤ) - 1) • root γ₀ = 0 := by
          rw [sub_smul, one_smul, natCast_zsmul, ← h', sub_self]
        rcases smul_eq_zero.1 h2 with h3 | h3
        · omega
        · rw [h3, map_zero] at h₀
          exact lt_irrefl _ h₀
      · intro h1
        exact absurd (Finset.mem_Icc.2 ⟨le_rfl, hK⟩) h1
    have hrest : ∀ e : F, ∀ γ ∈ L, elt K (D γ) e a b = 0 := by
      intro e γ hγ
      rw [elt_apply_of_ne K _ _ habne]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      rw [(hD γ k hk.1).apply_eq_zero, mul_zero]
      rw [hshift]
      intro h'
      have hf : f (root γ₀) = k * f (root γ) := by rw [h', map_nsmul, nsmul_eq_mul]
      have hle := hsort.1 γ hγ
      have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast hk.1
      have hkeq : (k : ℤ) = 1 := by nlinarith
      have hk' : k = 1 := by exact_mod_cast hkeq
      rw [hk', one_nsmul] at h'
      have := hinj γ₀ (List.mem_cons_self ..) γ (List.mem_cons_of_mem _ hγ) h'
      exact hnd.1 (this ▸ hγ)
    have hentry : ∀ e : Λ → F,
        ((γ₀ :: L).map fun γ => elt K (D γ) (e γ)).prod a b = e γ₀ * D γ₀ 1 a b := by
      intro e
      rw [list_prod_apply_of_idBelow h₀ habne hlev.le (hall e), List.map_cons, List.map_cons,
        List.sum_cons, List.map_map, hhead, List.sum_eq_zero, add_zero]
      intro x hx
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
      exact hrest (e γ) γ hγ
    have hc : c γ₀ = d γ₀ := by
      have := (hentry c).symm.trans ((congrArg (fun M => M a b) h).trans (hentry d))
      exact mul_right_cancel₀ hab this
    intro γ hγ
    rcases List.mem_cons.1 hγ with rfl | hγ
    · exact hc
    · refine eq_of_prod_eq hK root D f hD L hnd.2
        (fun γ hγ δ hδ => hinj γ (List.mem_cons_of_mem _ hγ) δ (List.mem_cons_of_mem _ hδ))
        (fun γ hγ => hpos γ (List.mem_cons_of_mem _ hγ))
        (fun γ hγ => hne γ (List.mem_cons_of_mem _ hγ)) hsort.2
        (fun γ hγ => hunit γ (List.mem_cons_of_mem _ hγ)) c d ?_ γ hγ
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, hc] at h
      exact (hunit γ₀ (List.mem_cons_self ..) (d γ₀)).mul_left_cancel h

end Unipotent

end CFSG.LieType.Steinberg.Graded
