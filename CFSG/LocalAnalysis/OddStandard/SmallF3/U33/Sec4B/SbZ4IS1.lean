module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma36

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X]

private lemma z4i_ab_cancel {Q : Subgroup X} (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    {a b c d : X} (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q) (hd : d ∈ Q)
    (h : a * c⁻¹ = b * d⁻¹) : a * b⁻¹ = c * d⁻¹ := by
  have hb' : b⁻¹ ∈ Q := Q.inv_mem hb
  have hd' : d⁻¹ ∈ Q := Q.inv_mem hd
  have hbdb : b * d⁻¹ * b⁻¹ = d⁻¹ := by
    rw [show b * d⁻¹ * b⁻¹ = (b * d⁻¹) * b⁻¹ from by group, hcomm b hb d⁻¹ hd']
    group
  have hstep : (b * d⁻¹) * (c * b⁻¹) = c * d⁻¹ := by
    rw [← hcomm b⁻¹ hb' c hc]
    rw [show (b * d⁻¹) * (b⁻¹ * c) = b * d⁻¹ * b⁻¹ * c from by group]
    rw [hbdb, hcomm d⁻¹ hd' c hc]
  calc a * b⁻¹ = (a * c⁻¹) * (c * b⁻¹) := by group
    _ = (b * d⁻¹) * (c * b⁻¹) := by rw [h]
    _ = c * d⁻¹ := hstep

theorem z4i_fpf_quot [Finite X] {Q N : Subgroup X} {ρ : X} (hNQ : N ≤ Q)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N)
    (hfpf : ∀ q ∈ Q, ρ * q * ρ⁻¹ = q → q = 1) {q : X} (hq : q ∈ Q)
    (hy : ρ * q * ρ⁻¹ * q⁻¹ ∈ N) : q ∈ N := by
  let f : ↥N → ↥N := fun n =>
    ⟨ρ * (n : X) * ρ⁻¹ * (n : X)⁻¹, N.mul_mem (hρN n n.2) (N.inv_mem n.2)⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h : ρ * (a : X) * ρ⁻¹ * (a : X)⁻¹ = ρ * (b : X) * ρ⁻¹ * (b : X)⁻¹ :=
      congrArg Subtype.val hab
    have hA : ρ * (a : X) * ρ⁻¹ ∈ Q := hNQ (hρN a a.2)
    have hB : ρ * (b : X) * ρ⁻¹ ∈ Q := hNQ (hρN b b.2)
    have hcancel : (ρ * (a : X) * ρ⁻¹) * (ρ * (b : X) * ρ⁻¹)⁻¹ =
        (a : X) * (b : X)⁻¹ := z4i_ab_cancel hcomm hA hB (hNQ a.2) (hNQ b.2) h
    have hconj : ρ * ((a : X) * (b : X)⁻¹) * ρ⁻¹ = (a : X) * (b : X)⁻¹ := by
      calc ρ * ((a : X) * (b : X)⁻¹) * ρ⁻¹
          = (ρ * (a : X) * ρ⁻¹) * (ρ * (b : X) * ρ⁻¹)⁻¹ := by group
        _ = (a : X) * (b : X)⁻¹ := hcancel
    have hmem : (a : X) * (b : X)⁻¹ ∈ Q := Q.mul_mem (hNQ a.2) (Q.inv_mem (hNQ b.2))
    have h1 : (a : X) * (b : X)⁻¹ = 1 := hfpf _ hmem hconj
    calc (a : X) = (a : X) * (b : X)⁻¹ * (b : X) := by group
      _ = 1 * (b : X) := by rw [h1]
      _ = (b : X) := by rw [one_mul]
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hfinj
  obtain ⟨n, hn⟩ := hsurj ⟨ρ * q * ρ⁻¹ * q⁻¹, hy⟩
  have hn' : ρ * (n : X) * ρ⁻¹ * (n : X)⁻¹ = ρ * q * ρ⁻¹ * q⁻¹ := by
    simpa only [f] using congrArg Subtype.val hn
  have hAn : ρ * (n : X) * ρ⁻¹ ∈ Q := hNQ (hρN n n.2)
  have hAq : ρ * q * ρ⁻¹ ∈ Q := by
    have h := hNQ hy
    rw [show ρ * q * ρ⁻¹ = (ρ * q * ρ⁻¹ * q⁻¹) * q from by group]
    exact Q.mul_mem h hq
  have hcancel : (ρ * (n : X) * ρ⁻¹) * (ρ * q * ρ⁻¹)⁻¹ = (n : X) * q⁻¹ :=
    z4i_ab_cancel hcomm hAn hAq (hNQ n.2) hq hn'
  have hconj : ρ * ((n : X) * q⁻¹) * ρ⁻¹ = (n : X) * q⁻¹ := by
    calc ρ * ((n : X) * q⁻¹) * ρ⁻¹
        = (ρ * (n : X) * ρ⁻¹) * (ρ * q * ρ⁻¹)⁻¹ := by group
      _ = (n : X) * q⁻¹ := hcancel
  have hmem : (n : X) * q⁻¹ ∈ Q := Q.mul_mem (hNQ n.2) (Q.inv_mem hq)
  have h1 : (n : X) * q⁻¹ = 1 := hfpf _ hmem hconj
  have hnq : (n : X) = q := by
    calc (n : X) = (n : X) * q⁻¹ * q := by group
      _ = 1 * q := by rw [h1]
      _ = q := by rw [one_mul]
  rw [← hnq]
  exact n.2

theorem z4i_lam_nontriv {N M : Subgroup X} {ρ l : X} (hρ3 : ρ ^ 3 = 1)
    (hlr : l * ρ * l⁻¹ = ρ⁻¹) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N)
    (hρM : ∀ m ∈ M, ρ * m * ρ⁻¹ ∈ M)
    (hfpf : ∀ m ∈ M, ρ * m * ρ⁻¹ * m⁻¹ ∈ N → m ∈ N) {m₀ : X} (hm₀ : m₀ ∈ M)
    (hm₀N : m₀ ∉ N) : ∃ m ∈ M, ⁅l, m⁆ ∉ N := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hsq : ρ * (ρ * ρ) = 1 := by rw [← pow_two, ← pow_succ', hρ3]
  have hρinv : ρ⁻¹ = ρ * ρ := inv_eq_of_mul_eq_one_right hsq
  have hρ2inv : (ρ * ρ)⁻¹ = ρ := inv_eq_of_mul_eq_one_left hsq
  have hsqinv : ρ⁻¹ * ρ⁻¹ = ρ := by
    calc ρ⁻¹ * ρ⁻¹ = (ρ * ρ)⁻¹ := by group
      _ = ρ := hρ2inv
  have hlrinv : l * ρ⁻¹ * l⁻¹ = ρ := by
    have e : l * ρ⁻¹ * l⁻¹ = (l * ρ * l⁻¹)⁻¹ := by group
    rw [e, hlr, inv_inv]
  have hρ2m : ∀ m : X, (ρ * ρ) * m * (ρ * ρ)⁻¹ = ρ⁻¹ * m * ρ := by
    intro m
    rw [← hρinv, inv_inv]
  have hρN2 : ∀ n ∈ N, ρ⁻¹ * n * ρ ∈ N := by
    intro n hn
    have h1 : ρ * (ρ * n * ρ⁻¹) * ρ⁻¹ ∈ N := hρN _ (hρN n hn)
    have e : ρ * (ρ * n * ρ⁻¹) * ρ⁻¹ = ρ⁻¹ * n * ρ := by
      calc ρ * (ρ * n * ρ⁻¹) * ρ⁻¹ = (ρ * ρ) * n * (ρ⁻¹ * ρ⁻¹) := by group
        _ = (ρ * ρ) * n * ρ := by rw [hsqinv]
        _ = ρ⁻¹ * n * ρ := by rw [← hρinv]
    rwa [e] at h1
  have hm' : ρ * m₀ * ρ⁻¹ ∈ M := hρM m₀ hm₀
  have hn₁ : ⁅l, m₀⁆ ∈ N := h m₀ hm₀
  have hn₂ : ⁅l, ρ * m₀ * ρ⁻¹⁆ ∈ N := h _ hm'
  have hl₁ : l * m₀ * l⁻¹ = ⁅l, m₀⁆ * m₀ := by
    simp only [commutatorElement_def]; group
  have hl₂ : l * (ρ * m₀ * ρ⁻¹) * l⁻¹ =
      ⁅l, ρ * m₀ * ρ⁻¹⁆ * (ρ * m₀ * ρ⁻¹) := by
    simp only [commutatorElement_def]; group
  have hkey : ⁅l, ρ * m₀ * ρ⁻¹⁆ * (ρ * m₀ * ρ⁻¹) =
      (ρ⁻¹ * ⁅l, m₀⁆ * ρ) * (ρ⁻¹ * m₀ * ρ) := by
    calc ⁅l, ρ * m₀ * ρ⁻¹⁆ * (ρ * m₀ * ρ⁻¹)
        = l * (ρ * m₀ * ρ⁻¹) * l⁻¹ := hl₂.symm
      _ = (l * ρ * l⁻¹) * (l * m₀ * l⁻¹) * (l * ρ⁻¹ * l⁻¹) := by group
      _ = ρ⁻¹ * (⁅l, m₀⁆ * m₀) * ρ := by rw [hlr, hlrinv, hl₁]
      _ = (ρ⁻¹ * ⁅l, m₀⁆ * ρ) * (ρ⁻¹ * m₀ * ρ) := by group
  have ha : (ρ * m₀ * ρ⁻¹) * (ρ⁻¹ * m₀ * ρ)⁻¹ ∈ N := by
    have h2 : ⁅l, ρ * m₀ * ρ⁻¹⁆ * ((ρ * m₀ * ρ⁻¹) * (ρ⁻¹ * m₀ * ρ)⁻¹) =
        ρ⁻¹ * ⁅l, m₀⁆ * ρ := by
      calc ⁅l, ρ * m₀ * ρ⁻¹⁆ * ((ρ * m₀ * ρ⁻¹) * (ρ⁻¹ * m₀ * ρ)⁻¹)
          = (⁅l, ρ * m₀ * ρ⁻¹⁆ * (ρ * m₀ * ρ⁻¹)) * (ρ⁻¹ * m₀ * ρ)⁻¹ := by group
        _ = ((ρ⁻¹ * ⁅l, m₀⁆ * ρ) * (ρ⁻¹ * m₀ * ρ)) * (ρ⁻¹ * m₀ * ρ)⁻¹ := by rw [hkey]
        _ = ρ⁻¹ * ⁅l, m₀⁆ * ρ := by group
    have h1 : (ρ * m₀ * ρ⁻¹) * (ρ⁻¹ * m₀ * ρ)⁻¹ =
        ⁅l, ρ * m₀ * ρ⁻¹⁆⁻¹ * (ρ⁻¹ * ⁅l, m₀⁆ * ρ) := by
      rw [← h2]; group
    rw [h1]
    exact N.mul_mem (N.inv_mem hn₂) (hρN2 _ hn₁)
  have haZ : (ρ * m₀ * ρ⁻¹) * ((ρ * ρ) * m₀ * (ρ * ρ)⁻¹)⁻¹ ∈ N := by
    rw [hρ2m m₀]; exact ha
  have hb : (ρ * ρ) * m₀ * (ρ * ρ)⁻¹ * m₀⁻¹ ∈ N := by
    have h2 : ρ * ((ρ * m₀ * ρ⁻¹) * (ρ⁻¹ * m₀ * ρ)⁻¹) * ρ⁻¹ =
        (ρ * ρ) * m₀ * (ρ * ρ)⁻¹ * m₀⁻¹ := by group
    rw [← h2]
    exact hρN _ ha
  have hfinal : ρ * m₀ * ρ⁻¹ * m₀⁻¹ ∈ N := by
    have h3 : ρ * m₀ * ρ⁻¹ * m₀⁻¹
        = ((ρ * m₀ * ρ⁻¹) * ((ρ * ρ) * m₀ * (ρ * ρ)⁻¹)⁻¹) *
          ((ρ * ρ) * m₀ * (ρ * ρ)⁻¹ * m₀⁻¹) := by group
    rw [h3]
    exact N.mul_mem haZ hb
  exact hm₀N (hfpf m₀ hm₀ hfinal)

theorem z4i_invol_coset {Z : Type} [Group Z] [Finite Z] {K Y : Subgroup Z} {u : Z}
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (hYK : Y ≤ K) (hcommK : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ Y)
    (hsqK : ∀ x ∈ K, x ^ 2 ∈ Y) (hcommY : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x)
    (hsqY : ∀ x ∈ Y, x * x = 1) (huK : ∀ k ∈ K, u * k * u⁻¹ ∈ K)
    (huY : ∀ y ∈ Y, u * y * u⁻¹ ∈ Y) (hregY : ActsRegularly u ⊥ Y)
    (hregK : ActsRegularly u Y K) :
    ∀ j : Z, (∃ s ∈ K, j = u * s) → j * j = 1 → j ≠ 1 → ∃ w ∈ K, j = w * u * w⁻¹ := by
  have hu2' : u ^ 2 = 1 := by rw [pow_two]; exact hu2
  have huord : orderOf u = 2 := orderOf_eq_prime hu2' hu1
  let Wseries : ℕ → Subgroup Z := fun i => if i = 0 then K else if i = 1 then Y else ⊥
  have h0 : Wseries 0 = K := by simp [Wseries]
  have h1 : Wseries 1 = Y := by simp [Wseries]
  have h2 : Wseries 2 = ⊥ := by simp [Wseries]
  have hle : ∀ i < 2, Wseries (i + 1) ≤ Wseries i := by
    intro i hi
    interval_cases i
    · simpa [Wseries] using hYK
    · simpa [Wseries] using bot_le
  have htnorm : ∀ i ≤ 2, ∀ g ∈ Wseries i, u * g * u⁻¹ ∈ Wseries i := by
    intro i hi g hg
    interval_cases i
    · simpa [Wseries] using huK g (by simpa [Wseries] using hg)
    · simpa [Wseries] using huY g (by simpa [Wseries] using hg)
    · have hg1 : g = 1 := by simpa [Wseries] using hg
      rw [hg1]
      simp [Wseries]
  have hcomm2 : ∀ i < 2, ∀ x ∈ Wseries i, ∀ y ∈ Wseries i, ⁅x, y⁆ ∈ Wseries (i + 1) := by
    intro i hi x hx y hy
    interval_cases i
    · simpa [Wseries] using hcommK x (by simpa [Wseries] using hx) y (by simpa [Wseries] using hy)
    · have hxY : x ∈ Y := by simpa [Wseries] using hx
      have hyY : y ∈ Y := by simpa [Wseries] using hy
      have hone : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hcommY x hxY y hyY)
      rw [hone]
      simp [Wseries]
  have hsq2 : ∀ i < 2, ∀ x ∈ Wseries i, x ^ 2 ∈ Wseries (i + 1) := by
    intro i hi x hx
    interval_cases i
    · simpa [Wseries] using hsqK x (by simpa [Wseries] using hx)
    · have hxY : x ∈ Y := by simpa [Wseries] using hx
      have hone : x ^ 2 = 1 := by rw [pow_two]; exact hsqY x hxY
      rw [hone]
      simp [Wseries]
  have hreg : ∀ i < 2, ActsRegularly u (Wseries (i + 1)) (Wseries i) := by
    intro i hi
    interval_cases i
    · simpa [Wseries] using hregK
    · simpa [Wseries] using hregY
  have hset := (lemma36 (W := K) (t := u) huord 2 Wseries h0 h2 hle htnorm hcomm2 hsq2 hreg).1
  intro j hj hjj hjne
  have hjord : orderOf j = 2 := by
    refine orderOf_eq_prime ?_ hjne
    rw [pow_two]
    exact hjj
  have : j ∈ {j : Z | ∃ w ∈ K, j = w * u * w⁻¹} := by
    rw [← hset]
    exact ⟨hj, hjord⟩
  exact this

@[expose] def z4iCuK (K Y : Subgroup X) (u : X) (hKY : ∀ k ∈ K, ∀ y ∈ Y, k * y = y * k) :
    Subgroup X where
  carrier := {x | x ∈ K ∧ ⁅u, x⁆ ∈ Y}
  mul_mem' := by
    intro a b ha hb
    refine ⟨K.mul_mem ha.1 hb.1, ?_⟩
    have hconj : a * ⁅u, b⁆ * a⁻¹ = ⁅u, b⁆ := by
      calc a * ⁅u, b⁆ * a⁻¹ = (a * ⁅u, b⁆) * a⁻¹ := by rw [mul_assoc]
        _ = (⁅u, b⁆ * a) * a⁻¹ := by rw [hKY a ha.1 (⁅u, b⁆) hb.2]
        _ = ⁅u, b⁆ := by group
    have hc : ⁅u, a * b⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [hc, hconj]
    exact Y.mul_mem ha.2 hb.2
  one_mem' := by
    refine ⟨K.one_mem, ?_⟩
    rw [show ⁅u, (1 : X)⁆ = 1 from by simp [commutatorElement_def]]
    exact Y.one_mem
  inv_mem' := by
    intro a ha
    refine ⟨K.inv_mem ha.1, ?_⟩
    have hconj : a⁻¹ * ⁅u, a⁆⁻¹ * a = ⁅u, a⁆⁻¹ := by
      calc a⁻¹ * ⁅u, a⁆⁻¹ * a = (a⁻¹ * ⁅u, a⁆⁻¹) * a := by rw [mul_assoc]
        _ = (⁅u, a⁆⁻¹ * a⁻¹) * a := by
              rw [hKY a⁻¹ (K.inv_mem ha.1) (⁅u, a⁆⁻¹) (Y.inv_mem ha.2)]
        _ = ⁅u, a⁆⁻¹ := by group
    have hc : ⁅u, a⁻¹⁆ = a⁻¹ * ⁅u, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [hc, hconj]
    exact Y.inv_mem ha.2

theorem mem_z4iCuK {K Y : Subgroup X} {u : X} (hKY : ∀ k ∈ K, ∀ y ∈ Y, k * y = y * k) {x : X} :
    x ∈ z4iCuK K Y u hKY ↔ x ∈ K ∧ ⁅u, x⁆ ∈ Y :=
  Iff.rfl

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
