module

public import CFSG.CharacterTheory.Wreathed.ConditionalOddFourierCore

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalFiveFixed

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalOddFourier

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p : ι}

theorem sign_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem one_le_mul_self_of_odd {a : ℤ} (ha : Odd a) : 1 ≤ a * a := by
  have hne : a ≠ 0 := by
    rintro rfl
    rw [Int.odd_iff] at ha
    norm_num at ha
  rcases lt_or_gt_of_ne hne with h | h <;> nlinarith

theorem four_le_mul_self_of_even {a : ℤ} (ha : Even a) (hne : a ≠ 0) : 4 ≤ a * a := by
  obtain ⟨k, rfl⟩ := ha
  have hk : k ≠ 0 := by
    rintro rfl
    exact hne (by ring)
  rcases lt_or_gt_of_ne hk with h | h <;> nlinarith

theorem fin_three_add_one_ne (e : Fin 3) : e + 1 ≠ e := by
  revert e
  decide

theorem fin_three_add_two_ne (e : Fin 3) : e + 2 ≠ e := by
  revert e
  decide

theorem fin_three_add_one_ne_add_two (e : Fin 3) : e + 1 ≠ e + 2 := by
  revert e
  decide

theorem sum_fin_three_eq {M : Type*} [AddCommMonoid M] {e f g : Fin 3} (hf : f ≠ e)
    (hg : g ≠ e) (hfg : f ≠ g) (u : Fin 3 → M) : ∑ i, u i = u e + u f + u g := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {e, f, g} := by
    revert e f g
    decide
  rw [huniv, Finset.sum_insert (by simp [hf.symm, hg.symm]), Finset.sum_pair hfg, add_assoc]

theorem fin_three_eq_or_eq {e f g h : Fin 3} (hf : f ≠ e) (hg : g ≠ e) (hfg : f ≠ g)
    (hh : h ≠ e) : h = f ∨ h = g := by
  revert e f g h
  decide

theorem sum_mul_unit_add_sum {q : ι} {α : Fin 3 → ι} (hq : q ∈ B) (hα : ∀ i, α i ∈ B)
    (f : ι → ℤ) (γ : Fin 3 → ℤ) :
    ∑ φ ∈ B, f φ * (unitVector q φ + ∑ i, γ i * unitVector (α i) φ) =
      f q + ∑ i, γ i * f (α i) := by
  have h := sum_mul_unitVector_add_sum hq hα f 1 γ
  simp only [one_mul] at h
  exact h

theorem sum_mul_unit_add_sum_add {q ω : ι} {α : Fin 3 → ι} (hq : q ∈ B) (hα : ∀ i, α i ∈ B)
    (hω : ω ∈ B) (f : ι → ℤ) (γ : Fin 3 → ℤ) (b : ℤ) :
    ∑ φ ∈ B, f φ * (unitVector q φ + ∑ i, γ i * unitVector (α i) φ + b * unitVector ω φ) =
      f q + ∑ i, γ i * f (α i) + b * f ω := by
  have h : ∀ φ, f φ * (unitVector q φ + ∑ i, γ i * unitVector (α i) φ + b * unitVector ω φ) =
      f φ * (unitVector q φ + ∑ i, γ i * unitVector (α i) φ) + b * (f φ * unitVector ω φ) :=
    fun φ => by ring
  rw [Finset.sum_congr rfl fun φ _ => h φ, Finset.sum_add_distrib, sum_mul_unit_add_sum hq hα,
    ← Finset.mul_sum, sum_mul_unitVector hω]

theorem sum_mul_neg_unit_add_sum_add {q ω : ι} {α : Fin 3 → ι} (hq : q ∈ B)
    (hα : ∀ i, α i ∈ B) (hω : ω ∈ B) (f : ι → ℤ) (γ : Fin 3 → ℤ) (b : ℤ) :
    ∑ φ ∈ B, f φ * (-unitVector q φ + ∑ i, γ i * unitVector (α i) φ + b * unitVector ω φ) =
      -f q + ∑ i, γ i * f (α i) + b * f ω := by
  have h : ∀ φ, f φ * (-unitVector q φ + ∑ i, γ i * unitVector (α i) φ + b * unitVector ω φ) =
      f φ * ((-1) * unitVector q φ + ∑ i, γ i * unitVector (α i) φ) +
        b * (f φ * unitVector ω φ) := fun φ => by ring
  rw [Finset.sum_congr rfl fun φ _ => h φ, Finset.sum_add_distrib,
    sum_mul_unitVector_add_sum hq hα, ← Finset.mul_sum, sum_mul_unitVector hω]
  ring

theorem sum_core_add_rest {α : Fin 3 → ι} (hp : p ∈ B) (hα : ∀ i, α i ∈ B)
    (hαinj : Function.Injective α) (hαp : ∀ i, α i ≠ p) (g : ι → ℤ) :
    ∑ φ ∈ B, g φ =
      g p + ∑ i, g (α i) + ∑ φ ∈ (B.erase p).filter (fun φ => ∀ i, φ ≠ α i), g φ := by
  rw [← Finset.add_sum_erase B g hp, add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (B.erase p) (fun φ => ∀ i, φ ≠ α i), add_comm]
  congr 1
  have him : (B.erase p).filter (fun φ => ¬ ∀ i, φ ≠ α i) = Finset.univ.image α := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_image, Finset.mem_univ,
      true_and, not_forall, not_not]
    constructor
    · rintro ⟨-, i, hi⟩
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨hαp i, hα i⟩, i, rfl⟩
  rw [him, Finset.sum_image fun i _ j _ h => hαinj h]

theorem exists_pair_of_sum_eq {h : Fin 3 → ℤ} (hs : ∀ i, h i = 1 ∨ h i = -1) {e : Fin 3}
    (he : h e = -1) (hsum : ∑ i, h i = -1) :
    ∃ f g : Fin 3, f ≠ e ∧ g ≠ e ∧ f ≠ g ∧ h f = 1 ∧ h g = -1 := by
  rw [sum_fin_three_eq (fin_three_add_one_ne e) (fin_three_add_two_ne e)
    (fin_three_add_one_ne_add_two e)] at hsum
  rcases hs (e + 1) with h1 | h1
  · exact ⟨e + 1, e + 2, fin_three_add_one_ne e, fin_three_add_two_ne e,
      fin_three_add_one_ne_add_two e, h1, by omega⟩
  · exact ⟨e + 2, e + 1, fin_three_add_two_ne e, fin_three_add_one_ne e,
      (fin_three_add_one_ne_add_two e).symm, by omega, h1⟩

theorem five_core {κ : Type*} {J : Finset κ} {α : Fin 3 → ι} {β η : Fin 3 → ℤ} {σ : ℤ}
    {e : Fin 3} {χ : κ → ι} {y₀ C : ι → ℤ} {x : κ → ι → ℤ} {d : ι → ℤ}
    (hp : p ∈ B) (hα : ∀ i, α i ∈ B) (hαinj : Function.Injective α) (hαp : ∀ i, α i ≠ p)
    (hχ : ∀ j ∈ J, χ j ∈ B) (hχp : ∀ j ∈ J, χ j ≠ p) (hχα : ∀ j ∈ J, ∀ i, χ j ≠ α i)
    (hJ : J.Nonempty) (hβ : ∀ i, β i = 1 ∨ β i = -1) (hσ : σ = 1 ∨ σ = -1)
    (hηe : η e = -β e) (hηi : ∀ i, i ≠ e → η i = β i) (hβe : β e = σ)
    (hy₀ : ∀ φ ∈ B, y₀ φ = unitVector p φ + ∑ i, β i * unitVector (α i) φ)
    (hx : ∀ j ∈ J, ∀ φ ∈ B, x j φ = -unitVector p φ + ∑ i, η i * unitVector (α i) φ +
      2 * σ * unitVector (χ j) φ)
    (hd : ∀ φ ∈ B, 0 < d φ) (hdp : d p = 1)
    (hdy₀ : ∑ φ ∈ B, d φ * y₀ φ = 0) (hdx : ∀ j ∈ J, ∑ φ ∈ B, d φ * x j φ = 0)
    (hdC : ∑ φ ∈ B, d φ * C φ = 0) (hCsq : ∑ φ ∈ B, C φ * C φ = 8) (hCp : C p = 1)
    (hCpar : ∀ φ ∈ B, C φ ≡ y₀ φ [ZMOD 2]) (hCy₀ : ∑ φ ∈ B, C φ * y₀ φ = 0)
    (hCx : ∀ j ∈ J, ∑ φ ∈ B, C φ * x j φ = 0) :
    ∃ ω ∈ B, ω ≠ p ∧ (∀ i, ω ≠ α i) ∧ (∀ j ∈ J, ω ≠ χ j) ∧
      ∃ f g : Fin 3, f ≠ e ∧ g ≠ e ∧ f ≠ g ∧ ∃ τ₀ : ℤ, (τ₀ = 1 ∨ τ₀ = -1) ∧
        β f = -τ₀ ∧ d ω = d (α f) - τ₀ ∧
        ∀ φ ∈ B, C φ = unitVector p φ - σ * unitVector (α e) φ - τ₀ * unitVector (α f) φ -
          β g * unitVector (α g) φ + 2 * τ₀ * unitVector ω φ := by
  set R := (B.erase p).filter (fun φ => ∀ i, φ ≠ α i) with hR
  have hmemR : ∀ φ, φ ∈ R ↔ φ ∈ B ∧ φ ≠ p ∧ ∀ i, φ ≠ α i := by
    intro φ
    rw [hR, Finset.mem_filter, Finset.mem_erase]
    tauto
  have hy₀α : ∀ i, y₀ (α i) = β i := fun i => by
    rw [hy₀ _ (hα i), unitVector_of_ne (hαp i), sum_mul_unitVector_apply hαinj, zero_add]
  have hy₀R : ∀ φ ∈ R, y₀ φ = 0 := fun φ hφ => by
    obtain ⟨hφB, hφp, hφα⟩ := (hmemR φ).mp hφ
    rw [hy₀ φ hφB, unitVector_of_ne hφp, sum_mul_unitVector_of_forall_ne β hφα, add_zero]
  have hCαodd : ∀ i, Odd (C (α i)) := fun i => by
    have h := hCpar _ (hα i)
    rw [hy₀α] at h
    rw [Int.odd_iff]
    unfold Int.ModEq at h
    rcases hβ i with hb | hb <;> rw [hb] at h <;> omega
  have hCReven : ∀ φ ∈ R, Even (C φ) := fun φ hφ => by
    have h := hCpar φ ((hmemR φ).mp hφ).1
    rw [hy₀R φ hφ] at h
    rw [Int.even_iff]
    unfold Int.ModEq at h
    omega
  have hnorm := sum_core_add_rest hp hα hαinj hαp (fun φ => C φ * C φ)
  rw [hCsq, hCp, ← hR] at hnorm
  have hRnn : 0 ≤ ∑ φ ∈ R, C φ * C φ := Finset.sum_nonneg fun φ _ => mul_self_nonneg _
  have hone : ∀ i, 1 ≤ C (α i) * C (α i) := fun i => one_le_mul_self_of_odd (hCαodd i)
  have hCα : ∀ i, C (α i) = 1 ∨ C (α i) = -1 := by
    intro i
    have h2 : (2 : ℤ) ≤ ∑ j ∈ Finset.univ.erase i, C (α j) * C (α j) := by
      calc (2 : ℤ) = ∑ _j ∈ Finset.univ.erase i, (1 : ℤ) := by
              simp [Finset.card_erase_of_mem]
        _ ≤ _ := Finset.sum_le_sum fun j _ => hone j
    have hsum := Finset.add_sum_erase Finset.univ (fun j => C (α j) * C (α j))
      (Finset.mem_univ i)
    have hle : C (α i) * C (α i) ≤ 5 := by linarith
    have h1 : C (α i) ≤ 2 := by nlinarith
    have h2' : -2 ≤ C (α i) := by nlinarith
    have hodd := hCαodd i
    rw [Int.odd_iff] at hodd
    omega
  have hsq3 : ∑ i, C (α i) * C (α i) = 3 := by
    rw [Fin.sum_univ_three]
    rcases hCα 0 with h0 | h0 <;> rcases hCα 1 with h1 | h1 <;> rcases hCα 2 with h2 | h2 <;>
      rw [h0, h1, h2] <;> norm_num
  have hR4 : ∑ φ ∈ R, C φ * C φ = 4 := by linarith
  obtain ⟨ω, hωR, hωne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by rw [hR4]; norm_num : ∑ φ ∈ R, C φ * C φ ≠ 0)
  have hCω0 : C ω ≠ 0 := fun h => hωne (by rw [h, mul_zero])
  have hCωsq : C ω * C ω = 4 := by
    have hle : C ω * C ω ≤ 4 := hR4 ▸ Finset.single_le_sum (f := fun φ => C φ * C φ)
      (fun φ _ => mul_self_nonneg _) hωR
    linarith [four_le_mul_self_of_even (hCReven ω hωR) hCω0]
  have hCRω : ∀ φ ∈ R, φ ≠ ω → C φ = 0 := by
    have h := Finset.add_sum_erase R (fun φ => C φ * C φ) hωR
    have hrest : ∑ φ ∈ R.erase ω, C φ * C φ = 0 := by linarith
    intro φ hφ hφω
    exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun φ _ =>
      mul_self_nonneg (C φ)).mp hrest φ (Finset.mem_erase.mpr ⟨hφω, hφ⟩))
  obtain ⟨hωB, hωp, hωα⟩ := (hmemR ω).mp hωR
  obtain ⟨τ₀, hτ₀, hCωτ⟩ : ∃ τ₀ : ℤ, (τ₀ = 1 ∨ τ₀ = -1) ∧ C ω = 2 * τ₀ := by
    have h1 : C ω ≤ 2 := by nlinarith
    have h2 : -2 ≤ C ω := by nlinarith
    obtain ⟨k, hk⟩ := hCReven ω hωR
    rcases (by omega : C ω = 2 ∨ C ω = -2) with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; norm_num⟩
  have hCrep : ∀ φ ∈ B, C φ = unitVector p φ + ∑ i, C (α i) * unitVector (α i) φ +
      2 * τ₀ * unitVector ω φ := by
    intro φ hφ
    by_cases hφp : φ = p
    · subst hφp
      rw [hCp, unitVector_self, sum_mul_unitVector_of_forall_ne _ fun i => (hαp i).symm,
        unitVector_of_ne (Ne.symm hωp)]
      ring
    by_cases hφα : ∃ i, φ = α i
    · obtain ⟨i, rfl⟩ := hφα
      rw [unitVector_of_ne (hαp i), sum_mul_unitVector_apply hαinj,
        unitVector_of_ne fun h => hωα i h.symm]
      ring
    · push Not at hφα
      have hφR : φ ∈ R := (hmemR φ).mpr ⟨hφ, hφp, hφα⟩
      rw [unitVector_of_ne hφp, sum_mul_unitVector_of_forall_ne _ hφα]
      by_cases hφω : φ = ω
      · subst hφω
        rw [unitVector_self, hCωτ]
        ring
      · rw [hCRω φ hφR hφω, unitVector_of_ne hφω]
        ring
  have hη : ∀ i, η i = 1 ∨ η i = -1 := fun i => by
    by_cases hie : i = e
    · subst hie
      rw [hηe]
      rcases hβ i with h | h <;> rw [h] <;> norm_num
    · rw [hηi i hie]
      exact hβ i
  have hωχ : ∀ j ∈ J, ω ≠ χ j := by
    intro j hj hωj
    have h1 := hCx j hj
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hx j hj φ hφ],
      sum_mul_neg_unit_add_sum_add hp hα (hχ j hj), hCp, ← hωj, hCωτ, Fin.sum_univ_three] at h1
    have h2 := hdC
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hCrep φ hφ],
      sum_mul_unit_add_sum_add hp hα hωB, hdp, Fin.sum_univ_three] at h2
    have h3 := hdx j hj
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hx j hj φ hφ],
      sum_mul_neg_unit_add_sum_add hp hα (hχ j hj), hdp, ← hωj, Fin.sum_univ_three] at h3
    have hdω := hd ω hωB
    have hP0 := sign_mul (hη 0) (hCα 0)
    have hP1 := sign_mul (hη 1) (hCα 1)
    have hP2 := sign_mul (hη 2) (hCα 2)
    have hQ := sign_mul hσ hτ₀
    have h1' : -1 + (η 0 * C (α 0) + η 1 * C (α 1) + η 2 * C (α 2)) + 4 * (σ * τ₀) = 0 := by
      linear_combination h1
    have hQ1 : σ * τ₀ = 1 := by omega
    have hneg : ∀ i, η i * C (α i) = -1 → C (α i) = -η i := fun i h => by
      rcases hη i with hi | hi <;> rw [hi] at h ⊢ <;> linarith
    have hc0 := hneg 0 (by omega)
    have hc1 := hneg 1 (by omega)
    have hc2 := hneg 2 (by omega)
    have hστ : σ = τ₀ := by
      rcases hσ with rfl | rfl <;> rcases hτ₀ with rfl | rfl <;> first | rfl | norm_num at hQ1
    subst hστ
    rw [hc0, hc1, hc2] at h2
    rcases hσ with rfl | rfl <;> linarith
  obtain ⟨j₀, hj₀⟩ := hJ
  have hCχ0 : C (χ j₀) = 0 := hCRω (χ j₀)
    ((hmemR _).mpr ⟨hχ j₀ hj₀, hχp j₀ hj₀, hχα j₀ hj₀⟩) fun h => hωχ j₀ hj₀ h.symm
  have e1 := hCx j₀ hj₀
  rw [Finset.sum_congr rfl fun φ hφ => by rw [hx j₀ hj₀ φ hφ],
    sum_mul_neg_unit_add_sum_add hp hα (hχ j₀ hj₀), hCp, hCχ0] at e1
  have e2 := hCy₀
  rw [Finset.sum_congr rfl fun φ hφ => by rw [hy₀ φ hφ], sum_mul_unit_add_sum hp hα,
    hCp] at e2
  have hsplitη : ∑ i, η i * C (α i) = ∑ i, β i * C (α i) - 2 * (β e * C (α e)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e),
      ← Finset.add_sum_erase _ (fun i => β i * C (α i)) (Finset.mem_univ e), hηe,
      Finset.sum_congr rfl fun i hi => by rw [hηi i (Finset.ne_of_mem_erase hi)]]
    ring
  have hhe : β e * C (α e) = -1 := by linarith
  have hsign : ∀ i, β i * C (α i) = 1 ∨ β i * C (α i) = -1 := fun i => sign_mul (hβ i) (hCα i)
  obtain ⟨f, g, hfe, hge, hfg, hf1, hg1⟩ := exists_pair_of_sum_eq hsign hhe (by linarith)
  have hval : ∀ i, β i * C (α i) = 1 → C (α i) = β i := fun i h => by
    rcases hβ i with hi | hi <;> rw [hi] at h ⊢ <;> linarith
  have hval' : ∀ i, β i * C (α i) = -1 → C (α i) = -β i := fun i h => by
    rcases hβ i with hi | hi <;> rw [hi] at h ⊢ <;> linarith
  have hCe := hval' e hhe
  have hCf := hval f hf1
  have hCg := hval' g hg1
  have e3 := hdC
  rw [Finset.sum_congr rfl fun φ hφ => by rw [hCrep φ hφ], sum_mul_unit_add_sum_add hp hα hωB,
    hdp, sum_fin_three_eq hfe hge hfg, hCe, hCf, hCg] at e3
  have e4 := hdy₀
  rw [Finset.sum_congr rfl fun φ hφ => by rw [hy₀ φ hφ], sum_mul_unit_add_sum hp hα, hdp,
    sum_fin_three_eq hfe hge hfg] at e4
  have hdf := hd (α f) (hα f)
  have hdω := hd ω hωB
  have hβf : β f = -τ₀ := by
    rcases hβ f with hb | hb <;> rcases hτ₀ with rfl | rfl <;> rw [hb] at e3 e4 ⊢ <;>
      first | rfl | linarith
  refine ⟨ω, hωB, hωp, hωα, hωχ, f, g, hfe, hge, hfg, τ₀, hτ₀, hβf, ?_, fun φ hφ => ?_⟩
  · rw [hβf] at e3 e4
    rcases hτ₀ with rfl | rfl <;> linarith
  · rw [hCrep φ hφ, sum_fin_three_eq hfe hge hfg, hCe, hCf, hCg, hβe, hβf]
    ring

theorem five_core_unique {α : Fin 3 → ι} {σ : ℤ} {e f g f' g' : Fin 3} {ω ω' : ι}
    {τ₀ τ₀' κ κ' : ℤ} {y₀ C : ι → ℤ} (hα : ∀ i, α i ∈ B) (hαinj : Function.Injective α)
    (hαp : ∀ i, α i ≠ p) (hfe : f ≠ e) (hge : g ≠ e) (hfg : f ≠ g) (hfe' : f' ≠ e)
    (hge' : g' ≠ e) (hfg' : f' ≠ g') (hωB : ω ∈ B) (hωp : ω ≠ p) (hωα : ∀ i, ω ≠ α i)
    (hωp' : ω' ≠ p) (hωα' : ∀ i, ω' ≠ α i) (hτ₀ : τ₀ = 1 ∨ τ₀ = -1)
    (hy : ∀ φ ∈ B, y₀ φ = unitVector p φ + σ * unitVector (α e) φ - τ₀ * unitVector (α f) φ +
      κ * unitVector (α g) φ)
    (hy' : ∀ φ ∈ B, y₀ φ = unitVector p φ + σ * unitVector (α e) φ -
      τ₀' * unitVector (α f') φ + κ' * unitVector (α g') φ)
    (hC : ∀ φ ∈ B, C φ = unitVector p φ - σ * unitVector (α e) φ - τ₀ * unitVector (α f) φ -
      κ * unitVector (α g) φ + 2 * τ₀ * unitVector ω φ)
    (hC' : ∀ φ ∈ B, C φ = unitVector p φ - σ * unitVector (α e) φ -
      τ₀' * unitVector (α f') φ - κ' * unitVector (α g') φ + 2 * τ₀' * unitVector ω' φ) :
    ω' = ω ∧ f' = f ∧ g' = g ∧ τ₀' = τ₀ ∧ κ' = κ := by
  have hτ0 : τ₀ ≠ 0 := by rcases hτ₀ with h | h <;> rw [h] <;> norm_num
  have hωω : ω' = ω ∧ τ₀' = τ₀ := by
    have h := (hC ω hωB).symm.trans (hC' ω hωB)
    by_cases hω : ω = ω'
    · subst hω
      simp only [unitVector, hωp, hωα, ite_false, ite_true] at h
      exact ⟨rfl, by linarith⟩
    · simp only [unitVector, hωp, hωα, hω, ite_false, ite_true] at h
      exact absurd (by linarith : τ₀ = 0) hτ0
  obtain ⟨hω', hτ'⟩ := hωω
  subst ω'
  subst τ₀'
  have hff : f' = f := by
    rcases fin_three_eq_or_eq hfe' hge' hfg' hfe with h | h
    · exact h.symm
    · exfalso
      have h1 := (hC (α f) (hα f)).symm.trans (hC' (α f) (hα f))
      have h2 := (hy (α f) (hα f)).symm.trans (hy' (α f) (hα f))
      rw [← h] at hfg' h1 h2
      have hfω : α f ≠ ω := fun h => hωα f h.symm
      simp only [unitVector, hαinj.eq_iff, hfe, hfg, hfg'.symm, (hαp f), hfω,
        ite_false, ite_true] at h1 h2
      exact hτ0 (by linarith)
  subst hff
  have hgg : g' = g := by
    rcases fin_three_eq_or_eq hfe hge hfg hge' with h | h
    · exact absurd h hfg'.symm
    · exact h
  subst hgg
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  have h2 := (hy (α g') (hα g')).symm.trans (hy' (α g') (hα g'))
  simp only [unitVector, hαinj.eq_iff, hge, hfg'.symm, (hαp g'), ite_false, ite_true] at h2
  linarith

end CFSG.Wreathed.ConditionalFiveFixed
