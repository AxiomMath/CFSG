module

public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedInteger

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalFiveFixed

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalOddFourier
  CFSG.Wreathed.ConditionalUniformOddFourier

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p : ι}

theorem five_fixed_count {M : ℕ} (hM : 1 ≤ M) {J : Finset ℕ} (hJcard : J.card = M)
    {q₁ q₂ q₃ q₄ q₅ : ι} {χ : ℕ → ι} {γ : ℕ → Fin 4 → ι} (h₁ : q₁ ∈ B) (h₂ : q₂ ∈ B)
    (h₃ : q₃ ∈ B) (h₄ : q₄ ∈ B) (h₅ : q₅ ∈ B) (h21 : q₂ ≠ q₁) (h31 : q₃ ≠ q₁) (h32 : q₃ ≠ q₂)
    (h41 : q₄ ≠ q₁) (h42 : q₄ ≠ q₂) (h43 : q₄ ≠ q₃) (h51 : q₅ ≠ q₁) (h52 : q₅ ≠ q₂)
    (h53 : q₅ ≠ q₃) (h54 : q₅ ≠ q₄) (hχB : ∀ j ∈ J, χ j ∈ B) (hχinj : Set.InjOn χ J)
    (hχq : ∀ j ∈ J, χ j ≠ q₁ ∧ χ j ≠ q₂ ∧ χ j ≠ q₃ ∧ χ j ≠ q₄ ∧ χ j ≠ q₅)
    (hγB : ∀ r ∈ Finset.Ico 1 M, ∀ l, γ r l ∈ B)
    (hγinj : ∀ r ∈ Finset.Ico 1 M, Function.Injective (γ r))
    (hγdisj : ∀ r ∈ Finset.Ico 1 M, ∀ t ∈ Finset.Ico 1 M, r ≠ t → ∀ l l', γ r l ≠ γ t l')
    (hγq : ∀ r ∈ Finset.Ico 1 M, ∀ l,
      γ r l ≠ q₁ ∧ γ r l ≠ q₂ ∧ γ r l ≠ q₃ ∧ γ r l ≠ q₄ ∧ γ r l ≠ q₅)
    (hγχ : ∀ r ∈ Finset.Ico 1 M, ∀ l, ∀ j ∈ J, γ r l ≠ χ j) :
    (({q₁, q₂, q₃, q₄, q₅} : Finset ι) ∪ J.image χ ∪
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 4))).image
          (fun rl => γ rl.1 rl.2)) ⊆ B ∧
      (({q₁, q₂, q₃, q₄, q₅} : Finset ι) ∪ J.image χ ∪
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 4))).image
          (fun rl => γ rl.1 rl.2)).card = 1 + 5 * M := by
  set Q : Finset ι := {q₁, q₂, q₃, q₄, q₅} with hQ
  set X := J.image χ with hX
  set Γ := ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 4))).image
    (fun rl => γ rl.1 rl.2) with hΓ
  have hmemQ : ∀ φ, φ ∈ Q ↔ φ = q₁ ∨ φ = q₂ ∨ φ = q₃ ∨ φ = q₄ ∨ φ = q₅ := fun φ => by
    simp [hQ]
  refine ⟨?_, ?_⟩
  · intro φ hφ
    rcases Finset.mem_union.mp hφ with hφ | hφ
    · rcases Finset.mem_union.mp hφ with hφ | hφ
      · rcases (hmemQ φ).mp hφ with rfl | rfl | rfl | rfl | rfl <;> assumption
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hφ
        exact hχB j hj
    · obtain ⟨⟨r, l⟩, hrl, rfl⟩ := Finset.mem_image.mp hφ
      exact hγB r (Finset.mem_product.mp hrl).1 l
  have hcQ : Q.card = 5 := by
    rw [hQ, Finset.card_insert_of_notMem (by simp [h21.symm, h31.symm, h41.symm, h51.symm]),
      Finset.card_insert_of_notMem (by simp [h32.symm, h42.symm, h52.symm]),
      Finset.card_insert_of_notMem (by simp [h43.symm, h53.symm]),
      Finset.card_pair (Ne.symm h54)]
  have hcX : X.card = M := by rw [hX, Finset.card_image_of_injOn hχinj, hJcard]
  have hcΓ : Γ.card = (M - 1) * 4 := by
    rw [hΓ, Finset.card_image_of_injOn, Finset.card_product, Nat.card_Ico, Finset.card_univ,
      Fintype.card_fin]
    rintro ⟨r, l⟩ hrl ⟨t, l'⟩ htl' h
    have hr := (Finset.mem_product.mp hrl).1
    have ht := (Finset.mem_product.mp htl').1
    simp only at h
    by_cases hrt : r = t
    · subst hrt
      rw [hγinj r hr h]
    · exact absurd h (hγdisj r hr t ht hrt l l')
  have hQX : Disjoint Q X := by
    rw [Finset.disjoint_left]
    intro φ hφQ hφX
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hφX
    obtain ⟨n1, n2, n3, n4, n5⟩ := hχq j hj
    rcases (hmemQ _).mp hφQ with h | h | h | h | h <;> contradiction
  have hQXΓ : Disjoint (Q ∪ X) Γ := by
    rw [Finset.disjoint_left]
    intro φ hφ hφΓ
    obtain ⟨⟨r, l⟩, hrl, rfl⟩ := Finset.mem_image.mp hφΓ
    have hr := (Finset.mem_product.mp hrl).1
    rcases Finset.mem_union.mp hφ with hφQ | hφX
    · obtain ⟨n1, n2, n3, n4, n5⟩ := hγq r hr l
      rcases (hmemQ _).mp hφQ with h | h | h | h | h <;> contradiction
    · obtain ⟨j, hj, h⟩ := Finset.mem_image.mp hφX
      exact hγχ r hr l j hj h.symm
  rw [Finset.card_union_of_disjoint hQXΓ, Finset.card_union_of_disjoint hQX, hcQ, hcX, hcΓ]
  omega


theorem five_fixed_columns {m M : ℕ} (hm : m = 2 * M) (hM : 2 ≤ M) {J : Finset ℕ}
    (hJ : J = (Finset.Ico 1 m).filter Odd) (hJcard : J.card = M) {y x : ℕ → ι → ℤ}
    {C d : ι → ℤ} {α : Fin 3 → ι} {β η : Fin 3 → ℤ} {σ : ℤ} {χ : ℕ → ι} {δ : ℤ} {e : Fin 3}
    (hp : p ∈ B) (hd : ∀ φ ∈ B, 0 < d φ) (hdp : d p = 1) (hα : ∀ i, α i ∈ B)
    (hαinj : Function.Injective α) (hαp : ∀ i, α i ≠ p) (hβ : ∀ i, β i = 1 ∨ β i = -1)
    (hσ : σ = 1 ∨ σ = -1) (hχB : ∀ j ∈ J, χ j ∈ B) (hχp : ∀ j ∈ J, χ j ≠ p)
    (hχα : ∀ j ∈ J, ∀ i, χ j ≠ α i) (hχinj : Set.InjOn χ J) (hηe : η e = -β e)
    (hηi : ∀ i, i ≠ e → η i = β i) (hβe : β e = σ) (hdχ : ∀ j ∈ J, d (χ j) = δ)
    (hy0 : ∀ φ ∈ B, y 0 φ = unitVector p φ + ∑ i, β i * unitVector (α i) φ)
    (hxJ : ∀ j ∈ J, ∀ φ ∈ B, x j φ = -unitVector p φ + ∑ i, η i * unitVector (α i) φ +
      2 * σ * unitVector (χ j) φ)
    (hxA : ∀ t ∈ Finset.Ico 1 m, x t (α e) = -σ) (hyχ : ∀ j ∈ J, ∀ r < M, y r (χ j) = 0)
    (hyA : ∀ r, 0 < r → r < M → y r (α e) = 0) (hyp : ∀ r, 0 < r → r < M → y r p = 0)
    (hyv : ∀ r < M, ∀ φ ∈ B, y r φ = 0 ∨ y r φ = 1 ∨ y r φ = -1)
    (hy4 : ∀ r < M, (B.filter fun φ => y r φ ≠ 0).card = 4)
    (hygram : ∀ r < M, ∀ t < M, ∑ φ ∈ B, y r φ * y t φ = if r = t then 4 else 0)
    (hydeg : ∀ r < M, ∑ φ ∈ B, d φ * y r φ = 0)
    (hxgram : ∀ j ∈ Finset.Ico 1 m, ∀ t ∈ Finset.Ico 1 m,
      ∑ φ ∈ B, x j φ * x t φ = if j = t then 8 else 4)
    (hxdeg : ∀ j ∈ Finset.Ico 1 m, ∑ φ ∈ B, d φ * x j φ = 0)
    (hxp : ∀ j ∈ Finset.Ico 1 m, x j p = -1)
    (hyx : ∀ r < M, ∀ j ∈ Finset.Ico 1 m, ∑ φ ∈ B, y r φ * x j φ = 0)
    (hpar : ∀ r, 0 < r → r < M → ∀ φ ∈ B, x (m - 2 * r) φ ≡ y 0 φ + y r φ [ZMOD 2])
    (hCsq : ∑ φ ∈ B, C φ * C φ = 8) (hCp : C p = 1) (hCpar : ∀ φ ∈ B, C φ ≡ y 0 φ [ZMOD 2])
    (hCx : ∀ j ∈ Finset.Ico 1 m, ∑ φ ∈ B, C φ * x j φ = 0)
    (hCy : ∀ r < M, ∑ φ ∈ B, C φ * y r φ = 0) (hCdeg : ∑ φ ∈ B, d φ * C φ = 0) :
    ∃ (ω : ι) (f g : Fin 3) (τ₀ : ℤ), ω ∈ B ∧ ω ≠ p ∧ (∀ i, ω ≠ α i) ∧ (∀ j ∈ J, ω ≠ χ j) ∧
      f ≠ e ∧ g ≠ e ∧ f ≠ g ∧ (τ₀ = 1 ∨ τ₀ = -1) ∧ β f = -τ₀ ∧ d ω = d (α f) - τ₀ ∧
      (∀ φ ∈ B, y 0 φ = unitVector p φ + σ * unitVector (α e) φ - τ₀ * unitVector (α f) φ +
        β g * unitVector (α g) φ) ∧
      (∀ j ∈ J, ∀ φ ∈ B, x j φ = fixedPart p (α e) (α f) (α g) σ τ₀ (β g) φ +
        2 * σ * unitVector (χ j) φ) ∧
      (∀ φ ∈ B, C φ = unitVector p φ - σ * unitVector (α e) φ - τ₀ * unitVector (α f) φ -
        β g * unitVector (α g) φ + 2 * τ₀ * unitVector ω φ) ∧
      (∀ t ∈ Finset.Ico 1 m, x t (α f) = -τ₀ ∧ x t (α g) = β g ∧ x t ω = 0) ∧
      (∀ r, 0 < r → r < M → y r (α f) = 0 ∧ y r (α g) = 0 ∧ y r ω = 0) ∧
      ∃ (γ : ℕ → Fin 4 → ι) (ε : ℕ → Fin 4 → ℤ),
        (∀ r, 0 < r → r < M →
          Function.Injective (γ r) ∧ (∀ l, γ r l ∈ B) ∧ (∀ l, ε r l = 1 ∨ ε r l = -1) ∧
          (∀ φ ∈ B, y r φ ≠ 0 ↔ ∃ l, φ = γ r l) ∧
          (∀ φ ∈ B, y r φ = ∑ l, (quadSign l * ε r l) * unitVector (γ r l) φ) ∧
          (∀ φ ∈ B, x (m - 2 * r) φ = fixedPart p (α e) (α f) (α g) σ τ₀ (β g) φ +
            ∑ l, ε r l * unitVector (γ r l) φ) ∧
          (∀ l, γ r l ≠ p ∧ (∀ i, γ r l ≠ α i) ∧ γ r l ≠ ω ∧ ∀ j ∈ J, γ r l ≠ χ j) ∧
          ε r 0 * d (γ r 0) + ε r 1 * d (γ r 1) = σ * δ ∧
          ε r 2 * d (γ r 2) + ε r 3 * d (γ r 3) = σ * δ) ∧
        (∀ r t, 0 < r → r < M → 0 < t → t < M → r ≠ t → ∀ l l', γ r l ≠ γ t l') ∧
        (∀ r, 0 < r → r < M → ∀ l, ∀ t ∈ Finset.Ico 1 m,
          x t (γ r l) = if t = m - 2 * r then ε r l else 0) ∧
        (∀ r, 0 < r → r < M → ∀ l, ∀ t < M,
          y t (γ r l) = if t = r then quadSign l * ε r l else 0) ∧
        (({p, α e, α f, α g, ω} : Finset ι) ∪ J.image χ ∪
            ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 4))).image
              (fun rl => γ rl.1 rl.2)) ⊆ B ∧
        (({p, α e, α f, α g, ω} : Finset ι) ∪ J.image χ ∪
            ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 4))).image
              (fun rl => γ rl.1 rl.2)).card = 1 + 5 * M := by
  have hJI : ∀ j ∈ J, j ∈ Finset.Ico 1 m := fun j hj => by
    rw [hJ] at hj
    exact (Finset.mem_filter.mp hj).1
  have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
  have hM0 : 0 < M := by omega
  have hcomm : ∀ f g : ι → ℤ, ∑ φ ∈ B, f φ * g φ = ∑ φ ∈ B, g φ * f φ :=
    fun f g => Finset.sum_congr rfl fun φ _ => mul_comm _ _
  obtain ⟨ω, hωB, hωp, hωα, hωχ, f, g, hfe, hge, hfg, τ₀, hτ₀, hβf, hdω, hC⟩ :=
    five_core hp hα hαinj hαp hχB hχp hχα hJne hβ hσ hηe hηi hβe hy0 hxJ hd hdp
      (hydeg 0 hM0) (fun j hj => hxdeg j (hJI j hj)) hCdeg hCsq hCp hCpar (hCy 0 hM0)
      (fun j hj => hCx j (hJI j hj))
  have hκ : β g = 1 ∨ β g = -1 := hβ g
  have hsum3 : ∀ u : Fin 3 → ℤ, ∑ i, u i = u e + u f + u g := sum_fin_three_eq hfe hge hfg
  have hy0' : ∀ φ ∈ B, y 0 φ = unitVector p φ + σ * unitVector (α e) φ -
      τ₀ * unitVector (α f) φ + β g * unitVector (α g) φ := by
    intro φ hφ
    rw [hy0 φ hφ, hsum3, hβe, hβf]
    ring
  have hηf : η f = -τ₀ := by rw [hηi f hfe, hβf]
  have hηg : η g = β g := hηi g hge
  have hxJ' : ∀ j ∈ J, ∀ φ ∈ B, x j φ = fixedPart p (α e) (α f) (α g) σ τ₀ (β g) φ +
      2 * σ * unitVector (χ j) φ := by
    intro j hj φ hφ
    rw [hxJ j hj φ hφ, hsum3, hηe, hβe, hηf, hηg, fixedPart]
    ring
  have hAp := hαp e
  have hBp := hαp f
  have hDp := hαp g
  have hBA : α f ≠ α e := fun h => hfe (hαinj h)
  have hDA : α g ≠ α e := fun h => hge (hαinj h)
  have hDB : α g ≠ α f := fun h => hfg (hαinj h).symm
  have hωA := hωα e
  have hωBq := hωα f
  have hωD := hωα g
  have hP1 : -d p - σ * d (α e) - τ₀ * d (α f) + β g * d (α g) = -(2 * σ * δ) := by
    obtain ⟨j₀, hj₀⟩ := hJne
    have h := hxdeg j₀ (hJI j₀ hj₀)
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hxJ' j₀ hj₀ φ hφ]] at h
    simp only [mul_add, Finset.sum_add_distrib] at h
    rw [sum_mul_fixedPart hp (hα e) (hα f) (hα g)] at h
    have h2 : ∑ φ ∈ B, d φ * (2 * σ * unitVector (χ j₀) φ) = 2 * σ * δ := by
      have h3 : ∀ φ, d φ * (2 * σ * unitVector (χ j₀) φ) =
          2 * σ * (d φ * unitVector (χ j₀) φ) := fun φ => by ring
      rw [Finset.sum_congr rfl fun φ _ => h3 φ, ← Finset.mul_sum,
        sum_mul_unitVector (hχB j₀ hj₀), hdχ j₀ hj₀]
    linarith
  have hodd_core : ∀ j ∈ J, x j (α f) = -τ₀ ∧ x j (α g) = β g ∧ x j ω = 0 := by
    intro j hj
    have hχf : α f ≠ χ j := fun h => hχα j hj f h.symm
    have hχg : α g ≠ χ j := fun h => hχα j hj g h.symm
    have hχω : ω ≠ χ j := hωχ j hj
    refine ⟨?_, ?_, ?_⟩
    · rw [hxJ' j hj _ (hα f)]
      simp [fixedPart, unitVector, hBp, hBA, hDB.symm, hχf]
    · rw [hxJ' j hj _ (hα g)]
      simp [fixedPart, unitVector, hDp, hDA, hDB, hχg]
    · rw [hxJ' j hj _ hωB]
      simp [fixedPart, unitVector, hωp, hωA, hωBq, hωD, hχω]
  have hk : ∀ r, 0 < r → r < M → m - 2 * r ∈ Finset.Ico 1 m := fun r h1 h2 => by
    rw [Finset.mem_Ico]
    omega
  have hEQ := fun r (hr0 : 0 < r) (hrM : r < M) => even_quadruple hp (hα e) (hα f) (hα g) hωB
    hAp hBp hDp hωp hBA hDA hωA hDB hωBq hωD hσ hτ₀ hκ hy0' hC (hyv r hrM) (hy4 r hrM)
    (hyp r hr0 hrM) (hyA r hr0 hrM)
    (by rw [hygram r hrM 0 hM0, ite_eq_right (by omega : ¬ r = 0)])
    (by rw [hcomm]; exact hCy r hrM) (hyx r hrM _ (hk r hr0 hrM)) (hxp _ (hk r hr0 hrM))
    (hxA _ (hk r hr0 hrM)) (by rw [hxgram _ (hk r hr0 hrM) _ (hk r hr0 hrM), ite_eq_left rfl])
    (by rw [hcomm]; exact hyx 0 hM0 _ (hk r hr0 hrM))
    (by rw [hcomm]; exact hCx _ (hk r hr0 hrM)) (hpar r hr0 hrM) (hxdeg _ (hk r hr0 hrM))
    (hydeg r hrM) hP1
  have hquad : ∀ r : ℕ, ∃ (γ : Fin 4 → ι) (ε : Fin 4 → ℤ), 0 < r → r < M →
      Function.Injective γ ∧ (∀ l, γ l ∈ B) ∧ (∀ l, ε l = 1 ∨ ε l = -1) ∧
      (∀ φ ∈ B, y r φ ≠ 0 ↔ ∃ l, φ = γ l) ∧
      (∀ φ ∈ B, y r φ = ∑ l, (quadSign l * ε l) * unitVector (γ l) φ) ∧
      (∀ φ ∈ B, x (m - 2 * r) φ = fixedPart p (α e) (α f) (α g) σ τ₀ (β g) φ +
        ∑ l, ε l * unitVector (γ l) φ) ∧
      (∀ l, γ l ≠ p ∧ γ l ≠ α e ∧ γ l ≠ α f ∧ γ l ≠ α g ∧ γ l ≠ ω) ∧
      ε 0 * d (γ 0) + ε 1 * d (γ 1) = σ * δ ∧ ε 2 * d (γ 2) + ε 3 * d (γ 3) = σ * δ := by
    intro r
    by_cases hr : 0 < r ∧ r < M
    · obtain ⟨-, -, -, -, -, -, γ, ε, h⟩ := hEQ r hr.1 hr.2
      exact ⟨γ, ε, fun _ _ => h⟩
    · exact ⟨fun _ => p, fun _ => 1, fun h1 h2 => absurd ⟨h1, h2⟩ hr⟩
  choose γ ε hγε using hquad
  have hγα : ∀ r, 0 < r → r < M → ∀ l i, γ r l ≠ α i := by
    intro r hr0 hrM l i
    obtain ⟨-, -, -, -, -, -, hcr, -, -⟩ := hγε r hr0 hrM
    obtain ⟨-, c2, c3, c4, -⟩ := hcr l
    by_cases hie : i = e
    · rw [hie]
      exact c2
    · rcases fin_three_eq_or_eq hfe hge hfg hie with h | h <;> rw [h]
      · exact c3
      · exact c4
  have hγχ : ∀ r, 0 < r → r < M → ∀ l, ∀ j ∈ J, γ r l ≠ χ j := by
    intro r hr0 hrM l j hj h
    obtain ⟨-, hBr, -, hsupp, -, -, -, -, -⟩ := hγε r hr0 hrM
    have hne := (hsupp _ (hBr l)).mpr ⟨l, rfl⟩
    rw [h, hyχ j hj r hrM] at hne
    exact hne rfl
  have hdisj : ∀ r t, 0 < r → r < M → 0 < t → t < M → r ≠ t → ∀ l l', γ r l ≠ γ t l' := by
    intro r t hr0 hrM ht0 htM hrt
    obtain ⟨hir, hBr, hεr, -, hyr, hxr, hcr, hr₀, hr₁⟩ := hγε r hr0 hrM
    obtain ⟨hit, hBt, hεt, -, hyt, hxt, hct, ht₀, ht₁⟩ := hγε t ht0 htM
    have hkr := hk r hr0 hrM
    have hkt := hk t ht0 htM
    have hkrt : ¬ m - 2 * r = m - 2 * t := by omega
    exact even_quadruples_disjoint hp (hα e) (hα f) (hα g) hAp hBp hDp hBA hDA hDB hσ hτ₀ hκ hd
      hir hit hBr hBt hεr hεt
      (fun l => ⟨(hcr l).1, (hcr l).2.1, (hcr l).2.2.1, (hcr l).2.2.2.1⟩)
      (fun l => ⟨(hct l).1, (hct l).2.1, (hct l).2.2.1, (hct l).2.2.2.1⟩) hxr hxt hyr hyt
      (by rw [hxgram _ hkr _ hkt, ite_eq_right hkrt])
      (by rw [hygram r hrM t htM, ite_eq_right hrt]) (hyx r hrM _ hkt) (hyx t htM _ hkr)
      hr₀ hr₁ ht₀ ht₁
  have hxγ : ∀ r, 0 < r → r < M → ∀ l, ∀ t ∈ Finset.Ico 1 m,
      x t (γ r l) = if t = m - 2 * r then ε r l else 0 := by
    intro r hr0 hrM l t ht
    obtain ⟨hir, hBr, -, -, -, -, hcr, -, -⟩ := hγε r hr0 hrM
    obtain ⟨c1, c2, c3, c4, -⟩ := hcr l
    have hPγ : fixedPart p (α e) (α f) (α g) σ τ₀ (β g) (γ r l) = 0 :=
      fixedPart_of_ne σ τ₀ (β g) c1 c2 c3 c4
    have ht' := Finset.mem_Ico.mp ht
    rcases Nat.even_or_odd t with ⟨k, hk'⟩ | hto
    · have hr'0 : 0 < (m - t) / 2 := by omega
      have hr'M : (m - t) / 2 < M := by omega
      have htk : t = m - 2 * ((m - t) / 2) := by omega
      obtain ⟨-, -, -, -, -, hxr', -, -, -⟩ := hγε _ hr'0 hr'M
      by_cases hrr : (m - t) / 2 = r
      · rw [ite_eq_left (by omega), htk, hxr' _ (hBr l), hrr, hPγ, zero_add,
          Finset.sum_eq_single l (fun l' _ hl' => by
            rw [unitVector_of_ne fun h => hl' (hir h).symm, mul_zero])
          fun h => absurd (Finset.mem_univ l) h, unitVector_self, mul_one]
      · rw [ite_eq_right (by omega), htk, hxr' _ (hBr l), hPγ, zero_add]
        exact Finset.sum_eq_zero fun l' _ => by
          rw [unitVector_of_ne (hdisj r _ hr0 hrM hr'0 hr'M (Ne.symm hrr) l l'), mul_zero]
    · have htJ : t ∈ J := by
        rw [hJ]
        exact Finset.mem_filter.mpr ⟨ht, hto⟩
      obtain ⟨k, hk'⟩ := hto
      rw [ite_eq_right (by omega), hxJ' t htJ _ (hBr l), hPγ, zero_add,
        unitVector_of_ne (hγχ r hr0 hrM l t htJ), mul_zero]
  have hyγ : ∀ r, 0 < r → r < M → ∀ l, ∀ t < M,
      y t (γ r l) = if t = r then quadSign l * ε r l else 0 := by
    intro r hr0 hrM l t htM
    obtain ⟨hir, hBr, -, -, hyr, -, hcr, -, -⟩ := hγε r hr0 hrM
    obtain ⟨c1, c2, c3, c4, -⟩ := hcr l
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · rw [ite_eq_right (by omega), hy0' _ (hBr l)]
      simp [unitVector, c1, c2, c3, c4]
    · by_cases htr : t = r
      · subst htr
        rw [ite_eq_left rfl, hyr _ (hBr l), Finset.sum_eq_single l (fun l' _ hl' => by
            rw [unitVector_of_ne fun h => hl' (hir h).symm, mul_zero])
          fun h => absurd (Finset.mem_univ l) h, unitVector_self, mul_one]
      · rw [ite_eq_right htr]
        obtain ⟨-, -, -, -, hyt, -, -, -, -⟩ := hγε t ht0 htM
        rw [hyt _ (hBr l)]
        exact Finset.sum_eq_zero fun l' _ => by
          rw [unitVector_of_ne (hdisj r t hr0 hrM ht0 htM (Ne.symm htr) l l'), mul_zero]
  have hrows : ∀ t ∈ Finset.Ico 1 m, x t (α f) = -τ₀ ∧ x t (α g) = β g ∧ x t ω = 0 := by
    intro t ht
    have ht' := Finset.mem_Ico.mp ht
    rcases Nat.even_or_odd t with ⟨k, hk'⟩ | hto
    · have hr0 : 0 < (m - t) / 2 := by omega
      have hrM : (m - t) / 2 < M := by omega
      have htk : t = m - 2 * ((m - t) / 2) := by omega
      obtain ⟨-, -, -, h1, h2, h3, -⟩ := hEQ _ hr0 hrM
      rw [htk]
      exact ⟨h1, h2, h3⟩
    · exact hodd_core t (by rw [hJ]; exact Finset.mem_filter.mpr ⟨ht, hto⟩)
  have hIco : ∀ r ∈ Finset.Ico 1 M, 0 < r ∧ r < M := fun r hr => by
    rw [Finset.mem_Ico] at hr
    omega
  obtain ⟨hsub, hcard⟩ := five_fixed_count (by omega) hJcard (hp) (hα e) (hα f) (hα g) hωB
    hAp hBp hBA hDp hDA hDB hωp hωA hωBq hωD hχB hχinj
    (fun j hj => ⟨hχp j hj, hχα j hj e, hχα j hj f, hχα j hj g, fun h => hωχ j hj h.symm⟩)
    (fun r hr l => (hγε r (hIco r hr).1 (hIco r hr).2).2.1 l)
    (fun r hr => (hγε r (hIco r hr).1 (hIco r hr).2).1)
    (fun r hr t ht hrt => hdisj r t (hIco r hr).1 (hIco r hr).2 (hIco t ht).1 (hIco t ht).2 hrt)
    (fun r hr l => by
      obtain ⟨c1, c2, c3, c4, c5⟩ := (hγε r (hIco r hr).1 (hIco r hr).2).2.2.2.2.2.2.1 l
      exact ⟨c1, c2, c3, c4, c5⟩)
    (fun r hr l j hj => hγχ r (hIco r hr).1 (hIco r hr).2 l j hj)
  refine ⟨ω, f, g, τ₀, hωB, hωp, hωα, hωχ, hfe, hge, hfg, hτ₀, hβf, hdω, hy0', hxJ', hC,
    hrows, fun r hr0 hrM => ?_, γ, ε, fun r hr0 hrM => ?_, hdisj, hxγ, hyγ, hsub, hcard⟩
  · obtain ⟨h1, h2, h3, -⟩ := hEQ r hr0 hrM
    exact ⟨h1, h2, h3⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, hcr, h8, h9⟩ := hγε r hr0 hrM
    exact ⟨h1, h2, h3, h4, h5, h6, fun l => ⟨(hcr l).1, hγα r hr0 hrM l, (hcr l).2.2.2.2,
      hγχ r hr0 hrM l⟩, h8, h9⟩

end CFSG.Wreathed.ConditionalFiveFixed
