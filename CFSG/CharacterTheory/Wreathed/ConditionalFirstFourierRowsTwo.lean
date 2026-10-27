module

public import CFSG.CharacterTheory.Wreathed.ConditionalFirstFourierRowsCore
public import CFSG.CharacterTheory.Wreathed.ConditionalUniformOddFourierTwo

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalFirstFourierRows

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalOddFourier
  CFSG.Wreathed.ConditionalUniformOddFourier

theorem exists_third : ∀ e f : Fin 3, ∃ g : Fin 3, g ≠ e ∧ g ≠ f := by decide

theorem sum_fin_three_of_ne {M : Type*} [AddCommMonoid M] {e f g : Fin 3} (hfe : f ≠ e)
    (hge : g ≠ e) (hgf : g ≠ f) (x : Fin 3 → M) : ∑ i, x i = x e + x f + x g := by
  have huniv : ({e, f, g} : Finset (Fin 3)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Fintype.card_fin,
      Finset.card_eq_three.mpr ⟨e, f, g, hfe.symm, hge.symm, hgf.symm, rfl⟩]
  rw [← huniv, Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hfe.symm, hge.symm⟩), Finset.sum_pair hgf.symm, add_assoc]

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p : ι}

theorem two_pos_shape {α : Fin 3 → ι} {β : Fin 3 → ℤ} {σ : ℤ} {e : Fin 3} {χ₁ χ₃ : ι}
    {d y₀ y₁ : ι → ℤ} (hσ : σ = 1 ∨ σ = -1) (hp : p ∈ B) (hαinj : Function.Injective α)
    (hα : ∀ i, α i ∈ B ∧ α i ≠ p) (hβ : ∀ i, β i = 1 ∨ β i = -1) (hβe : β e = σ)
    (h1B : χ₁ ∈ B) (h3B : χ₃ ∈ B) (h1p : χ₁ ≠ p) (h3p : χ₃ ≠ p) (h1α : ∀ i, χ₁ ≠ α i)
    (h3α : ∀ i, χ₃ ≠ α i) (h13 : χ₁ ≠ χ₃) (hdpos : ∀ φ ∈ B, 0 < d φ) (hdp : d p = 1)
    (hd13 : d χ₃ = d χ₁)
    (hy₀ : ∀ φ ∈ B, y₀ φ = unitVector p φ + ∑ i, β i * unitVector (α i) φ)
    (hy₀deg : ∑ φ ∈ B, d φ * y₀ φ = 0)
    (hy₁val : ∀ φ ∈ B, y₁ φ = 0 ∨ y₁ φ = 1 ∨ y₁ φ = -1)
    (hy₁4 : (B.filter fun φ => y₁ φ ≠ 0).card = 4) (hy₁p : y₁ p = 0)
    (hy01 : ∑ φ ∈ B, y₀ φ * y₁ φ = 0) (hy₁deg : ∑ φ ∈ B, d φ * y₁ φ = 0)
    (h1eq : y₁ χ₁ = y₁ (α e)) (h3eq : y₁ χ₃ = y₁ (α e)) (ha : y₁ (α e) ≠ 0) :
    ∃ f g : Fin 3, f ≠ e ∧ g ≠ e ∧ g ≠ f ∧
      (∀ φ ∈ B, y₁ φ = y₁ (α e) * (unitVector (α e) φ + unitVector χ₁ φ + unitVector χ₃ φ -
        unitVector (α f) φ)) ∧
      β f = σ ∧ β g = -σ ∧ d (α f) = d (α e) + 2 * d χ₁ := by
  have haval : y₁ (α e) = 1 ∨ y₁ (α e) = -1 := by
    rcases hy₁val (α e) (hα e).1 with h | h | h
    · exact absurd h ha
    · exact Or.inl h
    · exact Or.inr h
  have he1 : α e ≠ χ₁ := fun h => h1α e h.symm
  have he3 : α e ≠ χ₃ := fun h => h3α e h.symm
  have hS : ({α e, χ₁, χ₃} : Finset ι) ⊆ B.filter fun φ => y₁ φ ≠ 0 := by
    intro φ hφ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
    rw [Finset.mem_filter]
    rcases hφ with h | h | h <;> rw [h]
    · exact ⟨(hα e).1, ha⟩
    · exact ⟨h1B, by rw [h1eq]; exact ha⟩
    · exact ⟨h3B, by rw [h3eq]; exact ha⟩
  have hdiff : ((B.filter fun φ => y₁ φ ≠ 0) \ {α e, χ₁, χ₃}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hS, hy₁4,
      Finset.card_eq_three.mpr ⟨α e, χ₁, χ₃, he1, he3, h13, rfl⟩]
  obtain ⟨ψ, hψ⟩ := Finset.card_eq_one.mp hdiff
  have hψmem : ψ ∈ (B.filter fun φ => y₁ φ ≠ 0) \ {α e, χ₁, χ₃} := by
    rw [hψ]
    exact Finset.mem_singleton_self ψ
  rw [Finset.mem_sdiff, Finset.mem_filter] at hψmem
  obtain ⟨⟨hψB, hψ0⟩, hψS⟩ := hψmem
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hψS
  obtain ⟨hψe, hψ1, hψ3⟩ := hψS
  have hψp : ψ ≠ p := fun h => hψ0 (by rw [h, hy₁p])
  have hy₁zero : ∀ φ ∈ B, φ ≠ α e → φ ≠ χ₁ → φ ≠ χ₃ → φ ≠ ψ → y₁ φ = 0 := by
    intro φ hφ h1 h2 h3 h4
    by_contra hne
    have hmem : φ ∈ (B.filter fun φ => y₁ φ ≠ 0) \ {α e, χ₁, χ₃} := by
      rw [Finset.mem_sdiff, Finset.mem_filter]
      refine ⟨⟨hφ, hne⟩, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1, h2, h3⟩
    rw [hψ, Finset.mem_singleton] at hmem
    exact h4 hmem
  have hbval : y₁ ψ = 1 ∨ y₁ ψ = -1 := by
    rcases hy₁val ψ hψB with h | h | h
    · exact absurd h hψ0
    · exact Or.inl h
    · exact Or.inr h
  have hsum : ∀ g : ι → ℤ, ∑ φ ∈ B, y₁ φ * g φ =
      y₁ (α e) * g (α e) + y₁ (α e) * g χ₁ + y₁ (α e) * g χ₃ + y₁ ψ * g ψ := by
    intro g
    rw [sum_mul_four (hα e).1 h1B h3B hψB (h1α e) h13 (Ne.symm hψ1) (h3α e) hψe (Ne.symm hψ3)
      hy₁zero g, h1eq, h3eq]
  have hy₀χ : ∀ χ ∈ B, χ ≠ p → (∀ i, χ ≠ α i) → y₀ χ = 0 := by
    intro χ hχ hχp hχα
    rw [hy₀ χ hχ, unitVector_of_ne hχp, sum_mul_unitVector_of_forall_ne β hχα, zero_add]
  have hy₀α : ∀ k, y₀ (α k) = β k := by
    intro k
    rw [hy₀ (α k) (hα k).1, unitVector_of_ne (hα k).2, sum_mul_unitVector_apply hαinj, zero_add]
  have horth := hy01
  rw [Finset.sum_congr rfl fun φ _ => mul_comm (y₀ φ) (y₁ φ), hsum, hy₀α e, hβe,
    hy₀χ χ₁ h1B h1p h1α, hy₀χ χ₃ h3B h3p h3α] at horth
  obtain ⟨f, rfl⟩ : ∃ f, ψ = α f := by
    by_contra hno
    rw [hy₀χ ψ hψB hψp (fun i h => hno ⟨i, h⟩)] at horth
    rcases haval with h | h <;> rcases hσ with hs | hs <;> rw [h, hs] at horth <;>
      norm_num at horth
  have hfe : f ≠ e := fun h => hψe (by rw [h])
  rw [hy₀α f] at horth
  have hdeg := hy₁deg
  rw [Finset.sum_congr rfl fun φ _ => mul_comm (d φ) (y₁ φ), hsum, hd13] at hdeg
  have hde := hdpos (α e) (hα e).1
  have hdf := hdpos (α f) (hα f).1
  have hd1 := hdpos χ₁ h1B
  have hb : y₁ (α f) = -y₁ (α e) := by
    rcases haval with h | h <;> rcases hbval with h' | h' <;> rw [h, h'] at hdeg <;> omega
  have hβf : β f = σ := by
    rw [hb] at horth
    rcases haval with h | h <;> rcases hσ with hs | hs <;> rw [h, hs] at horth <;>
      linarith only [horth, hs]
  obtain ⟨g, hge, hgf⟩ := exists_third e f
  have hY0 : 1 + ∑ i, β i * d (α i) = 0 := by
    have hcongr : ∑ φ ∈ B, d φ * y₀ φ =
        ∑ φ ∈ B, d φ * (1 * unitVector p φ + ∑ i, β i * unitVector (α i) φ) :=
      Finset.sum_congr rfl fun φ hφ => by rw [hy₀ φ hφ, one_mul]
    rw [← hy₀deg, hcongr, sum_mul_unitVector_add_sum hp (fun i => (hα i).1), hdp, mul_one]
  rw [sum_fin_three_of_ne hfe hge hgf (fun i => β i * d (α i)), hβe, hβf] at hY0
  have hdg := hdpos (α g) (hα g).1
  have hβg : β g = -σ := by
    rcases hβ g with h | h <;> rcases hσ with hs | hs <;> rw [h, hs] at hY0 <;> omega
  have hef : α e ≠ α f := fun h => hfe (hαinj h).symm
  refine ⟨f, g, hfe, hge, hgf, fun φ hφ => ?_, hβf, hβg, ?_⟩
  · by_cases hφe : φ = α e
    · rw [hφe, unitVector_self, unitVector_of_ne he1, unitVector_of_ne he3,
        unitVector_of_ne hef]
      ring
    by_cases hφ1 : φ = χ₁
    · rw [hφ1, h1eq, unitVector_of_ne (h1α e), unitVector_self, unitVector_of_ne h13,
        unitVector_of_ne (h1α f)]
      ring
    by_cases hφ3 : φ = χ₃
    · rw [hφ3, h3eq, unitVector_of_ne (h3α e), unitVector_of_ne (Ne.symm h13), unitVector_self,
        unitVector_of_ne (h3α f)]
      ring
    by_cases hφf : φ = α f
    · rw [hφf, hb, unitVector_of_ne (Ne.symm hef), unitVector_of_ne (Ne.symm (h1α f)),
        unitVector_of_ne (Ne.symm (h3α f)), unitVector_self]
      ring
    rw [hy₁zero φ hφ hφe hφ1 hφ3 hφf, unitVector_of_ne hφe, unitVector_of_ne hφ1,
      unitVector_of_ne hφ3, unitVector_of_ne hφf]
    ring
  · rw [hb] at hdeg
    rcases haval with h | h <;> rw [h] at hdeg <;> linarith only [hdeg]

theorem sum_five (G : ι → ℤ) {q₁ q₂ q₃ q₄ q₅ : ι} (h12 : q₁ ≠ q₂) (h13 : q₁ ≠ q₃)
    (h14 : q₁ ≠ q₄) (h15 : q₁ ≠ q₅) (h23 : q₂ ≠ q₃) (h24 : q₂ ≠ q₄) (h25 : q₂ ≠ q₅)
    (h34 : q₃ ≠ q₄) (h35 : q₃ ≠ q₅) (h45 : q₄ ≠ q₅) :
    ∑ φ ∈ ({q₁, q₂, q₃, q₄, q₅} : Finset ι), G φ = G q₁ + G q₂ + G q₃ + G q₄ + G q₅ := by
  have h1 : q₁ ∉ ({q₂, q₃, q₄, q₅} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h12, h13, h14, h15⟩
  have h2 : q₂ ∉ ({q₃, q₄, q₅} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h23, h24, h25⟩
  have h3 : q₃ ∉ ({q₄, q₅} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h34, h35⟩
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_pair h45]
  ring

theorem two_pos_contradiction {α : Fin 3 → ι} {β : Fin 3 → ℤ} {σ a : ℤ} {e f g : Fin 3}
    {χ₁ χ₃ : ι} {d y₀ y₁ c₁ c₂ c₃ : ι → ℤ} (hσ : σ = 1 ∨ σ = -1) (ha : a = 1 ∨ a = -1)
    (hp : p ∈ B) (hαinj : Function.Injective α) (hα : ∀ i, α i ∈ B ∧ α i ≠ p) (hfe : f ≠ e)
    (hge : g ≠ e) (hgf : g ≠ f) (hβe : β e = σ) (hβf : β f = σ) (hβg : β g = -σ)
    (h1B : χ₁ ∈ B) (h3B : χ₃ ∈ B) (h1p : χ₁ ≠ p) (h3p : χ₃ ≠ p) (h1α : ∀ i, χ₁ ≠ α i)
    (h3α : ∀ i, χ₃ ≠ α i) (h13 : χ₁ ≠ χ₃) (hdpos : ∀ φ ∈ B, 0 < d φ) (hdp : d p = 1)
    (hd13 : d χ₃ = d χ₁)
    (hy₀ : ∀ φ ∈ B, y₀ φ = unitVector p φ + ∑ i, β i * unitVector (α i) φ)
    (hy₁ : ∀ φ ∈ B, y₁ φ = a * (unitVector (α e) φ + unitVector χ₁ φ + unitVector χ₃ φ -
      unitVector (α f) φ))
    (hd1 : ∀ φ ∈ B, c₁ φ - y₀ φ =
      -2 * unitVector p φ - 2 * σ * unitVector (α e) φ + 2 * σ * unitVector χ₁ φ)
    (hd3 : ∀ φ ∈ B, c₃ φ - y₀ φ =
      -2 * unitVector p φ - 2 * σ * unitVector (α e) φ + 2 * σ * unitVector χ₃ φ)
    (hsq2 : ∑ φ ∈ B, c₂ φ * c₂ φ = 8) (hg1 : ∑ φ ∈ B, c₂ φ * c₁ φ = 4)
    (hg3 : ∑ φ ∈ B, c₂ φ * c₃ φ = 4) (hp2 : c₂ p = -1) (ho0 : ∑ φ ∈ B, c₂ φ * y₀ φ = 0)
    (ho1 : ∑ φ ∈ B, c₂ φ * y₁ φ = 0) (hdeg2 : ∑ φ ∈ B, d φ * c₂ φ = 0) : False := by
  have hF1 : ∀ (χ : ι) (cj : ι → ℤ), χ ∈ B → (∀ φ ∈ B, cj φ - y₀ φ =
      -2 * unitVector p φ - 2 * σ * unitVector (α e) φ + 2 * σ * unitVector χ φ) →
      ∑ φ ∈ B, c₂ φ * cj φ = 4 → c₂ χ = c₂ (α e) + σ := by
    intro χ cj hχ hdj hgj
    have h : ∑ φ ∈ B, c₂ φ * (cj φ - y₀ φ) = 4 := by
      rw [Finset.sum_congr rfl fun φ _ => mul_sub (c₂ φ) (cj φ) (y₀ φ), Finset.sum_sub_distrib,
        hgj, ho0, sub_zero]
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hdj φ hφ], sum_mul_witness_sub σ hp (hα e).1 hχ,
      hp2] at h
    rcases hσ with hs | hs <;> rw [hs] at h ⊢ <;> linarith only [h]
  have hc₂1 := hF1 χ₁ c₁ h1B hd1 hg1
  have hc₂3 := hF1 χ₃ c₃ h3B hd3 hg3
  have hc₂f : c₂ (α f) = 3 * c₂ (α e) + 2 * σ := by
    have hcomp : ∑ φ ∈ B, c₂ φ * y₁ φ = a * (c₂ (α e) + c₂ χ₁ + c₂ χ₃ - c₂ (α f)) := by
      have h : ∑ φ ∈ B, c₂ φ * y₁ φ = ∑ φ ∈ B, a * (c₂ φ * unitVector (α e) φ +
          c₂ φ * unitVector χ₁ φ + c₂ φ * unitVector χ₃ φ - c₂ φ * unitVector (α f) φ) :=
        Finset.sum_congr rfl fun φ hφ => by rw [hy₁ φ hφ]; ring
      rw [h, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, sum_mul_unitVector (hα e).1, sum_mul_unitVector h1B,
        sum_mul_unitVector h3B, sum_mul_unitVector (hα f).1]
    have h := ho1
    rw [hcomp, hc₂1, hc₂3] at h
    rcases ha with ha' | ha' <;> rw [ha'] at h <;> linarith only [h]
  have hc₂g : c₂ (α g) = σ + 4 * c₂ (α e) := by
    have hcongr : ∑ φ ∈ B, c₂ φ * y₀ φ =
        ∑ φ ∈ B, c₂ φ * (1 * unitVector p φ + ∑ i, β i * unitVector (α i) φ) :=
      Finset.sum_congr rfl fun φ hφ => by rw [hy₀ φ hφ, one_mul]
    have h := ho0
    rw [hcongr, sum_mul_unitVector_add_sum hp (fun i => (hα i).1), hp2,
      sum_fin_three_of_ne hfe hge hgf (fun i => β i * c₂ (α i)), hβe, hβf, hβg, hc₂f] at h
    rcases hσ with hs | hs <;> rw [hs] at h ⊢ <;> linarith only [h]
  have hgle : c₂ (α g) * c₂ (α g) ≤ 8 := by
    rw [← hsq2]
    exact Finset.single_le_sum (f := fun φ => c₂ φ * c₂ φ) (fun φ _ => mul_self_nonneg _)
      (hα g).1
  rw [hc₂g] at hgle
  have hu0 : c₂ (α e) = 0 := by
    have h1 : -2 ≤ σ + 4 * c₂ (α e) := by nlinarith
    have h2 : σ + 4 * c₂ (α e) ≤ 2 := by nlinarith
    rcases hσ with hs | hs <;> rw [hs] at h1 h2 <;> omega
  have hfg : α f ≠ α g := fun h => hgf (hαinj h).symm
  have hS : ({p, α f, α g, χ₁, χ₃} : Finset ι) ⊆ B := by
    intro φ hφ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with h | h | h | h | h <;> rw [h]
    · exact hp
    · exact (hα f).1
    · exact (hα g).1
    · exact h1B
    · exact h3B
  have hsplit : ∀ G : ι → ℤ, ∑ φ ∈ B, G φ = ∑ φ ∈ B \ {p, α f, α g, χ₁, χ₃}, G φ +
      (G p + G (α f) + G (α g) + G χ₁ + G χ₃) := by
    intro G
    rw [← Finset.sum_sdiff hS, sum_five G (hα f).2.symm (hα g).2.symm h1p.symm h3p.symm hfg
      (h1α f).symm (h3α f).symm (h1α g).symm (h3α g).symm h13]
  have hrest : ∑ φ ∈ B \ {p, α f, α g, χ₁, χ₃}, c₂ φ * c₂ φ = 0 := by
    have h := hsplit fun φ => c₂ φ * c₂ φ
    rw [hsq2, hp2, hc₂f, hc₂g, hc₂1, hc₂3, hu0] at h
    rcases hσ with hs | hs <;> rw [hs] at h <;> linarith only [h]
  have hzero : ∀ φ ∈ B \ {p, α f, α g, χ₁, χ₃}, c₂ φ = 0 := fun φ hφ =>
    mul_self_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg fun φ _ => mul_self_nonneg (c₂ φ)).mp hrest φ hφ)
  have h := hsplit fun φ => d φ * c₂ φ
  rw [hdeg2, Finset.sum_eq_zero fun φ hφ => by rw [hzero φ hφ, mul_zero], hp2, hc₂f, hc₂g,
    hc₂1, hc₂3, hu0, hdp, hd13] at h
  have hdf := hdpos (α f) (hα f).1
  have hdg := hdpos (α g) (hα g).1
  have hd1 := hdpos χ₁ h1B
  rcases hσ with hs | hs <;> rw [hs] at h <;> linarith only [h, hdf, hdg, hd1]

theorem two_pos_column_zero {α : Fin 3 → ι} {β : Fin 3 → ℤ} {σ : ℤ} {e : Fin 3} {χ₁ χ₃ : ι}
    {d y₀ y₁ c₁ c₂ c₃ : ι → ℤ} (hσ : σ = 1 ∨ σ = -1) (hp : p ∈ B)
    (hαinj : Function.Injective α) (hα : ∀ i, α i ∈ B ∧ α i ≠ p)
    (hβ : ∀ i, β i = 1 ∨ β i = -1) (hβe : β e = σ) (h1B : χ₁ ∈ B) (h3B : χ₃ ∈ B)
    (h1p : χ₁ ≠ p) (h3p : χ₃ ≠ p) (h1α : ∀ i, χ₁ ≠ α i) (h3α : ∀ i, χ₃ ≠ α i) (h13 : χ₁ ≠ χ₃)
    (hdpos : ∀ φ ∈ B, 0 < d φ) (hdp : d p = 1) (hd13 : d χ₃ = d χ₁)
    (hy₀ : ∀ φ ∈ B, y₀ φ = unitVector p φ + ∑ i, β i * unitVector (α i) φ)
    (hy₀deg : ∑ φ ∈ B, d φ * y₀ φ = 0)
    (hy₁val : ∀ φ ∈ B, y₁ φ = 0 ∨ y₁ φ = 1 ∨ y₁ φ = -1)
    (hy₁4 : (B.filter fun φ => y₁ φ ≠ 0).card = 4) (hy₁p : y₁ p = 0)
    (hy01 : ∑ φ ∈ B, y₀ φ * y₁ φ = 0) (hy₁deg : ∑ φ ∈ B, d φ * y₁ φ = 0)
    (h1eq : y₁ χ₁ = y₁ (α e)) (h3eq : y₁ χ₃ = y₁ (α e))
    (hd1 : ∀ φ ∈ B, c₁ φ - y₀ φ =
      -2 * unitVector p φ - 2 * σ * unitVector (α e) φ + 2 * σ * unitVector χ₁ φ)
    (hd3 : ∀ φ ∈ B, c₃ φ - y₀ φ =
      -2 * unitVector p φ - 2 * σ * unitVector (α e) φ + 2 * σ * unitVector χ₃ φ)
    (hsq2 : ∑ φ ∈ B, c₂ φ * c₂ φ = 8) (hg1 : ∑ φ ∈ B, c₂ φ * c₁ φ = 4)
    (hg3 : ∑ φ ∈ B, c₂ φ * c₃ φ = 4) (hp2 : c₂ p = -1) (ho0 : ∑ φ ∈ B, c₂ φ * y₀ φ = 0)
    (ho1 : ∑ φ ∈ B, c₂ φ * y₁ φ = 0) (hdeg2 : ∑ φ ∈ B, d φ * c₂ φ = 0) : y₁ (α e) = 0 := by
  by_contra ha
  have haval : y₁ (α e) = 1 ∨ y₁ (α e) = -1 := by
    rcases hy₁val (α e) (hα e).1 with h | h | h
    · exact absurd h ha
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨f, g, hfe, hge, hgf, hy₁, hβf, hβg, -⟩ := two_pos_shape hσ hp hαinj hα hβ hβe h1B h3B
    h1p h3p h1α h3α h13 hdpos hdp hd13 hy₀ hy₀deg hy₁val hy₁4 hy₁p hy01 hy₁deg h1eq h3eq ha
  exact two_pos_contradiction hσ haval hp hαinj hα hfe hge hgf hβe hβf hβg h1B h3B h1p h3p h1α
    h3α h13 hdpos hdp hd13 hy₀ hy₁ hd1 hd3 hsq2 hg1 hg3 hp2 ho0 ho1 hdeg2

end CFSG.Wreathed.ConditionalFirstFourierRows
