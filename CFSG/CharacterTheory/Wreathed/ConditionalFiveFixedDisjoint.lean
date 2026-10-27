module

public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedCore

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalFiveFixed

open CFSG.Wreathed.ConditionalFourier

variable {ι : Type*} [DecidableEq ι] {B : Finset ι}

theorem sum_mul_sum_unitVector {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] {g : κ₁ → ι}
    {h : κ₂ → ι} (hg : ∀ l, g l ∈ B) (a : κ₁ → ℤ) (b : κ₂ → ℤ) :
    ∑ φ ∈ B, (∑ l, a l * unitVector (g l) φ) * (∑ l', b l' * unitVector (h l') φ) =
      ∑ l, ∑ l', a l * b l' * (if g l = h l' then 1 else 0) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ => ?_
  have hφ : ∀ φ, a l * unitVector (g l) φ * (b l' * unitVector (h l') φ) =
      a l * b l' * (unitVector (h l') φ * unitVector (g l) φ) := fun φ => by ring
  rw [Finset.sum_congr rfl fun φ _ => hφ φ, ← Finset.mul_sum, sum_mul_unitVector (hg l)]
  rfl

theorem pair_ne {a₀ a₁ b₀ b₁ : ι} {s₀ s₁ t₀ t₁ : ℤ} {d : ι → ℤ} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁)
    (hs₀ : s₀ = 1 ∨ s₀ = -1) (hs₁ : s₁ = 1 ∨ s₁ = -1) (ht₀ : t₀ = 1 ∨ t₀ = -1)
    (ht₁ : t₁ = 1 ∨ t₁ = -1) (hd₀ : 0 < d a₀) (hd₁ : 0 < d a₁)
    (hip : s₀ * t₀ * (if a₀ = b₀ then 1 else 0) + s₀ * t₁ * (if a₀ = b₁ then 1 else 0) +
      s₁ * t₀ * (if a₁ = b₀ then 1 else 0) + s₁ * t₁ * (if a₁ = b₁ then 1 else 0) = 0)
    (hdeg : s₀ * d a₀ + s₁ * d a₁ = t₀ * d b₀ + t₁ * d b₁) : a₀ ≠ b₀ := by
  intro h
  subst h
  rw [ite_eq_left_of_eq_true _ _ (eq_self a₀), ite_eq_right_of_eq_false _ _ (eq_false hb),
    ite_eq_right_of_eq_false _ _ (eq_false ha.symm)] at hip
  by_cases h11 : a₁ = b₁
  · subst h11
    rw [ite_eq_left_of_eq_true _ _ (eq_self a₁)] at hip
    rcases hs₀ with rfl | rfl <;> rcases hs₁ with rfl | rfl <;> rcases ht₀ with rfl | rfl <;>
      rcases ht₁ with rfl | rfl <;> linarith
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h11)] at hip
    rcases hs₀ with rfl | rfl <;> rcases ht₀ with rfl | rfl <;> linarith

theorem pair_disjoint {a₀ a₁ b₀ b₁ : ι} {s₀ s₁ t₀ t₁ : ℤ} {d : ι → ℤ} (ha : a₀ ≠ a₁)
    (hb : b₀ ≠ b₁) (hs₀ : s₀ = 1 ∨ s₀ = -1) (hs₁ : s₁ = 1 ∨ s₁ = -1) (ht₀ : t₀ = 1 ∨ t₀ = -1)
    (ht₁ : t₁ = 1 ∨ t₁ = -1) (hd₀ : 0 < d a₀) (hd₁ : 0 < d a₁)
    (hip : s₀ * t₀ * (if a₀ = b₀ then 1 else 0) + s₀ * t₁ * (if a₀ = b₁ then 1 else 0) +
      s₁ * t₀ * (if a₁ = b₀ then 1 else 0) + s₁ * t₁ * (if a₁ = b₁ then 1 else 0) = 0)
    (hdeg : s₀ * d a₀ + s₁ * d a₁ = t₀ * d b₀ + t₁ * d b₁) :
    a₀ ≠ b₀ ∧ a₀ ≠ b₁ ∧ a₁ ≠ b₀ ∧ a₁ ≠ b₁ :=
  ⟨pair_ne ha hb hs₀ hs₁ ht₀ ht₁ hd₀ hd₁ hip hdeg,
    pair_ne ha hb.symm hs₀ hs₁ ht₁ ht₀ hd₀ hd₁ (by linarith only [hip]) (by linarith only [hdeg]),
    pair_ne ha.symm hb hs₁ hs₀ ht₀ ht₁ hd₁ hd₀ (by linarith only [hip]) (by linarith only [hdeg]),
    pair_ne ha.symm hb.symm hs₁ hs₀ ht₁ ht₀ hd₁ hd₀ (by linarith only [hip])
      (by linarith only [hdeg])⟩

@[expose] def quadSign (l : Fin 4) : ℤ := if l.val < 2 then 1 else -1

theorem quadSign_zero : quadSign 0 = 1 := rfl

theorem quadSign_one : quadSign 1 = 1 := rfl

theorem quadSign_two : quadSign 2 = -1 := rfl

theorem quadSign_three : quadSign 3 = -1 := rfl

theorem quadSign_sq (l : Fin 4) : quadSign l * quadSign l = 1 := by
  unfold quadSign
  split_ifs <;> norm_num

theorem exists_quadruple_labels {yr xk : ι → ℤ}
    (hyv : ∀ φ ∈ B, yr φ = 0 ∨ yr φ = 1 ∨ yr φ = -1)
    (hy4 : (B.filter fun φ => yr φ ≠ 0).card = 4)
    (hxs : ∀ φ ∈ B, yr φ ≠ 0 → xk φ = 1 ∨ xk φ = -1) (hyx : ∑ φ ∈ B, yr φ * xk φ = 0) :
    ∃ γ : Fin 4 → ι, Function.Injective γ ∧ (∀ l, γ l ∈ B) ∧
      (∀ φ ∈ B, yr φ ≠ 0 ↔ ∃ l, φ = γ l) ∧ (∀ l, xk (γ l) = 1 ∨ xk (γ l) = -1) ∧
      ∀ l, yr (γ l) = quadSign l * xk (γ l) := by
  set Sy := B.filter fun φ => yr φ ≠ 0 with hSy
  have hmemSy : ∀ φ, φ ∈ Sy ↔ φ ∈ B ∧ yr φ ≠ 0 := fun φ => by rw [hSy, Finset.mem_filter]
  have hprod : ∀ φ ∈ Sy, yr φ * xk φ = 1 ∨ yr φ * xk φ = -1 := by
    intro φ hφ
    obtain ⟨hφB, hne⟩ := (hmemSy φ).mp hφ
    have hy : yr φ = 1 ∨ yr φ = -1 := by
      rcases hyv φ hφB with h | h
      · exact absurd h hne
      · exact h
    exact sign_mul hy (hxs φ hφB hne)
  set Qp := Sy.filter fun φ => yr φ * xk φ = 1 with hQp
  set Qm := Sy.filter fun φ => ¬ yr φ * xk φ = 1 with hQm
  have hmemQm : ∀ φ ∈ Qm, yr φ * xk φ = -1 := by
    intro φ hφ
    rw [hQm, Finset.mem_filter] at hφ
    rcases hprod φ hφ.1 with h | h
    · exact absurd h hφ.2
    · exact h
  have hsumSy : ∑ φ ∈ Sy, yr φ * xk φ = 0 := by
    rw [← hyx]
    refine Finset.sum_subset (Finset.filter_subset _ _) fun φ hφB hφ => ?_
    have : yr φ = 0 := by
      by_contra hne
      exact hφ ((hmemSy φ).mpr ⟨hφB, hne⟩)
    rw [this, zero_mul]
  have hsplit : ∑ φ ∈ Sy, yr φ * xk φ =
      ∑ φ ∈ Qp, yr φ * xk φ + ∑ φ ∈ Qm, yr φ * xk φ :=
    (Finset.sum_filter_add_sum_filter_not Sy _ _).symm
  have hp1 : ∑ φ ∈ Qp, yr φ * xk φ = Qp.card := by
    rw [Finset.sum_congr rfl fun φ hφ => (Finset.mem_filter.mp hφ).2]
    simp [hQp]
  have hm1 : ∑ φ ∈ Qm, yr φ * xk φ = -(Qm.card : ℤ) := by
    rw [Finset.sum_congr rfl fun φ hφ => hmemQm φ hφ]
    simp [hQm]
  have hcard : Qp.card + Qm.card = Sy.card := Finset.card_filter_add_card_filter_not _
  rw [hsplit, hp1, hm1] at hsumSy
  have hcp : Qp.card = 2 := by omega
  have hcm : Qm.card = 2 := by omega
  obtain ⟨g₀, g₁, h01, hQp2⟩ := Finset.card_eq_two.mp hcp
  obtain ⟨g₂, g₃, h23, hQm2⟩ := Finset.card_eq_two.mp hcm
  have hpS : ∀ φ ∈ Qp, φ ∈ Sy := fun φ hφ => (Finset.mem_filter.mp hφ).1
  have hmS : ∀ φ ∈ Qm, φ ∈ Sy := fun φ hφ => (Finset.mem_filter.mp hφ).1
  have hpm : ∀ φ ∈ Qp, ∀ ψ ∈ Qm, φ ≠ ψ := by
    rintro φ hφ ψ hψ rfl
    rw [hQm, Finset.mem_filter] at hψ
    exact hψ.2 (Finset.mem_filter.mp hφ).2
  have m0 : g₀ ∈ Qp := by rw [hQp2]; simp
  have m1 : g₁ ∈ Qp := by rw [hQp2]; simp
  have m2 : g₂ ∈ Qm := by rw [hQm2]; simp
  have m3 : g₃ ∈ Qm := by rw [hQm2]; simp
  let γ : Fin 4 → ι := ![g₀, g₁, g₂, g₃]
  have hγ : ∀ l, (l.val < 2 → γ l ∈ Qp) ∧ (¬ l.val < 2 → γ l ∈ Qm) := by
    intro l
    fin_cases l <;> simp [γ, m0, m1, m2, m3]
  have hγS : ∀ l, γ l ∈ Sy := fun l => by
    by_cases hl : l.val < 2
    · exact hpS _ ((hγ l).1 hl)
    · exact hmS _ ((hγ l).2 hl)
  have hinj : Function.Injective γ := by
    intro l l' hll'
    have h02 := hpm _ m0 _ m2
    have h03 := hpm _ m0 _ m3
    have h12 := hpm _ m1 _ m2
    have h13 := hpm _ m1 _ m3
    fin_cases l <;> fin_cases l' <;>
      simp [γ, h01, h23, h02, h03, h12, h13, h01.symm, h23.symm, h02.symm, h03.symm, h12.symm,
        h13.symm] at hll' ⊢
  refine ⟨γ, hinj, fun l => ((hmemSy _).mp (hγS l)).1, fun φ hφ => ⟨fun hne => ?_, ?_⟩,
    fun l => hxs _ ((hmemSy _).mp (hγS l)).1 ((hmemSy _).mp (hγS l)).2, fun l => ?_⟩
  · have hφS : φ ∈ Sy := (hmemSy φ).mpr ⟨hφ, hne⟩
    by_cases hφp : yr φ * xk φ = 1
    · have : φ ∈ Qp := Finset.mem_filter.mpr ⟨hφS, hφp⟩
      rw [hQp2, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · have : φ ∈ Qm := Finset.mem_filter.mpr ⟨hφS, hφp⟩
      rw [hQm2, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ((hmemSy _).mp (hγS l)).2
  · have hx := hxs _ ((hmemSy _).mp (hγS l)).1 ((hmemSy _).mp (hγS l)).2
    have hx2 : xk (γ l) * xk (γ l) = 1 := by rcases hx with h | h <;> rw [h] <;> norm_num
    by_cases hl : l.val < 2
    · have h := (Finset.mem_filter.mp ((hγ l).1 hl)).2
      simp only [quadSign, hl, ite_true]
      linear_combination xk (γ l) * h - yr (γ l) * hx2
    · have h := hmemQm _ ((hγ l).2 hl)
      simp only [quadSign, hl, ite_false]
      linear_combination xk (γ l) * h - yr (γ l) * hx2

theorem quadruple_disjoint {γr γt : Fin 4 → ι} {εr εt : Fin 4 → ℤ} {Ur Yr Ut Yt d : ι → ℤ}
    {V : ℤ} (hγr : Function.Injective γr) (hγt : Function.Injective γt) (hγrB : ∀ l, γr l ∈ B)
    (hεr : ∀ l, εr l = 1 ∨ εr l = -1) (hεt : ∀ l, εt l = 1 ∨ εt l = -1)
    (hd : ∀ φ ∈ B, 0 < d φ)
    (hUr : ∀ φ ∈ B, Ur φ = ∑ l, εr l * unitVector (γr l) φ)
    (hYr : ∀ φ ∈ B, Yr φ = ∑ l, (quadSign l * εr l) * unitVector (γr l) φ)
    (hUt : ∀ φ ∈ B, Ut φ = ∑ l, εt l * unitVector (γt l) φ)
    (hYt : ∀ φ ∈ B, Yt φ = ∑ l, (quadSign l * εt l) * unitVector (γt l) φ)
    (hUU : ∑ φ ∈ B, Ur φ * Ut φ = 0) (hUY : ∑ φ ∈ B, Ur φ * Yt φ = 0)
    (hYU : ∑ φ ∈ B, Yr φ * Ut φ = 0) (hYY : ∑ φ ∈ B, Yr φ * Yt φ = 0)
    (hr₀ : εr 0 * d (γr 0) + εr 1 * d (γr 1) = V) (hr₁ : εr 2 * d (γr 2) + εr 3 * d (γr 3) = V)
    (ht₀ : εt 0 * d (γt 0) + εt 1 * d (γt 1) = V)
    (ht₁ : εt 2 * d (γt 2) + εt 3 * d (γt 3) = V) :
    ∀ l l', γr l ≠ γt l' := by
  have key : ∀ (X Y : ι → ℤ) (εX εY : Fin 4 → ℤ) (gX gY : Fin 4 → ι),
      (∀ l, gX l ∈ B) → (∀ φ ∈ B, X φ = ∑ l, εX l * unitVector (gX l) φ) →
      (∀ φ ∈ B, Y φ = ∑ l, εY l * unitVector (gY l) φ) →
      ∑ φ ∈ B, X φ * Y φ = ∑ l, ∑ l', εX l * εY l' * (if gX l = gY l' then 1 else 0) := by
    intro X Y εX εY gX gY hgX hX hY
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hX φ hφ, hY φ hφ]]
    exact sum_mul_sum_unitVector hgX εX εY
  rw [key Ur Ut εr εt γr γt hγrB hUr hUt] at hUU
  rw [key Ur Yt εr (fun l => quadSign l * εt l) γr γt hγrB hUr hYt] at hUY
  rw [key Yr Ut (fun l => quadSign l * εr l) εt γr γt hγrB hYr hUt] at hYU
  rw [key Yr Yt (fun l => quadSign l * εr l) (fun l => quadSign l * εt l) γr γt hγrB hYr hYt]
    at hYY
  simp only [Fin.sum_univ_four, quadSign_zero, quadSign_one, quadSign_two, quadSign_three]
    at hUU hUY hYU hYY
  have hne : ∀ l l', l ≠ l' → γr l ≠ γr l' := fun l l' h e => h (hγr e)
  have hne' : ∀ l l', l ≠ l' → γt l ≠ γt l' := fun l l' h e => h (hγt e)
  have hdr : ∀ l, 0 < d (γr l) := fun l => hd _ (hγrB l)
  have hb₀₀ := pair_disjoint (hne 0 1 (by decide)) (hne' 0 1 (by decide)) (hεr 0) (hεr 1)
    (hεt 0) (hεt 1) (hdr 0) (hdr 1) (by linarith only [hUU, hUY, hYU, hYY])
    (by rw [hr₀, ht₀])
  have hb₀₁ := pair_disjoint (hne 0 1 (by decide)) (hne' 2 3 (by decide)) (hεr 0) (hεr 1)
    (hεt 2) (hεt 3) (hdr 0) (hdr 1) (by linarith only [hUU, hUY, hYU, hYY])
    (by rw [hr₀, ht₁])
  have hb₁₀ := pair_disjoint (hne 2 3 (by decide)) (hne' 0 1 (by decide)) (hεr 2) (hεr 3)
    (hεt 0) (hεt 1) (hdr 2) (hdr 3) (by linarith only [hUU, hUY, hYU, hYY])
    (by rw [hr₁, ht₀])
  have hb₁₁ := pair_disjoint (hne 2 3 (by decide)) (hne' 2 3 (by decide)) (hεr 2) (hεr 3)
    (hεt 2) (hεt 3) (hdr 2) (hdr 3) (by linarith only [hUU, hUY, hYU, hYY])
    (by rw [hr₁, ht₁])
  intro l l'
  fin_cases l <;> fin_cases l' <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    tauto

end CFSG.Wreathed.ConditionalFiveFixed
