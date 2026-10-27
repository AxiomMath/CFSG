module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneAxioms

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

variable {P : Type*} [Fintype P] [DecidableEq P] {𝓛 : Finset (Finset P)}

@[expose] def lineThrough (𝓛 : Finset (Finset P)) (p q : P) : Finset P :=
  if hx : ∃ L ∈ 𝓛, p ∈ L ∧ q ∈ L then hx.choose else ∅

theorem IsSteinerPlane.lineThrough_spec (h : IsSteinerPlane 𝓛) {p q : P} (hpq : p ≠ q) :
    lineThrough 𝓛 p q ∈ 𝓛 ∧ p ∈ lineThrough 𝓛 p q ∧ q ∈ lineThrough 𝓛 p q := by
  have hx : ∃ L ∈ 𝓛, p ∈ L ∧ q ∈ L := by
    obtain ⟨L, hL, -⟩ := h.existsUnique_line hpq
    exact ⟨L, hL⟩
  rw [lineThrough, dite_eq_left hx]
  exact hx.choose_spec

theorem IsSteinerPlane.eq_lineThrough (h : IsSteinerPlane 𝓛) {p q : P} (hpq : p ≠ q)
    {L : Finset P} (hL : L ∈ 𝓛) (hp : p ∈ L) (hq : q ∈ L) : L = lineThrough 𝓛 p q := by
  obtain ⟨h1, h2, h3⟩ := h.lineThrough_spec hpq
  exact h.eq_of_mem_of_mem hL h1 hpq hp hq h2 h3

@[expose] def meetPoint (L M : Finset P) (d : P) : P :=
  if hx : ∃ x, x ∈ L ∧ x ∈ M then hx.choose else d

theorem IsSteinerPlane.meetPoint_spec (h : IsSteinerPlane 𝓛) {L M : Finset P} (hL : L ∈ 𝓛)
    (hM : M ∈ 𝓛) (d : P) : meetPoint L M d ∈ L ∧ meetPoint L M d ∈ M := by
  have hx := h.exists_mem_inter hL hM
  rw [meetPoint, dite_eq_left hx]
  exact hx.choose_spec

theorem IsSteinerPlane.eq_meetPoint (h : IsSteinerPlane 𝓛) {L M : Finset P} (hL : L ∈ 𝓛)
    (hM : M ∈ 𝓛) (hne : L ≠ M) (d : P) {x : P} (hxL : x ∈ L) (hxM : x ∈ M) :
    x = meetPoint L M d := by
  by_contra hx
  obtain ⟨h1, h2⟩ := h.meetPoint_spec hL hM d
  exact hne (h.eq_of_mem_of_mem hL hM hx hxL h1 hxM h2)

section Frame

variable (h : IsSteinerPlane 𝓛) (p₀ : P)

@[expose] def vline (j : Fin 5) : Finset P :=
  (((linesThru 𝓛 p₀).equivFinOfCardEq (h.card_linesThru p₀)).symm j : Finset P)

theorem vline_mem_linesThru (j : Fin 5) : vline h p₀ j ∈ linesThru 𝓛 p₀ :=
  (((linesThru 𝓛 p₀).equivFinOfCardEq (h.card_linesThru p₀)).symm j).2

theorem vline_mem (j : Fin 5) : vline h p₀ j ∈ 𝓛 := (mem_linesThru.1 (vline_mem_linesThru h p₀ j)).1

theorem p₀_mem_vline (j : Fin 5) : p₀ ∈ vline h p₀ j :=
  (mem_linesThru.1 (vline_mem_linesThru h p₀ j)).2

theorem vline_injective : Function.Injective (vline h p₀) := by
  intro j k hjk
  have := ((linesThru 𝓛 p₀).equivFinOfCardEq (h.card_linesThru p₀)).symm.injective
    (Subtype.ext hjk)
  exact this

theorem exists_vline_eq {L : Finset P} (hL : L ∈ 𝓛) (hp : p₀ ∈ L) : ∃ j, vline h p₀ j = L := by
  refine ⟨(linesThru 𝓛 p₀).equivFinOfCardEq (h.card_linesThru p₀) ⟨L, mem_linesThru.2 ⟨hL, hp⟩⟩,
    ?_⟩
  simp [vline]

@[expose] def vpts (j : Fin 5) : Finset P := (vline h p₀ j).erase p₀

theorem card_vpts (j : Fin 5) : (vpts h p₀ j).card = 4 := by
  rw [vpts, Finset.card_erase_of_mem (p₀_mem_vline h p₀ j), h.card_line (vline_mem h p₀ j)]

theorem ne_p₀_of_mem_vpts {j : Fin 5} {q : P} (hq : q ∈ vpts h p₀ j) : q ≠ p₀ :=
  (Finset.mem_erase.1 hq).1

theorem mem_vline_of_mem_vpts {j : Fin 5} {q : P} (hq : q ∈ vpts h p₀ j) : q ∈ vline h p₀ j :=
  (Finset.mem_erase.1 hq).2

theorem eq_of_mem_vpts {i j : Fin 5} {q : P} (hi : q ∈ vpts h p₀ i) (hj : q ∈ vpts h p₀ j) :
    i = j :=
  vline_injective h p₀ (h.eq_of_mem_of_mem (vline_mem h p₀ i) (vline_mem h p₀ j)
    (Ne.symm (ne_p₀_of_mem_vpts h p₀ hi)) (p₀_mem_vline h p₀ i) (mem_vline_of_mem_vpts h p₀ hi)
    (p₀_mem_vline h p₀ j) (mem_vline_of_mem_vpts h p₀ hj))

theorem exists_mem_vpts {q : P} (hq : q ≠ p₀) : ∃ j, q ∈ vpts h p₀ j := by
  obtain ⟨L, ⟨hL, hp, hqL⟩, -⟩ := h.existsUnique_line (Ne.symm hq)
  obtain ⟨j, rfl⟩ := exists_vline_eq h p₀ hL hp
  exact ⟨j, Finset.mem_erase.2 ⟨hq, hqL⟩⟩

theorem p₀_not_mem_lineThrough {i k : Fin 5} (hik : i ≠ k) {q q' : P} (hq : q ∈ vpts h p₀ i)
    (hq' : q' ∈ vpts h p₀ k) : p₀ ∉ lineThrough 𝓛 q q' := by
  have hqq' : q ≠ q' := fun e => hik (eq_of_mem_vpts h p₀ hq (e ▸ hq'))
  obtain ⟨hM, hqM, hq'M⟩ := h.lineThrough_spec hqq'
  intro hp
  have e1 := h.eq_of_mem_of_mem hM (vline_mem h p₀ i) (Ne.symm (ne_p₀_of_mem_vpts h p₀ hq)) hp hqM
    (p₀_mem_vline h p₀ i) (mem_vline_of_mem_vpts h p₀ hq)
  have e2 := h.eq_of_mem_of_mem hM (vline_mem h p₀ k) (Ne.symm (ne_p₀_of_mem_vpts h p₀ hq')) hp
    hq'M (p₀_mem_vline h p₀ k) (mem_vline_of_mem_vpts h p₀ hq')
  exact hik (vline_injective h p₀ (e1.symm.trans e2))

theorem meetPoint_mem_vpts {M : Finset P} (hM : M ∈ 𝓛) (hp : p₀ ∉ M) (j : Fin 5) :
    meetPoint M (vline h p₀ j) p₀ ∈ M ∧ meetPoint M (vline h p₀ j) p₀ ∈ vpts h p₀ j := by
  obtain ⟨h1, h2⟩ := h.meetPoint_spec hM (vline_mem h p₀ j) p₀
  exact ⟨h1, Finset.mem_erase.2 ⟨fun e => hp (e ▸ h1), h2⟩⟩

theorem ne_vline_of_not_mem {M : Finset P} (hp : p₀ ∉ M) (j : Fin 5) : M ≠ vline h p₀ j :=
  fun e => hp (e ▸ p₀_mem_vline h p₀ j)

theorem eq_of_mem_vpts_of_mem {M : Finset P} (hM : M ∈ 𝓛) (hp : p₀ ∉ M) {j : Fin 5} {q q' : P}
    (hq : q ∈ vpts h p₀ j) (hq' : q' ∈ vpts h p₀ j) (hqM : q ∈ M) (hq'M : q' ∈ M) : q = q' := by
  by_contra hne
  exact ne_vline_of_not_mem h p₀ hp j (h.eq_of_mem_of_mem hM (vline_mem h p₀ j) hne hqM hq'M
    (mem_vline_of_mem_vpts h p₀ hq) (mem_vline_of_mem_vpts h p₀ hq'))

theorem vpts_nonempty (j : Fin 5) : (vpts h p₀ j).Nonempty := by
  rw [← Finset.card_pos, card_vpts]
  norm_num

@[expose] def o₀ : P := (vpts_nonempty h p₀ 0).choose

theorem o₀_mem : o₀ h p₀ ∈ vpts h p₀ 0 := (vpts_nonempty h p₀ 0).choose_spec

@[expose] def μ₁ (y : Fin 4) : P :=
  (((vpts h p₀ 1).equivFinOfCardEq (card_vpts h p₀ 1)).symm y : P)

theorem μ₁_mem (y : Fin 4) : μ₁ h p₀ y ∈ vpts h p₀ 1 :=
  (((vpts h p₀ 1).equivFinOfCardEq (card_vpts h p₀ 1)).symm y).2

theorem μ₁_injective : Function.Injective (μ₁ h p₀) := fun _ _ e =>
  ((vpts h p₀ 1).equivFinOfCardEq (card_vpts h p₀ 1)).symm.injective (Subtype.ext e)

@[expose] def muAux (j : Fin 5) (y : Fin 4) : P :=
  meetPoint (lineThrough 𝓛 (o₀ h p₀) (μ₁ h p₀ y)) (vline h p₀ j) p₀

theorem lineThrough_o₀_spec (y : Fin 4) :
    lineThrough 𝓛 (o₀ h p₀) (μ₁ h p₀ y) ∈ 𝓛 ∧ p₀ ∉ lineThrough 𝓛 (o₀ h p₀) (μ₁ h p₀ y) := by
  have hne : o₀ h p₀ ≠ μ₁ h p₀ y := fun e =>
    absurd (eq_of_mem_vpts h p₀ (o₀_mem h p₀) (e ▸ μ₁_mem h p₀ y)) (by decide)
  exact ⟨(h.lineThrough_spec hne).1,
    p₀_not_mem_lineThrough h p₀ (by decide) (o₀_mem h p₀) (μ₁_mem h p₀ y)⟩

theorem muAux_spec (j : Fin 5) (y : Fin 4) :
    muAux h p₀ j y ∈ lineThrough 𝓛 (o₀ h p₀) (μ₁ h p₀ y) ∧ muAux h p₀ j y ∈ vpts h p₀ j :=
  meetPoint_mem_vpts h p₀ (lineThrough_o₀_spec h p₀ y).1 (lineThrough_o₀_spec h p₀ y).2 j

theorem muAux_injective {j : Fin 5} (hj0 : j ≠ 0) :
    Function.Injective (muAux h p₀ j) := by
  intro y y' e
  by_contra hyy'
  obtain ⟨hy, hyj⟩ := muAux_spec h p₀ j y
  obtain ⟨hy', -⟩ := muAux_spec h p₀ j y'
  rw [e] at hy
  have hne : o₀ h p₀ ≠ muAux h p₀ j y' := fun e' =>
    hj0 (eq_of_mem_vpts h p₀ (o₀_mem h p₀) (e' ▸ e ▸ hyj)).symm
  have hM := (lineThrough_o₀_spec h p₀ y).1
  have hM' := (lineThrough_o₀_spec h p₀ y').1
  have hneo : o₀ h p₀ ≠ μ₁ h p₀ y := fun e' =>
    absurd (eq_of_mem_vpts h p₀ (o₀_mem h p₀) (e' ▸ μ₁_mem h p₀ y)) (by decide)
  have hneo' : o₀ h p₀ ≠ μ₁ h p₀ y' := fun e' =>
    absurd (eq_of_mem_vpts h p₀ (o₀_mem h p₀) (e' ▸ μ₁_mem h p₀ y')) (by decide)
  have heq := h.eq_of_mem_of_mem hM hM' hne (h.lineThrough_spec hneo).2.1 hy
    (h.lineThrough_spec hneo').2.1 hy'
  have h1 := (h.lineThrough_spec hneo).2.2
  have h2 := (h.lineThrough_spec hneo').2.2
  rw [← heq] at h2
  exact hyy' (μ₁_injective h p₀ (eq_of_mem_vpts_of_mem h p₀ hM (lineThrough_o₀_spec h p₀ y).2
    (μ₁_mem h p₀ y) (μ₁_mem h p₀ y') h1 h2))

@[expose] def mu (j : Fin 5) (x : Fin 4) : P :=
  if j = 0 then meetPoint (lineThrough 𝓛 (μ₁ h p₀ 0) (muAux h p₀ 2 x)) (vline h p₀ 0) p₀
  else if j = 1 then μ₁ h p₀ x else muAux h p₀ j x

theorem lineThrough_μ₁_spec (x : Fin 4) :
    lineThrough 𝓛 (μ₁ h p₀ 0) (muAux h p₀ 2 x) ∈ 𝓛 ∧
      p₀ ∉ lineThrough 𝓛 (μ₁ h p₀ 0) (muAux h p₀ 2 x) ∧
      μ₁ h p₀ 0 ∈ lineThrough 𝓛 (μ₁ h p₀ 0) (muAux h p₀ 2 x) ∧
      muAux h p₀ 2 x ∈ lineThrough 𝓛 (μ₁ h p₀ 0) (muAux h p₀ 2 x) := by
  have hne : μ₁ h p₀ 0 ≠ muAux h p₀ 2 x := fun e =>
    absurd (eq_of_mem_vpts h p₀ (μ₁_mem h p₀ 0) (e ▸ (muAux_spec h p₀ 2 x).2)) (by decide)
  exact ⟨(h.lineThrough_spec hne).1, p₀_not_mem_lineThrough h p₀ (by decide) (μ₁_mem h p₀ 0)
    (muAux_spec h p₀ 2 x).2, (h.lineThrough_spec hne).2.1, (h.lineThrough_spec hne).2.2⟩

theorem mu_zero (x : Fin 4) :
    mu h p₀ 0 x = meetPoint (lineThrough 𝓛 (μ₁ h p₀ 0) (muAux h p₀ 2 x)) (vline h p₀ 0) p₀ := by
  simp [mu]

theorem mu_one (x : Fin 4) : mu h p₀ 1 x = μ₁ h p₀ x := by
  simp [mu]

theorem mu_of_two_le {j : Fin 5} (hj0 : j ≠ 0) (hj1 : j ≠ 1) (x : Fin 4) :
    mu h p₀ j x = muAux h p₀ j x := by
  simp [mu, hj0, hj1]

theorem mu_zero_spec (x : Fin 4) :
    mu h p₀ 0 x ∈ lineThrough 𝓛 (μ₁ h p₀ 0) (muAux h p₀ 2 x) ∧ mu h p₀ 0 x ∈ vpts h p₀ 0 := by
  rw [mu_zero]
  obtain ⟨h1, h2, -, -⟩ := lineThrough_μ₁_spec h p₀ x
  exact meetPoint_mem_vpts h p₀ h1 h2 0

theorem mu_mem (j : Fin 5) (x : Fin 4) : mu h p₀ j x ∈ vpts h p₀ j := by
  by_cases hj0 : j = 0
  · subst hj0
    exact (mu_zero_spec h p₀ x).2
  by_cases hj1 : j = 1
  · subst hj1
    rw [mu_one]
    exact μ₁_mem h p₀ x
  rw [mu_of_two_le h p₀ hj0 hj1]
  exact (muAux_spec h p₀ j x).2

theorem mu_injective (j : Fin 5) : Function.Injective (mu h p₀ j) := by
  by_cases hj0 : j = 0
  · subst hj0
    intro x x' e
    obtain ⟨hx, hx0⟩ := mu_zero_spec h p₀ x
    obtain ⟨hx', -⟩ := mu_zero_spec h p₀ x'
    rw [e] at hx
    obtain ⟨hM, hpM, h1M, h2M⟩ := lineThrough_μ₁_spec h p₀ x
    obtain ⟨hM', -, h1M', h2M'⟩ := lineThrough_μ₁_spec h p₀ x'
    have hne : μ₁ h p₀ 0 ≠ mu h p₀ 0 x' := fun e' =>
      absurd (eq_of_mem_vpts h p₀ (μ₁_mem h p₀ 0) (e' ▸ e ▸ hx0)) (by decide)
    have heq := h.eq_of_mem_of_mem hM hM' hne h1M hx h1M' hx'
    rw [← heq] at h2M'
    exact muAux_injective h p₀ (by decide) (eq_of_mem_vpts_of_mem h p₀ hM hpM
      (muAux_spec h p₀ 2 x).2 (muAux_spec h p₀ 2 x').2 h2M h2M')
  by_cases hj1 : j = 1
  · subst hj1
    intro x x' e
    rw [mu_one, mu_one] at e
    exact μ₁_injective h p₀ e
  intro x x' e
  rw [mu_of_two_le h p₀ hj0 hj1, mu_of_two_le h p₀ hj0 hj1] at e
  exact muAux_injective h p₀ hj0 e

@[expose] def muEquiv (j : Fin 5) : Fin 4 ≃ vpts h p₀ j :=
  Equiv.ofBijective (fun x => ⟨mu h p₀ j x, mu_mem h p₀ j x⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun x x' e => mu_injective h p₀ j (congrArg Subtype.val e), ?_⟩
    rw [Fintype.card_fin, Fintype.card_coe, card_vpts])

theorem muEquiv_apply (j : Fin 5) (x : Fin 4) : (muEquiv h p₀ j x : P) = mu h p₀ j x := rfl

theorem mu_muEquiv_symm (j : Fin 5) (q : vpts h p₀ j) : mu h p₀ j ((muEquiv h p₀ j).symm q) = q :=
  congrArg Subtype.val ((muEquiv h p₀ j).apply_symm_apply q)

theorem exists_mu_eq {j : Fin 5} {q : P} (hq : q ∈ vpts h p₀ j) : ∃ x, mu h p₀ j x = q :=
  ⟨(muEquiv h p₀ j).symm ⟨q, hq⟩, mu_muEquiv_symm h p₀ j ⟨q, hq⟩⟩

end Frame

end CFSG.ComponentClassification.WittDesign
