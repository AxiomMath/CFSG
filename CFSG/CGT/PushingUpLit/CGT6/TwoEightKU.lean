module

public import CFSG.CGT.PushingUpLit.CGT6.TwoEightData

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Centralizer

variable {F L : Type} [Field F] [AddCommGroup L] [Module F L] [CharP F 2] (D : Data F L)

theorem F_add_self (t : F) : t + t = 0 := by
  rw [← two_mul]
  have : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [this, zero_mul]

omit [CharP F 2] in
theorem sigFun_comm2 (x x' : L) (u : Wd F L) :
    sigFun D x (sigFun D x' u) + u =
      sigFun D x u + sigFun D x' u + (u.2.2 * D.B x x', 0, 0) := by
  rcases u with ⟨p, y, s⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [sigFun, Prod.fst_add, map_add, map_smul, smul_eq_mul]
    ring
  · simp only [sigFun, Prod.snd_add, Prod.fst_add]
    abel
  · simp only [sigFun, Prod.snd_add]
    simp

omit [CharP F 2] in
theorem sigFun_fix_iff {x₁ : L} (hx₁ : x₁ ≠ 0) (w : Wd F L) :
    (∀ x, sigFun D x w = w) ↔ w.2.1 = 0 ∧ w.2.2 = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun u : Wd F L => u.2.1) (h x₁)
    simp only [sigFun, add_eq_left] at h1
    have hs' : w.2.2 = 0 := by
      rcases smul_eq_zero.mp h1 with h0 | h0
      · exact h0
      · exact absurd h0 hx₁
    refine ⟨?_, hs'⟩
    apply D.nondeg.2 w.2.1
    intro x
    have h2 := congrArg (fun u : Wd F L => u.1) (h x)
    simp only [sigFun] at h2
    rw [hs', mul_zero, add_zero] at h2
    simpa using h2
  · rintro ⟨hy, hs⟩ x
    rcases w with ⟨p, y, s⟩
    simp only at hy hs
    subst hy
    subst hs
    simp [sigFun]

structure CentAdd (a : Equiv.Perm (Wd F L)) : Prop where
  add : ∀ w w' : Wd F L, a (w + w') = a w + a w'
  comm : ∀ x w, a (sigFun D x w) = sigFun D x (a w)

variable {D}

omit [CharP F 2] in
theorem CentAdd.map_zero {a : Equiv.Perm (Wd F L)} (h : CentAdd D a) : a 0 = 0 := by
  have h0 := h.add 0 0
  rw [add_zero] at h0
  exact left_eq_add.mp h0

omit [CharP F 2] in
theorem CentAdd.layer1 {a : Equiv.Perm (Wd F L)} (h : CentAdd D a) {x₁ : L} (hx₁ : x₁ ≠ 0)
    (p : F) : (a (p, 0, 0)).2.1 = 0 ∧ (a (p, 0, 0)).2.2 = 0 := by
  have hfix : ∀ x, sigFun D x (a (p, 0, 0)) = a (p, 0, 0) := by
    intro x
    rw [← h.comm]
    congr 1
    simp [sigFun]
  exact (sigFun_fix_iff D hx₁ _).mp hfix

omit [CharP F 2] in
theorem CentAdd.layer2 {a : Equiv.Perm (Wd F L)} (h : CentAdd D a) {x₁ : L} (hx₁ : x₁ ≠ 0)
    (y : L) : (a (0, y, 0)).2.2 = 0 := by
  obtain ⟨x', hx'⟩ := B_eq_zero_of_ne D hx₁
  have h1 := sigFun_comm2 D x₁ x' (0, y, 0)
  simp only [zero_mul, Prod.mk_zero_zero, add_zero] at h1
  have h2 := congrArg a h1
  have e1 : a (sigFun D x₁ (sigFun D x' (0, y, 0))) =
      sigFun D x₁ (sigFun D x' (a (0, y, 0))) := by rw [h.comm, h.comm]
  have e2 : a (sigFun D x₁ (0, y, 0)) = sigFun D x₁ (a (0, y, 0)) := h.comm _ _
  have e3 : a (sigFun D x' (0, y, 0)) = sigFun D x' (a (0, y, 0)) := h.comm _ _
  simp only [h.add, e1, e2, e3] at h2
  have h3 := sigFun_comm2 D x₁ x' (a (0, y, 0))
  rw [h2] at h3
  have h4 : ((a (0, y, 0)).2.2 * D.B x₁ x', (0 : L), (0 : F)) = 0 := by
    have h5 := h3
    exact (add_eq_left.mp h5.symm)
  have h5 := congrArg Prod.fst h4
  simp only [Prod.fst_zero] at h5
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact h6
  · exact absurd h6 hx'

omit [CharP F 2] in
theorem CentAdd.exists_defs {a : Equiv.Perm (Wd F L)} (h : CentAdd D a) {x₁ : L}
    (hx₁ : x₁ ≠ 0) :
    ∃ (θ : F → F) (ξ : L → F) (ψ : L → L) (ζ : F → F) (η : F → L) (χ : F → F),
      (∀ p, a (p, 0, 0) = (θ p, 0, 0)) ∧ (∀ y, a (0, y, 0) = (ξ y, ψ y, 0)) ∧
      (∀ s, a (0, 0, s) = (ζ s, η s, χ s)) := by
  refine ⟨fun p => (a (p, 0, 0)).1, fun y => (a (0, y, 0)).1, fun y => (a (0, y, 0)).2.1,
    fun s => (a (0, 0, s)).1, fun s => (a (0, 0, s)).2.1, fun s => (a (0, 0, s)).2.2,
    fun p => ?_, fun y => ?_, fun s => rfl⟩
  · obtain ⟨h1, h2⟩ := h.layer1 hx₁ p
    exact Prod.ext rfl (Prod.ext h1 h2)
  · exact Prod.ext rfl (Prod.ext rfl (h.layer2 hx₁ y))

omit [CharP F 2] in
theorem CentAdd.form {a : Equiv.Perm (Wd F L)} (h : CentAdd D a)
    {θ : F → F} {ξ : L → F} {ψ : L → L} {ζ : F → F} {η : F → L} {χ : F → F}
    (hθ : ∀ p, a (p, 0, 0) = (θ p, 0, 0)) (hξ : ∀ y, a (0, y, 0) = (ξ y, ψ y, 0))
    (hζ : ∀ s, a (0, 0, s) = (ζ s, η s, χ s)) (p : F) (y : L) (s : F) :
    a (p, y, s) = (θ p + ξ y + ζ s, ψ y + η s, χ s) := by
  have hdec : ((p, y, s) : Wd F L) = (p, 0, 0) + (0, y, 0) + (0, 0, s) := by
    ext <;> simp
  rw [hdec, h.add, h.add, hθ, hξ, hζ]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

omit [CharP F 2] in
theorem CentAdd.relations {a : Equiv.Perm (Wd F L)} (h : CentAdd D a)
    {θ : F → F} {ξ : L → F} {ψ : L → L} {ζ : F → F} {η : F → L} {χ : F → F}
    (hθ : ∀ p, a (p, 0, 0) = (θ p, 0, 0)) (hξ : ∀ y, a (0, y, 0) = (ξ y, ψ y, 0))
    (hζ : ∀ s, a (0, 0, s) = (ζ s, η s, χ s)) :
    (∀ s x, ψ (s • x) = χ s • x) ∧
      (∀ s x, θ (D.Q x * s) + ξ (s • x) = D.B x (η s) + D.Q x * χ s) ∧
      (∀ x y, θ (D.B x y) = D.B x (ψ y)) := by
  have hform := h.form hθ hξ hζ
  refine ⟨fun s x => ?_, fun s x => ?_, fun x y => ?_⟩
  · have e := h.comm x (0, 0, s)
    have e1 : sigFun D x (0, 0, s) = (D.Q x * s, s • x, s) := by simp [sigFun]
    rw [e1, hform, hζ] at e
    have e2 := congrArg (fun u : Wd F L => u.2.1) e
    simp only [sigFun] at e2
    have e3 : ψ (s • x) + η s = η s + χ s • x := e2
    have e4 := congrArg (fun z => z - η s) e3
    simpa using e4
  · have e := h.comm x (0, 0, s)
    have e1 : sigFun D x (0, 0, s) = (D.Q x * s, s • x, s) := by simp [sigFun]
    rw [e1, hform, hζ] at e
    have e2 := congrArg (fun u : Wd F L => u.1) e
    simp only [sigFun] at e2
    have e3 : θ (D.Q x * s) + ξ (s • x) + ζ s = ζ s + D.B x (η s) + D.Q x * χ s := e2
    linear_combination e3
  · have e := h.comm x (0, y, 0)
    have e1 : sigFun D x (0, y, 0) = (D.B x y, 0, 0) + (0, y, 0) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [sigFun]
    rw [e1, h.add, hθ, hξ] at e
    have e2 := congrArg (fun u : Wd F L => u.1) e
    simp only [sigFun, Prod.fst_add] at e2
    have e3 : θ (D.B x y) + ξ y = ξ y + D.B x (ψ y) + D.Q x * 0 := e2
    linear_combination e3

theorem mem_S0_of_centralizes {Γ : Subgroup (Equiv.Perm (Wd F L))}
    (hΓσ : ∀ x, sigPerm D x ∈ Γ) {x₁ : L} (hx₁ : x₁ ≠ 0) (hΓl : lamPerm D x₁ ∈ Γ)
    (hΓQ : ∀ g ∈ Γ, ∀ w, Qt D (g w) = Qt D w)
    {a : Equiv.Perm (Wd F L)} (h : CentAdd D a) (ha2 : a * a = 1)
    (hnorm : ∀ g ∈ Γ, a * g * a⁻¹ ∈ Γ) : a ∈ S0 D := by
  obtain ⟨θ, ξ, ψ, ζ, η, χ, hθ, hξ, hζ⟩ := h.exists_defs hx₁
  have hform := h.form hθ hξ hζ
  obtain ⟨R1, R2, R3⟩ := h.relations hθ hξ hζ
  have haa : ∀ w, a (a w) = w := fun w => by
    have := congrArg (fun g : Equiv.Perm (Wd F L) => g w) ha2
    simpa using this
  obtain ⟨c, hc⟩ : ∃ c, c = χ 1 := ⟨_, rfl⟩
  have hψ : ∀ x, ψ x = c • x := fun x => by
    have := R1 1 x
    rw [one_smul] at this
    rw [this, hc]
  have hχ : ∀ s, χ s = c * s := fun s => by
    have h1 := R1 s x₁
    rw [hψ, ← mul_smul] at h1
    exact (smul_left_injective F hx₁ h1).symm
  have hcc : c * c = 1 := by
    have e := haa (0, 0, 1)
    rw [hζ 1, hform] at e
    have e3 := congrArg (fun u : Wd F L => u.2.2) e
    simp only at e3
    rw [hχ (χ 1), ← hc] at e3
    exact e3
  have hc1 : c = 1 := by
    rcases mul_self_eq_one_iff.mp hcc with h1 | h1
    · exact h1
    · rw [h1, CharTwo.neg_eq]
  have hψ1 : ∀ x, ψ x = x := fun x => by rw [hψ, hc1, one_smul]
  have hχ1 : ∀ s, χ s = s := fun s => by rw [hχ, hc1, one_mul]
  have hθ1 : ∀ t, θ t = t := fun t => by
    obtain ⟨y, hy⟩ := B_surj D hx₁ t
    have := R3 x₁ y
    rw [hy, hψ1, hy] at this
    exact this
  have R2' : ∀ s x, ξ (s • x) = D.B x (η s) := fun s x => by
    have := R2 s x
    rw [hθ1, hχ1] at this
    linear_combination this
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = η 1 := ⟨_, rfl⟩
  have hξ' : ∀ y, ξ y = D.B y x₀ := fun y => by
    have := R2' 1 y
    rw [one_smul] at this
    rw [this, hx₀]
  have hz : a (0, 0, 0) = 0 := h.map_zero
  have hη0 : η 0 = 0 := by
    have e2 := hζ 0
    rw [hz] at e2
    have := congrArg (fun u : Wd F L => u.2.1) e2
    simpa using this.symm
  have hζ0 : ζ 0 = 0 := by
    have e2 := hζ 0
    rw [hz] at e2
    have := congrArg (fun u : Wd F L => u.1) e2
    simpa using this.symm
  have hη : ∀ s, η s = s • x₀ := fun s => by
    by_cases hs : s = 0
    · subst hs
      rw [hη0, zero_smul]
    · apply sub_eq_zero.mp
      apply D.nondeg.2
      intro w
      have e := R2' s (s⁻¹ • w)
      rw [smul_inv_smul₀ hs, B_smul_left, hξ' w] at e
      have e' : s * D.B w x₀ = D.B w (η s) := by
        rw [e]
        field_simp
      rw [map_sub, B_smul_right]
      linear_combination (-1 : F) * e'
  have hfinal : ∀ p y s, a (p, y, s) = (p + D.B x₀ y + ζ s, y + s • x₀, s) := fun p y s => by
    rw [hform, hθ1, hξ', hψ1, hη, hχ1, B_symm D y x₀]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : F → F, ∀ s, ρ s = ζ s + D.Q x₀ * s :=
    ⟨fun s => ζ s + D.Q x₀ * s, fun s => rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : Equiv.Perm (Wd F L), b = sigPerm D x₀ * a := ⟨_, rfl⟩
  have hb : ∀ w : Wd F L, b w = (w.1 + ρ w.2.2, w.2.1, w.2.2) := fun w => by
    rcases w with ⟨p, y, s⟩
    rw [hbdef, Equiv.Perm.mul_apply, hfinal, sigPerm_apply]
    simp only [sigFun, map_add, map_smul, smul_eq_mul, D.alt, mul_zero, add_zero, hρ]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · linear_combination F_add_self (D.B x₀ y)
    · show y + s • x₀ + s • x₀ = y
      rw [add_assoc, add_self_L F, add_zero]
  have hb2 : b * b = 1 := by
    ext w : 1
    rw [Equiv.Perm.mul_apply, hb, hb]
    refine Prod.ext ?_ (Prod.ext rfl rfl)
    · simp only [Equiv.Perm.coe_one, id]
      rw [add_assoc, F_add_self, add_zero]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hbconj : ∀ g ∈ Γ, b * g * b⁻¹ ∈ Γ := fun g hg => by
    have := Γ.mul_mem (Γ.mul_mem (hΓσ x₀) (hnorm g hg)) (Γ.inv_mem (hΓσ x₀))
    rw [hbdef]
    simpa only [mul_inv_rev, mul_assoc] using this
  have hγ : b * lamPerm D x₁ * b⁻¹ ∈ Γ := hbconj _ hΓl
  have key : ∀ s y, ρ s * s + ρ (s + D.B x₁ y + D.Q x₁ * ρ s) *
      (s + D.B x₁ y + D.Q x₁ * ρ s) = 0 := by
    intro s y
    have hQ := hΓQ _ hγ (0, y, s)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hbinv, hb, lamPerm_apply, hb] at hQ
    simp only [lamFun, Qt, zero_add, zero_mul] at hQ
    rw [D.Q_add, D.Q_smul, B_smul_right D, B_symm D y x₁] at hQ
    linear_combination hQ - F_add_self (ρ s * D.B x₁ y) - F_add_self (D.Q x₁ * ρ s ^ 2)
  have hρ0 : ∀ s, ρ s = 0 := by
    intro s
    by_cases hs : s = 0
    · rw [hρ, hs, hζ0, mul_zero, add_zero]
    · obtain ⟨y, hy⟩ := B_surj D hx₁ (D.Q x₁ * ρ s + s)
      have e := key s y
      rw [hy] at e
      have hs' : s + (D.Q x₁ * ρ s + s) + D.Q x₁ * ρ s = 0 := by
        linear_combination F_add_self s + F_add_self (D.Q x₁ * ρ s)
      rw [hs', mul_zero, add_zero] at e
      rcases mul_eq_zero.mp e with h0 | h0
      · exact h0
      · exact absurd h0 hs
  refine ⟨x₀, ?_⟩
  ext w : 1
  rcases w with ⟨p, y, s⟩
  rw [sigPerm_apply, hfinal]
  have h1 : ζ s + D.Q x₀ * s = 0 := by rw [← hρ]; exact hρ0 s
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  · show p + D.B x₀ y + D.Q x₀ * s = p + D.B x₀ y + ζ s
    linear_combination (-1 : F) * h1 + F_add_self (D.Q x₀ * s)

end Centralizer

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
