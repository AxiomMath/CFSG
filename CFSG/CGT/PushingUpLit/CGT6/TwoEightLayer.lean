module

public import CFSG.CGT.PushingUpLit.CGT6.TwoEightKU

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Layer

variable {F L : Type} [Field F] [AddCommGroup L] [Module F L] [CharP F 2] {D : Data F L}

structure NormAdd (D : Data F L) (a : Equiv.Perm (Wd F L)) (α : L → L) : Prop where
  add : ∀ w w' : Wd F L, a (w + w') = a w + a w'
  conj : ∀ x w, a (sigFun D x w) = sigFun D (α x) (a w)
  surj : Function.Surjective α
  inj : Function.Injective α

theorem NormAdd.alpha_zero {a : Equiv.Perm (Wd F L)} {α : L → L} (h : NormAdd D a α) :
    α 0 = 0 := by
  have : sigPerm D (α 0) = sigPerm D 0 := by
    ext w : 1
    obtain ⟨u, rfl⟩ := a.surjective w
    have := h.conj 0 u
    rw [sigFun_zero] at this
    exact this.symm.trans (sigFun_zero D _).symm
  exact sigPerm_injective D this

theorem NormAdd.alpha_add {a : Equiv.Perm (Wd F L)} {α : L → L} (h : NormAdd D a α) (x y : L) :
    α (x + y) = α x + α y := by
  apply sigPerm_injective D
  ext w : 1
  obtain ⟨u, rfl⟩ := a.surjective w
  have h1 := h.conj (x + y) u
  rw [← sigFun_sigFun D x y u, h.conj, h.conj, sigFun_sigFun] at h1
  exact h1.symm

omit [CharP F 2] in
theorem NormAdd.layer1 {a : Equiv.Perm (Wd F L)} {α : L → L} (h : NormAdd D a α) {x₁ : L}
    (hx₁ : x₁ ≠ 0) (p : F) : (a (p, 0, 0)).2.1 = 0 ∧ (a (p, 0, 0)).2.2 = 0 := by
  have hfix : ∀ y, sigFun D y (a (p, 0, 0)) = a (p, 0, 0) := by
    intro y
    obtain ⟨x, rfl⟩ := h.surj y
    rw [← h.conj]
    congr 1
    simp [sigFun]
  exact (sigFun_fix_iff D hx₁ _).mp hfix

omit [CharP F 2] in
theorem NormAdd.layer2 {a : Equiv.Perm (Wd F L)} {α : L → L} (h : NormAdd D a α) {x₁ : L}
    (hx₁ : x₁ ≠ 0) (y : L) : (a (0, y, 0)).2.2 = 0 := by
  obtain ⟨x', hx'⟩ := B_eq_zero_of_ne D hx₁
  obtain ⟨x, hx⟩ := h.surj x₁
  obtain ⟨z, hz⟩ := h.surj x'
  have h1 := sigFun_comm2 D x z (0, y, 0)
  simp only [zero_mul, Prod.mk_zero_zero, add_zero] at h1
  have h2 := congrArg a h1
  have e1 : a (sigFun D x (sigFun D z (0, y, 0))) =
      sigFun D (α x) (sigFun D (α z) (a (0, y, 0))) := by rw [h.conj, h.conj]
  have e2 : a (sigFun D x (0, y, 0)) = sigFun D (α x) (a (0, y, 0)) := h.conj _ _
  have e3 : a (sigFun D z (0, y, 0)) = sigFun D (α z) (a (0, y, 0)) := h.conj _ _
  simp only [h.add, e1, e2, e3] at h2
  have h3 := sigFun_comm2 D (α x) (α z) (a (0, y, 0))
  rw [h2] at h3
  have h4 : ((a (0, y, 0)).2.2 * D.B (α x) (α z), (0 : L), (0 : F)) = 0 := by
    have h5 := h3
    exact (add_eq_left.mp h5.symm)
  have h5 := congrArg Prod.fst h4
  simp only [Prod.fst_zero] at h5
  rw [hx, hz] at h5
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact h6
  · exact absurd h6 hx'

omit [CharP F 2] in
theorem NormAdd.exists_defs {a : Equiv.Perm (Wd F L)} {α : L → L} (h : NormAdd D a α) {x₁ : L}
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
theorem NormAdd.rel {a : Equiv.Perm (Wd F L)} {α : L → L} (h : NormAdd D a α)
    {θ : F → F} {ξ : L → F} {ψ : L → L} {ζ : F → F} {η : F → L} {χ : F → F}
    (hθ : ∀ p, a (p, 0, 0) = (θ p, 0, 0)) (hξ : ∀ y, a (0, y, 0) = (ξ y, ψ y, 0))
    (hζ : ∀ s, a (0, 0, s) = (ζ s, η s, χ s)) (s : F) (x : L) :
    ψ (s • x) = χ s • α x := by
  have hdec : ((D.Q x * s, s • x, s) : Wd F L) =
      (D.Q x * s, 0, 0) + (0, s • x, 0) + (0, 0, s) := by
    ext <;> simp
  have e := h.conj x (0, 0, s)
  have e1 : sigFun D x (0, 0, s) = (D.Q x * s, s • x, s) := by simp [sigFun]
  rw [e1, hdec, h.add, h.add, hθ, hξ, hζ] at e
  have e2 := congrArg (fun u : Wd F L => u.2.1) e
  simp only [sigFun, Prod.fst_add, Prod.snd_add] at e2
  have e3 : 0 + ψ (s • x) + η s = η s + χ s • α x := e2
  have e4 := congrArg (fun z => z - η s) e3
  simpa using e4

omit [CharP F 2] in
theorem NormAdd.form {a : Equiv.Perm (Wd F L)} {α : L → L} (h : NormAdd D a α)
    {θ : F → F} {ξ : L → F} {ψ : L → L} {ζ : F → F} {η : F → L} {χ : F → F}
    (hθ : ∀ p, a (p, 0, 0) = (θ p, 0, 0)) (hξ : ∀ y, a (0, y, 0) = (ξ y, ψ y, 0))
    (hζ : ∀ s, a (0, 0, s) = (ζ s, η s, χ s)) (p : F) (y : L) (s : F) :
    a (p, y, s) = (θ p + ξ y + ζ s, ψ y + η s, χ s) := by
  have hdec : ((p, y, s) : Wd F L) = (p, 0, 0) + (0, y, 0) + (0, 0, s) := by
    ext <;> simp
  rw [hdec, h.add, h.add, hθ, hξ, hζ]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

theorem NormAdd.exists_g [Finite F] {a : Equiv.Perm (Wd F L)} {α : L → L} (h : NormAdd D a α)
    {x₁ : L} (hx₁ : x₁ ≠ 0) : ∃ g : F ≃+* F, ∀ s x, α (s • x) = g s • α x := by
  obtain ⟨θ, ξ, ψ, ζ, η, χ, hθ, hξ, hζ⟩ := h.exists_defs hx₁
  have hrel := h.rel hθ hξ hζ
  have hα0 := h.alpha_zero
  have hαx₁ : α x₁ ≠ 0 := fun h0 => hx₁ (h.inj (h0.trans hα0.symm))
  have hψ : ∀ x, ψ x = χ 1 • α x := fun x => by
    have := hrel 1 x
    rwa [one_smul] at this
  have hI : ∀ s x, χ 1 • α (s • x) = χ s • α x := fun s x => by
    rw [← hψ, hrel s x]
  have hc : χ 1 ≠ 0 := by
    intro h0
    have hχ0 : ∀ s, χ s = 0 := fun s => by
      have := hI s x₁
      rw [h0, zero_smul] at this
      exact (smul_eq_zero.mp this.symm).resolve_right hαx₁
    obtain ⟨w, hw⟩ := a.surjective (0, 0, 1)
    have h1 := h.form hθ hξ hζ w.1 w.2.1 w.2.2
    rw [hw] at h1
    have h2 := congrArg (fun u : Wd F L => u.2.2) h1
    simp only [hχ0] at h2
    exact one_ne_zero h2
  have hg : ∀ s x, α (s • x) = (χ s / χ 1) • α x := fun s x => by
    have := hI s x
    rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hinjsmul : ∀ {u v : F}, u • α x₁ = v • α x₁ → u = v := fun {u v} hh =>
    smul_left_injective F hαx₁ hh
  have hg_add : ∀ s t, χ (s + t) / χ 1 = χ s / χ 1 + χ t / χ 1 := fun s t => by
    apply hinjsmul
    rw [← hg (s + t) x₁, add_smul s t x₁, h.alpha_add, hg s x₁, hg t x₁, add_smul]
  have hg_mul : ∀ s t, χ (s * t) / χ 1 = (χ s / χ 1) * (χ t / χ 1) := fun s t => by
    apply hinjsmul
    rw [← hg (s * t) x₁, mul_smul, hg s, hg t, smul_smul]
  have hg_one : χ 1 / χ 1 = 1 := div_self hc
  have hg_zero : χ 0 / χ 1 = 0 := by
    have := hg_add 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let gr : F →+* F :=
    { toFun := fun s => χ s / χ 1
      map_one' := hg_one
      map_mul' := hg_mul
      map_zero' := hg_zero
      map_add' := hg_add }
  have hbij : Function.Bijective gr := Finite.injective_iff_bijective.mp gr.injective
  exact ⟨RingEquiv.ofBijective gr hbij, fun s x => hg s x⟩

end Layer

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
