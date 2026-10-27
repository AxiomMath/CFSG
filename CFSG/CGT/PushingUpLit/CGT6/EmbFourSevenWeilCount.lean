module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.CGT.PushingUpLit.CGT6.WeilCount

open Module
open scoped commutatorElement

structure WeilData (K : Type) [Field K] (U : Type) [AddCommGroup U] [Module K U] (Γ : Type)
    [Group Γ] where
  ρ : Γ →* (Module.End K U)ˣ
  lam : Subgroup.center Γ →* Kˣ
  hlam : ∀ z : Subgroup.center Γ, (ρ z : Module.End K U) = (lam z : K) • (1 : Module.End K U)
  hcomm : ∀ g h : Γ, ⁅g, h⁆ ∈ Subgroup.center Γ
  hnd : ∀ g : Γ, (∀ h : Γ, lam ⟨⁅g, h⁆, hcomm g h⟩ = 1) → g ∈ Subgroup.center Γ

section Pairing

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U] {Γ : Type} [Group Γ]
  (D : WeilData K U Γ)

@[expose] def WeilData.f (g h : Γ) : Kˣ := D.lam ⟨⁅g, h⁆, D.hcomm g h⟩

theorem WeilData.f_central_right {g z : Γ} (hz : z ∈ Subgroup.center Γ) : D.f g z = 1 := by
  have : ⁅g, z⁆ = 1 := by
    rw [commutatorElement_def]
    have := Subgroup.mem_center_iff.mp hz g
    rw [mul_inv_eq_one, this, mul_inv_cancel_right]
  unfold WeilData.f
  have h1 : (⟨⁅g, z⁆, D.hcomm g z⟩ : Subgroup.center Γ) = 1 := Subtype.ext this
  rw [h1, map_one]

theorem WeilData.f_one_left (h : Γ) : D.f 1 h = 1 := by
  unfold WeilData.f
  have h1 : (⟨⁅(1 : Γ), h⁆, D.hcomm 1 h⟩ : Subgroup.center Γ) = 1 := Subtype.ext (by simp)
  rw [h1, map_one]

theorem WeilData.f_one_right (g : Γ) : D.f g 1 = 1 := D.f_central_right (one_mem _)

theorem WeilData.f_central_left {z h : Γ} (hz : z ∈ Subgroup.center Γ) : D.f z h = 1 := by
  have : ⁅z, h⁆ = 1 := by
    rw [commutatorElement_def]
    have := Subgroup.mem_center_iff.mp hz h
    rw [← this]
    group
  unfold WeilData.f
  have h1 : (⟨⁅z, h⁆, D.hcomm z h⟩ : Subgroup.center Γ) = 1 := Subtype.ext this
  rw [h1, map_one]

theorem WeilData.f_mul_left (g g' h : Γ) : D.f (g * g') h = D.f g h * D.f g' h := by
  unfold WeilData.f
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  show ⁅g * g', h⁆ = ⁅g, h⁆ * ⁅g', h⁆
  have hc := (Subgroup.mem_center_iff.mp (D.hcomm g' h) g)
  simp only [commutatorElement_def] at hc ⊢
  calc g * g' * h * (g * g')⁻¹ * h⁻¹
      = (g * (g' * h * g'⁻¹ * h⁻¹) * g⁻¹) * (g * h * g⁻¹ * h⁻¹) := by group
    _ = (g' * h * g'⁻¹ * h⁻¹) * (g * h * g⁻¹ * h⁻¹) := by
      rw [show g * (g' * h * g'⁻¹ * h⁻¹) * g⁻¹ = (g' * h * g'⁻¹ * h⁻¹) from by
        rw [hc]; group]
    _ = (g * h * g⁻¹ * h⁻¹) * (g' * h * g'⁻¹ * h⁻¹) := by
      have hc2 := (Subgroup.mem_center_iff.mp (D.hcomm g h) (g' * h * g'⁻¹ * h⁻¹))
      simpa only [commutatorElement_def] using hc2

theorem WeilData.f_mul_right (g h h' : Γ) : D.f g (h * h') = D.f g h * D.f g h' := by
  unfold WeilData.f
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  show ⁅g, h * h'⁆ = ⁅g, h⁆ * ⁅g, h'⁆
  have hc := (Subgroup.mem_center_iff.mp (D.hcomm g h') h)
  simp only [commutatorElement_def] at hc ⊢
  calc g * (h * h') * g⁻¹ * (h * h')⁻¹
      = (g * h * g⁻¹ * h⁻¹) * (h * (g * h' * g⁻¹ * h'⁻¹) * h⁻¹) := by group
    _ = (g * h * g⁻¹ * h⁻¹) * (g * h' * g⁻¹ * h'⁻¹) := by
      rw [show h * (g * h' * g⁻¹ * h'⁻¹) * h⁻¹ = g * h' * g⁻¹ * h'⁻¹ from by
        rw [hc]; group]

theorem WeilData.f_swap (g h : Γ) : D.f h g = (D.f g h)⁻¹ := by
  unfold WeilData.f
  rw [← map_inv]
  congr 1
  apply Subtype.ext
  show ⁅h, g⁆ = ⁅g, h⁆⁻¹
  rw [commutatorElement_inv]

theorem WeilData.f_inv_right (g h : Γ) : D.f g h⁻¹ = (D.f g h)⁻¹ := by
  have h1 := D.f_mul_right g h h⁻¹
  rw [mul_inv_cancel, D.f_one_right] at h1
  exact (eq_inv_of_mul_eq_one_right h1.symm)

@[expose] def WeilData.chiL (h : Γ) : Γ →* Kˣ where
  toFun g := D.f g h
  map_one' := D.f_one_left h
  map_mul' g g' := D.f_mul_left g g' h

@[expose] def WeilData.chiR (g : Γ) : Γ →* Kˣ where
  toFun h := D.f g h
  map_one' := D.f_one_right g
  map_mul' h h' := D.f_mul_right g h h'

theorem WeilData.mem_center_of_f_right {k : Γ} (hk : ∀ g : Γ, D.f g k = 1) :
    k ∈ Subgroup.center Γ := by
  refine D.hnd k fun h => ?_
  have := D.f_swap k h
  rw [hk h] at this
  have h2 : D.f k h = 1 := by simpa using this
  exact h2

theorem WeilData.chiL_eq_one_iff (k : Γ) : D.chiL k = 1 ↔ k ∈ Subgroup.center Γ := by
  constructor
  · intro h
    exact D.mem_center_of_f_right fun g => by
      have := congrArg (fun χ : Γ →* Kˣ => χ g) h
      simpa [WeilData.chiL] using this
  · intro hk
    ext g
    exact congrArg Units.val (D.f_central_right hk)

theorem WeilData.chiR_eq_one_iff (g : Γ) : D.chiR g = 1 ↔ g ∈ Subgroup.center Γ := by
  constructor
  · intro h
    exact D.hnd g fun k => by
      have := congrArg (fun χ : Γ →* Kˣ => χ k) h
      simpa [WeilData.chiR, WeilData.f] using this
  · intro hg
    ext k
    exact congrArg Units.val (D.f_central_left hg)

end Pairing

section CharSum

variable {K : Type} [Field K] {M : Type} [Group M] [Fintype M]

open Classical in
theorem sum_hom_units (χ : M →* Kˣ) :
    ∑ m : M, ((χ m : Kˣ) : K) = if χ = 1 then (Fintype.card M : K) else 0 := by
  by_cases h : χ = 1
  · subst h
    simp
  · have hz : (if χ = 1 then (Fintype.card M : K) else 0) = 0 := by simp [h]
    rw [hz]
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, χ m₀ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact h (MonoidHom.ext hcon)
    have hs : ∑ m : M, ((χ m : Kˣ) : K) = ((χ m₀ : Kˣ) : K) * ∑ m : M, ((χ m : Kˣ) : K) := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.mulLeft m₀)
        (fun m => ((χ m₀ : Kˣ) : K) * ((χ m : Kˣ) : K)) (fun m => ((χ m : Kˣ) : K))
        (fun m => by simp [map_mul])).symm
    have h1 : (((χ m₀ : Kˣ) : K) - 1) * ∑ m : M, ((χ m : Kˣ) : K) = 0 := by
      rw [sub_mul, one_mul, ← hs, sub_self]
    have h2 : ((χ m₀ : Kˣ) : K) - 1 ≠ 0 := by
      intro h3
      apply hm₀
      ext
      exact sub_eq_zero.mp h3
    exact (mul_eq_zero.mp h1).resolve_left h2

end CharSum

section Ad

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U] {Γ : Type} [Group Γ]
  (D : WeilData K U Γ)

@[expose] def WeilData.Ad (g : Γ) : Module.End K U →ₗ[K] Module.End K U where
  toFun a := (D.ρ g : Module.End K U) * a * (((D.ρ g)⁻¹ : (Module.End K U)ˣ) : Module.End K U)
  map_add' a b := by simp only [mul_add, add_mul]
  map_smul' c a := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

theorem WeilData.Ad_apply (g : Γ) (a : Module.End K U) :
    D.Ad g a = (D.ρ g : Module.End K U) * a *
      (((D.ρ g)⁻¹ : (Module.End K U)ˣ) : Module.End K U) := rfl

theorem WeilData.Ad_mul (g g' : Γ) (a : Module.End K U) :
    D.Ad (g * g') a = D.Ad g (D.Ad g' a) := by
  simp only [WeilData.Ad_apply, map_mul, mul_inv_rev, Units.val_mul, mul_assoc]

theorem WeilData.Ad_mul_alg (g : Γ) (a b : Module.End K U) :
    D.Ad g (a * b) = D.Ad g a * D.Ad g b := by
  simp only [WeilData.Ad_apply]
  calc (D.ρ g : Module.End K U) * (a * b) * (((D.ρ g)⁻¹ : (Module.End K U)ˣ) : Module.End K U)
      = (D.ρ g : Module.End K U) * a * ((((D.ρ g)⁻¹ : (Module.End K U)ˣ) : Module.End K U) *
          (D.ρ g : Module.End K U)) * b * (((D.ρ g)⁻¹ : (Module.End K U)ˣ) : Module.End K U) := by
        rw [Units.inv_mul]; simp [mul_assoc]
    _ = _ := by simp [mul_assoc]

theorem WeilData.Ad_central {z : Γ} (hz : z ∈ Subgroup.center Γ) (a : Module.End K U) :
    D.Ad z a = a := by
  have h1 := D.hlam ⟨z, hz⟩
  simp only [WeilData.Ad_apply]
  have h2 : (D.ρ z : Module.End K U) * a = a * (D.ρ z : Module.End K U) := by
    rw [show (D.ρ z : Module.End K U) = (D.lam ⟨z, hz⟩ : K) • (1 : Module.End K U) from h1]
    simp
  rw [h2, mul_assoc, Units.mul_inv, mul_one]

theorem WeilData.Ad_ρ (g h : Γ) :
    D.Ad g (D.ρ h : Module.End K U) = ((D.f g h : Kˣ) : K) • (D.ρ h : Module.End K U) := by
  simp only [WeilData.Ad_apply]
  have h1 : (D.ρ g : Module.End K U) * (D.ρ h : Module.End K U) *
      (((D.ρ g)⁻¹ : (Module.End K U)ˣ) : Module.End K U) =
      ((D.ρ (⁅g, h⁆ * h) : (Module.End K U)ˣ) : Module.End K U) := by
    have : ⁅g, h⁆ * h = g * h * g⁻¹ := by simp [commutatorElement_def]
    rw [this, map_mul, map_mul, map_inv]
    simp [Units.val_mul]
  rw [h1, map_mul, Units.val_mul]
  have h2 := D.hlam ⟨⁅g, h⁆, D.hcomm g h⟩
  simp only at h2
  rw [h2]
  simp [WeilData.f]

end Ad

section Pi

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U] {Γ : Type} [Group Γ]
  [Fintype Γ] (D : WeilData K U Γ)

@[expose] def WeilData.pi (h : Γ) : Module.End K U →ₗ[K] Module.End K U :=
  (Fintype.card Γ : K)⁻¹ • ∑ g : Γ, (((D.f g h)⁻¹ : Kˣ) : K) • D.Ad g

theorem WeilData.pi_apply (h : Γ) (a : Module.End K U) :
    D.pi h a = (Fintype.card Γ : K)⁻¹ • ∑ g : Γ, (((D.f g h)⁻¹ : Kˣ) : K) • D.Ad g a := by
  simp [WeilData.pi, LinearMap.sum_apply]

open Classical in
theorem WeilData.pi_ρ_mul (hΓ : (Fintype.card Γ : K) ≠ 0) (h h₀ : Γ) (b : Module.End K U)
    (hb : ∀ g, D.Ad g b = b) :
    D.pi h ((D.ρ h₀ : Module.End K U) * b) =
      if h⁻¹ * h₀ ∈ Subgroup.center Γ then (D.ρ h₀ : Module.End K U) * b else 0 := by
  rw [D.pi_apply]
  have h1 : ∀ g : Γ, D.Ad g ((D.ρ h₀ : Module.End K U) * b) =
      ((D.f g h₀ : Kˣ) : K) • ((D.ρ h₀ : Module.End K U) * b) := fun g => by
    rw [D.Ad_mul_alg, D.Ad_ρ, hb g, smul_mul_assoc]
  simp only [h1, smul_smul]
  rw [← Finset.sum_smul]
  have h2 : ∀ g : Γ, (((D.f g h)⁻¹ : Kˣ) : K) * ((D.f g h₀ : Kˣ) : K) =
      ((D.chiL (h⁻¹ * h₀) g : Kˣ) : K) := fun g => by
    show _ = ((D.f g (h⁻¹ * h₀) : Kˣ) : K)
    rw [D.f_mul_right, D.f_inv_right, Units.val_mul]
  simp only [h2]
  rw [sum_hom_units]
  by_cases hk : h⁻¹ * h₀ ∈ Subgroup.center Γ
  · have hk' : D.chiL (h⁻¹ * h₀) = 1 := (D.chiL_eq_one_iff _).mpr hk
    simp [hk, hk', smul_smul, inv_mul_cancel₀ hΓ]
  · have hk' : D.chiL (h⁻¹ * h₀) ≠ 1 := fun h' => hk ((D.chiL_eq_one_iff _).mp h')
    simp [hk, hk']

theorem WeilData.Ad_pi (h g' : Γ) (a : Module.End K U) :
    D.Ad g' (D.pi h a) = ((D.f g' h : Kˣ) : K) • D.pi h a := by
  rw [D.pi_apply, map_smul, map_sum, smul_comm]
  congr 1
  have hs : ∀ g : Γ, D.Ad g' ((((D.f g h)⁻¹ : Kˣ) : K) • D.Ad g a) =
      (((D.f g h)⁻¹ : Kˣ) : K) • D.Ad (g' * g) a := fun g => by
    rw [map_smul, D.Ad_mul]
  simp only [hs]
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g') _ _ (fun g => ?_)
  show (((D.f g h)⁻¹ : Kˣ) : K) • D.Ad (g' * g) a =
    ((D.f g' h : Kˣ) : K) • ((((D.f (g' * g) h)⁻¹ : Kˣ) : K) • D.Ad (g' * g) a)
  rw [smul_smul, D.f_mul_left, mul_inv, Units.val_mul]
  congr 1
  rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

end Pi

section Section

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U] {Γ : Type} [Group Γ]
  [Fintype Γ] (D : WeilData K U Γ)

theorem hom_inv_eq_one_iff {M : Type} [Group M] (χ : M →* Kˣ) : χ⁻¹ = 1 ↔ χ = 1 := by
  constructor <;> intro h <;> refine MonoidHom.ext fun m => ?_ <;>
    have := congrArg (fun f : M →* Kˣ => f m) h <;> simpa using this

@[expose] def WeilData.chiM (g : Γ) : (Γ ⧸ Subgroup.center Γ) →* Kˣ :=
  QuotientGroup.lift (Subgroup.center Γ) (D.chiR g) (fun _ hz => D.f_central_right hz)

omit [Fintype Γ] in
theorem WeilData.chiM_mk (g h : Γ) : D.chiM g (QuotientGroup.mk h) = D.f g h := rfl

omit [Fintype Γ] in
theorem WeilData.chiM_eq_one_iff (g : Γ) : D.chiM g = 1 ↔ g ∈ Subgroup.center Γ := by
  rw [← D.chiR_eq_one_iff]
  constructor
  · intro h
    refine MonoidHom.ext fun k => ?_
    have := congrArg (fun χ : (Γ ⧸ Subgroup.center Γ) →* Kˣ => χ (QuotientGroup.mk k)) h
    exact this
  · intro h
    refine MonoidHom.ext fun m => ?_
    induction m using QuotientGroup.induction_on with
    | H k =>
      have := congrArg (fun χ : Γ →* Kˣ => χ k) h
      exact this

open Classical in
theorem WeilData.sum_pi_section (hΓ : (Fintype.card Γ : K) ≠ 0)
    (s : Γ ⧸ Subgroup.center Γ → Γ)
    (hs : ∀ m, (QuotientGroup.mk (s m) : Γ ⧸ Subgroup.center Γ) = m) (a : Module.End K U) :
    ∑ m : Γ ⧸ Subgroup.center Γ, D.pi (s m) a = a := by
  simp only [WeilData.pi_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have h1 : ∀ g : Γ, ∑ m : Γ ⧸ Subgroup.center Γ, (((D.f g (s m))⁻¹ : Kˣ) : K) • D.Ad g a =
      (if g ∈ Subgroup.center Γ then (Fintype.card (Γ ⧸ Subgroup.center Γ) : K) else 0) •
        D.Ad g a := fun g => by
    rw [← Finset.sum_smul]
    congr 1
    have h2 : ∀ m : Γ ⧸ Subgroup.center Γ, (((D.f g (s m))⁻¹ : Kˣ) : K) =
        ((((D.chiM g)⁻¹ : (Γ ⧸ Subgroup.center Γ) →* Kˣ) m : Kˣ) : K) := fun m => by
      rw [MonoidHom.inv_apply, ← hs m, D.chiM_mk, hs m]
    simp only [h2]
    rw [sum_hom_units]
    by_cases hg : g ∈ Subgroup.center Γ
    · have : (D.chiM g)⁻¹ = 1 := (hom_inv_eq_one_iff _).mpr ((D.chiM_eq_one_iff g).mpr hg)
      simp [hg, this]
    · have : (D.chiM g)⁻¹ ≠ 1 := fun h' =>
        hg ((D.chiM_eq_one_iff g).mp ((hom_inv_eq_one_iff _).mp h'))
      simp [hg, this]
  simp only [h1]
  have h3 : ∀ g : Γ, (if g ∈ Subgroup.center Γ then
      (Fintype.card (Γ ⧸ Subgroup.center Γ) : K) else 0) • D.Ad g a =
      if g ∈ Subgroup.center Γ then (Fintype.card (Γ ⧸ Subgroup.center Γ) : K) • a else 0 :=
    fun g => by
      by_cases hg : g ∈ Subgroup.center Γ
      · simp [hg, D.Ad_central hg]
      · simp [hg]
  simp only [h3]
  rw [← Finset.sum_filter, Finset.sum_const]
  have hcard : Fintype.card Γ = Fintype.card ↥(Subgroup.center Γ) *
      Fintype.card (Γ ⧸ Subgroup.center Γ) := by
    have := Subgroup.card_mul_index (Subgroup.center Γ)
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card] at this
    exact this.symm
  have hfilt : (Finset.univ.filter fun g : Γ => g ∈ Subgroup.center Γ).card =
      Fintype.card ↥(Subgroup.center Γ) := by
    rw [← Fintype.card_subtype]
  have hcardK : (Fintype.card Γ : K) = (Fintype.card ↥(Subgroup.center Γ) : K) *
      (Fintype.card (Γ ⧸ Subgroup.center Γ) : K) := by rw [hcard, Nat.cast_mul]
  rw [hfilt, ← Nat.cast_smul_eq_nsmul K, smul_smul, smul_smul, mul_assoc, ← hcardK,
    inv_mul_cancel₀ hΓ, one_smul]

end Section

section Iso

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U] {Γ : Type} [Group Γ]
  [Fintype Γ] (D : WeilData K U Γ)

@[expose] def WeilData.W1 : Submodule K (Module.End K U) :=
  ⨅ g : Γ, LinearMap.ker (D.Ad g - LinearMap.id)

omit [Fintype Γ] in
theorem WeilData.mem_W1 {b : Module.End K U} : b ∈ D.W1 ↔ ∀ g, D.Ad g b = b := by
  simp [WeilData.W1, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem WeilData.pi_mem_inv (h : Γ) (a : Module.End K U) :
    ((D.ρ h⁻¹ : (Module.End K U)ˣ) : Module.End K U) * D.pi h a ∈ D.W1 := by
  rw [D.mem_W1]
  intro g
  rw [D.Ad_mul_alg, D.Ad_pi, D.Ad_ρ, D.f_inv_right, smul_mul_assoc, mul_smul_comm, smul_smul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

open Classical in
theorem WeilData.finrank_end [FiniteDimensional K U] (hΓ : (Fintype.card Γ : K) ≠ 0) :
    (finrank K U) ^ 2 = Fintype.card (Γ ⧸ Subgroup.center Γ) * finrank K D.W1 := by
  let s : (Γ ⧸ Subgroup.center Γ) → Γ :=
    Function.surjInv (QuotientGroup.mk_surjective (s := Subgroup.center Γ))
  have hs : ∀ m, (QuotientGroup.mk (s m) : Γ ⧸ Subgroup.center Γ) = m :=
    Function.surjInv_eq _
  let Ψ : ((Γ ⧸ Subgroup.center Γ) → ↥D.W1) →ₗ[K] Module.End K U :=
    ∑ m : Γ ⧸ Subgroup.center Γ, (LinearMap.mulLeft K (D.ρ (s m) : Module.End K U)).comp
      (D.W1.subtype.comp (LinearMap.proj m))
  have hΨ : ∀ b, Ψ b = ∑ m : Γ ⧸ Subgroup.center Γ,
      (D.ρ (s m) : Module.End K U) * (b m : Module.End K U) := by
    intro b
    simp [Ψ]
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    funext m'
    have h1 : D.pi (s m') (Ψ b) = 0 := by rw [hb, map_zero]
    rw [hΨ, map_sum] at h1
    have h2 : ∀ m : Γ ⧸ Subgroup.center Γ, D.pi (s m')
        ((D.ρ (s m) : Module.End K U) * (b m : Module.End K U)) =
        if m = m' then (D.ρ (s m) : Module.End K U) * (b m : Module.End K U) else 0 := by
      intro m
      rw [D.pi_ρ_mul hΓ _ _ _ ((D.mem_W1).mp (b m).2)]
      have : (s m')⁻¹ * s m ∈ Subgroup.center Γ ↔ m = m' := by
        rw [← QuotientGroup.eq, hs, hs]
        exact eq_comm
      simp only [this]
    simp only [h2] at h1
    rw [Finset.sum_ite_eq' Finset.univ m'] at h1
    simp only [Finset.mem_univ, ↓reduceIte] at h1
    have h3 : (b m' : Module.End K U) = 0 := by
      have := congrArg (fun x => (((D.ρ (s m'))⁻¹ : (Module.End K U)ˣ) : Module.End K U) * x) h1
      simpa [← mul_assoc] using this
    exact Subtype.ext h3
  have hsurj : Function.Surjective Ψ := by
    intro a
    refine ⟨fun m => ⟨((D.ρ (s m)⁻¹ : (Module.End K U)ˣ) : Module.End K U) * D.pi (s m) a,
      D.pi_mem_inv _ _⟩, ?_⟩
    rw [hΨ]
    have : ∀ m : Γ ⧸ Subgroup.center Γ, (D.ρ (s m) : Module.End K U) *
        (((D.ρ (s m)⁻¹ : (Module.End K U)ˣ) : Module.End K U) * D.pi (s m) a) = D.pi (s m) a :=
      fun m => by
        rw [← mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
          one_mul]
    simp only [this]
    exact D.sum_pi_section hΓ s hs a
  have hequiv := LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  have h4 := hequiv.finrank_eq
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h4
  have h5 : finrank K (Module.End K U) = (finrank K U) ^ 2 := by
    rw [sq]
    exact Module.finrank_linearMap K K U U
  rw [← h5, ← h4]

end Iso

section Twist

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U] {Γ : Type} [Group Γ]
  [Fintype Γ] (D : WeilData K U Γ)

structure WeilTwist where
  σ : MulAut Γ
  T : (Module.End K U)ˣ
  hσc : ∀ z ∈ Subgroup.center Γ, σ z = z
  hT : ∀ g : Γ, D.ρ (σ g) = T * D.ρ g * T⁻¹

variable {D}

theorem WeilData.pi_congr (h h' : Γ) (hh : h⁻¹ * h' ∈ Subgroup.center Γ) :
    D.pi h = D.pi h' := by
  have hf : ∀ g : Γ, D.f g h' = D.f g h := fun g => by
    have : h' = h * (h⁻¹ * h') := by group
    rw [this, D.f_mul_right, D.f_central_right hh, mul_one]
  ext a : 1
  simp only [WeilData.pi_apply, hf]

omit [Fintype Γ] in
theorem WeilData.f_σ (Tw : WeilTwist D) (g h : Γ) : D.f (Tw.σ g) (Tw.σ h) = D.f g h := by
  unfold WeilData.f
  congr 1
  apply Subtype.ext
  show ⁅Tw.σ g, Tw.σ h⁆ = ⁅g, h⁆
  rw [← map_commutatorElement]
  exact Tw.hσc _ (D.hcomm g h)

@[expose] def WeilTwist.AdT (Tw : WeilTwist D) : Module.End K U →ₗ[K] Module.End K U where
  toFun a := (Tw.T : Module.End K U) * a * (((Tw.T)⁻¹ : (Module.End K U)ˣ) : Module.End K U)
  map_add' a b := by simp only [mul_add, add_mul]
  map_smul' c a := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

omit [Fintype Γ] in
theorem WeilTwist.AdT_apply (Tw : WeilTwist D) (a : Module.End K U) :
    Tw.AdT a = (Tw.T : Module.End K U) * a *
      (((Tw.T)⁻¹ : (Module.End K U)ˣ) : Module.End K U) := rfl

omit [Fintype Γ] in
theorem WeilTwist.AdT_Ad (Tw : WeilTwist D) (g : Γ) (a : Module.End K U) :
    Tw.AdT (D.Ad g a) = D.Ad (Tw.σ g) (Tw.AdT a) := by
  have h1 : ((D.ρ (Tw.σ g) : (Module.End K U)ˣ) : Module.End K U) =
      (Tw.T : Module.End K U) * (D.ρ g : Module.End K U) *
        (((Tw.T)⁻¹ : (Module.End K U)ˣ) : Module.End K U) := by
    rw [Tw.hT g]
    simp [Units.val_mul]
  have h2 : (((D.ρ (Tw.σ g))⁻¹ : (Module.End K U)ˣ) : Module.End K U) =
      (Tw.T : Module.End K U) * (((D.ρ g)⁻¹ : (Module.End K U)ˣ) : Module.End K U) *
        (((Tw.T)⁻¹ : (Module.End K U)ˣ) : Module.End K U) := by
    rw [Tw.hT g]
    simp [mul_inv_rev, Units.val_mul, mul_assoc]
  simp only [WeilTwist.AdT_apply, WeilData.Ad_apply, h1, h2, mul_assoc,
    Units.inv_mul_cancel_left]

theorem WeilTwist.AdT_pi (Tw : WeilTwist D) (h : Γ)
    (a : Module.End K U) : Tw.AdT (D.pi h a) = D.pi (Tw.σ h) (Tw.AdT a) := by
  rw [D.pi_apply, D.pi_apply, map_smul, map_sum]
  congr 1
  simp only [map_smul, Tw.AdT_Ad]
  refine (Fintype.sum_equiv Tw.σ.toEquiv _ _ fun g => ?_)
  show (((D.f g h)⁻¹ : Kˣ) : K) • D.Ad (Tw.σ g) (Tw.AdT a) =
    (((D.f (Tw.σ g) (Tw.σ h))⁻¹ : Kˣ) : K) • D.Ad (Tw.σ g) (Tw.AdT a)
  rw [D.f_σ Tw]

end Twist

section OrbitCount

open MulAction

variable {M : Type} [Group M] [Finite M]

theorem five_mul_card_orbits (σb : MulAut M) (h5 : σb ^ 5 = 1) :
    5 * Nat.card (Quotient (orbitRel (Subgroup.zpowers σb) M)) =
      Nat.card M + 4 * Nat.card (MonoidHom.eqLocus (σb : M →* M) (MonoidHom.id M)) := by
  classical
  have : Fintype M := Fintype.ofFinite M
  have : Fintype (Subgroup.zpowers σb) := Fintype.ofFinite _
  have : Fintype (Quotient (orbitRel (Subgroup.zpowers σb) M)) := Fintype.ofFinite _
  have hburn := sum_card_fixedBy_eq_card_orbits_mul_card_group (Subgroup.zpowers σb) M
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card (α := Subgroup.zpowers σb),
    Nat.card_zpowers] at hburn
  have hord : orderOf σb = 1 ∨ orderOf σb = 5 :=
    (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one h5)
  rcases hord with h1 | h5'
  ·
    have hσ1 : σb = 1 := orderOf_eq_one_iff.mp h1
    rw [h1, mul_one] at hburn
    subst hσ1
    have hC : Nat.card (MonoidHom.eqLocus ((1 : MulAut M) : M →* M) (MonoidHom.id M)) =
        Nat.card M := by
      have : MonoidHom.eqLocus ((1 : MulAut M) : M →* M) (MonoidHom.id M) = ⊤ := by
        ext m
        simp only [Subgroup.mem_top, iff_true]
        rfl
      rw [this, Subgroup.card_top]
    rw [hC]
    have hG : Subsingleton (Subgroup.zpowers (1 : MulAut M)) := by
      rw [Subgroup.zpowers_one_eq_bot]
      infer_instance
    have hsum : ∑ g : Subgroup.zpowers (1 : MulAut M), Fintype.card (fixedBy M g) =
        Fintype.card M := by
      rw [Finset.sum_eq_single (1 : Subgroup.zpowers (1 : MulAut M))]
      · simp
      · intro b _ hb
        exact absurd (Subsingleton.elim b 1) hb
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum, ← Nat.card_eq_fintype_card] at hburn
    omega
  · have hG5 : Nat.card (Subgroup.zpowers σb) = 5 := by rw [Nat.card_zpowers, h5']
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    rw [h5'] at hburn
    have hfix : ∀ g : Subgroup.zpowers σb, g ≠ 1 → ∀ m : M, (g • m = m ↔ σb m = m) := by
      intro g hg m
      constructor
      · intro hgm
        have htop : Subgroup.zpowers g = ⊤ := zpowers_eq_top_of_prime_card hG5 hg
        have hmem : (⟨σb, Subgroup.mem_zpowers σb⟩ : Subgroup.zpowers σb) ∈
            MulAction.stabilizer (Subgroup.zpowers σb) m := by
          have : Subgroup.zpowers g ≤ MulAction.stabilizer (Subgroup.zpowers σb) m :=
            Subgroup.zpowers_le.mpr hgm
          rw [htop] at this
          exact this (Subgroup.mem_top _)
        exact hmem
      · intro hm
        have hle : Subgroup.zpowers σb ≤ MulAction.stabilizer (MulAut M) m :=
          Subgroup.zpowers_le.mpr hm
        exact hle g.2
    have hsum : ∑ g : Subgroup.zpowers σb, Fintype.card (fixedBy M g) =
        Fintype.card M + 4 * Nat.card (MonoidHom.eqLocus (σb : M →* M) (MonoidHom.id M)) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : Subgroup.zpowers σb))]
      congr 1
      · rw [← Nat.card_eq_fintype_card (α := M)]
        rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (fun m => by simp))]
        exact (Nat.card_eq_fintype_card).symm
      · have hcard : ∀ g ∈ Finset.univ.erase (1 : Subgroup.zpowers σb),
            Fintype.card (fixedBy M g) =
              Nat.card (MonoidHom.eqLocus (σb : M →* M) (MonoidHom.id M)) := by
          intro g hg
          have hg1 : g ≠ 1 := Finset.ne_of_mem_erase hg
          rw [← Nat.card_eq_fintype_card]
          refine Nat.card_congr (Equiv.subtypeEquivRight fun m => ?_)
          rw [mem_fixedBy, hfix g hg1 m]
          rfl
        rw [Finset.sum_congr rfl hcard, Finset.sum_const, Finset.card_erase_of_mem
          (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card, hG5]
        rfl
    rw [hsum, ← Nat.card_eq_fintype_card] at hburn
    omega

end OrbitCount

section Fixed

open MulAction

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U] {Γ : Type} [Group Γ]
  [Fintype Γ] {D : WeilData K U Γ} (Tw : WeilTwist D)

@[expose] def WeilTwist.F : Submodule K (Module.End K U) := LinearMap.ker (Tw.AdT - LinearMap.id)

omit [Fintype Γ] in
theorem WeilTwist.mem_F {a : Module.End K U} : a ∈ Tw.F ↔ Tw.AdT a = a := by
  simp [WeilTwist.F, LinearMap.mem_ker, sub_eq_zero]

theorem WeilTwist.AdT_pi_section
    (s : Γ ⧸ Subgroup.center Γ → Γ)
    (hs : ∀ m, (QuotientGroup.mk (s m) : Γ ⧸ Subgroup.center Γ) = m)
    (σb : MulAut (Γ ⧸ Subgroup.center Γ))
    (hσb : ∀ g : Γ, σb (QuotientGroup.mk g) = QuotientGroup.mk (Tw.σ g))
    (m : Γ ⧸ Subgroup.center Γ) (a : Module.End K U) :
    Tw.AdT (D.pi (s m) a) = D.pi (s (σb m)) (Tw.AdT a) := by
  rw [Tw.AdT_pi]
  refine congrArg (fun π => π (Tw.AdT a)) (D.pi_congr _ _ ?_)
  rw [← QuotientGroup.eq]
  rw [← hσb, hs, hs]

theorem WeilTwist.pi_section_pow_zero
    (s : Γ ⧸ Subgroup.center Γ → Γ)
    (hs : ∀ m, (QuotientGroup.mk (s m) : Γ ⧸ Subgroup.center Γ) = m)
    (σb : MulAut (Γ ⧸ Subgroup.center Γ))
    (hσb : ∀ g : Γ, σb (QuotientGroup.mk g) = QuotientGroup.mk (Tw.σ g))
    {a : Module.End K U} (ha : a ∈ Tw.F) (m : Γ ⧸ Subgroup.center Γ)
    (h0 : D.pi (s m) a = 0) (i : ℕ) : D.pi (s ((σb ^ i) m)) a = 0 := by
  induction i with
  | zero => simpa using h0
  | succ i ih =>
    have h1 := Tw.AdT_pi_section s hs σb hσb ((σb ^ i) m) a
    rw [(Tw.mem_F).mp ha, ih, map_zero] at h1
    rw [pow_succ']
    exact h1.symm

omit [Fintype Γ] in
theorem exists_nat_pow_eq (σb : MulAut (Γ ⧸ Subgroup.center Γ)) (h5 : σb ^ 5 = 1) (k : ℤ) :
    ∃ i : ℕ, σb ^ k = σb ^ i := by
  have h5' : σb ^ (5 : ℤ) = 1 := by simpa using h5
  refine ⟨(k % 5).toNat, ?_⟩
  rw [zpow_eq_zpow_emod k h5', ← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]

open Classical in
theorem WeilTwist.five_finrank_F_le [FiniteDimensional K U] (hΓ : (Fintype.card Γ : K) ≠ 0)
    (σb : MulAut (Γ ⧸ Subgroup.center Γ))
    (hσb : ∀ g : Γ, σb (QuotientGroup.mk g) = QuotientGroup.mk (Tw.σ g)) (h5 : σb ^ 5 = 1) :
    5 * finrank K Tw.F ≤ (Nat.card (Γ ⧸ Subgroup.center Γ) +
      4 * Nat.card (MonoidHom.eqLocus (σb : (Γ ⧸ Subgroup.center Γ) →* (Γ ⧸ Subgroup.center Γ))
        (MonoidHom.id _))) * finrank K D.W1 := by
  let s : (Γ ⧸ Subgroup.center Γ) → Γ :=
    Function.surjInv (QuotientGroup.mk_surjective (s := Subgroup.center Γ))
  have hs : ∀ m, (QuotientGroup.mk (s m) : Γ ⧸ Subgroup.center Γ) = m :=
    Function.surjInv_eq _
  have : Fintype (Quotient (orbitRel (Subgroup.zpowers σb) (Γ ⧸ Subgroup.center Γ))) :=
    Fintype.ofFinite _
  let r : Quotient (orbitRel (Subgroup.zpowers σb) (Γ ⧸ Subgroup.center Γ)) →
      (Γ ⧸ Subgroup.center Γ) := Quotient.out
  let Θ : ↥Tw.F →ₗ[K] (Quotient (orbitRel (Subgroup.zpowers σb) (Γ ⧸ Subgroup.center Γ)) →
      ↥D.W1) := LinearMap.pi fun c => LinearMap.codRestrict D.W1
    ((LinearMap.mulLeft K ((D.ρ (s (r c))⁻¹ : (Module.End K U)ˣ) : Module.End K U)).comp
      ((D.pi (s (r c))).comp Tw.F.subtype)) (fun a => D.pi_mem_inv _ _)
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro a ha0
    have hc : ∀ c, D.pi (s (r c)) (a : Module.End K U) = 0 := fun c => by
      have h2 : (((D.ρ (s (r c))⁻¹ : (Module.End K U)ˣ) : Module.End K U) *
          D.pi (s (r c)) (a : Module.End K U)) = 0 :=
        congrArg Subtype.val (congrFun ha0 c)
      have h3 := congrArg (fun x => (D.ρ (s (r c)) : Module.End K U) * x) h2
      have h4 : (D.ρ (s (r c)) : Module.End K U) *
          (((D.ρ (s (r c))⁻¹ : (Module.End K U)ˣ) : Module.End K U) *
            D.pi (s (r c)) (a : Module.End K U)) = D.pi (s (r c)) (a : Module.End K U) := by
        rw [← mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
          one_mul]
      simp only [h4, mul_zero] at h3
      exact h3
    have hm : ∀ m : Γ ⧸ Subgroup.center Γ, D.pi (s m) (a : Module.End K U) = 0 := fun m => by
      have hq : (Quotient.mk (orbitRel (Subgroup.zpowers σb) (Γ ⧸ Subgroup.center Γ)) m) =
          Quotient.mk _ (r (Quotient.mk _ m)) := (Quotient.out_eq _).symm
      have hrel : m ∈ orbit (Subgroup.zpowers σb) (r (Quotient.mk _ m)) :=
        (orbitRel_apply).mp (Quotient.exact hq)
      obtain ⟨g, hg⟩ := (mem_orbit_iff).mp hrel
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      obtain ⟨i, hi⟩ := exists_nat_pow_eq σb h5 k
      have hgm : (g : MulAut (Γ ⧸ Subgroup.center Γ)) = σb ^ i := by rw [← hk, hi]
      have : g • r (Quotient.mk _ m) = (σb ^ i) (r (Quotient.mk _ m)) := by
        rw [Subgroup.smul_def, MulAut.smul_def, hgm]
      rw [this] at hg
      rw [← hg]
      exact Tw.pi_section_pow_zero s hs σb hσb a.2 _ (hc _) i
    have hsum := D.sum_pi_section hΓ s hs (a : Module.End K U)
    simp only [hm, Finset.sum_const_zero] at hsum
    exact Subtype.ext hsum.symm
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
  have h2 := five_mul_card_orbits σb h5
  calc 5 * finrank K Tw.F ≤ 5 * (Fintype.card (Quotient (orbitRel (Subgroup.zpowers σb)
        (Γ ⧸ Subgroup.center Γ))) * finrank K D.W1) := Nat.mul_le_mul_left _ h1
    _ = (5 * Nat.card (Quotient (orbitRel (Subgroup.zpowers σb) (Γ ⧸ Subgroup.center Γ)))) *
        finrank K D.W1 := by rw [Nat.card_eq_fintype_card]; ring
    _ = _ := by rw [h2]

end Fixed

end CFSG.CGT.PushingUpLit.CGT6.WeilCount
