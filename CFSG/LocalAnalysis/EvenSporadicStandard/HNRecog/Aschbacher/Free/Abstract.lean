module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Free.Linear
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Free.Wreath
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Free

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem four_le_finrank_range_of_fixed
    (σ : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* (V ≃ₗ[ZMod 2] V))
    (hσ : Function.Injective σ)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ g, ∀ u ∈ U, σ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (b : V ≃ₗ[ZMod 2] V) (hb : b * b = 1) (x₀ : alternatingGroup (Fin 5))
    (hcomm : ∀ y : alternatingGroup (Fin 5),
      σ (x₀ * y * x₀⁻¹, y) * b = b * σ (x₀ * y * x₀⁻¹, y))
    (S : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))
    (hS1 : ∃ x : alternatingGroup (Fin 5), x ≠ 1 ∧ (x, 1) ∈ S)
    (hS2 : ∃ y : alternatingGroup (Fin 5), y ≠ 1 ∧ (1, y) ∈ S)
    (w : V) (hw : ∀ s ∈ S, σ s w = w) (hbw : b w ≠ w) (hbS : ∀ s ∈ S, σ s (b w) = b w) :
    4 ≤ finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) + 1)) := by
  let u : V := w + b w
  have hu_def : u = w + b w := rfl
  let U : Submodule (ZMod 2) V := LinearMap.range ((b : V →ₗ[ZMod 2] V) + 1)
  have hU_def : U = LinearMap.range ((b : V →ₗ[ZMod 2] V) + 1) := rfl
  change 4 ≤ finrank (ZMod 2) U
  by_contra hcon
  have hUle : finrank (ZMod 2) U ≤ 3 := by omega
  have hself : ∀ v : V, v + v = 0 := by
    intro v
    have h2 : (2 : ZMod 2) • v = v + v := two_smul (ZMod 2) v
    rw [show (2 : ZMod 2) = 0 from by decide, zero_smul] at h2
    exact h2.symm
  have hu_ne_zero : u ≠ 0 := by
    intro hzero
    rw [hu_def] at hzero
    have hbw_eq : b w = w := by
      have h1 : w + b w = w + w := by
        rw [hzero]
        exact (hself w).symm
      exact add_left_cancel h1
    exact hbw hbw_eq
  have hu_mem : u ∈ U := by
    rw [hU_def]
    refine LinearMap.mem_range.mpr ⟨w, ?_⟩
    rw [hu_def, LinearMap.add_apply, Module.End.one_apply]
    exact add_comm (b w) w
  let dHom : Fpf.A5 →* (Fpf.A5 × Fpf.A5) :=
    { toFun := fun y => (x₀ * y * x₀⁻¹, y)
      map_one' := by
        change ((x₀ * 1 * x₀⁻¹, 1) : Fpf.A5 × Fpf.A5) = ((1 : Fpf.A5), 1)
        apply Prod.ext <;> group
      map_mul' := by
        intro y z
        change ((x₀ * (y * z) * x₀⁻¹, y * z) : Fpf.A5 × Fpf.A5)
          = ((x₀ * y * x₀⁻¹) * (x₀ * z * x₀⁻¹), y * z)
        apply Prod.ext <;> group }
  have hdHom_apply : ∀ y : Fpf.A5, dHom y = (x₀ * y * x₀⁻¹, y) := fun y => rfl
  have h_comm : ∀ y : Fpf.A5, ∀ z : V,
      σ (dHom y) ((b : V →ₗ[ZMod 2] V) z) = (b : V →ₗ[ZMod 2] V) (σ (dHom y) z) := by
    intro y z
    have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e z) (hcomm y)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
    change σ (x₀ * y * x₀⁻¹, y) ((b : V →ₗ[ZMod 2] V) z)
      = (b : V →ₗ[ZMod 2] V) (σ (x₀ * y * x₀⁻¹, y) z)
    exact h
  have hUinv : ∀ y : Fpf.A5, ∀ v ∈ U, σ (dHom y) v ∈ U := by
    intro y v hv
    rw [hU_def] at hv
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hv
    rw [hU_def]
    refine LinearMap.mem_range.mpr ⟨σ (dHom y) z, ?_⟩
    simp only [LinearMap.add_apply, Module.End.one_apply, map_add, h_comm y z]
  have ha0_5 : Fpf.a₀ ^ 5 = 1 := by
    have h := pow_orderOf_eq_one Fpf.a₀
    rwa [Fpf.orderOf_a₀] at h
  have hg1_5 : (dHom Fpf.a₀) ^ 5 = 1 := by
    rw [← map_pow, ha0_5]
    exact map_one dHom
  have hsig_5 : σ (dHom Fpf.a₀) ^ 5 = 1 := by
    rw [← map_pow, hg1_5]
    exact map_one σ
  let F : V →ₗ[ZMod 2] V := (σ (dHom Fpf.a₀) : V →ₗ[ZMod 2] V)
  have hF5 : F ^ 5 = 1 := by
    change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (σ (dHom Fpf.a₀))) ^ 5 = 1
    rw [← map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom (σ (dHom Fpf.a₀)) 5, hsig_5]
    rfl
  have hγ5 : (F.restrict (hUinv Fpf.a₀)) ^ 5 = 1 := by
    ext x
    have hpow : ∀ n : ℕ, (((F.restrict (hUinv Fpf.a₀)) ^ n) x : V) = (F ^ n) x := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        simp only [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih]
    rw [hpow 5, hF5]
    rfl
  have hγ1 : F.restrict (hUinv Fpf.a₀) = 1 :=
    eq_one_of_pow_five_of_finrank_le_three (V := U) _ hγ5 hUle
  have hfix_a0 : ∀ v ∈ U, σ (dHom Fpf.a₀) v = v := by
    intro v hv
    have h := congrArg (fun f : U →ₗ[ZMod 2] U => f ⟨v, hv⟩) hγ1
    have h2 : F v = v := congrArg Subtype.val h
    change F v = v
    exact h2
  let N : Subgroup Fpf.A5 :=
    { carrier := {y | ∀ v ∈ U, σ (dHom y) v = v}
      one_mem' := by intro v hv; simp
      mul_mem' := by
        intro y z hy hz v hv
        simp only [map_mul, LinearEquiv.mul_apply, hz v hv, hy v hv]
      inv_mem' := by
        intro y hy v hv
        rw [map_inv, map_inv]
        apply (σ (dHom y)).injective
        simp [hy v hv] }
  have ha0N : Fpf.a₀ ∈ N := by
    show ∀ v ∈ U, σ (dHom Fpf.a₀) v = v
    exact hfix_a0
  have ha0_ne : Fpf.a₀ ≠ 1 := by
    intro h
    have h5 := Fpf.orderOf_a₀
    rw [h, orderOf_one] at h5
    omega
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hb : Fpf.a₀ ∈ (⊥ : Subgroup Fpf.A5) := hbot ▸ ha0N
    rw [Subgroup.mem_bot] at hb
    exact ha0_ne hb
  have hNnormal : N.Normal :=
    ⟨fun n hn g => by
      intro v hv
      have hginv : σ (dHom g⁻¹) v ∈ U := hUinv g⁻¹ v hv
      have hnfix : σ (dHom n) (σ (dHom g⁻¹) v) = σ (dHom g⁻¹) v := hn _ hginv
      calc σ (dHom (g * n * g⁻¹)) v
          = σ (dHom g) (σ (dHom n) (σ (dHom g⁻¹) v)) := by
              simp only [map_mul, LinearEquiv.mul_apply]
        _ = σ (dHom g) (σ (dHom g⁻¹) v) := by rw [hnfix]
        _ = v := by
              simp only [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one,
                LinearEquiv.coe_one]
              rfl⟩
  haveI : IsSimpleGroup Fpf.A5 := alternatingGroup.isSimpleGroup (by simp)
  haveI : N.Normal := hNnormal
  have hNtop : N = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact absurd h hNne
    · exact h
  have hNmem : ∀ y : Fpf.A5, y ∈ N := by
    intro y
    rw [hNtop]
    exact Subgroup.mem_top y
  have hu_fixed_S : ∀ s ∈ S, σ s u = u := by
    intro s hs
    simp only [hu_def, map_add, hw s hs, hbS s hs]
  let K : Subgroup (Fpf.A5 × Fpf.A5) :=
    { carrier := {g | σ g u = u}
      one_mem' := by simp
      mul_mem' := by
        intro y z hy hz
        change σ y u = u at hy
        change σ z u = u at hz
        change σ (y * z) u = u
        simp only [map_mul, LinearEquiv.mul_apply, hz, hy]
      inv_mem' := by
        intro y hy
        change σ y u = u at hy
        change σ y⁻¹ u = u
        rw [map_inv]
        apply (σ y).injective
        simp [hy] }
  have hD : ∀ y : Fpf.A5, (x₀ * y * x₀⁻¹, y) ∈ K := by
    intro y
    rw [← hdHom_apply y]
    show σ (dHom y) u = u
    exact hNmem y u hu_mem
  have hSK : S ≤ K := by
    intro s hs
    exact hu_fixed_S s hs
  have h1 : ∃ x : Fpf.A5, x ≠ 1 ∧ (x, 1) ∈ K := by
    obtain ⟨x, hx1, hxS⟩ := hS1
    exact ⟨x, hx1, hSK hxS⟩
  have h2 : ∃ y : Fpf.A5, y ≠ 1 ∧ (1, y) ∈ K := by
    obtain ⟨y, hy1, hyS⟩ := hS2
    exact ⟨y, hy1, hSK hyS⟩
  have hKtop : K = ⊤ := eq_top_of_diag_mem x₀ K hD h1 h2
  have hKu : ∀ g : Fpf.A5 × Fpf.A5, σ g u = u := by
    intro g
    have hgK : g ∈ K := by rw [hKtop]; exact Subgroup.mem_top g
    exact hgK
  let Fix : Submodule (ZMod 2) V :=
    { carrier := {v | ∀ g : Fpf.A5 × Fpf.A5, σ g v = v}
      add_mem' := by
        intro x y hx hy g
        simp only [map_add, hx g, hy g]
      zero_mem' := by intro g; simp
      smul_mem' := by
        intro c x hx g
        simp only [LinearEquiv.map_smul, hx g] }
  have hFix_inv : ∀ g : Fpf.A5 × Fpf.A5, ∀ v ∈ Fix, σ g v ∈ Fix := by
    intro g v hv k
    calc σ k (σ g v) = (σ k * σ g) v := (LinearEquiv.mul_apply (σ k) (σ g) v).symm
      _ = σ (k * g) v := by rw [← map_mul]
      _ = v := hv (k * g)
      _ = σ g v := (hv g).symm
  have huFix : u ∈ Fix := by
    intro g
    exact hKu g
  have hFix_ne_bot : Fix ≠ ⊥ := by
    intro hbot
    have hb : u ∈ (⊥ : Submodule (ZMod 2) V) := hbot ▸ huFix
    rw [Submodule.mem_bot] at hb
    exact hu_ne_zero hb
  have hFix_top : Fix = ⊤ := by
    rcases hirr Fix hFix_inv with h | h
    · exact absurd h hFix_ne_bot
    · exact h
  have hσ_eq_one : ∀ g : Fpf.A5 × Fpf.A5, σ g = 1 := by
    intro g
    ext v
    have hv : v ∈ Fix := by rw [hFix_top]; exact Submodule.mem_top
    simpa using hv g
  have hg1 : ∀ g : Fpf.A5 × Fpf.A5, g = 1 := by
    intro g
    apply hσ
    simp [hσ_eq_one g]
  have hprod : (Fpf.a₀, (1 : Fpf.A5)) = 1 := hg1 (Fpf.a₀, 1)
  exact ha0_ne (Prod.ext_iff.mp hprod).1

end CFSG.EvenSporadicStandard.HNRecog.Free
