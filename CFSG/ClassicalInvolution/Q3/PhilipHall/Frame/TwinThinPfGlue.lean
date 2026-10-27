module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

variable {G : Type} [Group G]

theorem conj_mem_of_normalizer {X : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (X : Set G)) {x : G}
    (hx : x ∈ X) : y * x * y⁻¹ ∈ X :=
  (Subgroup.mem_normalizer_iff.mp hy x).mp hx

@[expose] def conjOn (X : Subgroup G) (y : G) (hy : y ∈ Subgroup.normalizer (X : Set G)) : ↥X →* ↥X where
  toFun x := ⟨y * x * y⁻¹, conj_mem_of_normalizer hy x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjOn_apply {X : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (X : Set G)) (x : ↥X) :
    ((conjOn X y hy x : ↥X) : G) = y * x * y⁻¹ := rfl

theorem conjOn_iterate {X : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (X : Set G)) (k : ℕ) (x : ↥X) :
    (((⇑(conjOn X y hy))^[k] x : ↥X) : G) = y ^ k * x * (y ^ k)⁻¹ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, conjOn_apply, pow_succ]
    simp [mul_assoc]

theorem centralizes_of_trivial_mod_ker {X : Subgroup G} {M : Type} [Group M] (φ : ↥X →* M)
    (hker : φ.ker ≤ Subgroup.center ↥X) {y : G} (hy : y ∈ Subgroup.normalizer (X : Set G))
    (htriv : ∀ x : ↥X, φ (conjOn X y hy x) = φ x) {L₀ : Subgroup G}
    (hyL₀ : ∀ l ∈ L₀, y * l = l * y) (hL₀ : L₀ ≤ X)
    (hgen : ∀ x ∈ X, x ∈ Subgroup.closure {u : G | ∃ l ∈ L₀, ∃ c ∈ X, u = c * l * c⁻¹}) :
    ∀ x ∈ X, y * x = x * y := by
  have hδker : ∀ x : ↥X, x⁻¹ * conjOn X y hy x ∈ Subgroup.center ↥X := by
    intro x
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, htriv, inv_mul_cancel]
  let δ : ↥X →* ↥X :=
    { toFun := fun x => x⁻¹ * conjOn X y hy x
      map_one' := by simp
      map_mul' := fun a b => by
        have hc := Subgroup.mem_center_iff.mp (hδker a)
        calc (a * b)⁻¹ * conjOn X y hy (a * b)
            = b⁻¹ * (a⁻¹ * conjOn X y hy a) * conjOn X y hy b := by
              rw [map_mul]; group
          _ = (a⁻¹ * conjOn X y hy a) * (b⁻¹ * conjOn X y hy b) := by
              rw [hc b⁻¹]
              group }
  have hδ : ∀ x : ↥X, δ x = x⁻¹ * conjOn X y hy x := fun x => rfl
  have hgenδ : ∀ u : G, (∃ l ∈ L₀, ∃ c ∈ X, u = c * l * c⁻¹) → ∃ hu : u ∈ X, δ ⟨u, hu⟩ = 1 := by
    rintro u ⟨l, hl, c, hc, rfl⟩
    have hlX : l ∈ X := hL₀ hl
    have hu : c * l * c⁻¹ ∈ X := X.mul_mem (X.mul_mem hc hlX) (X.inv_mem hc)
    refine ⟨hu, ?_⟩
    have h1 : δ ⟨l, hlX⟩ = 1 := by
      rw [hδ]
      apply Subtype.ext
      show l⁻¹ * (y * l * y⁻¹) = 1
      rw [hyL₀ l hl]
      group
    have h2 : (⟨c * l * c⁻¹, hu⟩ : ↥X) = ⟨c, hc⟩ * ⟨l, hlX⟩ * ⟨c, hc⟩⁻¹ := rfl
    rw [h2, map_mul, map_mul, map_inv]
    have hcen := Subgroup.mem_center_iff.mp (hδker ⟨c, hc⟩)
    rw [h1]
    simp
  have hS : Subgroup.closure {u : G | ∃ l ∈ L₀, ∃ c ∈ X, u = c * l * c⁻¹} ≤
      (MonoidHom.ker δ).map X.subtype := by
    rw [Subgroup.closure_le]
    intro u hu
    obtain ⟨hux, hδu⟩ := hgenδ u hu
    exact ⟨⟨u, hux⟩, hδu, rfl⟩
  intro x hx
  obtain ⟨x', hx', hxx⟩ := hS (hgen x hx)
  have hx'' : x' = ⟨x, hx⟩ := Subtype.ext hxx
  rw [hx''] at hx'
  have h1 : δ ⟨x, hx⟩ = 1 := hx'
  rw [hδ] at h1
  have h3 : x⁻¹ * (y * x * y⁻¹) = 1 := by
    have h2 := congrArg Subtype.val h1
    simpa [conjOn_apply] using h2
  show y * x = x * y
  calc y * x = x * (x⁻¹ * (y * x * y⁻¹)) * y := by group
    _ = x * y := by rw [h3]; group

section Induced

variable {X : Subgroup G} {M : Type} [Group M] (φ : ↥X →* M) {y : G}
  (hy : y ∈ Subgroup.normalizer (X : Set G))

theorem ker_invariant (hker : φ.ker ≤ Subgroup.center ↥X) (hZ : Subgroup.center ↥φ.range = ⊥)
    {x : ↥X} (hx : x ∈ φ.ker) : conjOn X y hy x ∈ φ.ker := by
  have hxc := Subgroup.mem_center_iff.mp (hker hx)
  have hc : conjOn X y hy x ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro w
    have hy' : y⁻¹ ∈ Subgroup.normalizer (X : Set G) := (Subgroup.normalizer _).inv_mem hy
    have hw : y⁻¹ * (w : G) * y⁻¹⁻¹ ∈ X := conj_mem_of_normalizer hy' w.2
    have h1 := hxc ⟨y⁻¹ * (w : G) * y⁻¹⁻¹, hw⟩
    have h2 := congrArg Subtype.val h1
    apply Subtype.ext
    simp only [conjOn_apply, Subgroup.coe_mul, inv_inv] at h2 ⊢
    calc (w : G) * (y * (x : G) * y⁻¹) = y * (y⁻¹ * w * y) * (x : G) * y⁻¹ := by group
      _ = y * ((x : G) * (y⁻¹ * w * y)) * y⁻¹ := by rw [← h2]; group
      _ = y * (x : G) * y⁻¹ * w := by group
  have hr : φ.rangeRestrict (conjOn X y hy x) ∈ Subgroup.center ↥φ.range := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨u, rfl⟩ := φ.rangeRestrict_surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc u]
  rw [hZ, Subgroup.mem_bot] at hr
  rw [MonoidHom.mem_ker]
  have := congrArg Subtype.val hr
  simpa using this

noncomputable def induced (hk : ∀ x : ↥X, x ∈ φ.ker → conjOn X y hy x ∈ φ.ker) :
    ↥φ.range →* ↥φ.range :=
  MonoidHom.liftOfRightInverse φ.rangeRestrict (Function.surjInv φ.rangeRestrict_surjective)
    (Function.rightInverse_surjInv _)
    ⟨φ.rangeRestrict.comp (conjOn X y hy), by
      intro x hx
      have hxk : x ∈ φ.ker := by
        rw [← MonoidHom.ker_rangeRestrict]
        exact hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
        MonoidHom.ker_rangeRestrict]
      exact hk x hxk⟩

theorem induced_apply (hk : ∀ x : ↥X, x ∈ φ.ker → conjOn X y hy x ∈ φ.ker) (x : ↥X) :
    induced φ hy hk (φ.rangeRestrict x) = φ.rangeRestrict (conjOn X y hy x) := by
  unfold induced
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

theorem induced_iterate (hk : ∀ x : ↥X, x ∈ φ.ker → conjOn X y hy x ∈ φ.ker) (k : ℕ) (x : ↥X) :
    ((⇑(induced φ hy hk))^[k] (φ.rangeRestrict x)) =
      φ.rangeRestrict ((⇑(conjOn X y hy))^[k] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, induced_apply, ih, Function.iterate_succ_apply]

include hy in
theorem centralizes_of_oddFix {L₀ : Subgroup G} (hker : φ.ker ≤ Subgroup.center ↥X)
    (hZ : Subgroup.center ↥φ.range = ⊥)
    (hfix : ∀ σ : ↥φ.range →* ↥φ.range, (∃ a : ℕ, ∀ r, (⇑σ)^[3 ^ a] r = r) →
      (∀ l : ↥X, (l : G) ∈ L₀ → σ (φ.rangeRestrict l) = φ.rangeRestrict l) →
        ∀ r, σ r = r)
    (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1)
    (hyL₀ : ∀ l ∈ L₀, y * l = l * y) (hL₀ : L₀ ≤ X)
    (hgen : ∀ x ∈ X, x ∈ Subgroup.closure {u : G | ∃ l ∈ L₀, ∃ c ∈ X, u = c * l * c⁻¹}) :
    ∀ x ∈ X, y * x = x * y := by
  have hk := fun x (hx : x ∈ φ.ker) => ker_invariant φ hy hker hZ hx
  obtain ⟨a, ha⟩ := hy3
  have hfixσ := hfix (induced φ hy hk) ⟨a, fun r => by
      obtain ⟨x, rfl⟩ := φ.rangeRestrict_surjective r
      rw [induced_iterate]
      congr 1
      apply Subtype.ext
      rw [conjOn_iterate, ha]
      simp⟩ (fun l hl => by
      rw [induced_apply]
      congr 1
      apply Subtype.ext
      rw [conjOn_apply]
      have := hyL₀ l hl
      calc y * (l : G) * y⁻¹ = l * y * y⁻¹ := by rw [this]
        _ = l := by group)
  refine centralizes_of_trivial_mod_ker φ hker hy (fun x => ?_) hyL₀ hL₀ hgen
  have := hfixσ (φ.rangeRestrict x)
  rw [induced_apply] at this
  have h2 := congrArg Subtype.val this
  exact h2

end Induced

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
