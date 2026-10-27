module

public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionAlpha

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools Equiv
open scoped commutatorElement

section ConjAct

variable {G : Type*} [Group G]

@[expose] def conjAct (N : Subgroup G) (S : Set G) (h : ∀ n ∈ N, ∀ x ∈ S, n * x * n⁻¹ ∈ S) :
    N →* Perm S where
  toFun n :=
    { toFun := fun x => ⟨(n : G) * x * (n : G)⁻¹, h n n.2 x x.2⟩
      invFun := fun x => ⟨(n : G)⁻¹ * x * (n : G), by
        simpa using h _ (N.inv_mem n.2) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
  map_one' := Equiv.ext fun x => Subtype.ext (by simp)
  map_mul' n m := Equiv.ext fun x => Subtype.ext (by simp [mul_assoc])

variable {N : Subgroup G} {S : Set G} {h : ∀ n ∈ N, ∀ x ∈ S, n * x * n⁻¹ ∈ S}

theorem coe_conjAct_apply (n : N) (x : S) :
    ((conjAct N S h n x : S) : G) = (n : G) * x * (n : G)⁻¹ :=
  rfl

end ConjAct

namespace Datum

section Pts

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A)

abbrev E (W : Subgroup G) : Subgroup G := W ⊔ zpowers d.t

@[expose] def pts (W : Subgroup G) : Set G :=
  {x | x ∈ d.E W ∧ IsConj d.t x}

variable {d}

omit [Finite G] in
theorem pts_conj {W : Subgroup G} {n : G} (hn : n ∈ normalizer ((d.E W : Subgroup G) : Set G))
    {x : G} (hx : x ∈ d.pts W) : n * x * n⁻¹ ∈ d.pts W :=
  ⟨(mem_normalizer_iff.mp hn x).mp hx.1, hx.2.trans (isConj_iff.mpr ⟨n, rfl⟩)⟩

variable (d)

@[expose] def ptsAction (W : Subgroup G) :
    ↥(normalizer ((d.E W : Subgroup G) : Set G)) →* Perm ↥(d.pts W) :=
  conjAct _ _ (fun _ hn _ hx => pts_conj hn hx)

end Pts

end Datum

namespace Facts

section Normalizer

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ : Subgroup G}

theorem normalizer_adj_le (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) :
    normalizer ((d.E W : Subgroup G) : Set G) ≤ normalizer (W : Set G) := by
  intro n hn
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  have hnw : n * w * n⁻¹ ∈ W ⊔ zpowers d.t := (mem_normalizer_iff.mp hn w).mp (mem_sup_left hw)
  have hWA : w ∈ A := (hR.property hW).1 hw |>.2
  have hnc : ¬ IsConj d.t (n * w * n⁻¹) := by
    intro hc
    exact F.not_isConj_of_mem d hR hWA (hc.trans (isConj_iff.mpr ⟨n⁻¹, by group⟩))
  exact (F.not_isConj_iff_mem d hR hα hW hnw).mp hnc

end Normalizer

end Facts

namespace Datum

theorem t_mem_pts {G : Type} [Group G] {A : Subgroup G} (d : Datum A) (W : Subgroup G) :
    d.t ∈ d.pts W :=
  ⟨mem_sup_right (mem_zpowers _), IsConj.refl _⟩

end Datum

namespace Facts

section Coset

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ : Subgroup G}

theorem mem_pts_iff (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) {x : G} : x ∈ d.pts W ↔ ∃ w ∈ W, x = d.t * w := by
  obtain ⟨hWV, -, -⟩ := hR.property hW
  have ht2 := d.t_mul_self
  constructor
  · rintro ⟨hxE, hxc⟩
    have hxW : x ∉ W := fun hx => (F.not_isConj_iff_mem d hR hα hW hxE).mpr hx hxc
    have hxt : x * d.t ∈ W := ((d.mem_adj_iff hWV).mp hxE).resolve_left hxW
    refine ⟨x * d.t, hxt, ?_⟩
    have hc := d.V_comm_t (hWV hxt)
    rw [← hc, mul_assoc, ht2, mul_one]
  · rintro ⟨w, hw, rfl⟩
    have hxE : d.t * w ∈ W ⊔ zpowers d.t :=
      mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hw)
    refine ⟨hxE, ?_⟩
    by_contra hnc
    have := (F.not_isConj_iff_mem d hR hα hW hxE).mp hnc
    exact F.t_not_mem_V d (by
      have := mul_mem (hWV this) (inv_mem (hWV hw))
      rwa [mul_inv_cancel_right] at this)

theorem card_pts (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) : Nat.card ↥(d.pts W) = 16 := by
  obtain ⟨-, -, hWc⟩ := hR.property hW
  rw [← hWc]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun w : W => (⟨d.t * w, (F.mem_pts_iff d hR hα hW).mpr ⟨w, w.2, rfl⟩⟩ : ↥(d.pts W)))
    ⟨fun w w' hww' => Subtype.ext (mul_left_cancel (congrArg Subtype.val hww')), ?_⟩)
  rintro ⟨x, hx⟩
  obtain ⟨w, hw, rfl⟩ := (F.mem_pts_iff d hR hα hW).mp hx
  exact ⟨⟨w, hw⟩, rfl⟩

theorem ptsAction_eq_one_iff (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    (hα : d.Alpha) {W : Subgroup G} (hW : W = V₁ ∨ W = V₂)
    (n : ↥(normalizer ((d.E W : Subgroup G) : Set G))) :
    d.ptsAction W n = 1 ↔ (n : G) ∈ centralizer ((d.E W : Subgroup G) : Set G) := by
  obtain ⟨hWV, -, -⟩ := hR.property hW
  have hfix : ∀ x ∈ d.pts W, d.ptsAction W n = 1 → (n : G) * x * (n : G)⁻¹ = x := by
    intro x hx h1
    have := congrArg (fun σ : Perm ↥(d.pts W) => ((σ ⟨x, hx⟩ : ↥(d.pts W)) : G)) h1
    simpa [Datum.ptsAction, coe_conjAct_apply] using this
  constructor
  · intro h1
    rw [mem_centralizer_iff]
    have ht : (n : G) * d.t * (n : G)⁻¹ = d.t := hfix _ (d.t_mem_pts W) h1
    have hw : ∀ w ∈ W, (n : G) * w * (n : G)⁻¹ = w := by
      intro w hw
      have hx := hfix (d.t * w) ((F.mem_pts_iff d hR hα hW).mpr ⟨w, hw, rfl⟩) h1
      have : (n : G) * (d.t * w) * (n : G)⁻¹ = ((n : G) * d.t * (n : G)⁻¹) *
          ((n : G) * w * (n : G)⁻¹) := by group
      rw [this, ht] at hx
      exact mul_left_cancel hx
    have hc : ∀ x ∈ d.E W, (n : G) * x * (n : G)⁻¹ = x := by
      intro x hx
      rcases (d.mem_adj_iff hWV).mp hx with hxW | hxW
      · exact hw x hxW
      · have e1 := hw _ hxW
        have : x = (x * d.t) * d.t := by rw [mul_assoc, d.t_mul_self, mul_one]
        rw [this]
        calc (n : G) * (x * d.t * d.t) * (n : G)⁻¹
            = ((n : G) * (x * d.t) * (n : G)⁻¹) * ((n : G) * d.t * (n : G)⁻¹) := by group
          _ = x * d.t * d.t := by rw [e1, ht]
    intro x hx
    have := hc x hx
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro hn
    refine Equiv.ext fun x => Subtype.ext ?_
    have hx := mem_centralizer_iff.mp hn x x.2.1
    show (n : G) * x * (n : G)⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact hx.symm

end Coset

end Facts

set_option maxRecDepth 100000 in
private theorem fin4_key : ∀ f : Fin 4 → Fin 4, Function.Injective f → f 0 = 0 →
    (∀ x, x ≠ 0 → f x ≠ x) → ∀ a b : Fin 4, a ≠ 0 → b ≠ 0 →
    b = a ∨ b = f a ∨ b = f (f a) := by
  decide

theorem exists_conj_pow_eq_of_card_four {G : Type*} [Group G] {U : Subgroup G}
    (hU : Nat.card U = 4) {y : G} (hy : y ∈ normalizer (U : Set G))
    (hfix : ∀ w ∈ U, y * w * y⁻¹ = w → w = 1) {a b : G} (ha : a ∈ U) (hb : b ∈ U)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ k : ℕ, y ^ k * a * (y ^ k)⁻¹ = b := by
  have hmem : ∀ w ∈ U, y * w * y⁻¹ ∈ U := fun w hw => (mem_set_normalizer_iff.mp hy w).mp hw
  let σ : U → U := fun w => ⟨y * w * y⁻¹, hmem w w.2⟩
  have hσinj : Function.Injective σ := by
    intro u v h
    have h' : y * (u : G) * y⁻¹ = y * (v : G) * y⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  have hσ1 : σ 1 = 1 := Subtype.ext (by simp [σ])
  have hσfix : ∀ w : U, w ≠ 1 → σ w ≠ w := by
    intro w hw h
    exact hw (Subtype.ext (hfix w w.2 (congrArg Subtype.val h)))
  have : Finite U := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype U := Fintype.ofFinite U
  let e0 : U ≃ Fin 4 := Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact hU)
  let e : U ≃ Fin 4 := e0.trans (Equiv.swap (e0 1) 0)
  have he1 : e 1 = 0 := by simp [e]
  let f : Fin 4 → Fin 4 := fun i => e (σ (e.symm i))
  have hfinj : Function.Injective f := e.injective.comp (hσinj.comp e.symm.injective)
  have hf0 : f 0 = 0 := by
    simp only [f, ← he1, Equiv.symm_apply_apply, hσ1]
  have hffix : ∀ x, x ≠ 0 → f x ≠ x := by
    intro x hx h
    apply hσfix (e.symm x)
    · intro h1
      apply hx
      rw [← he1, ← h1]
      simp
    · apply e.injective
      simpa [f] using h
  have hA : e ⟨a, ha⟩ ≠ 0 := by
    rw [← he1]
    intro h
    exact ha1 (congrArg Subtype.val (e.injective h))
  have hB : e ⟨b, hb⟩ ≠ 0 := by
    rw [← he1]
    intro h
    exact hb1 (congrArg Subtype.val (e.injective h))
  rcases fin4_key f hfinj hf0 hffix _ _ hA hB with h | h | h
  · refine ⟨0, ?_⟩
    have := congrArg Subtype.val (e.injective h)
    simpa using this.symm
  · refine ⟨1, ?_⟩
    have := congrArg Subtype.val (e.injective h)
    simpa [f, σ] using this.symm
  · refine ⟨2, ?_⟩
    have := congrArg Subtype.val (e.injective h)
    simp only [f, σ, Equiv.symm_apply_apply] at this
    rw [this, pow_two]
    simp only [mul_inv_rev, mul_assoc]

end CFSG.OddStandard.Seitz77
