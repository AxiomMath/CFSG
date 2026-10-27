module

public import CFSG.GH74.GLS.IVK.L2.TorusMatrices
public import CFSG.GH74.GLS.Stage4.HexSL2Defs
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG.GH74.GLS.Stage4.Hex
open scoped commutatorElement

section Cl

variable {G : Type} [Group G] {F : Type} [Field F]

noncomputable def clV (R₂ : Subgroup G) {V : Type} [CommGroup V] (π : ↥R₂ →* V)
    (τ : V ≃* Multiplicative (Fin 2 → F)) (g : G) : Multiplicative (Fin 2 → F) := by
  classical exact if hg : g ∈ R₂ then τ (π ⟨g, hg⟩) else 1

theorem clV_of_mem {R₂ : Subgroup G} {V : Type} [CommGroup V] (π : ↥R₂ →* V)
    (τ : V ≃* Multiplicative (Fin 2 → F)) {g : G} (hg : g ∈ R₂) :
    clV R₂ π τ g = τ (π ⟨g, hg⟩) := by
  simp [clV, hg]

theorem clV_mul {R₂ : Subgroup G} {V : Type} [CommGroup V] (π : ↥R₂ →* V)
    (τ : V ≃* Multiplicative (Fin 2 → F)) {g g' : G} (hg : g ∈ R₂) (hg' : g' ∈ R₂) :
    clV R₂ π τ (g * g') = clV R₂ π τ g * clV R₂ π τ g' := by
  rw [clV_of_mem π τ (R₂.mul_mem hg hg'), clV_of_mem π τ hg, clV_of_mem π τ hg', ← map_mul,
    ← map_mul]
  rfl

theorem clV_inv {R₂ : Subgroup G} {V : Type} [CommGroup V] (π : ↥R₂ →* V)
    (τ : V ≃* Multiplicative (Fin 2 → F)) {g : G} (hg : g ∈ R₂) :
    clV R₂ π τ g⁻¹ = (clV R₂ π τ g)⁻¹ := by
  rw [clV_of_mem π τ (R₂.inv_mem hg), clV_of_mem π τ hg, ← map_inv, ← map_inv]
  rfl

end Cl

structure SPLNatData {G : Type} [Group G] {F : Type} [Field F]
    (K₁ X₁ X₂ X₃ X₄ R₂ : Subgroup G) (ε : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    {V : Type} [CommGroup V] (π : ↥R₂ →* V) (ρ : ↥K₁ →* MulAut V)
    (τ : V ≃* Multiplicative (Fin 2 → F)) (w : G) : Prop where
  X₂_R : X₂ ≤ R₂
  X₃_R : X₃ ≤ R₂
  X₄_R : X₄ ≤ R₂
  π_ker : ∀ r : ↥R₂, π r = 1 ↔ (r : G) ∈ X₂
  K_R : ∀ k ∈ K₁, ∀ r ∈ R₂, k * r * k⁻¹ ∈ R₂
  ρ_π : ∀ (k : ↥K₁) (r : ↥R₂),
    ρ k (π r) = π ⟨(k : G) * r * (k : G)⁻¹, K_R k k.2 r r.2⟩
  τ_ρ : ∀ (k : ↥K₁) (v : V), τ (ρ k v) = Multiplicative.ofAdd
    (((ε k : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
      (Multiplicative.toAdd (τ v)))
  X₂₃ : X₂ ⊓ X₃ = ⊥
  X₂₄ : X₂ ⊓ X₄ = ⊥
  card₃ : Nat.card X₃ = Nat.card F
  card₄ : Nat.card X₄ = Nat.card F
  X₁_X₃ : ∀ k ∈ X₁, ∀ x ∈ X₃, k * x = x * k
  X₁_upper : ∀ s : F, ((ε.symm (sl2U s) : ↥K₁) : G) ∈ X₁
  w_mem : w ∈ K₁
  X₄_eq : ∀ x : G, x ∈ X₄ ↔ w * x * w⁻¹ ∈ X₃
  w_anti : ∃ s ∈ IVK.L2Torus.diagSub F, ε ⟨w, w_mem⟩ = s * IVK.L2Torus.w0 F
  H₃ : ∀ u : Fˣ, ∀ x ∈ X₃, ((ε.symm (sl2D u) : ↥K₁) : G) * x * ((ε.symm (sl2D u) : ↥K₁) : G)⁻¹ ∈ X₃
  H₄ : ∀ u : Fˣ, ∀ x ∈ X₄, ((ε.symm (sl2D u) : ↥K₁) : G) * x * ((ε.symm (sl2D u) : ↥K₁) : G)⁻¹ ∈ X₄

namespace SPLNatData

variable {G : Type} [Group G] {F : Type} [Field F] {K₁ X₁ X₂ X₃ X₄ R₂ : Subgroup G}
  {ε : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F} {V : Type} [CommGroup V] {π : ↥R₂ →* V}
  {ρ : ↥K₁ →* MulAut V} {τ : V ≃* Multiplicative (Fin 2 → F)} {w : G}
  (h : SPLNatData K₁ X₁ X₂ X₃ X₄ R₂ ε π ρ τ w)

include h

theorem cl_conj (k : ↥K₁) {r : G} (hr : r ∈ R₂) :
    clV R₂ π τ ((k : G) * r * (k : G)⁻¹) =
      Multiplicative.ofAdd
        (((ε k : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
          (Multiplicative.toAdd (clV R₂ π τ r))) := by
  have e1 := h.ρ_π k ⟨r, hr⟩
  have e2 := h.τ_ρ k (π ⟨r, hr⟩)
  rw [clV_of_mem π τ (h.K_R k k.2 r hr), clV_of_mem π τ hr, ← e2, e1]

theorem cl_one_iff {g : G} (hg : g ∈ R₂) : clV R₂ π τ g = 1 ↔ g ∈ X₂ := by
  rw [clV_of_mem π τ hg, MulEquiv.map_eq_one_iff]
  exact h.π_ker ⟨g, hg⟩

theorem cl_inj_of_inf {Y : Subgroup G} (hY : Y ≤ R₂) (hYX : X₂ ⊓ Y = ⊥) {x x' : G} (hx : x ∈ Y)
    (hx' : x' ∈ Y) (he : clV R₂ π τ x = clV R₂ π τ x') : x = x' := by
  have h1 : clV R₂ π τ (x'⁻¹ * x) = 1 := by
    rw [clV_mul π τ (R₂.inv_mem (hY hx')) (hY hx), clV_inv π τ (hY hx'), he]
    simp
  have h2 : x'⁻¹ * x ∈ X₂ := (h.cl_one_iff (R₂.mul_mem (R₂.inv_mem (hY hx')) (hY hx))).1 h1
  have h3 : x'⁻¹ * x ∈ X₂ ⊓ Y := ⟨h2, Y.mul_mem (Y.inv_mem hx') hx⟩
  rw [hYX] at h3
  exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp h3)).symm

theorem exists_param [Finite F] {Y : Subgroup G} (hY : Y ≤ R₂) (hYX : X₂ ⊓ Y = ⊥)
    (hcard : Nat.card Y = Nat.card F) (i : Fin 2)
    (hline : ∀ x ∈ Y, ∀ j : Fin 2, j ≠ i → Multiplicative.toAdd (clV R₂ π τ x) j = 0) :
    ∃ y : F → G, (∀ a, y a ∈ Y) ∧ (∀ g ∈ Y, ∃ a, y a = g) ∧
      ∀ a, clV R₂ π τ (y a) = Multiplicative.ofAdd (Pi.single i a) := by
  classical
  let f : ↥Y → F := fun x => Multiplicative.toAdd (clV R₂ π τ x) i
  have hfinj : Function.Injective f := by
    intro x x' hxx
    apply Subtype.ext
    apply h.cl_inj_of_inf hY hYX x.2 x'.2
    apply Multiplicative.toAdd.injective
    funext j
    by_cases hj : j = i
    · subst hj; exact hxx
    · rw [hline x x.2 j hj, hline x' x'.2 j hj]
  have : Finite ↥Y := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  have hfs : Function.Surjective f := hfinj.surjective_of_finite (Finite.card_eq.mp hcard).some
  choose g hg using hfs
  refine ⟨fun a => (g a : G), fun a => (g a).2, ?_, ?_⟩
  · intro x hx
    refine ⟨f ⟨x, hx⟩, ?_⟩
    have := hfinj (hg (f ⟨x, hx⟩))
    exact congrArg Subtype.val this
  · intro a
    apply Multiplicative.toAdd.injective
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [toAdd_ofAdd, Pi.single_eq_same]
      exact hg a
    · rw [toAdd_ofAdd, Pi.single_eq_of_ne hj]
      exact hline _ (g a).2 j hj

theorem exists_x34 [Finite F] :
    ∃ x₃ x₄ : F → G,
      (∀ a a', x₃ (a + a') = x₃ a * x₃ a') ∧ (∀ b b', x₄ (b + b') = x₄ b * x₄ b') ∧
      (∀ g, g ∈ X₃ ↔ ∃ a, x₃ a = g) ∧ (∀ g, g ∈ X₄ ↔ ∃ b, x₄ b = g) ∧
      (∀ s b, ∃ y ∈ X₂, ((ε.symm (sl2U s) : ↥K₁) : G) * x₄ b * ((ε.symm (sl2U s) : ↥K₁) : G)⁻¹ =
        x₃ (s * b) * x₄ b * y) ∧
      (∀ (u : Fˣ) a, ((ε.symm (sl2D u) : ↥K₁) : G) * x₃ a * ((ε.symm (sl2D u) : ↥K₁) : G)⁻¹ =
        x₃ ((u : F) * a)) ∧
      (∀ (u : Fˣ) b, ((ε.symm (sl2D u) : ↥K₁) : G) * x₄ b * ((ε.symm (sl2D u) : ↥K₁) : G)⁻¹ =
        x₄ ((u : F)⁻¹ * b)) := by
  classical
  have hA : ∀ x ∈ X₃, ∀ j : Fin 2, j ≠ 0 → Multiplicative.toAdd (clV R₂ π τ x) j = 0 := by
    intro x hx j hj
    have hj1 : j = 1 := by fin_cases j <;> simp_all
    subst hj1
    have hk1 := h.X₁_upper 1
    have hc : ((ε.symm (sl2U 1) : ↥K₁) : G) * x * ((ε.symm (sl2U 1) : ↥K₁) : G)⁻¹ = x := by
      rw [h.X₁_X₃ _ hk1 x hx]; group
    have e := h.cl_conj (ε.symm (sl2U 1)) (h.X₃_R hx)
    rw [hc, MulEquiv.apply_symm_apply] at e
    have e0 := congrArg (fun z : Multiplicative (Fin 2 → F) => Multiplicative.toAdd z 0) e
    simp [coe_sl2U, dotProduct, Fin.sum_univ_two] at e0
    exact e0
  have hB : ∀ x ∈ X₄, ∀ j : Fin 2, j ≠ 1 → Multiplicative.toAdd (clV R₂ π τ x) j = 0 := by
    intro x hx j hj
    have hj0 : j = 0 := by fin_cases j <;> simp_all
    subst hj0
    have hx3 : w * x * w⁻¹ ∈ X₃ := (h.X₄_eq x).1 hx
    have e := h.cl_conj ⟨w, h.w_mem⟩ (h.X₄_R hx)
    have e1 := hA _ hx3 1 (by decide)
    rw [e] at e1
    obtain ⟨s, hs, hsw⟩ := h.w_anti
    simp only [toAdd_ofAdd] at e1
    rw [hsw] at e1
    have hdet := s.2
    rw [Matrix.det_fin_two] at hdet
    have hs01 : (s : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := hs.1
    have hs10 : (s : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hs.2
    rw [hs01, hs10] at hdet
    have hδ : (s : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
      intro h0
      rw [h0] at hdet
      simp at hdet
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, IVK.L2Torus.w0, IVK.L2Torus.sl2_val,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, hs10] at e1
    exact e1.resolve_left hδ
  obtain ⟨x₃, hx₃mem, hx₃surj, hx₃cl⟩ :=
    h.exists_param h.X₃_R h.X₂₃ h.card₃ 0 hA
  obtain ⟨x₄, hx₄mem, hx₄surj, hx₄cl⟩ :=
    h.exists_param h.X₄_R h.X₂₄ h.card₄ 1 hB
  have hR₃ : ∀ a, x₃ a ∈ R₂ := fun a => h.X₃_R (hx₃mem a)
  have hR₄ : ∀ b, x₄ b ∈ R₂ := fun b => h.X₄_R (hx₄mem b)
  refine ⟨x₃, x₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a a'
    apply h.cl_inj_of_inf h.X₃_R h.X₂₃ (hx₃mem _) (X₃.mul_mem (hx₃mem a) (hx₃mem a'))
    rw [clV_mul π τ (hR₃ a) (hR₃ a'), hx₃cl, hx₃cl, hx₃cl, ← ofAdd_add, Pi.single_add]
  · intro b b'
    apply h.cl_inj_of_inf h.X₄_R h.X₂₄ (hx₄mem _) (X₄.mul_mem (hx₄mem b) (hx₄mem b'))
    rw [clV_mul π τ (hR₄ b) (hR₄ b'), hx₄cl, hx₄cl, hx₄cl, ← ofAdd_add, Pi.single_add]
  · intro g
    exact ⟨fun hg => hx₃surj g hg |>.imp fun a ha => ha, fun ⟨a, ha⟩ => ha ▸ hx₃mem a⟩
  · intro g
    exact ⟨fun hg => hx₄surj g hg |>.imp fun a ha => ha, fun ⟨a, ha⟩ => ha ▸ hx₄mem a⟩
  · intro s b
    have hkR : ((ε.symm (sl2U s) : ↥K₁) : G) * x₄ b * ((ε.symm (sl2U s) : ↥K₁) : G)⁻¹ ∈ R₂ :=
      h.K_R _ (ε.symm (sl2U s)).2 _ (hR₄ b)
    have hc : clV R₂ π τ (((ε.symm (sl2U s) : ↥K₁) : G) * x₄ b * ((ε.symm (sl2U s) : ↥K₁) : G)⁻¹) =
        clV R₂ π τ (x₃ (s * b) * x₄ b) := by
      rw [h.cl_conj (ε.symm (sl2U s)) (hR₄ b), hx₄cl, MulEquiv.apply_symm_apply,
        clV_mul π τ (hR₃ _) (hR₄ b), hx₃cl, hx₄cl, ← ofAdd_add]
      congr 1
      funext j
      fin_cases j <;> simp [coe_sl2U, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hyR : (x₃ (s * b) * x₄ b)⁻¹ * (((ε.symm (sl2U s) : ↥K₁) : G) * x₄ b *
        ((ε.symm (sl2U s) : ↥K₁) : G)⁻¹) ∈ R₂ :=
      R₂.mul_mem (R₂.inv_mem (R₂.mul_mem (hR₃ _) (hR₄ b))) hkR
    have hy1 : clV R₂ π τ ((x₃ (s * b) * x₄ b)⁻¹ * (((ε.symm (sl2U s) : ↥K₁) : G) * x₄ b *
        ((ε.symm (sl2U s) : ↥K₁) : G)⁻¹)) = 1 := by
      rw [clV_mul π τ (R₂.inv_mem (R₂.mul_mem (hR₃ _) (hR₄ b))) hkR,
        clV_inv π τ (R₂.mul_mem (hR₃ _) (hR₄ b)), hc]
      simp
    refine ⟨_, (h.cl_one_iff hyR).1 hy1, ?_⟩
    group
  · intro u a
    apply h.cl_inj_of_inf h.X₃_R h.X₂₃ (h.H₃ u _ (hx₃mem a)) (hx₃mem _)
    rw [h.cl_conj (ε.symm (sl2D u)) (hR₃ a), hx₃cl, MulEquiv.apply_symm_apply, hx₃cl]
    congr 1
    funext j
    fin_cases j <;> simp [coe_sl2D, Matrix.mulVec, dotProduct, Pi.single_apply]
  · intro u b
    apply h.cl_inj_of_inf h.X₄_R h.X₂₄ (h.H₄ u _ (hx₄mem b)) (hx₄mem _)
    rw [h.cl_conj (ε.symm (sl2D u)) (hR₄ b), hx₄cl, MulEquiv.apply_symm_apply, hx₄cl]
    congr 1
    funext j
    fin_cases j <;> simp [coe_sl2D, Matrix.mulVec, dotProduct, Pi.single_apply]


end SPLNatData

end CFSG.GH74.GLS.SP.Local
