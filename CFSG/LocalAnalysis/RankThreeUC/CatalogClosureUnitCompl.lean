module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOrthCompl
public import CFSG.LieType.BorelTits.FormFlag
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOrthFlag

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace UnitClosure

open Subgroup CFSG.LieType.BorelTits LinClosure

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure UnitData (F : ReflForm K V) (Γ : Subgroup (V ≃ₗ[K] V)) : Prop where
  herm : ∀ u v, F.σ (F.β u v) = F.β v u
  invol : ∀ c, F.σ (F.σ c) = c
  trace : ∀ a, F.σ a = a → ∃ c, c + F.σ c = a
  iso : ∀ (g : Γ) (u v : V), F.β (g • u) (g • v) = F.β u v
  eichler : ∀ (x y : V) (c : K), F.β x x = 0 → F.β x y = 0 → c + F.σ c = -F.β y y →
    ∃ g : Γ, ∀ v, g • v = v + F.β x v • (y + c • x) - F.β y v • x

variable {F : ReflForm K V} {Γ : Subgroup (V ≃ₗ[K] V)}

theorem UnitData.iso_inv (hU : UnitData F Γ) (g : Γ) (u v : V) :
    F.β (g⁻¹ • u) v = F.β u (g • v) := by
  rw [← hU.iso g (g⁻¹ • u) v, smul_inv_smul]

theorem UnitData.smul_mem_perp_iff (hU : UnitData F Γ) {U : Submodule K V} {g : Γ}
    (hg : g ∈ stabG Γ U) (y : V) : g • y ∈ F.perp U ↔ y ∈ F.perp U := by
  simp only [ReflForm.mem_perp]
  constructor
  · intro h n hn
    have := h (g • n) (smul_mem_of_mem_stabG hg hn)
    rwa [hU.iso] at this
  · intro h n hn
    rw [← hU.iso_inv]
    exact h _ (inv_smul_mem_of_mem_stabG hg hn)

theorem toDual_surjective [FiniteDimensional K V] (F : ReflForm K V) :
    Function.Surjective F.toDual := by
  have h1 : (⊤ : Submodule K V).map F.toDual = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [F.finrank_map_toDual, finrank_top, Subspace.dual_finrank_eq]
  intro f
  have : f ∈ (⊤ : Submodule K V).map F.toDual := by rw [h1]; trivial
  obtain ⟨x, -, hx⟩ := this
  exact ⟨x, hx⟩

section Complement

variable [CharP K 2] [FiniteDimensional K V]

theorem exists_isotropic_compl (hU : UnitData F Γ) (E : Subgroup Γ) [Finite E]
    (hE : Odd (Nat.card E)) {W : Submodule K V} (hW : F.IsTotallyIsotropic W)
    (hWE : ∀ e ∈ E, ∀ x ∈ W, e • x ∈ W) :
    ∃ X : Submodule K V, IsCompl X (F.perp W) ∧ F.IsTotallyIsotropic X ∧
      ∀ e ∈ E, ∀ x ∈ X, e • x ∈ X := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set Y := F.perp W with hY
  have hYE : ∀ e ∈ E, ∀ x ∈ Y, e • x ∈ Y := fun e he x hx =>
    (hU.smul_mem_perp_iff (le_stabG_of_invariant hWE he) x).2 hx
  obtain ⟨X, hXc, hXE⟩ := exists_invariant_complG E hE Y hYE
  have hc : IsCompl X Y := hXc.symm
  set π : V →ₗ[K] V := X.subtype ∘ₗ X.projectionOnto Y hc with hπ
  have hπX : ∀ x, π x ∈ X := fun x => (X.projectionOnto Y hc x).2
  have hπ_X : ∀ x ∈ X, π x = x := fun x hx => by
    have := Submodule.projectionOnto_apply_left hc ⟨x, hx⟩
    simp only [hπ, LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val this
  have hπ_Y : ∀ a ∈ Y, π a = 0 := fun a ha => by
    have := Submodule.projectionOnto_apply_right hc ⟨a, ha⟩
    simp only [hπ, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [this]; rfl
  have hπ_sub : ∀ x, x - π x ∈ Y := fun x => by
    rw [← Submodule.ker_projectionOnto hc, LinearMap.mem_ker, map_sub]
    have := Submodule.projectionOnto_apply_left hc (X.projectionOnto Y hc x)
    simp only [hπ, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [this, sub_self]
  have hπ_smul : ∀ e ∈ E, ∀ x, π (e • x) = e • π x := fun e he x => by
    have h1 : e • x = e • π x + e • (x - π x) := by rw [← smul_add]; congr 1; abel
    rw [h1, map_add, hπ_X _ (hXE e he _ (hπX x)), hπ_Y _ (hYE e he _ (hπ_sub x)), add_zero]
  obtain ⟨t, ht⟩ := hU.trace 1 (map_one F.σ)
  have hsurj := toDual_surjective F
  choose N0 hN0 using fun x => hsurj (t • (F.toDual x).comp π)
  have hN0' : ∀ x y, F.β (N0 x) y = t * F.β x (π y) := fun x y => by
    have := congrArg (fun f : Module.Dual K V => f y) (hN0 x)
    simpa using this
  let N : V →ₗ[K] V :=
    { toFun := N0
      map_add' := fun x x' => by
        apply F.toDual_injective
        rw [map_add, hN0, hN0, hN0, map_add]
        ext y
        simp [mul_add]
      map_smul' := fun c x => by
        apply F.toDual_injective
        rw [RingHom.id_apply, map_smulₛₗ, hN0, hN0]
        ext y
        simp
        ring }
  have hBN : ∀ x y, F.β (N x) y = t * F.β x (π y) := hN0'
  have hNW : ∀ x, N x ∈ W := fun x => by
    have : N x ∈ F.perp (F.perp W) := by
      intro a ha
      rw [← hU.herm (N x) a, hBN, hπ_Y a ha, F.β_zero_right, mul_zero, map_zero]
    rwa [F.perp_perp W] at this
  have hWY : W ≤ Y := hW
  have hN_smul : ∀ e ∈ E, ∀ x, N (e • x) = e • N x := fun e he x => by
    apply F.toDual_injective
    refine LinearMap.ext fun y => ?_
    rw [ReflForm.toDual_apply, ReflForm.toDual_apply, hBN]
    have h1 : F.β (e • N x) y = F.β (N x) (e⁻¹ • y) := by
      simpa using hU.iso_inv e⁻¹ (N x) y
    rw [h1, hBN, hπ_smul e⁻¹ (E.inv_mem he), ← hU.iso e (x) (e⁻¹ • π y), smul_inv_smul]
  refine ⟨X.map (LinearMap.id + N), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := (Submodule.mem_inf).1 hz
    obtain ⟨x, hx, rfl⟩ := hz1
    simp only [LinearMap.add_apply, LinearMap.id_apply] at hz2 ⊢
    have hxY : x ∈ Y := by
      have := Y.sub_mem hz2 (hWY (hNW x))
      simpa using this
    have : x ∈ X ⊓ Y := ⟨hx, hxY⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at this
    subst this
    simp
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v ∈ X ⊔ Y := by rw [hc.sup_eq_top]; trivial
    obtain ⟨x, hx, a, ha, rfl⟩ := Submodule.mem_sup.1 hv
    exact Submodule.mem_sup.2 ⟨x + N x, ⟨x, hx, rfl⟩, a - N x, Y.sub_mem ha (hWY (hNW x)),
      by abel⟩
  · rintro y ⟨x', hx', rfl⟩
    rw [F.mem_perp]
    rintro n ⟨x, hx, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.id_apply]
    have e1 : F.β (N x) (N x') = 0 := F.mem_perp.1 (hW (hNW x')) (N x) (hNW x)
    have e2 : F.β (N x) x' = t * F.β x x' := by rw [hBN, hπ_X x' hx']
    have e3 : F.β x (N x') = F.σ t * F.β x x' := by
      rw [← hU.herm (N x') x, hBN, hπ_X x hx, map_mul, hU.herm]
    rw [F.add_left, F.add_right, F.add_right, e1, e2, e3, add_zero]
    linear_combination (F.β x x') * ht + (F.β x x') * h2
  · intro e he y hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨e • x, hXE e he x hx, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.id_apply, smul_add, hN_smul e he x]

end Complement

end UnitClosure

end CFSG.LocalAnalysis.RankThreeUC
