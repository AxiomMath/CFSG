module

public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A2Trace
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec8t84a2_trace_split_grp {Q V X : Type*} [Group Q] [Group V] [Finite V]
    (hQc : ∀ x y : Q, x * y = y * x) (hQ2 : ∀ x : Q, x * x = 1)
    (hVc : ∀ u v : V, u * v = v * u) (hV2 : ∀ v : V, v * v = 1) (hV16 : Nat.card V = 16)
    (σ : X → Q ≃* Q) (ρ : X → V ≃* V) (t : Q) (ht : t ≠ 1) (π : Q →* V)
    (hπ : Function.Surjective π) (hker : ∀ q, π q = 1 → q = 1 ∨ q = t)
    (β : Q → Q → V) (hβl : ∀ x x' y, β (x * x') y = β x y * β x' y)
    (hβr : ∀ x y y', β x (y * y') = β x y * β x y') (halt : ∀ x, β x x = 1)
    (hβt : ∀ x, β x t = π x) (hσt : ∀ x, σ x t = t) (hπσ : ∀ x q, π (σ x q) = ρ x (π q))
    (hβσ : ∀ x q q', β (σ x q) (σ x q') = ρ x (β q q')) :
    ∃ L : Subgroup Q, t ∉ L ∧ (∀ q : Q, q ∈ L ∨ q * t ∈ L) ∧ ∀ x, ∀ q ∈ L, σ x q ∈ L := by
  letI : CommGroup Q := { ‹Group Q› with mul_comm := hQc }
  letI : CommGroup V := { ‹Group V› with mul_comm := hVc }
  have hQ2' : ∀ x : Additive Q, 2 • x = 0 := by
    intro x
    rw [← ofMul_toMul x, ← ofMul_pow, pow_two, hQ2 x.toMul, ofMul_one]
  have hV2' : ∀ v : Additive V, 2 • v = 0 := by
    intro v
    rw [← ofMul_toMul v, ← ofMul_pow, pow_two, hV2 v.toMul, ofMul_one]
  letI : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule (n := 2) hQ2'
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) hV2'
  haveI : Finite (Additive V) := ‹Finite V›
  have hcard : Nat.card (Additive V) = 16 := by
    rw [← Nat.card_congr (Additive.ofMul : V ≃ Additive V), hV16]
  have hfr : Module.finrank (ZMod 2) (Additive V) = 4 := by
    apply Nat.pow_right_injective (show 2 ≤ 2 by norm_num)
    change 2 ^ Module.finrank (ZMod 2) (Additive V) = 2 ^ 4
    rw [FiniteField.pow_finrank_eq_natCard, hcard]
  have hVeven : Even (Module.finrank (ZMod 2) (Additive V)) := by
    rw [hfr]; exact ⟨2, rfl⟩
  let σl : X → Additive Q ≃ₗ[ZMod 2] Additive Q := fun x =>
    { toLinearMap := AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive (σ x)).toAddMonoidHom
      invFun := (MulEquiv.toAdditive (σ x)).symm
      left_inv := (MulEquiv.toAdditive (σ x)).left_inv
      right_inv := (MulEquiv.toAdditive (σ x)).right_inv }
  let ρl : X → Additive V ≃ₗ[ZMod 2] Additive V := fun x =>
    { toLinearMap := AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive (ρ x)).toAddMonoidHom
      invFun := (MulEquiv.toAdditive (ρ x)).symm
      left_inv := (MulEquiv.toAdditive (ρ x)).left_inv
      right_inv := (MulEquiv.toAdditive (ρ x)).right_inv }
  let πl : Additive Q →ₗ[ZMod 2] Additive V :=
    AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive π)
  have hσl : ∀ x q, σl x (Additive.ofMul q) = Additive.ofMul (σ x q) := fun _ _ => rfl
  have hρl : ∀ x v, ρl x (Additive.ofMul v) = Additive.ofMul (ρ x v) := fun _ _ => rfl
  have hπl : ∀ q, πl (Additive.ofMul q) = Additive.ofMul (π q) := fun _ => rfl
  have hβ_one_right : ∀ m : Additive Q, β m.toMul 1 = 1 := by
    intro m
    simpa [hV2] using hβr m.toMul 1 1
  have hβ_one_left : ∀ n : Additive Q, β 1 n.toMul = 1 := by
    intro n
    simpa [hV2] using hβl 1 1 n.toMul
  let βf : Additive Q →+ (Additive Q →ₗ[ZMod 2] Additive V) :=
    { toFun := fun m =>
        AddMonoidHom.toZModLinearMap 2
          { toFun := fun n => Additive.ofMul (β m.toMul n.toMul)
            map_zero' := by simp [hβ_one_right m]
            map_add' := by
              intro a b
              simpa using congrArg Additive.ofMul (hβr m.toMul a.toMul b.toMul) }
      map_zero' := by
        ext n
        simp [hβ_one_left n]
      map_add' := by
        intro m₁ m₂
        ext n
        change Additive.ofMul (β (m₁ + m₂).toMul n.toMul) =
          Additive.ofMul (β m₁.toMul n.toMul) + Additive.ofMul (β m₂.toMul n.toMul)
        rw [toMul_add]
        exact congrArg Additive.ofMul (hβl m₁.toMul m₂.toMul n.toMul) }
  let βl : Additive Q →ₗ[ZMod 2] Additive Q →ₗ[ZMod 2] Additive V :=
    AddMonoidHom.toZModLinearMap 2 βf
  have hβl_ofMul : ∀ q q', βl (Additive.ofMul q) (Additive.ofMul q') =
      Additive.ofMul (β q q') := fun _ _ => rfl
  have ht' : (Additive.ofMul t : Additive Q) ≠ 0 := by
    intro h
    exact ht (by simpa using h)
  have hσt' : ∀ x, σl x (Additive.ofMul t) = (Additive.ofMul t : Additive Q) := by
    intro x
    rw [hσl x t, hσt x]
  have hπ' : Function.Surjective πl := by
    intro w
    obtain ⟨q, hq⟩ := hπ w.toMul
    exact ⟨Additive.ofMul q, by rw [hπl q, hq]; exact ofMul_toMul w⟩
  have hker' : ∀ m : Additive Q, πl m = 0 → m = 0 ∨ m = Additive.ofMul t := by
    intro m hm
    have hm' : π m.toMul = 1 := by
      rw [← ofMul_toMul m, hπl m.toMul] at hm
      simpa using hm
    rcases hker m.toMul hm' with h | h
    · left; apply Additive.toMul.injective; simpa using h
    · right; apply Additive.toMul.injective; simpa using h
  have halt' : ∀ m : Additive Q, βl m m = 0 := by
    intro m
    rw [← ofMul_toMul m, hβl_ofMul m.toMul m.toMul, halt m.toMul,
      ofMul_one]
  have hβt' : ∀ m : Additive Q, βl m (Additive.ofMul t) = πl m := by
    intro m
    rw [← ofMul_toMul m, hβl_ofMul m.toMul t, hπl m.toMul, hβt m.toMul]
  have hπσ' : ∀ x m, πl (σl x m) = ρl x (πl m) := by
    intro x m
    rw [← ofMul_toMul m, hσl x m.toMul, hπl (σ x m.toMul), hπl m.toMul,
      hρl x (π m.toMul)]
    exact congrArg Additive.ofMul (hπσ x m.toMul)
  have hβσ' : ∀ x m m', βl (σl x m) (σl x m') = ρl x (βl m m') := by
    intro x m m'
    rw [← ofMul_toMul m, ← ofMul_toMul m']
    rw [hσl x m.toMul, hσl x m'.toMul, hβl_ofMul (σ x m.toMul) (σ x m'.toMul),
      hβl_ofMul m.toMul m'.toMul, hρl x (β m.toMul m'.toMul), hβσ x m.toMul m'.toMul]
  obtain ⟨L, hLcompl, hLinv⟩ :=
    sec8t84a2_trace_split (M := Additive Q) (V := Additive V) hVeven σl ρl
      (Additive.ofMul t) ht' πl hπ' hker' βl halt' hβt' hσt' hπσ' hβσ'
  refine ⟨{ carrier := {q : Q | Additive.ofMul q ∈ L}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, ?_, ?_, ?_⟩
  · intro a b ha hb
    show Additive.ofMul (a * b) ∈ L
    rw [ofMul_mul]
    exact L.add_mem ha hb
  · show Additive.ofMul (1 : Q) ∈ L
    rw [ofMul_one]
    exact L.zero_mem
  · intro a ha
    show Additive.ofMul a⁻¹ ∈ L
    rw [ofMul_inv]
    exact L.neg_mem ha
  ·
    intro htm
    have htm' : (Additive.ofMul t : Additive Q) ∈ L := htm
    have hspan : (Additive.ofMul t : Additive Q) ∈
        Submodule.span (ZMod 2) {Additive.ofMul t} :=
      Submodule.mem_span_singleton_self _
    have hzero : (Additive.ofMul t : Additive Q) = 0 :=
      Submodule.disjoint_def.mp hLcompl.disjoint _ hspan htm'
    exact ht' hzero
  ·
    intro q
    obtain ⟨a, l, ha, hl, hal⟩ :=
      (Submodule.codisjoint_iff_exists_add_eq.mp hLcompl.codisjoint) (Additive.ofMul q)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
    rcases (show c = 0 ∨ c = 1 from
        (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c) with hc0 | hc1
    · left
      change Additive.ofMul q ∈ L
      have ha0 : a = 0 := by rw [← hc, hc0, zero_smul]
      rw [← hal, ha0, zero_add]
      exact hl
    · right
      change Additive.ofMul (q * t) ∈ L
      have ha1 : a = Additive.ofMul t := by rw [← hc, hc1, one_smul]
      have hgoal : Additive.ofMul (q * t) = l := by
        rw [ofMul_mul, ← hal, ha1, add_comm (Additive.ofMul t) l, add_assoc,
          ZModModule.add_self, add_zero]
      rw [hgoal]
      exact hl
  ·
    intro x q hq
    show Additive.ofMul (σ x q) ∈ L
    simpa [hσl x q] using hLinv x (Additive.ofMul q) hq

end CFSG.OddStandard.SmallF3.Omega
