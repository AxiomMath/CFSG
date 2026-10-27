module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerLinearSemiregular
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def linearCentralizer (P : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Subalgebra (ZMod 2) (Module.End (ZMod 2) V) :=
  Subalgebra.centralizer (ZMod 2)
    ((fun x : V ≃ₗ[ZMod 2] V => (x : Module.End (ZMod 2) V)) '' (P : Set (V ≃ₗ[ZMod 2] V)))

theorem mem_linearCentralizer {P : Subgroup (V ≃ₗ[ZMod 2] V)} {e : Module.End (ZMod 2) V} :
    e ∈ linearCentralizer P ↔ ∀ x ∈ P, (x : Module.End (ZMod 2) V) * e = e * x := by
  simp [linearCentralizer, Subalgebra.mem_centralizer_iff]

theorem toLinearMap_mem_linearCentralizer {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ P) :
    (x : Module.End (ZMod 2) V) ∈ linearCentralizer P := by
  rw [mem_linearCentralizer]
  intro y hy
  rw [← LinearEquiv.coe_toLinearMap_mul, hPcomm y hy x hx, LinearEquiv.coe_toLinearMap_mul]

theorem eq_zero_or_exists_of_mem_linearCentralizer {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {z : V}
    (hPtrans : ∀ v : V, v ≠ 0 → ∃ x ∈ P, x z = v) {e : Module.End (ZMod 2) V}
    (he : e ∈ linearCentralizer P) : e = 0 ∨ ∃ x ∈ P, e = (x : Module.End (ZMod 2) V) := by
  rw [mem_linearCentralizer] at he
  have happ : ∀ x ∈ P, e (x z) = x (e z) := fun x hx => by
    have := congrArg (fun f : Module.End (ZMod 2) V => f z) (he x hx)
    exact this.symm
  by_cases hez : e z = 0
  · left
    ext v
    by_cases hv : v = 0
    · simp [hv]
    obtain ⟨x, hx, rfl⟩ := hPtrans v hv
    simp [happ x hx, hez]
  · obtain ⟨x, hx, hxz⟩ := hPtrans (e z) hez
    right
    refine ⟨x, hx, ?_⟩
    ext v
    by_cases hv : v = 0
    · simp [hv]
    obtain ⟨y, hy, rfl⟩ := hPtrans v hv
    rw [happ y hy, ← hxz, LinearEquiv.coe_coe, ← LinearEquiv.mul_apply, hPcomm y hy x hx,
      LinearEquiv.mul_apply]

theorem card_stabilizer_le_finrank [Finite V] {Y P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hPnorm : ∀ g ∈ Y, ∀ a ∈ P, g * a * g⁻¹ ∈ P)
    {z : V} (hz : z ≠ 0) (hPtrans : ∀ v : V, v ≠ 0 → ∃ x ∈ P, x z = v) :
    Nat.card (MulAction.stabilizer Y z) ≤ Module.finrank (ZMod 2) V := by
  classical
  have := finite_linearEquiv_zmod_two (V := V)
  set E := linearCentralizer P with hEdef
  have hE : ∀ e : E, (e : Module.End (ZMod 2) V) = 0 ∨
      ∃ x ∈ P, (e : Module.End (ZMod 2) V) = (x : Module.End (ZMod 2) V) := fun e =>
    eq_zero_or_exists_of_mem_linearCentralizer hPcomm hPtrans e.2
  have hEcomm : ∀ a b : E, a * b = b * a := by
    intro a b
    apply Subtype.ext
    simp only [Subalgebra.coe_mul]
    rcases hE a with ha | ⟨x, hx, ha⟩
    · simp [ha]
    rcases hE b with hb | ⟨y, hy, hb⟩
    · simp [hb]
    rw [ha, hb, ← LinearEquiv.coe_toLinearMap_mul, hPcomm x hx y hy,
      LinearEquiv.coe_toLinearMap_mul]
  let : CommRing E := { (inferInstance : Ring E) with mul_comm := hEcomm }
  have : Nontrivial E := by
    refine ⟨⟨0, 1, fun h => hz ?_⟩⟩
    have h' := congrArg (fun e : E => (e : Module.End (ZMod 2) V) z) h
    simpa using h'.symm
  have : NoZeroDivisors E := by
    refine ⟨fun {a b} hab => ?_⟩
    rcases hE a with ha | ⟨x, hx, ha⟩
    · exact Or.inl (Subtype.ext ha)
    right
    apply Subtype.ext
    ext v
    have h := congrArg (fun e : E => (e : Module.End (ZMod 2) V) v) hab
    simp only [Subalgebra.coe_mul, ha, Module.End.mul_apply, LinearEquiv.coe_coe,
      ZeroMemClass.coe_zero, LinearMap.zero_apply] at h
    simpa using x.injective (h.trans (map_zero x).symm)
  have : IsDomain E := NoZeroDivisors.to_isDomain E
  let φ : P →* E :=
    { toFun := fun x => ⟨(x : Module.End (ZMod 2) V), toLinearMap_mem_linearCentralizer hPcomm x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h := congrArg (fun e : E => (e : Module.End (ZMod 2) V)) hxy
    exact Subtype.ext (LinearEquiv.toLinearMap_injective h)
  have : IsCyclic P := isCyclic_of_injective_ringHom φ hφ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
  set χ := ((g : V ≃ₗ[ZMod 2] V) : Module.End (ZMod 2) V).charpoly with hχ
  set χE := χ.map (algebraMap (ZMod 2) E) with hχE
  have hχmonic : χ.Monic := LinearMap.charpoly_monic _
  have hχE0 : χE ≠ 0 := (hχmonic.map _).ne_zero
  let r : MulAction.stabilizer Y z → E := fun y =>
    ⟨(((y : Y) : V ≃ₗ[ZMod 2] V) * g * ((y : Y) : V ≃ₗ[ZMod 2] V)⁻¹ :
        V ≃ₗ[ZMod 2] V), toLinearMap_mem_linearCentralizer hPcomm
      (hPnorm _ (y : Y).2 _ g.2)⟩
  have hroot : ∀ y, r y ∈ χE.roots.toFinset := by
    intro y
    rw [Multiset.mem_toFinset, mem_roots hχE0, IsRoot.def, hχE, eval_map_algebraMap]
    apply Subtype.ext
    rw [aeval_subalgebra_coe, ZeroMemClass.coe_zero]
    have hconj : ((r y : E) : Module.End (ZMod 2) V) =
        ((y : Y) : V ≃ₗ[ZMod 2] V).conjAlgEquiv (ZMod 2)
          ((g : V ≃ₗ[ZMod 2] V) : Module.End (ZMod 2) V) := by
      ext v
      rfl
    rw [hconj, aeval_algHom_apply, hχ, LinearMap.aeval_self_charpoly, map_zero]
  have hrinj : Function.Injective r := by
    intro y₁ y₂ hy
    have h := congrArg (fun e : E => (e : Module.End (ZMod 2) V)) hy
    have h' : ((y₁ : Y) : V ≃ₗ[ZMod 2] V) * g * ((y₁ : Y) : V ≃ₗ[ZMod 2] V)⁻¹ =
        ((y₂ : Y) : V ≃ₗ[ZMod 2] V) * g * ((y₂ : Y) : V ≃ₗ[ZMod 2] V)⁻¹ :=
      LinearEquiv.toLinearMap_injective h
    set c : V ≃ₗ[ZMod 2] V := ((y₂ : Y) : V ≃ₗ[ZMod 2] V)⁻¹ * ((y₁ : Y) : V ≃ₗ[ZMod 2] V)
      with hc
    have hcg : c * g = g * c := by
      rw [hc]
      calc ((y₂ : Y) : V ≃ₗ[ZMod 2] V)⁻¹ * ((y₁ : Y) : V ≃ₗ[ZMod 2] V) * g
          = ((y₂ : Y) : V ≃ₗ[ZMod 2] V)⁻¹ * (((y₁ : Y) : V ≃ₗ[ZMod 2] V) * g *
              ((y₁ : Y) : V ≃ₗ[ZMod 2] V)⁻¹) * ((y₁ : Y) : V ≃ₗ[ZMod 2] V) := by group
        _ = ((y₂ : Y) : V ≃ₗ[ZMod 2] V)⁻¹ * (((y₂ : Y) : V ≃ₗ[ZMod 2] V) * g *
              ((y₂ : Y) : V ≃ₗ[ZMod 2] V)⁻¹) * ((y₁ : Y) : V ≃ₗ[ZMod 2] V) := by rw [h']
        _ = g * (((y₂ : Y) : V ≃ₗ[ZMod 2] V)⁻¹ * ((y₁ : Y) : V ≃ₗ[ZMod 2] V)) := by group
    have hcz : c z = z := by
      have h₁ : ((y₁ : Y) : V ≃ₗ[ZMod 2] V) z = z := y₁.2
      have h₂ : ((y₂ : Y) : V ≃ₗ[ZMod 2] V) z = z := y₂.2
      rw [hc, LinearEquiv.mul_apply, h₁, LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq, h₂]
    have hc1 : c = 1 := by
      ext v
      by_cases hv : v = 0
      · simp [hv]
      obtain ⟨x, hx, rfl⟩ := hPtrans v hv
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      have hxk : x = (g : V ≃ₗ[ZMod 2] V) ^ k := by
        rw [← Subgroup.coe_zpow, hk]
      have hcx : c * x = x * c := by
        rw [hxk]
        exact (Commute.zpow_right hcg k).eq
      change c (x z) = x z
      rw [← LinearEquiv.mul_apply, hcx, LinearEquiv.mul_apply, hcz]
    have : ((y₁ : Y) : V ≃ₗ[ZMod 2] V) = ((y₂ : Y) : V ≃ₗ[ZMod 2] V) := by
      rw [hc, inv_mul_eq_one] at hc1
      exact hc1.symm
    exact Subtype.ext (Subtype.ext this)
  calc Nat.card (MulAction.stabilizer Y z)
      ≤ Nat.card χE.roots.toFinset :=
        Nat.card_le_card_of_injective (fun y => ⟨r y, hroot y⟩)
          (fun y₁ y₂ h => hrinj (congrArg Subtype.val h))
    _ = χE.roots.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ χE.roots.card := Multiset.toFinset_card_le _
    _ ≤ χE.natDegree := card_roots' _
    _ = Module.finrank (ZMod 2) V := by
        rw [hχE, hχmonic.natDegree_map, hχ, LinearMap.charpoly_natDegree]

end CFSG.ProperTwoGeneratedCore.Assembly
