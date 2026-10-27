module

public import CFSG.HardMathSupport.Timmesfeld.Proving.FixedPointsCard
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

variable {G : Type*} [Group G]

def conjSubgroupHom (x : G) (Z : Subgroup G) (hx : ∀ v ∈ Z, x * v * x⁻¹ ∈ Z) : Z →* Z :=
  MonoidHom.mk' (fun v => ⟨x * v * x⁻¹, hx v v.2⟩) (fun a b => Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group))

theorem conjSubgroupHom_val (x : G) (Z : Subgroup G) (hx : ∀ v ∈ Z, x * v * x⁻¹ ∈ Z)
    (v : Z) : ((conjSubgroupHom x Z hx v : Z) : G) = x * v * x⁻¹ := by
  unfold conjSubgroupHom
  rw [MonoidHom.mk'_apply]

theorem card_inf_centralizer_le {p : ℕ} (hp : p.Prime) (Z : Subgroup G)
    (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hexp : ∀ a ∈ Z, a ^ p = 1) [Finite Z]
    (x : G) (hx : ∀ v ∈ Z, x * v * x⁻¹ ∈ Z) {z : G} (hz : z ∈ Z)
    (hgen : ∀ v ∈ Z, v ∈ Subgroup.closure
      ({z, x * z * x⁻¹, x * (x * z * x⁻¹) * x⁻¹} : Set G)) :
    Nat.card ↥(Z ⊓ Subgroup.centralizer ({x} : Set G)) ≤ p := by
  let _ : CommGroup Z :=
    { (inferInstance : Group Z) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  set σ := conjSubgroupHom x Z hx with hσ
  have hexpZ : ∀ v : Z, v ^ p = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_pow, hexp v v.2]; rfl)
  set z' : Z := ⟨z, hz⟩ with hz'
  have hgenZ : ∀ v : Z, v ∈ Subgroup.closure ({z', σ z', σ (σ z')} : Set Z) := by
    intro v
    have himg : Z.subtype '' ({z', σ z', σ (σ z')} : Set Z) =
        ({z, x * z * x⁻¹, x * (x * z * x⁻¹) * x⁻¹} : Set G) := by
      simp only [Set.image_insert_eq, Set.image_singleton, Subgroup.coe_subtype]
      rw [hσ, conjSubgroupHom_val, hz', conjSubgroupHom_val]
      rfl
    have hmap : (Subgroup.closure ({z', σ z', σ (σ z')} : Set Z)).map Z.subtype =
        Subgroup.closure ({z, x * z * x⁻¹, x * (x * z * x⁻¹) * x⁻¹} : Set G) := by
      rw [MonoidHom.map_closure, himg]
    have hv : (v : G) ∈ (Subgroup.closure ({z', σ z', σ (σ z')} : Set Z)).map Z.subtype := by
      rw [hmap]
      exact hgen v v.2
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hv
    have : w = v := Subtype.ext hwv
    exact this ▸ hw
  have key := card_fixed_le (V := Z) hp hexpZ σ z' hgenZ
  refine le_trans (le_of_eq ?_) key
  refine Eq.symm (Nat.card_congr ?_)
  exact
    { toFun := fun v => ⟨(v.1 : G), Subgroup.mem_inf.mpr ⟨v.1.2, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := congrArg (fun w : Z => (w : G)) v.2
        simp only [hσ, conjSubgroupHom_val] at h
        rw [mul_inv_eq_iff_eq_mul] at h
        exact h.symm⟩⟩
      invFun := fun g => ⟨⟨(g : G), (Subgroup.mem_inf.mp g.2).1⟩, Subtype.ext (by
        simp only [hσ, conjSubgroupHom_val]
        have hc := (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp g.2).2)
        rw [mul_inv_eq_iff_eq_mul]
        exact hc.symm)⟩
      left_inv := fun v => rfl
      right_inv := fun g => rfl }

end CFSG.HardMathSupport.Timmesfeld.Proving

end
