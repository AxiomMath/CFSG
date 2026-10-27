module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.Transfer
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

section

variable {X : Type*} [Group X]

theorem exists_fixed_mem_comm_eq (V U K S : Subgroup X) [Finite K]
    (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v * v = 1) (hUV : U ≤ V)
    (hKU : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U) (hSK : S ≤ K)
    (hSodd : ¬ 2 ∣ (S.subgroupOf K).index) (z : X) (hz : z ∈ V)
    (hzU : ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ U) (hzS : ∀ s ∈ S, s * z * s⁻¹ = z) :
    ∃ m ∈ U, (∀ k ∈ K, k * z * k⁻¹ * z⁻¹ = k * m * k⁻¹ * m⁻¹) ∧
      ∀ s ∈ S, s * m * s⁻¹ = m := by
  classical
  let _ : CommGroup U := { (inferInstance : Group U) with
    mul_comm := fun a b => Subtype.ext (hVc _ (hUV a.2) _ (hUV b.2)) }
  have hsq : ∀ a : Additive U, (2 : ℕ) • a = 0 := by
    intro a
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero, pow_two]
    exact Subtype.ext (hV2 _ (hUV a.toMul.2))
  let _ : Module (ZMod 2) (Additive U) := AddCommGroup.zmodModule (n := 2) hsq
  let act : K → Additive U → Additive U := fun k a =>
    Additive.ofMul ⟨(k : X) * (a.toMul : X) * (k : X)⁻¹, hKU _ k.2 _ a.toMul.2⟩
  have act_val : ∀ k a, ((act k a).toMul : X) = (k : X) * (a.toMul : X) * (k : X)⁻¹ :=
    fun _ _ => rfl
  let _inst : DistribMulAction K (Additive U) :=
    { smul := act
      one_smul := fun a => by
        show act 1 a = a
        apply Additive.toMul.injective; apply Subtype.ext
        rw [act_val]; simp
      mul_smul := fun k l a => by
        show act (k * l) a = act k (act l a)
        apply Additive.toMul.injective; apply Subtype.ext
        rw [act_val, act_val, act_val]; simp [mul_assoc]
      smul_zero := fun k => by
        show act k 0 = 0
        apply Additive.toMul.injective; apply Subtype.ext
        rw [act_val]; simp
      smul_add := fun k a b => by
        show act k (a + b) = act k a + act k b
        apply Additive.toMul.injective; apply Subtype.ext
        simp only [act_val, toMul_add, Subgroup.coe_mul]
        simp [mul_assoc] }
  have hsmul : ∀ (k : K) (a : Additive U), ((k • a).toMul : X) = (k : X) * (a.toMul : X) * (k : X)⁻¹ :=
    fun _ _ => rfl
  let c : K → Additive U := fun k => Additive.ofMul ⟨(k : X) * z * (k : X)⁻¹ * z⁻¹, hzU k k.2⟩
  have hc : ∀ g h : K, c (g * h) = c g + g • c h := by
    intro g h
    apply Additive.toMul.injective; apply Subtype.ext
    change ((g * h : K) : X) * z * ((g * h : K) : X)⁻¹ * z⁻¹ =
      ((g : X) * z * (g : X)⁻¹ * z⁻¹) *
        ((g : X) * ((h : X) * z * (h : X)⁻¹ * z⁻¹) * (g : X)⁻¹)
    have hcomm := hVc _ (hUV (hzU g g.2)) _ (hUV (hKU g g.2 _ (hzU h h.2)))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    rw [hcomm]
    group
  have hS0 : ∀ s ∈ S.subgroupOf K, c s = 0 := by
    intro s hs
    have hs' : (s : X) ∈ S := hs
    apply Additive.toMul.injective; apply Subtype.ext
    show (s : X) * z * (s : X)⁻¹ * z⁻¹ = 1
    rw [hzS _ hs']; simp
  obtain ⟨m, hm⟩ := exists_coboundary_of_odd_index (S.subgroupOf K) hSodd c hc hS0
  have hfix := fixed_of_coboundary_of_vanishes (S.subgroupOf K) c m hm hS0
  refine ⟨(m.toMul : X), m.toMul.2, fun k hk => ?_, fun s hs => ?_⟩
  · have h1 := congrArg (fun a : Additive U => (a.toMul : X)) (hm ⟨k, hk⟩)
    simpa [c, hsmul, sub_eq_add_neg, toMul_add, toMul_neg] using h1
  · have hs' : (⟨s, hSK hs⟩ : K) ∈ S.subgroupOf K := hs
    have h1 := congrArg (fun a : Additive U => (a.toMul : X)) (hfix _ hs')
    simpa [hsmul] using h1

end

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
