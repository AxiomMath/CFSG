module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT8W11
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

namespace E3S3O

@[expose] def q8Map (p q : QuaternionGroup 2) : QuaternionGroup 2 → QuaternionGroup 2
  | .a k => p ^ k.val
  | .xa k => q * p ^ k.val

theorem q8_three_aut : ∀ p q : QuaternionGroup 2,
    (∀ g h, q8Map p q (g * h) = q8Map p q g * q8Map p q h) →
    (∀ g, q8Map p q (q8Map p q (q8Map p q g)) = g) → (∃ g, q8Map p q g ≠ g) →
    ∃ x y : QuaternionGroup 2, ∀ m : QuaternionGroup 2,
      m ∈ [1, x⁻¹ * q8Map p q x, (x⁻¹ * q8Map p q x) ^ 2, (x⁻¹ * q8Map p q x) ^ 3,
        y⁻¹ * q8Map p q y, (x⁻¹ * q8Map p q x) * (y⁻¹ * q8Map p q y),
        (x⁻¹ * q8Map p q x) ^ 2 * (y⁻¹ * q8Map p q y),
        (x⁻¹ * q8Map p q x) ^ 3 * (y⁻¹ * q8Map p q y)] := by
  decide

variable {G : Type} [Group G]

theorem le_commutator_of_q8 {H M : Subgroup G} (e : ↥M ≃* QuaternionGroup 2) (hMH : M ≤ H)
    {y : G} (hyH : y ∈ H) (hyM : conjSub y M = M) (hy3 : ∀ m ∈ M, y ^ 3 * m = m * y ^ 3)
    (hyc : ∃ m ∈ M, y * m ≠ m * y) : M ≤ ⁅H, H⁆ := by
  have hα : ∀ m ∈ M, y * m * y⁻¹ ∈ M := fun m hm => by
    rw [← hyM]
    exact conj_mem_conjSub hm
  let α : ↥M →* ↥M :=
    { toFun := fun m => ⟨y * m * y⁻¹, hα m m.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hαv : ∀ m : ↥M, ((α m : ↥M) : G) = y * m * y⁻¹ := fun _ => rfl
  set p := e (α (e.symm (QuaternionGroup.a 1))) with hp
  set q := e (α (e.symm (QuaternionGroup.xa 0))) with hq
  have hβ : ∀ g, e (α (e.symm g)) = q8Map p q g := by
    intro g
    cases g with
    | a k =>
      have h1 : (QuaternionGroup.a k : QuaternionGroup 2) = QuaternionGroup.a 1 ^ k.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
      rw [q8Map, h1, map_pow, map_pow, map_pow]
    | xa k =>
      have h1 : (QuaternionGroup.xa k : QuaternionGroup 2) =
          QuaternionGroup.xa 0 * QuaternionGroup.a 1 ^ k.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val, QuaternionGroup.xa_mul_a, zero_add]
      rw [q8Map, h1, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow]
  have hhom : ∀ g h, q8Map p q (g * h) = q8Map p q g * q8Map p q h := fun g h => by
    rw [← hβ, ← hβ, ← hβ, map_mul, map_mul, map_mul]
  have h3 : ∀ g, q8Map p q (q8Map p q (q8Map p q g)) = g := fun g => by
    rw [← hβ, ← hβ, ← hβ, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    rw [← e.apply_symm_apply g]
    congr 1
    apply Subtype.ext
    set m := e.symm g
    rw [MulEquiv.symm_apply_apply, hαv, hαv, hαv]
    calc y * (y * (y * (m : G) * y⁻¹) * y⁻¹) * y⁻¹ = y ^ 3 * m * (y ^ 3)⁻¹ := by
          simp only [pow_three]
          group
      _ = m := by rw [hy3 m m.2, mul_inv_cancel_right]
  have hne : ∃ g, q8Map p q g ≠ g := by
    obtain ⟨m, hm, hym⟩ := hyc
    refine ⟨e ⟨m, hm⟩, fun h1 => hym ?_⟩
    rw [← hβ, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg (fun z => ((e.symm z : ↥M) : G)) h1
    simp only [MulEquiv.symm_apply_apply, hαv] at h2
    calc y * m = y * m * y⁻¹ * y := by group
      _ = m * y := by rw [h2]
  obtain ⟨x, z, hxz⟩ := q8_three_aut p q hhom h3 hne
  have hcomm : ∀ g, ((e.symm (g⁻¹ * q8Map p q g) : ↥M) : G) ∈ ⁅H, H⁆ := by
    intro g
    rw [← hβ, map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      hαv]
    set n : G := ((e.symm g : ↥M) : G)
    have hnH : n⁻¹ ∈ H := H.inv_mem (hMH (e.symm g).2)
    have e1 : n⁻¹ * (y * n * y⁻¹) = ⁅n⁻¹, y⁆ := by
      rw [commutatorElement_def, inv_inv]
      group
    rw [e1]
    exact Subgroup.commutator_mem_commutator hnH hyH
  intro m hm
  have hmem := hxz (e ⟨m, hm⟩)
  have hm' : m = ((e.symm (e ⟨m, hm⟩) : ↥M) : G) := by rw [MulEquiv.symm_apply_apply]
  rw [hm']
  set u := x⁻¹ * q8Map p q x
  set v := z⁻¹ * q8Map p q z
  have hu := hcomm x
  have hv := hcomm z
  have hpow : ∀ n : ℕ, ((e.symm (u ^ n) : ↥M) : G) ∈ ⁅H, H⁆ := fun n => by
    rw [map_pow, Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hu n
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h <;> rw [h]
  · rw [map_one, OneMemClass.coe_one]
    exact Subgroup.one_mem _
  · exact hu
  · exact hpow 2
  · exact hpow 3
  · exact hv
  · rw [map_mul, Subgroup.coe_mul]
    exact Subgroup.mul_mem _ hu hv
  · rw [map_mul, Subgroup.coe_mul]
    exact Subgroup.mul_mem _ (hpow 2) hv
  · rw [map_mul, Subgroup.coe_mul]
    exact Subgroup.mul_mem _ (hpow 3) hv

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
