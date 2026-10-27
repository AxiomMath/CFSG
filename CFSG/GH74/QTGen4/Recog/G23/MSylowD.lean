module

public import CFSG.GH74.QTGen4.Recog.G23.MSylow
public import Mathlib.GroupTheory.Sylow
public meta import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open scoped MatrixGroups Pointwise

instance instDecidableEqSL3Two : DecidableEq SL(3, ZMod 2) := fun a b =>
  decidable_of_iff ((a : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (b : Matrix (Fin 3) (Fin 3) (ZMod 2)))
    ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩

abbrev UpperPred (g : SL(3, ZMod 2)) : Prop :=
  (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0

theorem upper_one : UpperPred 1 := by decide +kernel

theorem upper_mul_closed : ∀ a b : SL(3, ZMod 2), UpperPred a → UpperPred b → UpperPred (a * b) := by
  decide +kernel

theorem upper_inv_closed : ∀ a : SL(3, ZMod 2), UpperPred a → UpperPred a⁻¹ := by decide +kernel

def upperSub : Subgroup SL(3, ZMod 2) where
  carrier := {g | UpperPred g}
  mul_mem' ha hb := upper_mul_closed _ _ ha hb
  one_mem' := upper_one
  inv_mem' ha := upper_inv_closed _ ha

theorem card_upperSub : Nat.card upperSub = 8 := by
  have e : Nat.card upperSub = Nat.card {g : SL(3, ZMod 2) // UpperPred g} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [e, Nat.card_eq_fintype_card]
  decide +kernel

theorem card_upperSub_involutions :
    Nat.card {u : SL(3, ZMod 2) // u ∈ upperSub ∧ u * u = 1 ∧ u ≠ 1} = 5 := by
  have e : Nat.card {u : SL(3, ZMod 2) // u ∈ upperSub ∧ u * u = 1 ∧ u ≠ 1} =
      Nat.card {u : SL(3, ZMod 2) // UpperPred u ∧ u * u = 1 ∧ u ≠ 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [e, Nat.card_eq_fintype_card]
  decide +kernel

theorem SL3_two_involutions_conj : ∀ a b : SL(3, ZMod 2), a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 →
    ∃ g : SL(3, ZMod 2), g * a * g⁻¹ = b := by
  let tM : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]
  let conjFor : Matrix (Fin 3) (Fin 3) (ZMod 2) → Matrix (Fin 3) (Fin 3) (ZMod 2) := fun A =>
    match (A 0 0).val, (A 0 1).val, (A 0 2).val, (A 1 0).val, (A 1 1).val,
        (A 1 2).val, (A 2 0).val, (A 2 1).val, (A 2 2).val with
    | 0, 0, 1, 0, 1, 0, 1, 0, 0 => !![1, 0, 0; 0, 0, 1; 1, 1, 0]
    | 0, 0, 1, 1, 1, 1, 1, 0, 0 => !![1, 0, 0; 1, 0, 1; 1, 1, 0]
    | 0, 1, 0, 1, 0, 0, 0, 0, 1 => !![1, 0, 0; 1, 1, 0; 0, 0, 1]
    | 0, 1, 0, 1, 0, 0, 1, 1, 1 => !![1, 0, 0; 1, 1, 0; 1, 0, 1]
    | 0, 1, 1, 0, 1, 0, 1, 1, 0 => !![1, 0, 0; 0, 0, 1; 1, 1, 1]
    | 0, 1, 1, 1, 0, 1, 0, 0, 1 => !![1, 0, 0; 1, 0, 1; 0, 1, 1]
    | 1, 0, 0, 0, 0, 1, 0, 1, 0 => !![0, 0, 1; 1, 0, 0; 1, 1, 0]
    | 1, 0, 0, 0, 1, 0, 0, 1, 1 => !![0, 0, 1; 0, 1, 0; 1, 0, 0]
    | 1, 0, 0, 0, 1, 0, 1, 0, 1 => !![0, 1, 0; 0, 0, 1; 1, 0, 0]
    | 1, 0, 0, 0, 1, 0, 1, 1, 1 => !![0, 0, 1; 0, 1, 1; 1, 0, 0]
    | 1, 0, 0, 0, 1, 1, 0, 0, 1 => !![0, 0, 1; 1, 0, 0; 0, 1, 0]
    | 1, 0, 0, 1, 0, 1, 1, 1, 0 => !![0, 0, 1; 1, 0, 0; 1, 1, 1]
    | 1, 0, 0, 1, 1, 0, 0, 0, 1 => !![0, 1, 0; 1, 0, 0; 0, 0, 1]
    | 1, 0, 0, 1, 1, 0, 1, 0, 1 => !![0, 1, 0; 1, 0, 0; 1, 0, 1]
    | 1, 0, 0, 1, 1, 1, 0, 0, 1 => !![0, 0, 1; 1, 0, 0; 0, 1, 1]
    | 1, 0, 1, 0, 1, 0, 0, 0, 1 => !![1, 0, 0; 0, 0, 1; 0, 1, 0]
    | 1, 0, 1, 0, 1, 1, 0, 0, 1 => !![1, 0, 0; 1, 0, 1; 0, 1, 0]
    | 1, 1, 0, 0, 1, 0, 0, 0, 1 => !![1, 0, 0; 0, 1, 0; 0, 0, 1]
    | 1, 1, 0, 0, 1, 0, 0, 1, 1 => !![1, 0, 0; 0, 1, 0; 1, 0, 1]
    | 1, 1, 1, 0, 0, 1, 0, 1, 0 => !![1, 0, 0; 1, 0, 1; 1, 1, 1]
    | 1, 1, 1, 0, 1, 0, 0, 0, 1 => !![1, 0, 0; 0, 0, 1; 0, 1, 1]
    | _, _, _, _, _, _, _, _, _ => 1
  have checked : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.det = 1 → A * A = 1 → A ≠ 1 →
      (conjFor A).det = 1 ∧ conjFor A * tM = A * conjFor A := by
    dsimp only [conjFor, tM]
    decide +kernel
  intro a b ha ha1 hb hb1
  have haM : (a : Matrix (Fin 3) (Fin 3) (ZMod 2)) * a = 1 := congrArg Subtype.val ha
  have hbM : (b : Matrix (Fin 3) (Fin 3) (ZMod 2)) * b = 1 := congrArg Subtype.val hb
  have haM1 : (a : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hbM1 : (b : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hca := checked a a.2 haM haM1
  have hcb := checked b b.2 hbM hbM1
  let ca : SL(3, ZMod 2) := ⟨conjFor a, hca.1⟩
  let cb : SL(3, ZMod 2) := ⟨conjFor b, hcb.1⟩
  let t : SL(3, ZMod 2) := ⟨tM, by dsimp only [tM]; decide +kernel⟩
  have hca' : ca * t = a * ca := Subtype.ext hca.2
  have hcb' : cb * t = b * cb := Subtype.ext hcb.2
  have hta : ca⁻¹ * a * ca = t := by
    calc ca⁻¹ * a * ca = ca⁻¹ * (a * ca) := by group
      _ = ca⁻¹ * (ca * t) := by rw [← hca']
      _ = t := by group
  refine ⟨cb * ca⁻¹, ?_⟩
  calc (cb * ca⁻¹) * a * (cb * ca⁻¹)⁻¹ = cb * (ca⁻¹ * a * ca) * cb⁻¹ := by group
    _ = cb * t * cb⁻¹ := by rw [hta]
    _ = b := by rw [hcb', mul_assoc, mul_inv_cancel, mul_one]

theorem card_involutions_conj (P : Subgroup SL(3, ZMod 2)) (g : SL(3, ZMod 2))
    (hP : ∀ u : SL(3, ZMod 2), u ∈ P ↔ g⁻¹ * u * g ∈ upperSub) :
    Nat.card {u : SL(3, ZMod 2) // u ∈ P ∧ u * u = 1 ∧ u ≠ 1} =
      Nat.card {v : SL(3, ZMod 2) // v ∈ upperSub ∧ v * v = 1 ∧ v ≠ 1} := by
  refine Nat.card_congr
    { toFun := fun u => ⟨g⁻¹ * u.1 * g, (hP u.1).mp u.2.1, ?_, ?_⟩
      invFun := fun v => ⟨g * v.1 * g⁻¹, (hP _).mpr (by simpa [mul_assoc] using v.2.1), ?_, ?_⟩
      left_inv := fun u => Subtype.ext (by group)
      right_inv := fun v => Subtype.ext (by group) }
  · have e : g⁻¹ * u.1 * g * (g⁻¹ * u.1 * g) = g⁻¹ * (u.1 * u.1) * g := by group
    rw [e, u.2.2.1]
    group
  · intro h
    apply u.2.2.2
    have : u.1 = g * (g⁻¹ * u.1 * g) * g⁻¹ := by group
    rw [this, h]
    group
  · have e : g * v.1 * g⁻¹ * (g * v.1 * g⁻¹) = g * (v.1 * v.1) * g⁻¹ := by group
    rw [e, v.2.2.1]
    group
  · intro h
    apply v.2.2.2
    have : v.1 = g⁻¹ * (g * v.1 * g⁻¹) * g := by group
    rw [this, h]
    group

theorem exists_conj_eq_upperSub (P : Subgroup SL(3, ZMod 2)) (hP : Nat.card P = 8) :
    ∃ g : SL(3, ZMod 2), ∀ u : SL(3, ZMod 2), u ∈ P ↔ g⁻¹ * u * g ∈ upperSub := by
  have hG : Nat.card SL(3, ZMod 2) = 168 := card_SL3_two
  have hdiv : ∀ H : Subgroup SL(3, ZMod 2), Nat.card H = 8 → ¬ 2 ∣ H.index := by
    intro H hH h2
    have hm := Subgroup.card_mul_index H
    rw [hG, hH] at hm
    have h21 : H.index = 21 := by omega
    rw [h21] at h2
    norm_num at h2
  have hQ0 : IsPGroup 2 upperSub := IsPGroup.of_card (n := 3) (by rw [card_upperSub]; norm_num)
  have hPP : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q0 : Sylow 2 SL(3, ZMod 2) := hQ0.toSylow (hdiv upperSub card_upperSub)
  let Qp : Sylow 2 SL(3, ZMod 2) := hPP.toSylow (hdiv P hP)
  have : Finite (Sylow 2 SL(3, ZMod 2)) := Sylow.finite_of_finiteIndex Q0
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(3, ZMod 2) Q0 Qp
  have hsub : (MulAut.conj g) • (upperSub : Subgroup SL(3, ZMod 2)) = P := by
    have h1 := congrArg (fun S : Sylow 2 SL(3, ZMod 2) => (S : Subgroup SL(3, ZMod 2))) hg
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  refine ⟨g, fun u => ?_⟩
  rw [← hsub, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, mul_assoc]

theorem SL3_two_order_eight_involutions : ∀ P : Subgroup SL(3, ZMod 2), Nat.card P = 8 →
    Nat.card {u : SL(3, ZMod 2) // u ∈ P ∧ u * u = 1 ∧ u ≠ 1} = 5 := by
  intro P hP
  obtain ⟨g, hg⟩ := exists_conj_eq_upperSub P hP
  rw [card_involutions_conj P g hg, card_upperSub_involutions]

end CFSG.GH74.QTGen4.Recog.G23
