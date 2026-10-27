module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM6
public import CFSG.ClassicalInvolution.Asc77.AscFusionR8

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

theorem sq_eq_one_of_mem_L (h2 : (2 : F) ≠ 0) (k : Fin 2) {a : StatedSp 2 F}
    (ha : a ∈ longRootSp2 F 2 k) (h : a * a = 1) : a = 1 ∨ a = longInv F 2 k := by
  obtain ⟨A₀, rfl⟩ := ha
  have hA : A₀ * A₀ = 1 := longBlock_injective k (by rw [map_mul, map_one]; exact h)
  by_cases h1 : A₀ = 1
  · left
    rw [h1, map_one]
  · right
    have hord : orderOf A₀ = 2 := orderOf_eq_prime (by rwa [sq]) h1
    have hA' : A₀ = -1 := (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff F h2 A₀).1 hord
    rw [hA']
    rfl

theorem negOne_eq_longInv_mul (k : Fin 2) :
    negOne F = longInv F 2 k * longInv F 2 (Fin.rev k) := by
  fin_cases k
  · rfl
  · exact (longInv_one_mul_zero (F := F)).symm

theorem longInv_ne_one (h2 : (2 : F) ≠ 0) (k : Fin 2) : longInv F 2 k ≠ 1 := by
  intro h
  have := (isClassicalSL2_longRootSp2 (K := F) (n := 2) h2 k).orderOf_eq_two
  rw [h, orderOf_one] at this
  omega

theorem longInv_rev_not_mem (h2 : (2 : F) ≠ 0) (k : Fin 2) :
    longInv F 2 (Fin.rev k) ∉ longRootSp2 F 2 k := fun h =>
  longInv_ne_one h2 (Fin.rev k)
    (Subgroup.disjoint_def.1 (disjoint_L (F := F) k) h (longInv_mem (Fin.rev k)))

theorem conj_mul_L (k : Fin 2) {x₁ y₁ x₂ y₂ : StatedSp 2 F} (hx₁ : x₁ ∈ longRootSp2 F 2 k)
    (hy₁ : y₁ ∈ longRootSp2 F 2 k) (hx₂ : x₂ ∈ longRootSp2 F 2 (Fin.rev k))
    (hy₂ : y₂ ∈ longRootSp2 F 2 (Fin.rev k)) :
    x₁ * x₂ * (y₁ * y₂) * (x₁ * x₂)⁻¹ = (x₁ * y₁ * x₁⁻¹) * (x₂ * y₂ * x₂⁻¹) := by
  have e1 : x₂ * y₁ = y₁ * x₂ := (commute_L k hy₁ hx₂).symm
  have e2 : x₂ * y₂ * x₂⁻¹ * x₁⁻¹ = x₁⁻¹ * (x₂ * y₂ * x₂⁻¹) :=
    (commute_L k (inv_mem hx₁) (mul_mem (mul_mem hx₂ hy₂) (inv_mem hx₂))).symm
  calc x₁ * x₂ * (y₁ * y₂) * (x₁ * x₂)⁻¹ = x₁ * (x₂ * y₁) * y₂ * x₂⁻¹ * x₁⁻¹ := by group
    _ = x₁ * y₁ * (x₂ * y₂ * x₂⁻¹ * x₁⁻¹) := by rw [e1]; group
    _ = (x₁ * y₁ * x₁⁻¹) * (x₂ * y₂ * x₂⁻¹) := by rw [e2]; group

theorem eq_of_mul_eq_L (k : Fin 2) {a a' b b' : StatedSp 2 F} (ha : a ∈ longRootSp2 F 2 k)
    (ha' : a' ∈ longRootSp2 F 2 k) (hb : b ∈ longRootSp2 F 2 (Fin.rev k))
    (hb' : b' ∈ longRootSp2 F 2 (Fin.rev k)) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have e : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = b' * b⁻¹ := by rw [h]; group
  have h1 : a'⁻¹ * a = 1 := Subgroup.disjoint_def.1 (disjoint_L (F := F) k)
    (mul_mem (inv_mem ha') ha) (e ▸ mul_mem hb' (inv_mem hb))
  have haa : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h1, mul_one]
  refine ⟨haa, ?_⟩
  subst haa
  exact mul_left_cancel h

@[expose] noncomputable def rho (F : Type) [Field F] : StatedSp 2 F :=
  longBlock F 2 0 C25W.Sp.gStd * longBlock F 2 1 C25W.Sp.gStd

theorem exists_conj_rho_of_mem [Finite F] (hodd : Odd (Nat.card F))
    (k : Fin 2) {a b : StatedSp 2 F} (ha : a ∈ longRootSp2 F 2 k)
    (hb : b ∈ longRootSp2 F 2 (Fin.rev k)) (hab : a * b * (a * b) = negOne F) :
    ∃ g : StatedSp 2 F, g * (a * b) * g⁻¹ = rho F := by
  have hab' : a * a * (b * b) = longInv F 2 k * longInv F 2 (Fin.rev k) := by
    rw [← negOne_eq_longInv_mul, ← hab]
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [(commute_L k ha hb)]
      _ = a * b * (a * b) := by group
  obtain ⟨haa, hbb⟩ := eq_of_mul_eq_L k (mul_mem ha ha) (longInv_mem k) (mul_mem hb hb)
    (longInv_mem (Fin.rev k)) hab'
  obtain ⟨A₀, rfl⟩ := ha
  obtain ⟨B₀, rfl⟩ := hb
  have hA : A₀ * A₀ = -1 := longBlock_injective k (by rw [map_mul]; exact haa)
  have hB : B₀ * B₀ = -1 := longBlock_injective (Fin.rev k) (by rw [map_mul]; exact hbb)
  obtain ⟨c, hc⟩ := AscFusion.sl2_exists_conj_of_sq_eq_neg_one hodd hA C25W.Sp.gStd_sq
  obtain ⟨d, hd⟩ := AscFusion.sl2_exists_conj_of_sq_eq_neg_one hodd hB C25W.Sp.gStd_sq
  refine ⟨longBlock F 2 k c * longBlock F 2 (Fin.rev k) d, ?_⟩
  have e1 : longBlock F 2 k c * longBlock F 2 k A₀ * (longBlock F 2 k c)⁻¹ =
      longBlock F 2 k C25W.Sp.gStd := by
    rw [← map_inv, ← map_mul, ← map_mul, hc]
  have e2 : longBlock F 2 (Fin.rev k) d * longBlock F 2 (Fin.rev k) B₀ *
      (longBlock F 2 (Fin.rev k) d)⁻¹ = longBlock F 2 (Fin.rev k) C25W.Sp.gStd := by
    rw [← map_inv, ← map_mul, ← map_mul, hd]
  rw [conj_mul_L k ⟨c, rfl⟩ ⟨A₀, rfl⟩ ⟨d, rfl⟩ ⟨B₀, rfl⟩, e1, e2]
  fin_cases k
  · rfl
  · exact commute_L 1 ⟨_, rfl⟩ ⟨_, rfl⟩

theorem conj_negOne (g : StatedSp 2 F) : g⁻¹ * negOne F * g = negOne F := by
  rw [mul_assoc, negOne_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_conj_rho [Finite F] (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F))
    {h : StatedSp 2 F} (hh : h * h = negOne F) : ∃ g : StatedSp 2 F, g * h * g⁻¹ = rho F := by
  have hmap : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F, M.map (RingEquiv.refl F) = M := by
    intro M
    ext
    simp
  obtain ⟨u, w, s, huw, hs, hs4, hsc, hcomm⟩ :=
    C25W.Sp.exists_stable_rotation (m := 0) (RingEquiv.refl F) (mat 2 F h) (fun _ => rfl) h2
      (mat_transpose_mul_gram_mul h) (-1) (by ring)
      (by rw [hmap, ← map_mul, hh, mat_negOne, neg_one_smul])
  rw [hmap] at hcomm
  have hhs : h * s = s * h := mat_injective (by rw [map_mul, map_mul, hcomm])
  obtain ⟨i, hi, -⟩ := exists_isLongRootSp2_of_isHyperbolicPlane h2
    (P := Submodule.span F {u, w}) ⟨u, w, huw, rfl⟩
  have hs1 : s * s ≠ 1 := by
    intro h1
    exact hsc ⟨1, by rw [h1, map_one, one_smul]⟩
  have hsi : s * s = i := hi.eq_of_orderOf_eq_two h2 (mul_mem hs hs)
    (orderOf_eq_prime (by rw [pow_two]; exact hs4) hs1)
  obtain ⟨k, g, -, hig⟩ := hi
  have hhi : h * i = i * h := by
    rw [← hsi]
    calc h * (s * s) = h * s * s := by group
      _ = s * h * s := by rw [hhs]
      _ = s * (h * s) := by group
      _ = s * (s * h) := by rw [hhs]
      _ = s * s * h := by group
  have hc₁ : g⁻¹ * h * g * longInv F 2 k = longInv F 2 k * (g⁻¹ * h * g) := by
    have e : longInv F 2 k = g⁻¹ * i * g := by rw [hig]; group
    rw [e]
    calc g⁻¹ * h * g * (g⁻¹ * i * g) = g⁻¹ * (h * i) * g := by group
      _ = g⁻¹ * (i * h) * g := by rw [hhi]
      _ = g⁻¹ * i * g * (g⁻¹ * h * g) := by group
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_commute_longInv h2 k hc₁
  rw [complGroup_longInv_two h2] at hb
  have hsq : a * b * (a * b) = negOne F := by
    rw [← hab]
    calc g⁻¹ * h * g * (g⁻¹ * h * g) = g⁻¹ * (h * h) * g := by group
      _ = negOne F := by rw [hh, conj_negOne]
  obtain ⟨c, hc⟩ := exists_conj_rho_of_mem hodd k ha hb hsq
  refine ⟨c * g⁻¹, ?_⟩
  rw [← hab] at hc
  calc c * g⁻¹ * h * (c * g⁻¹)⁻¹ = c * (g⁻¹ * h * g) * c⁻¹ := by group
    _ = rho F := hc

end CFSG.ClassicalInvolution.Asc77.C5O.M
