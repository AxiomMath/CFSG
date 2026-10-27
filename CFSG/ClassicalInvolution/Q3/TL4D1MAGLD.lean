module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAGLC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Generic Matrix
open scoped commutatorElement

@[expose] noncomputable def slOf (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : det3 A = 1) :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨A, by rw [det_eq_det3]; exact h⟩

theorem slOf_val (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : det3 A = 1) : (slOf A h).1 = A := rfl

theorem pi_single_zmod_two (w : Fin 3 → ZMod 2) (k : Fin 3) :
    (Pi.single k (w k) : Fin 3 → ZMod 2) = 0 ∨
      (Pi.single k (w k) : Fin 3 → ZMod 2) = Pi.single k 1 := by
  have : w k = 0 ∨ w k = 1 := by
    generalize w k = x
    revert x
    decide
  rcases this with h | h
  · left
    rw [h, Pi.single_zero]
  · right
    rw [h]

theorem vec_eq_sum_single (w : Fin 3 → ZMod 2) :
    w = (Pi.single 0 (w 0) : Fin 3 → ZMod 2) + (Pi.single 1 (w 1) : Fin 3 → ZMod 2) +
      (Pi.single 2 (w 2) : Fin 3 → ZMod 2) := by
  funext i
  fin_cases i <;> simp

theorem agl32_normal_not_two {Q : Subgroup (Equiv.Perm (Fin 8))} (hQ : Q ≤ agl32)
    (hQn : ∀ g ∈ agl32, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) (h2 : ¬ IsPGroup 2 Q) : Q = agl32 := by
  set L := (Q.subgroupOf agl32).map linHom with hL
  have hLn : L.Normal := by
    refine ⟨fun x hx A => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hx
    let g : ↥agl32 := ⟨aperm A 0, aperm_mem_agl32 A 0⟩
    have hg : linHom g = A := linPart_eq rfl
    refine ⟨g * q * g⁻¹, Subgroup.mem_subgroupOf.mpr (hQn _ g.2 _ (Subgroup.mem_subgroupOf.mp hq)),
      ?_⟩
    rw [map_mul, map_mul, map_inv, hg]
  have hs := isSimpleGroup_sl3Two
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with hbot | htop
  · exfalso
    apply h2
    intro q
    refine ⟨1, Subtype.ext ?_⟩
    have hq : linHom ⟨q, hQ q.2⟩ = 1 := by
      have : linHom ⟨q, hQ q.2⟩ ∈ L := ⟨⟨q, hQ q.2⟩, Subgroup.mem_subgroupOf.mpr q.2, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    have he := aperm_linPart ⟨q, hQ q.2⟩
    rw [← linHom_apply, hq] at he
    show (q : Equiv.Perm (Fin 8)) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two, ← he, aperm_one_mul_self]
  ·
    have hsurj : ∀ A, ∃ q ∈ Q, ∃ b, q = aperm A b := by
      intro A
      have hA : A ∈ L := htop ▸ Subgroup.mem_top A
      obtain ⟨q, hq, hqA⟩ := hA
      refine ⟨q, Subgroup.mem_subgroupOf.mp hq, transPart q, ?_⟩
      rw [← aperm_linPart q, ← linHom_apply, hqA]
    have hcomm : ∀ (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2),
        aperm 1 (A.1 *ᵥ v + v) ∈ Q := by
      intro A v
      obtain ⟨q, hq, b, rfl⟩ := hsurj A
      rw [← comm_aperm_trans, mul_assoc, mul_assoc]
      refine Q.mul_mem hq ?_
      rw [← mul_assoc]
      exact hQn _ (aperm_mem_agl32 1 v) _ (Q.inv_mem hq)
    obtain ⟨d1, d2, d3, e1, e2, e3⟩ := transvection_facts
    have hek : ∀ k : Fin 3, aperm 1 (Pi.single k 1) ∈ Q := by
      intro k
      fin_cases k
      · have := hcomm (slOf _ d1) ![0, 1, 0]
        rwa [slOf_val, e1] at this
      · have := hcomm (slOf _ d2) ![1, 0, 0]
        rwa [slOf_val, e2] at this
      · have := hcomm (slOf _ d3) ![1, 0, 0]
        rwa [slOf_val, e3] at this
    have hadd : ∀ u w : Fin 3 → ZMod 2, aperm 1 u ∈ Q → aperm 1 w ∈ Q → aperm 1 (u + w) ∈ Q := by
      intro u w hu hw
      have := Q.mul_mem hw hu
      rwa [aperm_mul, mul_one, show (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)).1 = 1 from rfl,
        one_mulVec] at this
    have hsingle : ∀ (w : Fin 3 → ZMod 2) (k : Fin 3),
        aperm 1 (Pi.single k (w k) : Fin 3 → ZMod 2) ∈ Q := by
      intro w k
      rcases pi_single_zmod_two w k with h | h
      · rw [h, aperm_one_zero]
        exact Q.one_mem
      · rw [h]
        exact hek k
    have htr : ∀ w, aperm 1 w ∈ Q := by
      intro w
      rw [vec_eq_sum_single w]
      exact hadd _ _ (hadd _ _ (hsingle w 0) (hsingle w 1)) (hsingle w 2)
    refine le_antisymm hQ fun σ hσ => ?_
    obtain ⟨A, b, rfl⟩ := exists_aperm_eq hσ
    obtain ⟨q, hq, b', rfl⟩ := hsurj A
    have : aperm A b = aperm A b' * (aperm 1 ((A⁻¹).1 *ᵥ b' + (A⁻¹).1 *ᵥ b)) := by
      rw [aperm_mul, mul_one]
      congr 1
      rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, mul_inv_val, one_mulVec, one_mulVec,
        add_comm b' b, add_assoc, two_smul_zero, add_zero]
    rw [this]
    exact Q.mul_mem hq (htr _)

end CFSG.ClassicalInvolution.Q3.TL4
