
module

public import CFSG.Monster.B.E6.StdF4Opposite
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Vec

@[expose] public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

open CFSG.Monster.B.Classical.E6Adjoint CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Fischer
open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std CFSG.Monster.B.E6.StdF4
open CFSG.LieType.Chevalley.C2E6Overlap (K barHom)

theorem root_seventy : e6Certificate.root 70 = theta := by
  decide +kernel

theorem root_seventyOne : e6Certificate.root 71 = -theta := by
  decide +kernel

theorem pinnedX_single_eq {a b : Fin 78} (ha : 6 ≤ (a : ℕ)) (hab : brMask a b = 0)
    (hf : fbit a b = false) :
    ((pinnedX Tag.E6 K (e6Certificate.root ((a : ℕ) - 6)) 1 : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) (Finsupp.single (lab b) 1) =
        Finsupp.single (lab b) 1 := by
  rw [pinnedX_eq (isRoot_certRoot (by omega)) 1, rootOp_apply, rootVec_lab ha, bracket_lab,
    form_lab, hab, hf, toVec_zero]
  simp

theorem units_inv_apply_eq {M : Type*} [AddCommGroup M] [Module K M] {u : (Module.End K M)ˣ}
    {w : M} (h : (u : Module.End K M) w = w) :
    ((u⁻¹ : (Module.End K M)ˣ) : Module.End K M) w = w := by
  conv_lhs => rw [← h]
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]

theorem conj_pinnedX_one_apply {g : ModGL Tag.E6 K} (hg : g ∈ adjointGroup Tag.E6 K)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (w : RootModule Tag.E6 K) :
    ((g * pinnedX Tag.E6 K α 1 * g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) w =
      w + bracket K ((g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K α)) w +
        form K ((g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K α)) w •
          (g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K α) := by
  have h1 : (g : Module.End K (RootModule Tag.E6 K))
      (((g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) w) = w := by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, pinnedX_eq hα,
    rootOp_apply]
  simp only [one_smul, one_pow, map_add, map_smul]
  rw [adjointGroup_bracket hg, h1, ← adjointGroup_form hg (rootVec Tag.E6 K α), h1]

theorem exists_orderOf_tMinus_mul {x : stdGroup} (hx : x ∈ rootClass) :
    ∃ i : Fin 5, orderOf (tMinus * x) = repOrder i := by
  obtain ⟨q, -, hcov, -, hord⟩ := fiveOrbits_of_mem_rootClass tMinus_mem_rootClass
  obtain ⟨i, hi⟩ := hcov x hx
  exact ⟨i, hord i x hi⟩

theorem not_inverts_of_orderOf {x : stdGroup} (hx : x ∈ rootClass)
    (hinv : x * (rootInv * tMinus) * x⁻¹ = (rootInv * tMinus)⁻¹)
    (ho : orderOf (rootInv * x) = 2 ∨ orderOf (rootInv * x) = 4) : False := by
  have hr : rootInv * rootInv = 1 := rootInv_mul_self
  have ht : tMinus * tMinus = 1 := by
    rw [← pow_two]
    exact sq_of_mem_rootClass tMinus_mem_rootClass
  have hxx : x * x = 1 := by
    rw [← pow_two]
    exact sq_of_mem_rootClass hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hri : rootInv⁻¹ = rootInv := inv_eq_of_mul_eq_one_right hr
  have hti : tMinus⁻¹ = tMinus := inv_eq_of_mul_eq_one_right ht
  have h' := hinv
  rw [hxi, mul_inv_rev, hti, hri] at h'
  have hkey : rootInv * tMinus * x = x * (tMinus * rootInv) := by
    calc rootInv * tMinus * x = x * x * (rootInv * tMinus) * x := by rw [hxx, one_mul]
      _ = x * (x * (rootInv * tMinus) * x) := by group
      _ = x * (tMinus * rootInv) := by rw [h']
  have e1 : x * rootInv * (rootInv * tMinus) = x * tMinus := by
    rw [mul_assoc, ← mul_assoc rootInv, hr, one_mul]
  have e2 : rootInv * tMinus * (x * rootInv) = x * tMinus := by
    rw [← mul_assoc, hkey, mul_assoc, mul_assoc, hr, mul_one]
  have hcomm : Commute (x * rootInv) (rootInv * tMinus) := e1.trans e2.symm
  have hoa : orderOf (x * rootInv) = orderOf (rootInv * x) := by
    rw [← orderOf_inv (rootInv * x), mul_inv_rev, hxi, hri]
  have hco : (orderOf (x * rootInv)).Coprime (orderOf (rootInv * tMinus)) := by
    rw [hoa, orderOf_rootInv_mul_tMinus]
    rcases ho with h | h <;> rw [h] <;> decide
  have hmul := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco
  rw [e1, hoa, orderOf_rootInv_mul_tMinus] at hmul
  have hxt : orderOf (x * tMinus) = orderOf (tMinus * x) := by
    rw [← orderOf_inv (tMinus * x), mul_inv_rev, hxi, hti]
  obtain ⟨i, hi⟩ := exists_orderOf_tMinus_mul hx
  rw [← hxt, hmul] at hi
  rcases ho with h | h <;> rw [h] at hi <;> revert hi <;> revert i <;> decide

end CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

