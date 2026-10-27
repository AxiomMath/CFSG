module

public import CFSG.LargeExtraspecial.S14C13Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem cLin_congr {t : S.O} [NQHyp S g t] {z w : S.O} (hz : z ∈ Ct S t) (hw : w ∈ Ct S t)
    (h : z = w) (v : NQ S g t) : cLin (g := g) hz v = cLin (g := g) hw v := by
  subst h
  rfl

theorem cLin_mul_apply {t : S.O} [NQHyp S g t] {z w : S.O} (hz : z ∈ Ct S t)
    (hw : w ∈ Ct S t) (v : NQ S g t) :
    cLin (g := g) (mul_mem hz hw) v = cLin (g := g) hz (cLin (g := g) hw v) := by
  have hv := nqMk_surjective (S := S) (g := g) (t := t) v
  rcases hv with ⟨n, hn⟩
  rw [← hn]
  show nqMk (cConj (mul_mem hz hw) n) = nqMk (cConj hz (cConj hw n))
  congr 1

theorem cLin_of_mem_Nbar {t : S.O} [hN : NQHyp S g t] {z : S.O} (hz : z ∈ Ct S t)
    (hzN : z ∈ Nbar S g t) (v : NQ S g t) : cLin (g := g) hz v = v := by
  have hv := nqMk_surjective (S := S) (g := g) (t := t) v
  rcases hv with ⟨n, hn⟩
  rw [← hn, cLin_mk, nqMk_eq_iff, coe_cConj]
  have h1 := hN.comm z hzN _ (inv_mem n.2)
  convert h1 using 1
  group

theorem mem_Ct_of_mem_Nbar (haQ : g * S.z * g⁻¹ ∈ S.QG) {t n : S.O} (hn : n ∈ Nbar S g t) :
    n ∈ Ct S t :=
  Subgroup.mem_inf.mpr ⟨Rbar_le_Mbar (Nbar_le_Rbar hn), Rbar_le_centralizer haQ (Nbar_le_Rbar hn)⟩

theorem cLin_comm_of_mem {t : S.O} [NQHyp S g t] {z w : S.O} (hz : z ∈ Ct S t)
    (hw : w ∈ Ct S t) (h : z * w * z⁻¹ * w⁻¹ ∈ Nbar S g t) (v : NQ S g t) :
    cLin (g := g) hz (cLin (g := g) hw v) = cLin (g := g) hw (cLin (g := g) hz v) := by
  have hcC := mem_Ct_of_mem_Nbar (NQHyp.conj_mem (S := S) (g := g) (t := t)) h
  rw [← cLin_mul_apply (g := g) hz hw, ← cLin_mul_apply (g := g) hw hz,
    cLin_congr (g := g) (mul_mem hz hw) (mul_mem hcC (mul_mem hw hz)) (by group),
    cLin_mul_apply (g := g) hcC (mul_mem hw hz), cLin_of_mem_Nbar (g := g) hcC h]

theorem cLin_sq {t : S.O} [NQHyp S g t] {a : S.O} (ha : a ∈ Ct S t)
    (ha2 : a * a ∈ Nbar S g t) (v : NQ S g t) :
    cLin (g := g) ha (cLin (g := g) ha v) = v := by
  rw [← cLin_mul_apply (g := g) ha ha]
  exact cLin_of_mem_Nbar (g := g) _ ha2 v

theorem cLin_cube {t : S.O} [NQHyp S g t] {a b : S.O} (ha : a ∈ Ct S t) (hb : b ∈ Ct S t)
    (h3 : (a * b) ^ 3 ∈ Nbar S g t) (v : NQ S g t) :
    cLin (g := g) ha (cLin (g := g) hb (cLin (g := g) ha (cLin (g := g) hb
      (cLin (g := g) ha (cLin (g := g) hb v))))) = v := by
  have hab := mul_mem ha hb
  have e : (a * b) ^ 3 = (a * b) * (a * b) * (a * b) := pow_three' _
  rw [← cLin_mul_apply (g := g) ha hb, ← cLin_mul_apply (g := g) ha hb,
    ← cLin_mul_apply (g := g) ha hb, ← cLin_mul_apply (g := g) hab hab,
    ← cLin_mul_apply (g := g) (mul_mem hab hab) hab,
    cLin_congr (g := g) _ (pow_mem hab 3) e.symm]
  exact cLin_of_mem_Nbar (g := g) _ h3 v

theorem comm_inv_mul_mem (haQ : g * S.z * g⁻¹ ∈ S.QG) {t a x y : S.O} (hx : x ∈ Ct S t)
    (hax : a * x * a⁻¹ * x⁻¹ ∈ Nbar S g t) (hya : y * a * y⁻¹ * a⁻¹ ∈ Nbar S g t) :
    (x⁻¹ * y) * a * (x⁻¹ * y)⁻¹ * a⁻¹ ∈ Nbar S g t := by
  have e : (x⁻¹ * y) * a * (x⁻¹ * y)⁻¹ * a⁻¹ =
      x⁻¹ * (y * a * y⁻¹ * a⁻¹) * x⁻¹⁻¹ * (x⁻¹ * (a * x * a⁻¹ * x⁻¹) * x⁻¹⁻¹) := by
    group
  rw [e]
  exact mul_mem (conj_mem_Nbar_of_mem_Ct haQ (inv_mem hx) hya)
    (conj_mem_Nbar_of_mem_Ct haQ (inv_mem hx) hax)

end CFSG.LargeExtraspecial.S14
