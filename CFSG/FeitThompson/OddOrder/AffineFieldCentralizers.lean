module

public import CFSG.FeitThompson.OddOrder.ShiftedInversionIteration
public import CFSG.FeitThompson.Foundations.NormOneGroupOrder
public import CFSG.FeitThompson.Foundations.CoprimeActionFittingFaithful
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Sylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Finset SemidirectProduct

variable {F : Type*} [Field F] {U : Subgroup Fˣ} {p q m : ℕ}

def mulRightInvAut (F : Type*) [Field F] : Fˣ →* MulAut (Multiplicative F) where
  toFun u := AddEquiv.toMultiplicative (AddAut.mulRight u⁻¹)
  map_one' := by ext z; simp
  map_mul' u v := by ext z; simp [mul_assoc, mul_comm]

@[simp] theorem toAdd_mulRightInvAut_apply (u : Fˣ) (w : Multiplicative F) :
    Multiplicative.toAdd (mulRightInvAut F u w) = Multiplicative.toAdd w * ((u⁻¹ : Fˣ) : F) := by
  simp [mulRightInvAut]

def mulRightInvAutOn (U : Subgroup Fˣ) : U →* MulAut (Multiplicative F) :=
  (mulRightInvAut F).comp U.subtype

@[simp] theorem toAdd_mulRightInvAutOn_apply (u : U) (w : Multiplicative F) :
    Multiplicative.toAdd (mulRightInvAutOn U u w)
      = Multiplicative.toAdd w * (((u : Fˣ)⁻¹ : Fˣ) : F) := by
  simp [mulRightInvAutOn]

@[simp] theorem toAdd_inv_mulRightInvAutOn_apply (u : U) (w : Multiplicative F) :
    Multiplicative.toAdd ((mulRightInvAutOn U u)⁻¹ w)
      = Multiplicative.toAdd w * ((u : Fˣ) : F) := by
  rw [← map_inv, toAdd_mulRightInvAutOn_apply]; simp

theorem inv_mulRightInvAutOn_apply_ofAdd (u : U) (z : F) :
    (mulRightInvAutOn U u)⁻¹ (Multiplicative.ofAdd z)
      = Multiplicative.ofAdd (z * ((u : Fˣ) : F)) :=
  Multiplicative.toAdd.injective (toAdd_inv_mulRightInvAutOn_apply u (Multiplicative.ofAdd z))

abbrev fieldAffineGroup (F : Type*) [Field F] (U : Subgroup Fˣ) : Type _ :=
  Multiplicative F ⋊[mulRightInvAutOn U] U

def fieldAffineBase (F : Type*) [Field F] (U : Subgroup Fˣ) :
    Subgroup (fieldAffineGroup F U) := (inl : Multiplicative F →* fieldAffineGroup F U).range

def fieldAffineUnits (F : Type*) [Field F] (U : Subgroup Fˣ) :
    Subgroup (fieldAffineGroup F U) := (inr : U →* fieldAffineGroup F U).range

theorem fieldAffineBase_eq_range_inl :
    fieldAffineBase F U = (inl : Multiplicative F →* fieldAffineGroup F U).range := (rfl)

theorem fieldAffineUnits_eq_range_inr :
    fieldAffineUnits F U = (inr : U →* fieldAffineGroup F U).range := (rfl)

theorem fieldAffineBase_eq_ker_rightHom :
    fieldAffineBase F U = (rightHom : fieldAffineGroup F U →* U).ker := range_inl_eq_ker_rightHom

@[simp] theorem mem_fieldAffineBase_iff {x : fieldAffineGroup F U} :
    x ∈ fieldAffineBase F U ↔ x.right = 1 := by
  rw [fieldAffineBase_eq_ker_rightHom, MonoidHom.mem_ker, rightHom_eq_right]

@[simp] theorem mem_fieldAffineUnits_iff {x : fieldAffineGroup F U} :
    x ∈ fieldAffineUnits F U ↔ x.left = 1 :=
  ⟨fun ⟨u, hu⟩ => by rw [← hu, left_inr],
    fun h => ⟨x.right, SemidirectProduct.ext (by rw [left_inr, h]) (by rw [right_inr])⟩⟩

theorem inl_mem_fieldAffineBase (w : Multiplicative F) :
    (inl w : fieldAffineGroup F U) ∈ fieldAffineBase F U := ⟨w, rfl⟩

theorem inr_mem_fieldAffineUnits (u : U) :
    (inr u : fieldAffineGroup F U) ∈ fieldAffineUnits F U := ⟨u, rfl⟩

instance : (fieldAffineBase F U).Normal := by
  rw [fieldAffineBase_eq_ker_rightHom]; infer_instance

instance : IsMulCommutative (fieldAffineBase F U) := by
  rw [fieldAffineBase_eq_range_inl]; infer_instance

theorem inv_inr_mul_inl_mul_inr (u : U) (z : F) :
    (inr u : fieldAffineGroup F U)⁻¹ * inl (Multiplicative.ofAdd z) * inr u
      = inl (Multiplicative.ofAdd (z * ((u : Fˣ) : F))) := by
  rw [← map_inv inr u, ← inl_aut_inv, inv_mulRightInvAutOn_apply_ofAdd]

theorem fieldAffineBase_inf_fieldAffineUnits :
    fieldAffineBase F U ⊓ fieldAffineUnits F U = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
  rw [mem_fieldAffineBase_iff] at h1
  rw [mem_fieldAffineUnits_iff] at h2
  exact Subgroup.mem_bot.mpr (SemidirectProduct.ext h2 h1)

theorem natCard_fieldAffineBase : Nat.card (fieldAffineBase F U) = Nat.card F :=
  Nat.card_congr (MonoidHom.ofInjective (inl_injective (φ := mulRightInvAutOn U))).symm.toEquiv

theorem natCard_fieldAffineGroup :
    Nat.card (fieldAffineGroup F U) = Nat.card F * Nat.card U := SemidirectProduct.card

theorem le_fieldAffineBase_of_isPGroup [Fact p.Prime] (hU : ¬ p ∣ Nat.card U)
    {Q : Subgroup (fieldAffineGroup F U)} (hQ : IsPGroup p Q) : Q ≤ fieldAffineBase F U := by
  have himg : IsPGroup p (Q.map (rightHom : fieldAffineGroup F U →* U)) := hQ.map _
  have h1 : Nat.card (Q.map (rightHom : fieldAffineGroup F U →* U)) = 1 :=
    himg.card_eq_or_dvd.resolve_right fun h => hU (h.trans (Subgroup.card_subgroup_dvd_card _))
  rw [fieldAffineBase_eq_ker_rightHom, ← Subgroup.map_eq_bot_iff]
  exact (Subgroup.eq_bot_iff_card _).mpr h1

theorem isPGroup_fieldAffineBase (hFcard : Nat.card F = p ^ q) :
    IsPGroup p (fieldAffineBase F U) :=
  IsPGroup.of_card (by rw [natCard_fieldAffineBase, hFcard])

theorem factorization_natCard_fieldAffineGroup (hp : p.Prime) (hU : ¬ p ∣ Nat.card U)
    (hUpos : Nat.card U ≠ 0) (hFcard : Nat.card F = p ^ q) :
    (Nat.card (fieldAffineGroup F U)).factorization p = q := by
  rw [natCard_fieldAffineGroup, hFcard, Nat.factorization_mul (pow_ne_zero _ hp.pos.ne') hUpos]
  simp [hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hU]

def fieldAffineSylow [Fact p.Prime] [Finite F] (hU : ¬ p ∣ Nat.card U)
    (hFcard : Nat.card F = p ^ q) : Sylow p (fieldAffineGroup F U) :=
  have : Finite U := Finite.of_injective (fun u => (u : Fˣ)) Subtype.val_injective
  Sylow.ofCard (fieldAffineBase F U) (by
    rw [natCard_fieldAffineBase, hFcard,
      factorization_natCard_fieldAffineGroup Fact.out hU Nat.card_pos.ne' hFcard])

@[simp] theorem coe_fieldAffineSylow [Fact p.Prime] [Finite F] (hU : ¬ p ∣ Nat.card U)
    (hFcard : Nat.card F = p ^ q) :
    ((fieldAffineSylow hU hFcard : Sylow p (fieldAffineGroup F U)) : Subgroup _)
      = fieldAffineBase F U := (rfl)

theorem coe_eq_fieldAffineBase [Fact p.Prime] (hU : ¬ p ∣ Nat.card U)
    (hFcard : Nat.card F = p ^ q) (Q : Sylow p (fieldAffineGroup F U)) :
    (Q : Subgroup (fieldAffineGroup F U)) = fieldAffineBase F U :=
  (Q.3 (isPGroup_fieldAffineBase hFcard) (le_fieldAffineBase_of_isPGroup hU Q.isPGroup')).symm

theorem subsingleton_sylow_fieldAffineGroup [Fact p.Prime] (hU : ¬ p ∣ Nat.card U)
    (hFcard : Nat.card F = p ^ q) : Subsingleton (Sylow p (fieldAffineGroup F U)) :=
  ⟨fun Q R => Sylow.ext ((coe_eq_fieldAffineBase hU hFcard Q).trans
    (coe_eq_fieldAffineBase hU hFcard R).symm)⟩

theorem mem_centralizer_inl_ofAdd_iff (z : F) (x : fieldAffineGroup F U) :
    x ∈ Subgroup.centralizer {(inl (Multiplicative.ofAdd z) : fieldAffineGroup F U)} ↔
      z * (((x.right : Fˣ)⁻¹ : Fˣ) : F) = z := by
  rw [Subgroup.mem_centralizer_singleton_iff, SemidirectProduct.ext_iff]
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, left_inl, right_inl,
    mul_one, one_mul, and_true, map_one, MulAut.one_apply]
  rw [mul_comm (Multiplicative.ofAdd z) x.left, mul_right_inj,
    ← Multiplicative.toAdd.apply_eq_iff_eq, toAdd_mulRightInvAutOn_apply]
  simp

theorem centralizer_inl_ofAdd_eq_fieldAffineBase {z : F} (hz : z ≠ 0) :
    Subgroup.centralizer {(inl (Multiplicative.ofAdd z) : fieldAffineGroup F U)}
      = fieldAffineBase F U := by
  ext x
  rw [mem_centralizer_inl_ofAdd_iff, mem_fieldAffineBase_iff]
  constructor
  · intro h
    have h1 : (((x.right : Fˣ)⁻¹ : Fˣ) : F) = 1 := mul_left_cancel₀ hz (by rw [h, mul_one])
    exact Subtype.ext (by simpa using inv_eq_one.mp (Units.ext h1 : ((x.right : Fˣ)⁻¹) = 1))
  · intro h
    rw [h]
    simp

theorem inl_mem_centralizer_inr_iff (u : U) (w : Multiplicative F) :
    (inl w : fieldAffineGroup F U) ∈ Subgroup.centralizer {(inr u : fieldAffineGroup F U)} ↔
      Multiplicative.toAdd w * (((u : Fˣ)⁻¹ : Fˣ) : F) = Multiplicative.toAdd w := by
  rw [Subgroup.mem_centralizer_singleton_iff, SemidirectProduct.ext_iff]
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, left_inl, right_inl,
    left_inr, right_inr, mul_one, one_mul, and_true, map_one]
  constructor
  · intro h
    rw [← toAdd_mulRightInvAutOn_apply, ← h]
  · intro h
    exact (Multiplicative.toAdd.injective (by rw [toAdd_mulRightInvAutOn_apply, h])).symm

theorem fieldAffineBase_inf_centralizer_inr_eq_bot {u : U} (hu : u ≠ 1) :
    fieldAffineBase F U ⊓ Subgroup.centralizer {(inr u : fieldAffineGroup F U)} = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
  rw [mem_fieldAffineBase_iff] at h1
  have hx' : x = inl x.left := SemidirectProduct.ext rfl (by rw [right_inl, h1])
  rw [hx', inl_mem_centralizer_inr_iff] at h2
  have hu1 : (((u : Fˣ)⁻¹ : Fˣ) : F) - 1 ≠ 0 := by
    intro h
    refine hu (Subtype.ext ?_)
    have h0 : ((u : Fˣ)⁻¹ : Fˣ) = 1 := Units.ext (by rw [sub_eq_zero] at h; exact h)
    simpa using inv_eq_one.mp h0
  have hz : Multiplicative.toAdd x.left * ((((u : Fˣ)⁻¹ : Fˣ) : F) - 1) = 0 := by
    rw [mul_sub, mul_one, h2, sub_self]
  rw [Subgroup.mem_bot, hx']
  exact congrArg inl (Multiplicative.toAdd.injective ((mul_eq_zero.mp hz).resolve_right hu1))

section Config

theorem normOneSubgroup_eq_normOneUnits (hp : p.Prime) (hFcard : Nat.card F = p ^ q)
    (hm : m = (p ^ q - 1) / (p - 1)) : normOneSubgroup F m = normOneUnits F := by
  have hm' : m = ∑ i ∈ range q, p ^ i := by rw [hm, Nat.geomSum_eq hp.two_le]
  ext u
  rw [mem_normOneSubgroup, normOneUnits_eq_rootsOfUnity hp hFcard, mem_rootsOfUnity, ← hm']

theorem natCard_normOneSubgroup (hp : p.Prime) (hFcard : Nat.card F = p ^ q)
    (hm : m = (p ^ q - 1) / (p - 1)) : Nat.card (normOneSubgroup F m) = m := by
  rw [normOneSubgroup_eq_normOneUnits hp hFcard hm, natCard_normOneUnits_eq_div hp hFcard, hm]

theorem not_dvd_geomSum (hp : p.Prime) (hq : q ≠ 0) : ¬ p ∣ ∑ i ∈ range q, p ^ i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  rw [Finset.sum_range_succ']
  simp only [pow_zero, pow_succ]
  intro h
  have h2 : p ∣ ∑ i ∈ range n, p ^ i * p := Finset.dvd_sum fun i _ => ⟨p ^ i, by ring⟩
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h2).mp h))

theorem not_dvd_of_eq_div (hp : p.Prime) (hq : q ≠ 0) (hm : m = (p ^ q - 1) / (p - 1)) :
    ¬ p ∣ m := by
  rw [hm, ← Nat.geomSum_eq hp.two_le]
  exact not_dvd_geomSum hp hq

theorem not_dvd_natCard_normOneSubgroup (hp : p.Prime) (hq : q ≠ 0) (hFcard : Nat.card F = p ^ q)
    (hm : m = (p ^ q - 1) / (p - 1)) : ¬ p ∣ Nat.card (normOneSubgroup F m) := by
  rw [natCard_normOneSubgroup hp hFcard hm]
  exact not_dvd_of_eq_div hp hq hm

def fieldAffineSylowOfConfig (hp : p.Prime) (hq : q.Prime) (_hqp : q < p)
    (hFcard : Nat.card F = p ^ q) (hm : m = (p ^ q - 1) / (p - 1))
    (_hcop : Nat.Coprime m (p - 1)) : Sylow p (fieldAffineGroup F (normOneSubgroup F m)) :=
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := finite_of_natCard_eq_prime_pow hp hFcard
  fieldAffineSylow (not_dvd_natCard_normOneSubgroup hp hq.ne_zero hFcard hm) hFcard

theorem coe_eq_fieldAffineBase_of_config (hp : p.Prime) (hq : q.Prime) (_hqp : q < p)
    (hFcard : Nat.card F = p ^ q) (hm : m = (p ^ q - 1) / (p - 1))
    (_hcop : Nat.Coprime m (p - 1))
    (Q : Sylow p (fieldAffineGroup F (normOneSubgroup F m))) :
    (Q : Subgroup (fieldAffineGroup F (normOneSubgroup F m)))
      = fieldAffineBase F (normOneSubgroup F m) :=
  have : Fact p.Prime := ⟨hp⟩
  coe_eq_fieldAffineBase (not_dvd_natCard_normOneSubgroup hp hq.ne_zero hFcard hm) hFcard Q

theorem fieldAffine_sylow_and_centralizers_of_config (hp : p.Prime) (hq : q.Prime) (_hqp : q < p)
    (hFcard : Nat.card F = p ^ q) (hm : m = (p ^ q - 1) / (p - 1))
    (_hcop : Nat.Coprime m (p - 1)) :
    (∀ Q : Sylow p (fieldAffineGroup F (normOneSubgroup F m)),
        (Q : Subgroup (fieldAffineGroup F (normOneSubgroup F m)))
          = fieldAffineBase F (normOneSubgroup F m)) ∧
      (∀ z : F, z ≠ 0 → Subgroup.centralizer
          {(inl (Multiplicative.ofAdd z) : fieldAffineGroup F (normOneSubgroup F m))}
            = fieldAffineBase F (normOneSubgroup F m)) ∧
      (∀ u : normOneSubgroup F m, u ≠ 1 →
        fieldAffineBase F (normOneSubgroup F m) ⊓ Subgroup.centralizer
          {(inr u : fieldAffineGroup F (normOneSubgroup F m))} = ⊥) :=
  have : Fact p.Prime := ⟨hp⟩
  ⟨fun Q => coe_eq_fieldAffineBase
      (not_dvd_natCard_normOneSubgroup hp hq.ne_zero hFcard hm) hFcard Q,
    fun _ hz => centralizer_inl_ofAdd_eq_fieldAffineBase hz,
    fun _ hu => fieldAffineBase_inf_centralizer_inr_eq_bot hu⟩

end Config

end

end CFSG.FeitThompson
