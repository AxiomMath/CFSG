module

public import CFSG.FeitThompson.Foundations.NormOneGroupOrder
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.GroupTheory.Complement

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

variable {p q : ℕ} {F : Type*} [Field F]

def botSubfieldUnits (F : Type*) [Field F] : Subgroup Fˣ :=
  (⊥ : Subfield F).toSubring.toSubmonoid.units

theorem mem_botSubfieldUnits {u : Fˣ} : u ∈ botSubfieldUnits F ↔ (u : F) ∈ (⊥ : Subfield F) := by
  refine ⟨fun hu => ((Submonoid.mem_units_iff _ u).1 hu).1, fun hu =>
    Submonoid.mem_units_of_val_mem_inv_val_mem _ hu ?_⟩
  have h1 : ((u⁻¹ : Fˣ) : F) = (u : F)⁻¹ := by simp
  rw [h1]
  exact (⊥ : Subfield F).inv_mem hu

theorem natCard_botSubfieldUnits (hp : p.Prime) (h : Nat.card F = p ^ q) :
    Nat.card (botSubfieldUnits F) = p - 1 := by
  have : Finite F := finite_of_natCard_eq_prime_pow hp h
  have e : (botSubfieldUnits F) ≃* ((⊥ : Subfield F))ˣ := Submonoid.unitsEquivUnitsType _
  rw [Nat.card_congr e.toEquiv, Nat.card_units, natCard_bot_subfield hp h]

theorem isComplement'_botSubfieldUnits_normOneUnits (hp : p.Prime) (h : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    Subgroup.IsComplement' (botSubfieldUnits F) (normOneUnits F) := by
  have : Finite F := finite_of_natCard_eq_prime_pow hp h
  rw [← Nat.geomSum_eq hp.two_le q] at hcop
  refine Subgroup.isComplement'_of_coprime ?_ ?_
  · rw [natCard_botSubfieldUnits hp h, natCard_normOneUnits hp h,
      natCard_units_eq_sub_one_mul_geomSum hp h]
  · rw [natCard_botSubfieldUnits hp h, natCard_normOneUnits hp h]
    exact hcop.symm

theorem disjoint_botSubfieldUnits_normOneUnits (hp : p.Prime) (h : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    Disjoint (botSubfieldUnits F) (normOneUnits F) :=
  (isComplement'_botSubfieldUnits_normOneUnits hp h hcop).disjoint

theorem botSubfieldUnits_sup_normOneUnits (hp : p.Prime) (h : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    botSubfieldUnits F ⊔ normOneUnits F = ⊤ :=
  (isComplement'_botSubfieldUnits_normOneUnits hp h hcop).sup_eq_top

theorem botSubfieldUnits_mul_normOneUnits (hp : p.Prime) (h : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    (botSubfieldUnits F : Set Fˣ) * (normOneUnits F : Set Fˣ) = Set.univ :=
  (Subgroup.isComplement'_def.1
    (isComplement'_botSubfieldUnits_normOneUnits hp h hcop)).mul_eq

theorem existsUnique_units_mul_eq (hp : p.Prime) (h : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) (z : Fˣ) :
    ∃! cu : botSubfieldUnits F × normOneUnits F, (cu.1 : Fˣ) * (cu.2 : Fˣ) = z :=
  (Subgroup.isComplement'_def.1
    (isComplement'_botSubfieldUnits_normOneUnits hp h hcop)).existsUnique z

theorem existsUnique_mul_eq (hp : p.Prime) (h : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) {z : F} (hz : z ≠ 0) :
    ∃! cu : F × F, (cu.1 ∈ (⊥ : Subfield F) ∧ cu.1 ≠ 0) ∧
      (cu.2 ≠ 0 ∧ cu.2 ^ ((p ^ q - 1) / (p - 1)) = 1) ∧ cu.1 * cu.2 = z := by
  obtain ⟨⟨c, u⟩, hcu, huniq⟩ := existsUnique_units_mul_eq hp h hcop (Units.mk0 z hz)
  refine ⟨((c : Fˣ), (u : Fˣ)), ⟨⟨mem_botSubfieldUnits.1 c.2, (c : Fˣ).ne_zero⟩,
    ⟨(u : Fˣ).ne_zero, (mem_normOneUnits_iff_pow_eq_one hp h _).1 u.2⟩,
    congrArg Units.val hcu⟩, ?_⟩
  rintro ⟨d, v⟩ ⟨⟨hd, hd0⟩, ⟨hv0, hv⟩, hdv⟩
  have hd' : Units.mk0 d hd0 ∈ botSubfieldUnits F := mem_botSubfieldUnits.2 hd
  have hv' : Units.mk0 v hv0 ∈ normOneUnits F := (mem_normOneUnits_iff_pow_eq_one hp h _).2 hv
  have key := huniq (⟨Units.mk0 d hd0, hd'⟩, ⟨Units.mk0 v hv0, hv'⟩) (by ext; simpa using hdv)
  exact Prod.ext (congrArg (fun w : botSubfieldUnits F => ((w : Fˣ) : F)) (congrArg Prod.fst key))
    (congrArg (fun w : normOneUnits F => ((w : Fˣ) : F)) (congrArg Prod.snd key))

end

end CFSG.FeitThompson
