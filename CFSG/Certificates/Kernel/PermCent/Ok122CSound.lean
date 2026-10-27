module

public import Certificates.Data.Kernel.PermCent.Ok122C
public import CFSG.Certificates.Kernel.PermCent.AllPermsCSound
public import CFSG.GH74.GLS.C3.Prop121.L122FinInputs

public section

namespace CFSG.Certificates.Kernel.PkCV

open Equiv Equiv.Perm CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2

theorem ite_true_eq (c : Prop) [Decidable c] (x : Bool) :
    (if c then x else true) = (!decide c || x) := by
  by_cases h : c <;> simp [h]

theorem ok122_eq_G : ok122 = ok122G inv7 ord3 swaps7 fun σ => σ.support.card := by
  unfold ok122 ok122G swaps7
  simp only [swap_inv]
  simp only [inV]
  simp only [ite_true_eq, Bool.decide_and, decide_not, Bool.decide_or, Bool.decide_eq_true, List.any_filter,
    List.all_filter, List.all_flatMap, List.all_map, Function.comp_def, swap_inv, Bool.not_and,
    Bool.not_not, Bool.or_assoc]

theorem ok122G_map {G H : Type*} [Group G] [DecidableEq G] [Group H] [DecidableEq H] (f : H → G)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hinv : ∀ a, f a⁻¹ = (f a)⁻¹) (hone : f 1 = 1)
    (hf : Function.Injective f) (I O S : List H) (nm : G → Nat) :
    ok122G (I.map f) (O.map f) (S.map f) nm = ok122G I O S fun σ => nm (f σ) := by
  unfold ok122G
  simp only [List.all_map, List.any_map, List.filter_map, Function.comp_def, ← hmul, ← hinv, ← hone,
    hf.eq_iff]

variable {n : Nat} [Small n]

theorem beq_val (a b : CV n) : Nat.beq a.1 b.1 = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff, Subtype.ext_iff]

theorem cmC_eq (a b : CV n) : cmC a b = decide (a * b = b * a) := eq22C_eq a b b a

theorem inVC_eq (a b t : CV n) :
    inVC a b (a * b) t = decide (t = 1 ∨ t = a ∨ t = b ∨ t = a * b) := by
  rw [inVC, powOneC_eq, pow_one, beq_val, beq_val, beq_val]
  simp only [Bool.decide_or, Bool.or_assoc]

theorem ok122B_eq (I O S : List (CV 7)) :
    ok122B I O S = ok122G I O S fun σ => numMoved (ev σ) := by
  unfold ok122B ok122G
  simp only [forceCL_eq, forceC_eq, inVC_eq, cmC_eq, ← conj_fast, beq_val, Bool.or_assoc]

theorem decide_ev_one (x : CV n) [Decidable (ev x = 1)] : decide (ev x = 1) = decide (x = 1) := by
  simp only [one_eq_ev, ev_eq_iff]

theorem sign_eq_one_iff (σ : Perm (Fin n)) : sign σ = 1 ↔ ¬ sign σ = -1 := by
  rcases Int.units_eq_one_or (sign σ) with h | h <;> rw [h] <;> decide

theorem inv7_eq : inv7 = inv7P.map ev := by
  unfold inv7 inv7P
  rw [allPerms_eq 7 inferInstance, List.filter_map, List.map_map]
  refine congrArg₂ List.map rfl (List.filter_congr fun x hx => ?_)
  rw [Function.comp_apply, par_of_mem_allPermsP hx, powOneC_eq, powOneC_eq, pow_one, pow_two]
  simp only [ev_mul', one_eq_ev, ne_eq, ev_eq_iff, sign_eq_one_iff]
  by_cases h1 : x.1 * x.1 = 1 <;> by_cases h2 : x.1 = 1 <;>
    by_cases h3 : sign (ev x.1) = -1 <;> simp [h1, h2, h3]

theorem ord3_eq : ord3 = ord3P.map ev := by
  unfold ord3 ord3P
  rw [allPerms_eq 7 inferInstance, List.filter_map, List.map_map]
  refine congrArg₂ List.map rfl (List.filter_congr fun x _ => ?_)
  rw [Function.comp_apply, powOneC_eq, powOneC_eq, pow_one, pow_three']
  simp only [ev_mul', one_eq_ev, ev_eq_iff, Bool.decide_and, decide_not]

theorem swaps7_eq : swaps7 = swapsP.map ev := by
  unfold swapsP
  rw [List.map_map]
  simp only [Function.comp_def, ev_cOf, List.map_id']

theorem ok122_eq : ok122 = ok122F := by
  rw [ok122_eq_G, inv7_eq, ord3_eq, swaps7_eq,
    ok122G_map ev ev_mul ev_inv ev_one ev_injective, ok122F, forceCL_eq, forceCL_eq, forceCL_eq,
    ok122B_eq]
  rfl

theorem comm3_eq : (inv7.all fun a => ord3.any fun ρ => decide (ρ * a = a * ρ)) = comm3F := by
  rw [inv7_eq, ord3_eq, comm3F, forceCL_eq, forceCL_eq]
  simp only [List.all_map, List.any_map, Function.comp_def, ev_mul', ev_eq_iff, cmC_eq]

end CFSG.Certificates.Kernel.PkCV

end
