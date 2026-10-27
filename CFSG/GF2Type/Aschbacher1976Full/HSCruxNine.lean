module

public import CFSG.GF2Type.Aschbacher1976Full.HSFiniteDefs
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.GF2Type.Aschbacher1976Full.HSCruxNineK

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.CruxNine

open Equiv

@[expose] def Pres (g : Perm (Fin 6)) : Prop :=
  ∀ x y : Fin 6, ((x : ℕ) < 3 ↔ (y : ℕ) < 3) ↔ (((g x : Fin 6) : ℕ) < 3 ↔ ((g y : Fin 6) : ℕ) < 3)

instance (g : Perm (Fin 6)) : Decidable (Pres g) := by unfold Pres; infer_instance

@[expose] def Nl : List (Perm (Fin 6)) := (Six.allP 6).filter (fun g => decide (Pres g))

theorem mem_Nl {g : Perm (Fin 6)} : g ∈ Nl ↔ Pres g := by
  simp only [Nl, List.mem_filter, Six.mem_allP, decide_eq_true_eq, true_and]

@[expose] def c3 : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def d3 : Perm (Fin 6) := swap 3 4 * swap 4 5

@[expose] def E9l : List (Perm (Fin 6)) :=
  [1, c3, c3 * c3, d3, c3 * d3, c3 * c3 * d3, d3 * d3, c3 * d3 * d3, c3 * c3 * d3 * d3]

@[expose] def nineL : List (Perm (Fin 6)) :=
  [swap 0 1 * swap 3 4, swap 0 1 * swap 3 5, swap 0 1 * swap 4 5,
   swap 0 2 * swap 3 4, swap 0 2 * swap 3 5, swap 0 2 * swap 4 5,
   swap 1 2 * swap 3 4, swap 1 2 * swap 3 5, swap 1 2 * swap 4 5]

@[expose] def fin4 (n : ℕ) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩

@[expose] def lab (c0 c1 c2 : Fin 6) : Fin 4 :=
  fin4 (2 * (if (c0 : ℕ) < 3 then 0 else 1) + (if ((c1 : ℕ) + 6 - (c0 : ℕ)) % 3 = 1 then 0 else 1))

@[expose] def act (g : Perm (Fin 6)) : Fin 4 → Fin 4 :=
  ![lab (g 0) (g 1) (g 2), lab (g 0) (g 2) (g 1), lab (g 3) (g 4) (g 5), lab (g 3) (g 5) (g 4)]

@[expose] def cI : Fin 4 → Fin 4 := act (swap 0 1 * swap 3 4)

theorem E9_one : (1 : Perm (Fin 6)) ∈ E9l := by decide +kernel

theorem E9_mul : ∀ e ∈ E9l, ∀ f ∈ E9l, e * f ∈ E9l := by
  have h : (E9l.map CFSG.Permutation.FinPack.enc == CruxNineK.E9C) = true := by decide +kernel
  exact CruxNineK.mul2_sound h h h CruxNineK.mul_check

theorem E9_inv : ∀ e ∈ E9l, e⁻¹ ∈ E9l := CruxNineK.inv_sound (by decide +kernel)

theorem E9_cube : ∀ e ∈ E9l, e ^ 3 = 1 := CruxNineK.cube_sound (by decide +kernel)

theorem E9_prod : ∀ e ∈ E9l, ∃ s ∈ nineL, ∃ t ∈ nineL, e = s * t :=
  CruxNineK.prod_sound (by decide +kernel) (by decide +kernel)

theorem nineL_prod : ∀ s ∈ nineL, ∀ t ∈ nineL, s * t ∈ E9l := by
  have h : (nineL.map CFSG.Permutation.FinPack.enc == CruxNineK.nineC) = true := by decide +kernel
  exact CruxNineK.mul2_sound h h (by decide +kernel) CruxNineK.nine_mul_check

theorem E9_free : ∀ e ∈ E9l, e ≠ 1 → ∀ s ∈ nineL, e * s ≠ s * e :=
  CruxNineK.free_sound (by decide +kernel) (by decide +kernel)

theorem E9_orbit : ∀ x y : Fin 6, (∃ e ∈ E9l, e x = y) ↔ (((x : ℕ) < 3) ↔ ((y : ℕ) < 3)) := by
  decide +kernel

theorem nineSet_sub_nineL : ∀ a b d e : Fin 6, (a : ℕ) < 3 → (b : ℕ) < 3 → 3 ≤ (d : ℕ) →
    3 ≤ (e : ℕ) → a ≠ b → d ≠ e → swap a b * swap d e ∈ nineL := by
  decide +kernel

theorem nineL_act : ∀ s ∈ nineL, act s = cI := CruxNineK.act_sound (by decide +kernel)

theorem Nl_ker : ∀ g ∈ Nl, act g = id → g ∈ E9l := fun g hg =>
  CruxNineK.ker_sound E9l (by decide +kernel) g (mem_Nl.1 hg)

theorem act_one : act 1 = id := by decide +kernel

theorem act_hom : ∀ g ∈ Nl, ∀ h ∈ Nl, ∀ x : Fin 4, act (g * h) x = act g (act h x) :=
  fun g hg h hh => CruxNineK.hom_sound g (mem_Nl.1 hg) h (mem_Nl.1 hh)

theorem act_sq : ∀ g ∈ Nl, act (g * g) = id ∨ act (g * g) = cI := fun g hg =>
  CruxNineK.sq_sound g (mem_Nl.1 hg)

theorem act_comm : ∀ g ∈ Nl, ∀ h ∈ Nl,
    act (g * h * g⁻¹ * h⁻¹) = id ∨ act (g * h * g⁻¹ * h⁻¹) = cI :=
  fun g hg h hh => CruxNineK.comm_sound g (mem_Nl.1 hg) h (mem_Nl.1 hh)

theorem act_cdep : ∀ g ∈ Nl, ∀ h ∈ Nl, (∀ z : Fin 4, act g (act h z) = act h (act g z)) →
    act g = id ∨ act g = cI ∨ act h = id ∨ act h = cI ∨ act h = act g ∨
      act h = (fun z => act g (cI z)) :=
  fun g hg h hh => CruxNineK.cdep_sound g (mem_Nl.1 hg) h (mem_Nl.1 hh)

end CFSG.GF2Type.Aschbacher1976Full.HS.CruxNine
