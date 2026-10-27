module

public import CFSG.GH74.Uniqueness.SU.SU13TA3Gen
public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup

@[expose] def pa : Perm (Fin 9) := swap 0 1 * swap 0 2

@[expose] def pb : Perm (Fin 9) := swap 3 4 * swap 3 5

@[expose] def pc : Perm (Fin 9) := swap 6 7 * swap 6 8

@[expose] def pw : Perm (Fin 9) :=
  (swap 0 6 * swap 0 3) * (swap 1 7 * swap 1 4) * (swap 2 8 * swap 2 5)

@[expose] def pt : Perm (Fin 9) := (swap 0 3 * swap 1 4) * (swap 2 5 * swap 6 7)

@[expose] def px : Perm (Fin 9) := (swap 0 3 * swap 1 5) * (swap 2 4 * swap 6 7)

theorem pa_pow_three : pa ^ 3 = 1 := by decide

theorem pb_pow_three : pb ^ 3 = 1 := by decide

theorem pc_pow_three : pc ^ 3 = 1 := by decide

theorem sign_pa : Perm.sign pa = 1 := by decide

theorem sign_pb : Perm.sign pb = 1 := by decide

theorem sign_pc : Perm.sign pc = 1 := by decide

theorem sign_pw : Perm.sign pw = 1 := by decide

theorem sign_pt : Perm.sign pt = 1 := by decide

theorem sign_px : Perm.sign px = 1 := by decide

@[expose] def ea : alternatingGroup (Fin 9) := ⟨pa, Perm.mem_alternatingGroup.mpr sign_pa⟩

@[expose] def eb : alternatingGroup (Fin 9) := ⟨pb, Perm.mem_alternatingGroup.mpr sign_pb⟩

@[expose] def ec : alternatingGroup (Fin 9) := ⟨pc, Perm.mem_alternatingGroup.mpr sign_pc⟩

@[expose] def ew : alternatingGroup (Fin 9) := ⟨pw, Perm.mem_alternatingGroup.mpr sign_pw⟩

@[expose] def et : alternatingGroup (Fin 9) := ⟨pt, Perm.mem_alternatingGroup.mpr sign_pt⟩

@[expose] def ex : alternatingGroup (Fin 9) := ⟨px, Perm.mem_alternatingGroup.mpr sign_px⟩

theorem coe_ea : (ea : Perm (Fin 9)) = pa := rfl

theorem coe_eb : (eb : Perm (Fin 9)) = pb := rfl

theorem coe_ec : (ec : Perm (Fin 9)) = pc := rfl

theorem coe_et : (et : Perm (Fin 9)) = pt := rfl

theorem coe_ex : (ex : Perm (Fin 9)) = px := rfl

theorem ea_pow_three : ea ^ 3 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, OneMemClass.coe_one]; exact pa_pow_three)

theorem eb_pow_three : eb ^ 3 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, OneMemClass.coe_one]; exact pb_pow_three)

theorem ec_pow_three : ec ^ 3 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, OneMemClass.coe_one]; exact pc_pow_three)

theorem commute_ea_eb : Commute ea eb := Subtype.ext (by decide)

theorem commute_ea_ec : Commute ea ec := Subtype.ext (by decide)

theorem commute_eb_ec : Commute eb ec := Subtype.ext (by decide)

theorem et_mul_ea : et * ea * et⁻¹ = eb := Subtype.ext (by decide)

theorem et_mul_eb : et * eb * et⁻¹ = ea := Subtype.ext (by decide)

theorem et_mul_ec : et * ec * et⁻¹ = ec⁻¹ := Subtype.ext (by decide)

theorem ex_mul_ea : ex * ea * ex⁻¹ = eb⁻¹ := Subtype.ext (by decide)

theorem ex_mul_eb : ex * eb * ex⁻¹ = ea⁻¹ := Subtype.ext (by decide)

theorem ex_mul_ec : ex * ec * ex⁻¹ = ec⁻¹ := Subtype.ext (by decide)

theorem ew_mul_ea : ew * ea * ew⁻¹ = eb := Subtype.ext (by decide)

theorem ew_mul_eb : ew * eb * ew⁻¹ = ec := Subtype.ext (by decide)

theorem ew_mul_ec : ew * ec * ew⁻¹ = ea := Subtype.ext (by decide)

theorem ec_ne_one : ec ≠ 1 := fun h => by
  have := congrArg (fun x : alternatingGroup (Fin 9) => (x : Perm (Fin 9))) h
  revert this
  decide

theorem isThreeCycle_pa : pa.IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem isThreeCycle_pb : pb.IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem isThreeCycle_pc : pc.IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem disjoint_pa_pb : Equiv.Perm.Disjoint pa pb := fun x => by fin_cases x <;> decide

theorem disjoint_pab_pc : Equiv.Perm.Disjoint (pa * pb) pc := fun x => by
  fin_cases x <;> decide

theorem cycleType_ec : (ec : Perm (Fin 9)).cycleType = {3} := isThreeCycle_pc

theorem cycleType_ea_mul_eb : ((ea * eb : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType =
    {3, 3} := by
  show (pa * pb).cycleType = {3, 3}
  rw [disjoint_pa_pb.cycleType_mul, isThreeCycle_pa.cycleType, isThreeCycle_pb.cycleType]
  rfl

theorem cycleType_ea_mul_eb_mul_ec :
    ((ea * eb * ec : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {3, 3, 3} := by
  show (pa * pb * pc).cycleType = {3, 3, 3}
  rw [disjoint_pab_pc.cycleType_mul, (disjoint_pa_pb.cycleType_mul), isThreeCycle_pa.cycleType,
    isThreeCycle_pb.cycleType, isThreeCycle_pc.cycleType]
  rfl

theorem cycleType_et : (et : Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
  have hd : Equiv.Perm.Disjoint (swap (0 : Fin 9) 3 * swap 1 4) (swap 2 5 * swap 6 7) :=
    fun x => by fin_cases x <;> decide
  show pt.cycleType = {2, 2, 2, 2}
  rw [pt, hd.cycleType_mul, cycleType_swap_mul_swap_of_nodup (by decide),
    cycleType_swap_mul_swap_of_nodup (by decide)]
  rfl

theorem cycleType_ex : (ex : Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
  have hd : Equiv.Perm.Disjoint (swap (0 : Fin 9) 3 * swap 1 5) (swap 2 4 * swap 6 7) :=
    fun x => by fin_cases x <;> decide
  show px.cycleType = {2, 2, 2, 2}
  rw [px, hd.cycleType_mul, cycleType_swap_mul_swap_of_nodup (by decide),
    cycleType_swap_mul_swap_of_nodup (by decide)]
  rfl

theorem cycleType_et_mul_ex : ((et * ex : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType =
    {2, 2} := by
  have h : ((et * ex : alternatingGroup (Fin 9)) : Perm (Fin 9)) = swap 1 2 * swap 4 5 := by
    decide
  rw [h]
  exact cycleType_swap_mul_swap_of_nodup (by decide)

theorem commute_swap_zero_one_pc : Commute (swap (0 : Fin 9) 1) pc := by
  show swap (0 : Fin 9) 1 * pc = pc * swap 0 1
  decide

theorem commute_swap_six_seven_pa_mul_pb : Commute (swap (6 : Fin 9) 7) (pa * pb) := by
  show swap (6 : Fin 9) 7 * (pa * pb) = pa * pb * swap 6 7
  decide

theorem commute_oddThree_pa_mul_pb_mul_pc :
    Commute (swap (0 : Fin 9) 3 * swap 1 4 * swap 2 5) (pa * pb * pc) := by
  show swap (0 : Fin 9) 3 * swap 1 4 * swap 2 5 * (pa * pb * pc) =
    pa * pb * pc * (swap 0 3 * swap 1 4 * swap 2 5)
  decide

theorem card_centralizer_ec :
    Nat.card (centralizer ({ec} : Set (alternatingGroup (Fin 9)))) = 1080 := by
  have h := card_centralizer_alternatingGroup (g := ec) (ρ := swap 0 1)
    (Perm.sign_swap (by decide)) commute_swap_zero_one_pc
  have h2 : Nat.card (centralizer ({(ec : Perm (Fin 9))} : Set (Perm (Fin 9)))) = 2160 := by
    rw [nat_card_centralizer, cycleType_ec]
    simp [Nat.factorial]
  omega

theorem card_centralizer_ea_mul_eb :
    Nat.card (centralizer ({ea * eb} : Set (alternatingGroup (Fin 9)))) = 54 := by
  have h := card_centralizer_alternatingGroup (g := ea * eb) (ρ := swap 6 7)
    (Perm.sign_swap (by decide)) commute_swap_six_seven_pa_mul_pb
  have h2 : Nat.card (centralizer ({((ea * eb : alternatingGroup (Fin 9)) : Perm (Fin 9))} :
      Set (Perm (Fin 9)))) = 108 := by
    rw [nat_card_centralizer, cycleType_ea_mul_eb]
    simp [Nat.factorial]
  omega

theorem card_centralizer_ea_mul_eb_mul_ec :
    Nat.card (centralizer ({ea * eb * ec} : Set (alternatingGroup (Fin 9)))) = 81 := by
  have h := card_centralizer_alternatingGroup (g := ea * eb * ec)
    (ρ := swap 0 3 * swap 1 4 * swap 2 5) (by decide) commute_oddThree_pa_mul_pb_mul_pc
  have h2 : Nat.card (centralizer ({((ea * eb * ec : alternatingGroup (Fin 9)) :
      Perm (Fin 9))} : Set (Perm (Fin 9)))) = 162 := by
    rw [nat_card_centralizer, cycleType_ea_mul_eb_mul_ec]
    simp [Nat.factorial]
  omega

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
