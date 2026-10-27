module

public import CFSG.GH74.Generic.BProg.B2.T4PGVTBasic
import CFSG.GH74.Generic.S1.KL5Ord

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint Subgroup

theorem card_dvd_factorial {k : ℕ} (G : Subgroup (Equiv.Perm (Fin k))) :
    Nat.card ↥G ∣ Nat.factorial k := by
  have h1 : Nat.card ↥G ∣ Nat.card (Equiv.Perm (Fin k)) := Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card (Equiv.Perm (Fin k)) = Nat.factorial k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rwa [h2] at h1

theorem q3_alt (n : ℕ) (hn : n ≤ 11) :
    Q3Empty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n))) := by
  rintro N _ _ H t K hs ⟨e⟩
  have h1 : Nat.card ↥H ∣ Nat.factorial 11 := by
    rw [Nat.card_congr e.toEquiv]
    exact (card_dvd_factorial _).trans (Nat.factorial_dvd_factorial hn)
  exact hs.false_of_dvd ((Subgroup.card_dvd_of_le inf_le_left).trans h1) (by decide)

theorem q3_m11 : Q3Empty (fun X _ => NativeSporadic.IsSporadic X .M11) := by
  rintro N _ _ H t K hs ⟨e⟩
  have h1 : Nat.card ↥H ∣ Nat.factorial 11 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_dvd_factorial NativeSporadic.M11
  exact hs.false_of_dvd ((Subgroup.card_dvd_of_le inf_le_left).trans h1) (by decide)

theorem q3_m12 : Q3Empty (fun X _ => NativeSporadic.IsSporadic X .M12) := by
  rintro N _ _ H t K hs ⟨e⟩
  have h1 : Nat.card ↥H ∣ Nat.factorial 12 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_dvd_factorial NativeSporadic.M12
  exact hs.false_of_dvd ((Subgroup.card_dvd_of_le inf_le_left).trans h1) (by decide)

theorem q3_m22 : Q3Empty (fun X _ => NativeSporadic.IsSporadic X .M22) :=
  fun _ _ _ _ _ _ hs he => hs.false_of_card (card_of_isSporadic_M22 he) (by decide)

theorem q3_m23 : Q3Empty (fun X _ => NativeSporadic.IsSporadic X .M23) :=
  fun _ _ _ _ _ _ hs he => hs.false_of_card (card_of_isSporadic_M23 he) (by decide)

theorem q3_j1 : Q3Empty (fun X _ => NativeSporadic.IsSporadic X .J1) :=
  fun _ _ _ _ _ _ hs he => hs.false_of_card (card_of_isSporadic_J1 he) (by decide)

theorem q3_j2 : Q3Empty (fun X _ => NativeSporadic.IsSporadic X .J2) :=
  fun _ _ _ _ _ _ hs he => hs.false_of_card (card_of_isSporadic_J2 he) (by decide)

theorem q3_j3 : Q3Empty (fun X _ => NativeSporadic.IsSporadic X .J3) :=
  fun _ _ _ _ _ _ hs he => hs.false_of_card (card_of_isSporadic_J3 he) (by decide)

theorem q3_mcl : Q3Empty (fun X _ => NativeSporadic.IsSporadic X .McL) :=
  fun _ _ _ _ _ _ hs he => hs.false_of_card (card_of_isSporadic_McL he) (by decide)

theorem q3_ly : Q3Empty (fun X _ => NativeSporadic.IsSporadic X .Ly) :=
  fun _ _ _ _ _ _ hs he => hs.false_of_card (card_of_isSporadic_Ly he) (by decide)

theorem q3_l28 : Q3Empty (fun X _ => LieModel X .PSL 2 2 3) := fun _ _ _ _ _ _ hs hS =>
  hs.false_of_card (m := 504)
    ((CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hS).trans (by decide)) (by decide)

theorem q3_l216 : Q3Empty (fun X _ => LieModel X .PSL 2 2 4) := fun _ _ _ _ _ _ hs hS =>
  hs.false_of_card (m := 4080)
    ((CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hS).trans (by decide)) (by decide)

theorem q3_l34 : Q3Empty (fun X _ => LieModel X .PSL 3 2 2) := fun _ _ _ _ _ _ hs hS =>
  hs.false_of_card (m := 20160)
    ((CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hS).trans (by decide)) (by decide)

theorem q3_u34 : Q3Empty (fun X _ => LieModel X .PSU 3 2 2) := by
  intro N _ _ H t K hs hS
  have hc := CFSG.GH74.Generic.S1.kl5_card_mul_gcd_psu_three
    (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hS)
  exact hs.false_of_card (m := 62400) (by norm_num at hc; exact hc) (by decide)

theorem q3_sz8 : Q3Empty (fun X _ => LieModel X .twistedB2 0 2 3) := fun _ _ _ _ _ _ hs hS =>
  hs.false_of_card (m := 29120)
    ((CFSG.GH74.card_of_lieModel_twistedB2 hS).trans (by decide)) (by decide)

theorem q3_l3three : Q3Empty (fun X _ => LieModel X .PSL 3 3 1) := by
  intro N _ _ H t K hs hS
  have hc : Nat.card ↥H = 5616 :=
    (CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hS).trans (by decide)
  have h1 := hs.card_cent_lt
  have h2 := Nat.le_of_dvd Nat.card_pos hs.card_dvd_cent
  rw [hs.card_K] at h2
  omega

theorem q3_u3three : Q3Empty (fun X _ => LieModel X .PSU 3 3 1) := fun _ _ _ _ _ _ hs hS =>
  hs.false_of_card (m := 6048)
    ((CFSG.GH74.card_of_lieModel_PSU (n := 3) (by norm_num) (by norm_num) hS).trans (by decide))
    (by decide)

end CFSG.GH74.Generic.BProg.B2.T4.PGV
