module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.Relations

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable def negSet (t : WP) : Finset (Fin 240) :=
  Finset.univ.filter fun r => (t : Equiv.Perm (Fin 240)) r = zPerm r

private theorem cp_mem_negSet {t : WP} {r : Fin 240} :
    r ∈ negSet t ↔ (t : Equiv.Perm (Fin 240)) r = zPerm r := by
  simp [negSet]

private theorem cp_mem_smul_finset_wp {x : WP} {S : Finset (Fin 240)} {r : Fin 240} :
    r ∈ x • S ↔ ((x⁻¹ : WP) : Equiv.Perm (Fin 240)) r ∈ S := by
  conv_lhs => rw [← inv_inv x]
  exact Finset.mem_inv_smul_finset_iff

private theorem cp_coe_zPerm_comm (x : WP) (s : Fin 240) :
    zPerm ((x : Equiv.Perm (Fin 240)) s) = (x : Equiv.Perm (Fin 240)) (zPerm s) := by
  have hx : (x : Equiv.Perm (Fin 240)) ∈ wE8 := (Subgroup.mem_inf.1 x.2).1
  have h := zPerm_comm (x : Equiv.Perm (Fin 240)) hx
  exact (congrArg (fun g : Equiv.Perm (Fin 240) => g s) h).symm

theorem negSet_conj (x t : WP) : negSet (x * t * x⁻¹) = x • negSet t := by
  ext r
  rw [cp_mem_negSet, cp_mem_smul_finset_wp, cp_mem_negSet]
  obtain ⟨s, rfl⟩ : ∃ s, r = (x : Equiv.Perm (Fin 240)) s :=
    ⟨((x⁻¹ : WP) : Equiv.Perm (Fin 240)) r, by simp⟩
  have e : (((x * t * x⁻¹ : WP)) : Equiv.Perm (Fin 240)) ((x : Equiv.Perm (Fin 240)) s) =
      (x : Equiv.Perm (Fin 240)) ((t : Equiv.Perm (Fin 240)) s) := by
    simp
  have e' : ((x⁻¹ : WP) : Equiv.Perm (Fin 240)) ((x : Equiv.Perm (Fin 240)) s) = s := by
    simp
  rw [e, cp_coe_zPerm_comm x s, e']
  exact (x : Equiv.Perm (Fin 240)).injective.eq_iff

theorem centralizer_le_stabilizer (t : WP) :
    Subgroup.centralizer {t} ≤ MulAction.stabilizer WP (negSet t) := by
  intro x hx
  rw [MulAction.mem_stabilizer_iff, ← negSet_conj]
  have h : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.1 hx
  rw [h, mul_inv_cancel_right]

theorem coe_smul_negSet (x t : WP) :
    ((x • negSet t : Finset (Fin 240)) : Set (Fin 240)) =
      (x : Equiv.Perm (Fin 240)) '' (negSet t : Set (Fin 240)) := by
  ext r
  simp only [Finset.coe_smul_finset, Set.mem_smul_set, Set.mem_image, Subgroup.smul_def,
    Equiv.Perm.smul_def]

theorem coe_negSet {m : ℕ} (hm : m < 256 ∧ framePop m % 2 = 0) :
    (negSet (eW m) : Set (Fin 240)) = Om1Facts.neg m := by
  ext r
  simp [negSet, Om1Facts.neg, coe_eW_eq_e hm, zPerm_eq_z]

theorem ncard_orb_negSet {ws : List (List ℕ)} (hws : ∀ w ∈ ws, wordOK w = true) {m : ℕ}
    (hm : m < 256 ∧ framePop m % 2 = 0) :
    (Om1Facts.orb (Om1Facts.G ws) (Om1Facts.neg m)).ncard =
      (MulAction.orbit (closureW ws) (negSet (eW m))).ncard := by
  have e : Om1Facts.orb (Om1Facts.G ws) (Om1Facts.neg m) =
      (fun S : Finset (Fin 240) => (S : Set (Fin 240))) ''
        MulAction.orbit (closureW ws) (negSet (eW m)) := by
    ext S'
    simp only [Om1Facts.orb, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, hx, rfl⟩ := exists_of_mem_G hws hg
      refine ⟨x • negSet (eW m), ⟨⟨x, hx⟩, rfl⟩, ?_⟩
      rw [coe_smul_negSet, coe_negSet hm]
    · rintro ⟨S, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
      refine ⟨x, (mem_closureW_iff hws).1 hx, ?_⟩
      have e2 := coe_smul_negSet x (eW m)
      rw [coe_negSet hm] at e2
      exact e2
  rw [e, Set.ncard_image_of_injective _ Finset.coe_injective]

private theorem cp_card_S0 : Nat.card (closureW wS0) = 4096 := by
  rw [card_closureW (wordOK_of_sub wS0_sub)]
  exact Certificates.certificate197001.2.1.1

private theorem cp_card_P3 : Nat.card (closureW wP3) = 27 := by
  rw [card_closureW (wordOK_of_sub wP3_sub)]
  exact Certificates.certificate197001.2.1.2.1

private theorem cp_card_Sa : Nat.card (closureW wSa) = 2048 := by
  rw [card_closureW (wordOK_of_sub wSa_sub)]
  exact Certificates.certificate197001.2.1.2.2.1

private theorem cp_card_Pa3 : Nat.card (closureW wPa3) = 9 := by
  rw [card_closureW (wordOK_of_sub wPa3_sub)]
  exact Certificates.certificate197001.2.1.2.2.2.1

private theorem cp_card_Pa5 : Nat.card (closureW wPa5) = 5 := by
  rw [card_closureW (wordOK_of_sub wPa5_sub)]
  exact Certificates.certificate197001.2.1.2.2.2.2.1

private theorem cp_card_Sc : Nat.card (closureW wSc) = 1024 := by
  rw [card_closureW (wordOK_of_sub wSc_sub)]
  exact Certificates.certificate197001.2.1.2.2.2.2.2.1

private theorem cp_card_Pc : Nat.card (closureW wPc) = 3 := by
  rw [card_closureW (wordOK_of_sub wPc_sub)]
  exact Certificates.certificate197001.2.1.2.2.2.2.2.2

private theorem cp_orbit_wX {m o : ℕ} (hm : m < 256 ∧ framePop m % 2 = 0)
    (h : o ≤ (Om1Facts.orb (Om1Facts.G wX) (Om1Facts.neg m)).ncard) :
    o ≤ (MulAction.orbit (closureW wX) (negSet (eW m))).ncard :=
  h.trans_eq (ncard_orb_negSet (wordOK_of_sub wX_sub) hm)

private theorem cp_closureW_mono {ws ws' : List (List ℕ)} (h : ∀ w ∈ ws, w ∈ ws') :
    closureW ws ≤ closureW ws' :=
  Subgroup.closure_mono (Set.image_mono fun w hw => h w hw)

private theorem cp_closureW_le {ws : List (List ℕ)} {K : Subgroup WP} (h : ∀ w ∈ ws, wpE w ∈ K) :
    closureW ws ≤ K := by
  rw [closureW, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  exact h w hw

private theorem cp_pkg {C : Subgroup WP} {t : WP} {c o : ℕ}
    (ho : o ≤ (MulAction.orbit (closureW wX) (negSet t)).ncard)
    (hC : C ≤ Subgroup.centralizer {t}) (hc : c ≤ Nat.card C) (hco : c * o = 348364800) :
    C = MulAction.stabilizer WP (negSet t) ∧
      MulAction.orbit (closureW wX) (negSet t) = MulAction.orbit WP (negSet t) ∧
      Nat.card C = c ∧ (MulAction.orbit WP (negSet t)).ncard = o := by
  refine OmGen.stab_eq_of_card (negSet t) C (closureW wX) (hC.trans (centralizer_le_stabilizer t))
    hc ho ?_
  rw [hco]
  exact card_wPlus.le

theorem classPkg0 :
    closureW wT = T0 ∧ T0 = MulAction.stabilizer WP (negSet t0) ∧ Nat.card T0 = 110592 ∧
      Nat.card (closureW wS0) = 4096 ∧ Nat.card (closureW wP3) = 27 ∧
      closureW wS0 ≤ T0 ∧ closureW wP3 ≤ T0 ∧
      MulAction.orbit (closureW wX) (negSet t0) = MulAction.orbit WP (negSet t0) ∧
      (MulAction.orbit WP (negSet t0)).ncard = 3150 := by
  have hCT : closureW wT ≤ T0 := cp_closureW_le fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.2 (comm_t0_of_mem (List.mem_append_left _ hw))
  have hS0C : closureW wS0 ≤ closureW wT :=
    cp_closureW_mono fun w hw => List.mem_append_left _ hw
  have hP3C : closureW wP3 ≤ closureW wT :=
    cp_closureW_mono fun w hw => List.mem_append_right _ hw
  have hdvd : 110592 ∣ Nat.card (closureW wT) := by
    have d1 : 4096 ∣ Nat.card (closureW wT) := cp_card_S0 ▸ Subgroup.card_dvd_of_le hS0C
    have d2 : 27 ∣ Nat.card (closureW wT) := cp_card_P3 ▸ Subgroup.card_dvd_of_le hP3C
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1 d2
  have hc : 110592 ≤ Nat.card (closureW wT) := Nat.le_of_dvd Nat.card_pos hdvd
  obtain ⟨hCeq, horb, hcard, hncard⟩ := cp_pkg (o := 3150) (c := 110592)
    (cp_orbit_wX ⟨by norm_num, by decide⟩ Certificates.certificate197001.2.2.1.1) hCT hc
    (by norm_num)
  have hTeq : T0 = MulAction.stabilizer WP (negSet t0) :=
    le_antisymm (centralizer_le_stabilizer t0) (hCeq.ge.trans hCT)
  have hCT' : closureW wT = T0 := hCeq.trans hTeq.symm
  refine ⟨hCT', hTeq, ?_, cp_card_S0, cp_card_P3, hS0C.trans hCT, hP3C.trans hCT, horb, hncard⟩
  rw [← hCT']
  exact hcard

theorem classPkgA :
    Nat.card (Subgroup.centralizer {ta}) ∣ 2 ^ 11 * 45 ∧ Nat.card (closureW wSa) = 2 ^ 11 ∧
      closureW wSa ≤ Subgroup.centralizer {ta} := by
  have hSaC : closureW wSa ≤ closureW wCa :=
    cp_closureW_mono fun w hw => List.mem_append_left _ (List.mem_append_left _ hw)
  have hPa3C : closureW wPa3 ≤ closureW wCa :=
    cp_closureW_mono fun w hw => List.mem_append_left _ (List.mem_append_right _ hw)
  have hPa5C : closureW wPa5 ≤ closureW wCa :=
    cp_closureW_mono fun w hw => List.mem_append_right _ hw
  have hCa : closureW wCa ≤ Subgroup.centralizer {ta} := cp_closureW_le fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.2 (comm_ta_of_mem hw)
  have hdvd : 92160 ∣ Nat.card (closureW wCa) := by
    have d1 : 2048 ∣ Nat.card (closureW wCa) := cp_card_Sa ▸ Subgroup.card_dvd_of_le hSaC
    have d2 : 9 ∣ Nat.card (closureW wCa) := cp_card_Pa3 ▸ Subgroup.card_dvd_of_le hPa3C
    have d3 : 5 ∣ Nat.card (closureW wCa) := cp_card_Pa5 ▸ Subgroup.card_dvd_of_le hPa5C
    have d12 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2048 9) d1 d2
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime (2048 * 9) 5) d12 d3
  have hc : 92160 ≤ Nat.card (closureW wCa) := Nat.le_of_dvd Nat.card_pos hdvd
  obtain ⟨hCeq, -, hcard, -⟩ := cp_pkg (o := 3780) (c := 92160)
    (cp_orbit_wX ⟨by norm_num, by decide⟩ Certificates.certificate197001.2.2.1.2.1) hCa hc
    (by norm_num)
  refine ⟨?_, by rw [cp_card_Sa]; norm_num, hSaC.trans hCa⟩
  have h1 := Subgroup.card_dvd_of_le (centralizer_le_stabilizer ta)
  rw [← hCeq, hcard] at h1
  simpa using h1

theorem classPkgC :
    Subgroup.centralizer {tc} = closureW wCc ∧ Nat.card (Subgroup.centralizer {tc}) = 2 ^ 10 * 3 ∧
      Nat.card (closureW wSc) = 2 ^ 10 ∧ closureW wSc ≤ Subgroup.centralizer {tc} := by
  have hScC : closureW wSc ≤ closureW wCc :=
    cp_closureW_mono fun w hw => List.mem_append_left _ hw
  have hPcC : closureW wPc ≤ closureW wCc :=
    cp_closureW_mono fun w hw => List.mem_append_right _ hw
  have hCc : closureW wCc ≤ Subgroup.centralizer {tc} := cp_closureW_le fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.2 (comm_tc_of_mem hw)
  have hdvd : 3072 ∣ Nat.card (closureW wCc) := by
    have d1 : 1024 ∣ Nat.card (closureW wCc) := cp_card_Sc ▸ Subgroup.card_dvd_of_le hScC
    have d2 : 3 ∣ Nat.card (closureW wCc) := cp_card_Pc ▸ Subgroup.card_dvd_of_le hPcC
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 1024 3) d1 d2
  have hc : 3072 ≤ Nat.card (closureW wCc) := Nat.le_of_dvd Nat.card_pos hdvd
  obtain ⟨hCeq, -, hcard, -⟩ := cp_pkg (o := 113400) (c := 3072)
    (cp_orbit_wX ⟨by norm_num, by decide⟩ Certificates.certificate197001.2.2.1.2.2) hCc hc
    (by norm_num)
  have hCeq' : Subgroup.centralizer {tc} = closureW wCc :=
    le_antisymm (centralizer_le_stabilizer tc |>.trans hCeq.ge) hCc
  refine ⟨hCeq', ?_, by rw [cp_card_Sc]; norm_num, hScC.trans hCc⟩
  rw [hCeq', hcard]
  norm_num

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1
