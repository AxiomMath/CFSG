module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.E32Orbits
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.Short
public import Certificates.Certificate27586

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Certificates.Native
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour
  Certificates.TitsAschbacherE32 Certificates.TitsAschbacherNLocal
open CFSG.Quasithin (tπ twoF4N twoF4S)

theorem nlocCheck_eq_true : nlocCheck () = true :=
  Certificates.certificate27586

theorem nlocCheck_parts :
    inK (compA 1755 CFSG.Quasithin.titsPiArr CFSG.Quasithin.titsPiArr) = true ∧
      kWords.all (fun w => lettersIn 1 12 w && inK (vProd w)) = true ∧
      eqA 1755 (compA 1755 (vProd [4, 5]) (vA 10))
        (compA 1755 (compA 1755 (vA 12) (vA 10)) (vProd [4, 5])) = true ∧
      eqA 1755 (compA 1755 (vProd [1, 5]) (vA 10))
        (compA 1755 (compA 1755 (vA 11) (vA 10)) (vProd [1, 5])) = true ∧
      (List.range 32).all (fun m => m % 8 == 0 ||
        kWords.any fun w => !commA (fA m) (vProd w)) = true ∧
      (List.range 32).all (fun m => m % 4 == 0 ||
        kWords.any fun w => !commInU11 (fA m) (vProd w)) = true ∧
      nLetters Certificates.TitsAschbacherNLocal.yWord = true ∧
      isInvA 1755 (yArr ()) (invCand 1755 (yArr ())) = true ∧
      eqA 1755 (powA (yArr ()) 3) (idA 1755) = true ∧ (!eqA 1755 (yArr ()) (idA 1755)) = true ∧
      commA (yArr ()) (vA 10) = true ∧ conjEqA (yArr ()) (vA 12) (vA 11) = true ∧
      conjEqA (yArr ()) (compA 1755 (vA 11) (vA 12)) (vA 12) = true ∧
      (List.range 32).all (fun m => m % 4 == 0 || !commInU10 (yArr ()) (fA m)) = true ∧
      all5 1755 titsKLevels
        (fun k => cTest k && cTest (compA 1755 k CFSG.Quasithin.titsPiArr)) = true ∧
      all5 1755 titsSLevels (fun s => tTest (invCand 1755 (yArr ())) (yArr ()) s &&
        tTest (invCand 1755 (yArr ())) (yArr ()) (compA 1755 s CFSG.Quasithin.titsPiArr)) =
        true := by
  have h := nlocCheck_eq_true
  unfold nlocCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem fBits_eleven_bound : ∀ m < 32, m % 8 = 0 → ∀ i ∈ fBits m, 11 ≤ i ∧ i ≤ 12 := by
  decide

theorem fBits_ten_bound : ∀ m < 32, m % 4 = 0 → ∀ i ∈ fBits m, 10 ≤ i ∧ i ≤ 12 := by decide

theorem fBits_four_mul : ∀ i < 8, fBits (4 * i) = u10Bits i := by decide

theorem u10Bits_even : ∀ m < 8, m % 2 = 0 → ∀ i ∈ u10Bits m, 11 ≤ i ∧ i ≤ 12 := by decide

theorem u10Bits_odd : ∀ m < 8, m % 2 = 1 → u10Bits m = 10 :: u10Bits (m - 1) := by decide

theorem kWords_bound : ∀ w ∈ kWords, ∀ i ∈ w, i < 13 := by decide

theorem fElt_four_mul {i : ℕ} (hi : i < 8) : fElt (4 * i) = u10Elt i := by
  rw [fElt, u10Elt, fBits_four_mul i hi]

theorem fElt_mem_parrottU_eleven {m : ℕ} (hm : m < 32) (h8 : m % 8 = 0) :
    fElt m ∈ parrottU 11 :=
  prod_mem_parrottU (fBits_eleven_bound m hm h8)

theorem fElt_mem_parrottU_ten {m : ℕ} (hm : m < 32) (h4 : m % 4 = 0) : fElt m ∈ parrottU 10 :=
  prod_mem_parrottU (fBits_ten_bound m hm h4)

theorem parrottV_mem_parrottF {i : ℕ} (hi : i ∈ ({7, 9, 10, 11, 12} : Set ℕ)) :
    parrottV i ∈ parrottF :=
  subset_closure ⟨i, hi, rfl⟩

theorem parrottU_eleven_le_ten : parrottU 11 ≤ parrottU 10 :=
  closure_mono (Set.image_mono fun i hi => ⟨by have := hi.1; omega, hi.2⟩)

theorem parrottU_ten_le_parrottF : parrottU 10 ≤ parrottF := by
  rw [parrottU, closure_le]
  rintro _ ⟨i, ⟨h1, h2⟩, rfl⟩
  apply parrottV_mem_parrottF
  have : i = 10 ∨ i = 11 ∨ i = 12 := by omega
  rcases this with rfl | rfl | rfl <;> simp

theorem parrottU_ten_le_titsD
    : parrottU 10 ≤ titsD :=
  parrottU_ten_le_parrottF.trans parrottF_le_titsD

theorem parrottV_eleven_twelve
    : parrottV 11 * parrottV 11 = 1 ∧ parrottV 12 * parrottV 12 = 1 ∧
      parrottV 11 * parrottV 12 = parrottV 12 * parrottV 11 :=
  ⟨parrottF_elemAbelian.2 _ (parrottV_mem_parrottF (by simp)),
    parrottF_elemAbelian.2 _ (parrottV_mem_parrottF (by simp)),
    parrottF_elemAbelian.1 _ (parrottV_mem_parrottF (by simp)) _
      (parrottV_mem_parrottF (by simp))⟩

theorem mem_parrottU_eleven_iff
    {x : Equiv.Perm (Fin 1755)} :
    x ∈ parrottU 11 ↔
      x = 1 ∨ x = parrottV 11 ∨ x = parrottV 12 ∨ x = parrottV 11 * parrottV 12 := by
  obtain ⟨h1, h2, h12⟩ := parrottV_eleven_twelve
  have e : Set.Icc 11 12 = ({11, 12} : Set ℕ) := by
    ext i
    simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rw [parrottU, e, Set.image_pair]
  exact CFSG.LocalAnalysis.EvenBN.Tits.mem_closure_pair_iff h1 h2 h12

theorem mem_parrottU_eleven_iff_fElt
    {x : Equiv.Perm (Fin 1755)} : x ∈ parrottU 11 ↔ ∃ j ∈ [0, 8, 16, 24], fElt j = x := by
  obtain ⟨-, -, -, -, -, e0, e16, e8, e24, -, -⟩ := elt_values
  rw [mem_parrottU_eleven_iff]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, by simp, e0⟩, ⟨8, by simp, e8⟩, ⟨16, by simp, e16⟩, ⟨24, by simp, e24⟩]
  · rintro ⟨j, hj, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    exacts [Or.inl e0, Or.inr (Or.inl e8), Or.inr (Or.inr (Or.inl e16)),
      Or.inr (Or.inr (Or.inr e24))]

theorem parrottU_ten_cases
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ parrottU 10) :
    x ∈ parrottU 11 ∨ ∃ u ∈ parrottU 11, x = parrottV 10 * u := by
  obtain ⟨m, hm, rfl⟩ := mem_parrottU_ten_iff.1 hx
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · exact Or.inl (prod_mem_parrottU (u10Bits_even m hm h))
  · refine Or.inr ⟨u10Elt (m - 1),
      prod_mem_parrottU (u10Bits_even (m - 1) (by omega) (by omega)), ?_⟩
    rw [u10Elt, u10Elt, u10Bits_odd m hm h, List.map_cons, List.prod_cons]

theorem card_parrottU_eleven
    : Nat.card (parrottU 11) = 4 := by
  have hmem : ∀ j : Fin 4, fElt (8 * j) ∈ parrottU 11 := fun j =>
    fElt_mem_parrottU_eleven (by have := j.2; omega) (by omega)
  let f : Fin 4 → parrottU 11 := fun j => ⟨fElt (8 * j), hmem j⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => Fin.ext ?_, fun x => ?_⟩
    · have := fElt_injOn (by have := a.2; omega) (by have := b.2; omega)
        (congrArg Subtype.val hab)
      omega
    · obtain ⟨j, hj, hjx⟩ := mem_parrottU_eleven_iff_fElt.1 x.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      have hj' : ∃ k : Fin 4, 8 * (k : ℕ) = j := by
        rcases hj with rfl | rfl | rfl | rfl
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
      obtain ⟨k, hk⟩ := hj'
      exact ⟨k, Subtype.ext (by simp only [f]; rw [hk, hjx])⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_fin]

theorem card_parrottU_ten
    : Nat.card (parrottU 10) = 8 := by
  have hmem : ∀ i : Fin 8, u10Elt i ∈ parrottU 10 := fun i =>
    mem_parrottU_ten_iff.2 ⟨i, i.2, rfl⟩
  let f : Fin 8 → parrottU 10 := fun i => ⟨u10Elt i, hmem i⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => Fin.ext ?_, fun x => ?_⟩
    · have e : fElt (4 * a) = fElt (4 * b) := by
        rw [fElt_four_mul a.2, fElt_four_mul b.2]
        exact congrArg Subtype.val hab
      have := fElt_injOn (by have := a.2; omega) (by have := b.2; omega) e
      omega
    · obtain ⟨m, hm, hmx⟩ := mem_parrottU_ten_iff.1 x.2
      exact ⟨⟨m, hm⟩, Subtype.ext hmx⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_fin]

theorem parrottV_ne
    : parrottV 11 ≠ 1 ∧ parrottV 12 ≠ 1 ∧ parrottV 11 ≠ parrottV 12 ∧
      parrottV 10 ∉ parrottU 11 := by
  obtain ⟨-, -, -, -, -, e0, e16, e8, -, e4, -⟩ := elt_values
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := fElt_injOn (a := 8) (b := 0) (by norm_num) (by norm_num) (by rw [e8, e0, h])
    omega
  · have := fElt_injOn (a := 16) (b := 0) (by norm_num) (by norm_num) (by rw [e16, e0, h])
    omega
  · have := fElt_injOn (a := 8) (b := 16) (by norm_num) (by norm_num) (by rw [e8, e16, h])
    omega
  · obtain ⟨j, hj, hjx⟩ := mem_parrottU_eleven_iff_fElt.1 h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    have hj32 : j < 32 := by omega
    have := fElt_injOn (a := j) (b := 4) hj32 (by norm_num) (by rw [hjx, e4])
    omega

theorem tπ_mul_self_mem_titsK
    : tπ * tπ ∈ titsK :=
  (mem_titsK_iff_sift (rep_compA CFSG.Quasithin.tπ_rep CFSG.Quasithin.tπ_rep)).1
    nlocCheck_parts.1

@[expose] noncomputable def hatC
    : Subgroup (Equiv.Perm (Fin 1755)) :=
  CFSG.Quasithin.extSub titsK tπ CFSG.Quasithin.tπ_norm_K tπ_mul_self_mem_titsK

theorem mem_hatC_iff
    {x : Equiv.Perm (Fin 1755)} : x ∈ hatC ↔ x ∈ titsK ∨ x * tπ⁻¹ ∈ titsK :=
  Iff.rfl

theorem titsK_le_hatC
    : titsK ≤ hatC :=
  CFSG.Quasithin.le_extSub

theorem hatC_le_twoF4S
    : hatC ≤ twoF4S :=
  CFSG.Quasithin.extSub_mono titsK_le_titsS

theorem hatC_inf_titsD
    : hatC ⊓ titsD = titsK :=
  le_antisymm (fun _ hx => CFSG.Quasithin.mem_of_mem_extSub_of_mem_D titsK_le_titsD hx.1 hx.2)
    (le_inf titsK_le_hatC titsK_le_titsD)

theorem card_hatC
    : Nat.card hatC = 2048 := by
  have h := relIndex_mul_card titsK hatC
  have h2 : titsK.relIndex hatC = 2 :=
    CFSG.Quasithin.relIndex_extSub fun h => CFSG.Quasithin.tπ_not_mem_D (titsK_le_titsD h)
  have h3 : titsK ⊓ hatC = titsK := inf_of_le_left titsK_le_hatC
  rw [h2, h3, titsQK_facts.2.2.2] at h
  exact h.symm

@[expose] noncomputable def nlocY : Equiv.Perm (Fin 1755) :=
  nElt Certificates.TitsAschbacherNLocal.yWord

theorem rep_nlocY
    : Rep 1755 (yArr ()) nlocY :=
  (rep_nElt nlocCheck_parts.2.2.2.2.2.2.1).1

theorem nlocY_facts
    : nlocY ∈ titsN ∧ nlocY ^ 3 = 1 ∧ nlocY ≠ 1 ∧
      nlocY * parrottV 10 = parrottV 10 * nlocY ∧
      nlocY * parrottV 11 * nlocY⁻¹ = parrottV 12 ∧
      nlocY * parrottV 12 * nlocY⁻¹ = parrottV 11 * parrottV 12 := by
  obtain ⟨-, -, -, -, -, -, h7, -, h9, h10, h11, h12, h13, -⟩ := nlocCheck_parts
  have ry := rep_nlocY
  have r10 := rep_vA (i := 10) (by norm_num)
  have r11 := rep_vA (i := 11) (by norm_num)
  have r12 := rep_vA (i := 12) (by norm_num)
  refine ⟨nArr_mem h7, eq_of_eqA (rep_powA ry 3) rep_idA h9, fun he => ?_,
    (commA_iff ry r10).1 h11, ?_, ?_⟩
  · rw [(eqA_iff ry rep_idA).2 he] at h10
    exact absurd h10 (by decide)
  · have e := eq_of_eqA (rep_compA r12 ry) (rep_compA ry r11) h12
    rw [← e, mul_inv_cancel_right]
  · have e := eq_of_eqA (rep_compA (rep_compA r11 r12) ry) (rep_compA ry r12) h13
    rw [← e, mul_inv_cancel_right]

theorem kWords_mem_titsK
    : ∀ w ∈ kWords, (w.map parrottV).prod ∈ titsK := by
  intro w hw
  have h := List.all_eq_true.1 nlocCheck_parts.2.1 w hw
  rw [Bool.and_eq_true] at h
  exact (mem_titsK_iff_sift (rep_vProd (kWords_bound w hw))).1 h.2

theorem kElt_facts
    : parrottV 4 * parrottV 5 * parrottV 10 * (parrottV 4 * parrottV 5)⁻¹ =
        parrottV 12 * parrottV 10 ∧
      parrottV 1 * parrottV 5 * parrottV 10 * (parrottV 1 * parrottV 5)⁻¹ =
        parrottV 11 * parrottV 10 := by
  obtain ⟨-, -, h3, h4, -⟩ := nlocCheck_parts
  have r45 : Rep 1755 (vProd [4, 5]) (parrottV 4 * parrottV 5) := by
    simpa using rep_vProd (l := [4, 5]) (by decide)
  have r15 : Rep 1755 (vProd [1, 5]) (parrottV 1 * parrottV 5) := by
    simpa using rep_vProd (l := [1, 5]) (by decide)
  have r10 := rep_vA (i := 10) (by norm_num)
  have r11 := rep_vA (i := 11) (by norm_num)
  have r12 := rep_vA (i := 12) (by norm_num)
  have e1 := eq_of_eqA (rep_compA r45 r10) (rep_compA (rep_compA r12 r10) r45) h3
  have e2 := eq_of_eqA (rep_compA r15 r10) (rep_compA (rep_compA r11 r10) r15) h4
  exact ⟨by rw [e1, mul_inv_cancel_right], by rw [e2, mul_inv_cancel_right]⟩

theorem mem_parrottU_eleven_of_comm
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ parrottF)
    (hc : ∀ w ∈ kWords, x * (w.map parrottV).prod = (w.map parrottV).prod * x) :
    x ∈ parrottU 11 := by
  obtain ⟨m, hm, rfl⟩ := mem_parrottF_iff.1 hx
  have h := List.all_eq_true.1 nlocCheck_parts.2.2.2.2.1 m (List.mem_range.2 hm)
  rw [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact fElt_mem_parrottU_eleven hm h
  · exfalso
    obtain ⟨w, hw, hcw⟩ := List.any_eq_true.1 h
    have hc' : commA (fA m) (vProd w) = true :=
      (commA_iff (rep_fArrs hm) (rep_vProd (kWords_bound w hw))).2 (hc w hw)
    rw [hc'] at hcw
    exact absurd hcw (by decide)

theorem mem_parrottU_ten_of_comm
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ parrottF)
    (hc : ∀ w ∈ kWords,
      (w.map parrottV).prod * x * ((w.map parrottV).prod)⁻¹ * x⁻¹ ∈ parrottU 11) :
    x ∈ parrottU 10 := by
  obtain ⟨m, hm, rfl⟩ := mem_parrottF_iff.1 hx
  have h := List.all_eq_true.1 nlocCheck_parts.2.2.2.2.2.1 m (List.mem_range.2 hm)
  rw [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact fElt_mem_parrottU_ten hm h
  · exfalso
    obtain ⟨w, hw, hcw⟩ := List.any_eq_true.1 h
    have rk : Rep 1755 (vProd w) (w.map parrottV).prod := rep_vProd (kWords_bound w hw)
    obtain ⟨j, hj, hju⟩ := mem_parrottU_eleven_iff_fElt.1 (inv_mem (hc w hw))
    have hj32 : j < 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      omega
    have e : fElt m * (w.map parrottV).prod = fElt j * (w.map parrottV).prod * fElt m := by
      rw [hju]
      group
    have hc' : commInU11 (fA m) (vProd w) = true := List.any_eq_true.2 ⟨j, hj,
      (eqA_iff (rep_compA (rep_fArrs hm) rk)
        (rep_compA (rep_compA (rep_fArrs hj32) rk) (rep_fArrs hm))).2 e⟩
    rw [hc'] at hcw
    exact absurd hcw (by decide)

theorem nlocY_comm_not_mem
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ parrottF) (hx10 : x ∉ parrottU 10) :
    nlocY * x * nlocY⁻¹ * x⁻¹ ∉ parrottU 10 := by
  obtain ⟨m, hm, rfl⟩ := mem_parrottF_iff.1 hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14, -⟩ := nlocCheck_parts
  have h := List.all_eq_true.1 h14 m (List.mem_range.2 hm)
  rw [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact absurd (fElt_mem_parrottU_ten hm h) hx10
  · intro hu
    obtain ⟨i, hi, hiu⟩ := mem_parrottU_ten_iff.1 hu
    have e : nlocY * fElt m = fElt (4 * i) * fElt m * nlocY := by
      rw [fElt_four_mul hi, hiu]
      group
    have hc' : commInU10 (yArr ()) (fA m) = true := List.any_eq_true.2 ⟨i, List.mem_range.2 hi,
      (eqA_iff (rep_compA rep_nlocY (rep_fArrs hm))
        (rep_compA (rep_compA (rep_fArrs (by omega)) (rep_fArrs hm)) rep_nlocY)).2 e⟩
    rw [hc'] at h
    exact absurd h (by decide)

theorem chainArrays_titsK :
    ChainArrays titsQK (titsKArrs.extract 0 2) titsKArrs (baseArr 1755 titsKBase)
      (wordsArr 2 7 titsKDerivations) :=
  chainArrays_ofArrays' titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsQK_baseCount : titsQK.baseCount = 5 := by
  show (finList 1755 titsKBase).length = 5
  simp [finList, titsKBase]

theorem hatC_comm_mem
    {c : Equiv.Perm (Fin 1755)} (hc : c ∈ hatC) (h10 : c * parrottV 10 = parrottV 10 * c)
    (h11 : c * parrottV 11 = parrottV 11 * c) (h12 : c * parrottV 12 = parrottV 12 * c)
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ parrottF) : c * x * c⁻¹ * x⁻¹ ∈ parrottU 11 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, -⟩ := nlocCheck_parts
  have key : ∃ a, Rep 1755 a c ∧ cTest a = true := by
    rcases hc with hcK | hcK
    · have hQ : c ∈ titsQK.originalSubgroup := by
        rw [titsQK_facts.2.2.1]
        exact hcK
      obtain ⟨a, ha, hp⟩ := all5_spec chainArrays_titsK (by norm_num : 0 < 4)
        titsLocalChains_check.2.2.2.2.1 titsQK_baseCount h15 hQ
      rw [Bool.and_eq_true] at hp
      exact ⟨a, ha, hp.1⟩
    · have hQ : c * tπ⁻¹ ∈ titsQK.originalSubgroup := by
        rw [titsQK_facts.2.2.1]
        exact hcK
      obtain ⟨a, ha, hp⟩ := all5_spec chainArrays_titsK (by norm_num : 0 < 4)
        titsLocalChains_check.2.2.2.2.1 titsQK_baseCount h15 hQ
      rw [Bool.and_eq_true] at hp
      have hrep := rep_compA ha CFSG.Quasithin.tπ_rep
      rw [inv_mul_cancel_right] at hrep
      exact ⟨_, hrep, hp.2⟩
  obtain ⟨a, ha, hca⟩ := key
  have hcomm : (commA a (vA 10) && commA a (vA 11) && commA a (vA 12)) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨(commA_iff ha (rep_vA (by norm_num))).2 h10,
      (commA_iff ha (rep_vA (by norm_num))).2 h11⟩, (commA_iff ha (rep_vA (by norm_num))).2 h12⟩
  unfold cTest at hca
  rw [hcomm, Bool.not_true, Bool.false_or] at hca
  have hgen : ∀ j ∈ ({7, 9, 10, 11, 12} : Set ℕ),
      c * parrottV j * c⁻¹ * (parrottV j)⁻¹ ∈ parrottU 11 := by
    intro j hj
    have hjl : j ∈ [7, 9, 10, 11, 12] := by
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp
    have hj13 : j < 13 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hjl
      omega
    obtain ⟨i, hi, hie⟩ := List.any_eq_true.1 (List.all_eq_true.1 hca j hjl)
    have hi32 : i < 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    have e := eq_of_eqA (rep_compA ha (rep_vA hj13))
      (rep_compA (rep_compA (rep_fArrs hi32) (rep_vA hj13)) ha) hie
    have e' : c * parrottV j * c⁻¹ * (parrottV j)⁻¹ = fElt i := by
      rw [e]
      group
    rw [e']
    exact mem_parrottU_eleven_iff_fElt.2 ⟨i, hi, rfl⟩
  have hF : ((closure (parrottV '' {7, 9, 10, 11, 12}) : Subgroup _) : Set _) ⊆
      {x | x ∈ parrottF ∧ c * x * c⁻¹ * x⁻¹ ∈ parrottU 11} := by
    apply closure_subset_of_mul_mem
    · exact ⟨one_mem _, by simp⟩
    · rintro a ⟨haF, haU⟩ b ⟨hbF, hbU⟩
      refine ⟨mul_mem haF hbF, ?_⟩
      have hab : a * (c * b * c⁻¹ * b⁻¹) = (c * b * c⁻¹ * b⁻¹) * a :=
        parrottF_elemAbelian.1 _ haF _ (parrottU_ten_le_parrottF (parrottU_eleven_le_ten hbU))
      have e : c * (a * b) * c⁻¹ * (a * b)⁻¹ =
          (c * a * c⁻¹ * a⁻¹) * (a * (c * b * c⁻¹ * b⁻¹) * a⁻¹) := by
        group
      rw [e, hab, mul_inv_cancel_right]
      exact mul_mem haU hbU
    · rintro _ ⟨j, hj, rfl⟩
      exact ⟨parrottV_mem_parrottF hj, hgen j hj⟩
  exact (hF hx).2

theorem mem_hatC_of_conj
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ twoF4S) (hy : nlocY⁻¹ * x * nlocY ∈ twoF4S) :
    x ∈ hatC := by
  obtain ⟨-, -, -, -, -, -, -, h8, -, -, -, -, -, -, -, h16⟩ := nlocCheck_parts
  have ry := rep_nlocY
  have ryi : Rep 1755 (invCand 1755 (yArr ())) nlocY⁻¹ := rep_inv_of_isInvA ry h8
  have key : ∀ {a : Array ℕ} {s : Equiv.Perm (Fin 1755)}, Rep 1755 a s →
      tTest (invCand 1755 (yArr ())) (yArr ()) a = true → nlocY⁻¹ * s * nlocY ∈ twoF4S →
      s ∈ hatC := by
    intro a s ha ht hs
    unfold tTest at ht
    rw [Bool.or_eq_true, Bool.or_eq_true] at ht
    rcases ht with (ht | ht) | ht
    · exfalso
      unfold notInT at ht
      rw [Bool.and_eq_true] at ht
      have r1 := rep_compA (rep_compA ryi ha) ry
      rcases hs with hs | hs
      · rw [(mem_titsS_iff_sift r1).2 hs] at ht
        exact absurd ht.1 (by decide)
      · rw [(mem_titsS_iff_sift (rep_compA r1 CFSG.Quasithin.tπ_inv_rep)).2 hs] at ht
        exact absurd ht.2 (by decide)
    · exact Or.inl ((mem_titsK_iff_sift ha).1 ht)
    · exact Or.inr ((mem_titsK_iff_sift (rep_compA ha CFSG.Quasithin.tπ_inv_rep)).1 ht)
  rcases hx with hxS | hxS
  · have hQ : x ∈ titsQS.originalSubgroup := by
      rw [titsQS_facts.2.2.1]
      exact hxS
    obtain ⟨a, ha, hp⟩ := all5_spec titsS_chainArrays (by norm_num : 0 < 4)
      titsLocalChains_check.2.1 CFSG.Quasithin.titsQS_baseCount h16 hQ
    rw [Bool.and_eq_true] at hp
    exact key ha hp.1 hy
  · have hQ : x * tπ⁻¹ ∈ titsQS.originalSubgroup := by
      rw [titsQS_facts.2.2.1]
      exact hxS
    obtain ⟨a, ha, hp⟩ := all5_spec titsS_chainArrays (by norm_num : 0 < 4)
      titsLocalChains_check.2.1 CFSG.Quasithin.titsQS_baseCount h16 hQ
    rw [Bool.and_eq_true] at hp
    have hrep := rep_compA ha CFSG.Quasithin.tπ_rep
    rw [inv_mul_cancel_right] at hrep
    exact key hrep hp.2 hy

end CFSG.LocalAnalysis.EvenBN.Tits.Model
