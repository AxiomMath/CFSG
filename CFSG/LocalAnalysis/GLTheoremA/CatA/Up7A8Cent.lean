module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112DiagChev

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open CFSG.LocalAnalysis.GLTheoremA.AltDown
open scoped commutatorElement

theorem up7a8_comm_mul_central {T : Type} [Group T] {a b z w : T}
    (hz : z ∈ Subgroup.center T) (hw : w ∈ Subgroup.center T) :
    ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz1 : ∀ g : T, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  have hw1 : ∀ g : T, g * w = w * g := fun g => Subgroup.mem_center_iff.1 hw g
  have hz2 : ∀ g : T, g * z⁻¹ = z⁻¹ * g := fun g => Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hz) g
  have hw2 : ∀ g : T, g * w⁻¹ = w⁻¹ * g := fun g => Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hw) g
  have hconj : z⁻¹ * w * z = w := by rw [mul_assoc, hz1 w, inv_mul_cancel_left]
  have key : ∀ X : T, w⁻¹ * (z⁻¹ * (w * (z * X))) = X := by
    intro X
    have : w⁻¹ * (z⁻¹ * (w * (z * X))) = w⁻¹ * ((z⁻¹ * w * z) * X) := by simp only [mul_assoc]
    rw [this, hconj, inv_mul_cancel_left]
  simp only [commutatorElement_def, mul_inv_rev, ← mul_assoc]
  simp only [hz1, hw1, hz2, hw2, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel,
    mul_inv_cancel, mul_one, one_mul]
  exact key _

theorem up7a8_eq_top_of_sup_center {T : Type} [Group T] (hT : commutator T = ⊤)
    {H : Subgroup T} (hH : H ⊔ Subgroup.center T = ⊤) : H = ⊤ := by
  have hsup : ∀ x : T, ∃ h ∈ H, ∃ z ∈ Subgroup.center T, h * z = x := fun x => by
    have hx : x ∈ H ⊔ Subgroup.center T := hH ▸ Subgroup.mem_top x
    exact Subgroup.mem_sup_of_normal_right.1 hx
  refine eq_top_iff.2 ?_
  rw [← hT]
  refine Subgroup.commutator_le.2 fun x _ y _ => ?_
  obtain ⟨h1, hh1, z1, hz1, rfl⟩ := hsup x
  obtain ⟨h2, hh2, z2, hz2, rfl⟩ := hsup y
  rw [up7a8_comm_mul_central hz1 hz2, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hh1 hh2) (H.inv_mem hh1)) (H.inv_mem hh2)

theorem up7a8_fixSubgroup_one {T : Type} [Group T] : fixSubgroup (1 : MulAut T) = ⊤ := by
  ext g
  simp [mem_fixSubgroup]

theorem up7a8_top_of_centMod {G : Type} [Group G] [Finite G] {X K J : Subgroup G} {y : G}
    (hK : GLAPComponent 3 X K) (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hyp : y ^ 3 = 1)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J) (hCM : CentMod 3 K y) :
    imageMod 3 K J = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hap : IsPGroup 3 (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  have hα : chevAut 3 K ⟨y, hyN⟩ = 1 := (chevAut_eq_one_iff Nat.prime_three hK hyN).2 hCM
  have hJ' := glaPComponent_chevTransfer Nat.prime_three hyN hap hJ
  rw [hα, up7a8_fixSubgroup_one] at hJ'
  haveI : IsSimpleGroup (PSimple 3 K) := (chev_pSimple_simple_nonabelian Nat.prime_three hK).1
  haveI : IsSimpleGroup ↥(⊤ : Subgroup (PSimple 3 K)) := Subgroup.topEquiv.isSimpleGroup
  have hJ'top : chevTransfer 3 K J = ⊤ := by
    have hne : chevTransfer 3 K J ≠ ⊥ := by
      intro h
      have hnt := nontrivial_of_glaPComponent Nat.prime_three hJ'
      rw [h] at hnt
      exact not_nontrivial _ hnt
    exact eq_of_isSubnormal_of_isSimpleGroup hJ'.2.1 hne
  have hsup : imageMod 3 K J ⊔ Subgroup.center (PQuot 3 K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (QuotientGroup.mk' (Subgroup.center (PQuot 3 K)) x : PSimple 3 K) ∈ chevTransfer 3 K J := by
      rw [hJ'top]
      exact Subgroup.mem_top _
    rw [chevTransfer_eq] at hx
    obtain ⟨j, hj, hjx⟩ := Subgroup.mem_map.1 hx
    have hcen : j⁻¹ * x ∈ Subgroup.center (PQuot 3 K) := QuotientGroup.eq.1 hjx
    have hx' : x = j * (j⁻¹ * x) := (mul_inv_cancel_left j x).symm
    rw [hx']
    exact Subgroup.mul_mem_sup hj hcen
  exact up7a8_eq_top_of_sup_center
    (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK).1 hsup

theorem up7a8_pQuot_iso_of_top {G : Type} [Group G] [Finite G] {K J : Subgroup G}
    (hJK : J ≤ K) (htop : imageMod 3 K J = ⊤) : Nonempty (PQuot 3 J ≃* PQuot 3 K) :=
  (cover_facts Nat.prime_three hJK (sup_glaPPrimeCoreOf_eq_of_barX_eq_top hJK htop)).2

theorem up7a8_natCard_alt (j : ℕ) (hj : 5 ≤ j) : Nat.card (alternatingGroup (Fin j)) = j.factorial / 2 := by
  haveI : Nontrivial (Fin j) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin]

theorem up7a8_prime_dvd_2520 {r : ℕ} (hr : r.Prime) (h : r ∣ 2520) : r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
  have h' : r ∣ 2 ^ 3 * 3 ^ 2 * 5 * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hr).1 h2 with h3 | h3
      · left; exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h3)
      · right; left; exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h3)
    · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h2
  · right; right; right; exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1

theorem up7a8_prime_dvd_20160 {r : ℕ} (hr : r.Prime) (h : r ∣ 20160) : r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
  have h' : r ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hr).1 h2 with h3 | h3
      · left; exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h3)
      · right; left; exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h3)
    · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h2
  · right; right; right; exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1

section LieCerts


theorem up7a8_not_chev_card_2520 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {T : Type} [Group T] [Finite T]
    (hT : Nat.card T = 2520) : ¬ IsChevSimple r T := by
  have hb := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  by_cases h3 : r = 3
  · subst h3
    exact I1416QRows.not_isChevSimple_of_card hb Nat.prime_three (by norm_num) (a := 2) (m := 280)
      (by rw [hT]; norm_num) (by norm_num) (by norm_num)
      (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩) (fun h => by norm_num at h)
  by_cases h5 : r = 5
  · subst h5
    exact I1416QRows.not_isChevSimple_of_card hb (by norm_num) (by norm_num) (a := 1) (m := 504)
      (by rw [hT]; norm_num) (by norm_num) (by norm_num)
      (fun h => by norm_num at h) (fun _ => by norm_num)
  by_cases h7 : r = 7
  · subst h7
    exact I1416QRows.not_isChevSimple_of_card hb (by norm_num) (by norm_num) (a := 1) (m := 360)
      (by rw [hT]; norm_num) (by norm_num) (by norm_num)
      (fun h => by norm_num at h) (fun h => by norm_num at h)
  have hnd : ¬ r ∣ 2520 := by
    intro hd
    rcases up7a8_prime_dvd_2520 hr hd with h | h | h | h
    · exact hr2 h
    · exact h3 h
    · exact h5 h
    · exact h7 h
  exact I1416QRows.not_isChevSimple_of_card hb hr hr2 (a := 0) (m := 2520) (by rw [hT]; simp)
    hnd (by simp) (fun h => absurd h h3) (fun h => absurd h h5)

theorem up7a8_not_chev_card_20160 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {T : Type} [Group T] [Finite T]
    (hT : Nat.card T = 20160) : ¬ IsChevSimple r T := by
  have hb := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  by_cases h3 : r = 3
  · subst h3
    exact I1416QRows.not_isChevSimple_of_card hb Nat.prime_three (by norm_num) (a := 2) (m := 2240)
      (by rw [hT]; norm_num) (by norm_num) (by norm_num)
      (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩) (fun h => by norm_num at h)
  by_cases h5 : r = 5
  · subst h5
    exact I1416QRows.not_isChevSimple_of_card hb (by norm_num) (by norm_num) (a := 1) (m := 4032)
      (by rw [hT]; norm_num) (by norm_num) (by norm_num)
      (fun h => by norm_num at h) (fun _ => by norm_num)
  by_cases h7 : r = 7
  · subst h7
    exact I1416QRows.not_isChevSimple_of_card hb (by norm_num) (by norm_num) (a := 1) (m := 2880)
      (by rw [hT]; norm_num) (by norm_num) (by norm_num)
      (fun h => by norm_num at h) (fun h => by norm_num at h)
  have hnd : ¬ r ∣ 20160 := by
    intro hd
    rcases up7a8_prime_dvd_20160 hr hd with h | h | h | h
    · exact hr2 h
    · exact h3 h
    · exact h5 h
    · exact h7 h
  exact I1416QRows.not_isChevSimple_of_card hb hr hr2 (a := 0) (m := 20160) (by rw [hT]; simp)
    hnd (by simp) (fun h => absurd h h3) (fun h => absurd h h5)

theorem up7a8_not_chev_alt7 {r : ℕ} (hr : r.Prime) {S : Type} [Group S] [Finite S]
    (e : S ≃* alternatingGroup (Fin 7)) : ¬ IsChevSimple r S := by
  by_cases hr2 : r = 2
  · subst hr2
    exact CFSG.LocalAnalysis.GLTheoremA.i112d_not_chev_alt7 e
  · exact up7a8_not_chev_card_2520 hr hr2
      ((Nat.card_congr e.toEquiv).trans (by rw [up7a8_natCard_alt 7 (by norm_num)]; norm_num))

theorem up7a8_not_chev_alt8_odd {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {S : Type} [Group S] [Finite S]
    (e : S ≃* alternatingGroup (Fin 8)) : ¬ IsChevSimple r S :=
  up7a8_not_chev_card_20160 hr hr2
    ((Nat.card_congr e.toEquiv).trans (by rw [up7a8_natCard_alt 8 (by norm_num)]; norm_num))

end LieCerts

end CFSG.LocalAnalysis.GLTheoremA
