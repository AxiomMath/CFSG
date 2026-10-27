module

import CFSG.LieType.PSp43Local.Elements
public import CFSG.LieType.PSp43Local.Sylow
import CFSG.LieType.PSp43Local.WreathKer
import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LieType.PSp43Local

open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435
open CFSG.GH74.Exceptional CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private noncomputable abbrev pspA : PSp43 := uPSp (Multiplicative.ofAdd (1, 0, 0))

private noncomputable abbrev pspB : PSp43 := uPSp (Multiplicative.ofAdd (0, 1, 0))

private noncomputable abbrev pspT : PSp43 := levPSp 1

private theorem pspA_mem_E0 : pspA ∈ E0 := MonoidHom.mem_range.mpr ⟨_, rfl⟩

private theorem pspB_mem_E0 : pspB ∈ E0 := MonoidHom.mem_range.mpr ⟨_, rfl⟩

private theorem uPSp_pow_three (v : T3) : uPSp (Multiplicative.ofAdd v) ^ 3 = 1 := by
  rw [← map_pow]
  have hv0 : (3 : ℕ) • v = 0 := by
    have h : ∀ w : T3, (3 : ℕ) • w = 0 := by decide
    exact h v
  rw [← ofAdd_nsmul, hv0, ofAdd_zero, map_one]

private theorem uPSp_ne_one {v : T3} (hv : v ≠ 0) : uPSp (Multiplicative.ofAdd v) ≠ 1 := by
  intro h
  apply hv
  have h' : (Multiplicative.ofAdd v : Multiplicative T3) = 1 := uPSp_injective (by rw [h, map_one])
  simpa using h'

private theorem card_zpowers_of_pow_three {x : PSp43} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = 3 := by
  rw [Nat.card_zpowers, orderOf_eq_prime h3 h1]

private theorem card_zpowers_uPSp {v : T3} (hv : v ≠ 0) :
    Nat.card (Subgroup.zpowers (uPSp (Multiplicative.ofAdd v))) = 3 :=
  card_zpowers_of_pow_three (uPSp_pow_three v) (uPSp_ne_one hv)

private theorem card_zpowers_pspA : Nat.card (Subgroup.zpowers pspA) = 3 :=
  card_zpowers_uPSp (v := (1, 0, 0)) (by decide)

private theorem card_zpowers_pspB : Nat.card (Subgroup.zpowers pspB) = 3 :=
  card_zpowers_uPSp (v := (0, 1, 0)) (by decide)

private theorem pspT_ne_one : pspT ≠ 1 :=
  fun h => levPSp_one_not_mem_E0 (by change pspT ∈ E0; rw [h]; exact E0.one_mem)

private theorem card_zpowers_pspT : Nat.card (Subgroup.zpowers pspT) = 3 :=
  card_zpowers_of_pow_three levPSp_one_pow_three pspT_ne_one

private theorem pspA_not_mem_zpowers_pspB : pspA ∉ Subgroup.zpowers pspB := by
  rintro ⟨k, hk⟩
  have h' : (Multiplicative.ofAdd (1, 0, 0) : Multiplicative T3) =
      (Multiplicative.ofAdd (0, 1, 0) : Multiplicative T3) ^ k := by
    apply uPSp_injective
    rw [map_zpow]
    exact hk.symm
  rw [← ofAdd_zsmul] at h'
  simpa using congrArg (fun v : Multiplicative T3 => (Multiplicative.toAdd v).1) h'

private theorem inf_zpowers_eq_bot_of_not_mem {x y : PSp43}
    (hx : Nat.card (Subgroup.zpowers x) = 3) (hy : Nat.card (Subgroup.zpowers y) = 3)
    (hxy : x ∉ Subgroup.zpowers y) : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
  have hle : Subgroup.zpowers x ⊓ Subgroup.zpowers y ≤ Subgroup.zpowers y := inf_le_right
  have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) ∣ 3 := by
    simpa [hy] using Subgroup.card_dvd_of_le hle
  by_contra hbot
  have hne1 : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) ≠ 1 := by
    intro h1
    exact hbot (Subgroup.card_eq_one.mp h1)
  have hcard3 : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard3, hy])
  have hle' : Subgroup.zpowers y ≤ Subgroup.zpowers x := by
    rw [← heq]
    exact inf_le_left
  have heq' : Subgroup.zpowers y = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle' (by rw [hy, hx])
  exact hxy (heq' ▸ Subgroup.mem_zpowers x)

private theorem card_closure_pair_of_commute {x y : PSp43}
    (hx : Nat.card (Subgroup.zpowers x) = 3) (hy : Nat.card (Subgroup.zpowers y) = 3)
    (hcomm : x * y = y * x) (hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Nat.card (Subgroup.closure ({x, y} : Set PSp43)) = 9 := by
  have hpair : Subgroup.closure ({x, y} : Set PSp43) = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [show ({x, y} : Set PSp43) = {x} ∪ {y} by ext z; simp [or_comm],
      Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
  rw [hpair]
  have h := CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers x) (Subgroup.zpowers y)
    (fun a ha b hb => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact Commute.zpow_zpow (show Commute x y from hcomm) m n)
    hdisj
  rw [h, hx, hy]

private theorem pspA_mul_pspB : pspA * pspB = pspB * pspA := E0_comm pspA_mem_E0 pspB_mem_E0

private theorem pspA_mul_pspT : pspA * pspT = pspT * pspA := by
  have h := levPSp_conj 1 (Multiplicative.ofAdd (1, 0, 0))
  change levPSp 1 * uPSp (Multiplicative.ofAdd (1, 0, 0)) * (levPSp 1)⁻¹ =
    uPSp (Multiplicative.ofAdd (levAct (levA 1) (1, 0, 0))) at h
  rw [show levAct (levA 1) (1, 0, 0) = (1, 0, 0) by decide +kernel] at h
  have := congrArg (fun x => x * pspT) h
  simpa [pspT, pspA, mul_assoc] using this.symm

private theorem pspT_not_mem_zpowers_pspA : pspT ∉ Subgroup.zpowers pspA :=
  fun h => levPSp_one_not_mem_E0 ((Subgroup.zpowers_le.mpr pspA_mem_E0) h)

private theorem card_closure_pspA_pspB :
    Nat.card (Subgroup.closure ({pspA, pspB} : Set PSp43)) = 9 :=
  card_closure_pair_of_commute card_zpowers_pspA card_zpowers_pspB pspA_mul_pspB
    (inf_zpowers_eq_bot_of_not_mem card_zpowers_pspA card_zpowers_pspB
      pspA_not_mem_zpowers_pspB)

private theorem card_closure_pspA_pspT :
    Nat.card (Subgroup.closure ({pspA, pspT} : Set PSp43)) = 9 := by
  rw [show ({pspA, pspT} : Set PSp43) = {pspT, pspA} by ext z; simp [or_comm]]
  exact card_closure_pair_of_commute card_zpowers_pspT card_zpowers_pspA pspA_mul_pspT.symm
    (inf_zpowers_eq_bot_of_not_mem card_zpowers_pspT card_zpowers_pspA
      pspT_not_mem_zpowers_pspA)

private noncomputable def w3OfSylowQ0 : ↥sylowQ0 ≃* W3 := Classical.choice nonempty_mulEquiv_sylowQ0

private theorem centerIn_map_mulEquiv' (c : PSp43 ≃* PSp43) (D : Subgroup PSp43) :
    (CFSG.centerIn D).map c.toMonoidHom = CFSG.centerIn (D.map c.toMonoidHom) := by
  rw [CFSG.centerIn, CFSG.centerIn, Subgroup.map_inf _ _ _ c.injective]
  change D.map c.toMonoidHom ⊓
      Subgroup.map (↑c : PSp43 →* PSp43) (Subgroup.centralizer (D : Set PSp43)) =
    D.map c.toMonoidHom ⊓ Subgroup.centralizer ((D.map c.toMonoidHom : Subgroup PSp43) : Set PSp43)
  rw [← CFSG.Fischer.centralizer_image_eq_map c (D : Set PSp43)]
  change D.map c.toMonoidHom ⊓
      Subgroup.centralizer ((D.map c.toMonoidHom : Subgroup PSp43) : Set PSp43) =
    D.map c.toMonoidHom ⊓ Subgroup.centralizer ((D.map c.toMonoidHom : Subgroup PSp43) : Set PSp43)
  rfl

private theorem map_centralizer_mulEquiv (c : PSp43 ≃* PSp43) (K : Subgroup PSp43) :
    (Subgroup.centralizer (K : Set PSp43)).map c.toMonoidHom =
      Subgroup.centralizer ((K.map c.toMonoidHom : Subgroup PSp43) : Set PSp43) := by
  change Subgroup.map (↑c : PSp43 →* PSp43) (Subgroup.centralizer (K : Set PSp43)) =
    Subgroup.centralizer ((K.map c.toMonoidHom : Subgroup PSp43) : Set PSp43)
  rw [← CFSG.Fischer.centralizer_image_eq_map c (K : Set PSp43)]
  change Subgroup.centralizer ((K.map c.toMonoidHom : Subgroup PSp43) : Set PSp43) =
    Subgroup.centralizer ((K.map c.toMonoidHom : Subgroup PSp43) : Set PSp43)
  rfl

private theorem mem_pspA_pspB_pspT_of_sylow_three {D : Subgroup PSp43}
    (hDQ : D ≤ sylowQ0) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1)
    (hnc : ¬ IsMulCommutative D) : pspA ∈ D ∧ pspB ∈ D ∧ pspT ∈ D := by
  have hne : D ≠ baseIn w3OfSylowQ0 := fun h => hnc (by
    rw [h]
    exact ⟨⟨fun x y => Subtype.ext (baseIn_comm w3OfSylowQ0 x.2 y.2)⟩⟩)
  have hmem (u : PSp43) (hu : u ∈ E0) (hu3 : (u * pspT) ^ 3 = 1) : u * pspT ∈ D := by
    refine mem_of_pow_three_eq_one_of_not_mem_baseIn w3OfSylowQ0 hDQ hD h3 hne
      (mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) hu3 ?_
    rw [show baseIn w3OfSylowQ0 = E0 by
      rw [← thompsonSubgroup_sylowQ0]; exact (thompsonSubgroup_eq_baseIn w3OfSylowQ0).symm]
    intro hE
    apply levPSp_one_not_mem_E0
    change pspT ∈ E0
    rw [show pspT = u⁻¹ * (u * pspT) by group]
    exact E0.mul_mem (E0.inv_mem hu) hE
  have htD : pspT ∈ D := by
    simpa using hmem 1 E0.one_mem (by simpa using levPSp_one_pow_three)
  have hatD := hmem pspA pspA_mem_E0 uPSp_a_mul_levPSp_one_pow_three
  have hbtD := hmem pspB pspB_mem_E0 uPSp_b_mul_levPSp_one_pow_three
  have haD : pspA ∈ D := by
    have h := D.mul_mem hatD (D.inv_mem htD)
    rwa [show (pspA * pspT) * pspT⁻¹ = pspA by group] at h
  have hbD : pspB ∈ D := by
    have h := D.mul_mem hbtD (D.inv_mem htD)
    rwa [show (pspB * pspT) * pspT⁻¹ = pspB by group] at h
  exact ⟨haD, hbD, htD⟩

private theorem card_eq_nine_or_twenty_seven {H D : Subgroup PSp43}
    (hHD : H ≤ D) (hD : Nat.card D = 27) (h9 : 9 ∣ Nat.card H) :
    Nat.card H = 9 ∨ Nat.card H = 27 := by
  have hdiv : Nat.card H ∣ 3 ^ 3 := by
    simpa [hD] using Subgroup.card_dvd_of_le hHD
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow (p := 3) (m := 3) (by norm_num : Nat.Prime 3)).mp hdiv
  have hk2 : 2 ≤ k := by
    have h : 3 ^ 2 ∣ 3 ^ k := by rwa [hcard] at h9
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp h
  rcases (by omega : k = 2 ∨ k = 3) with rfl | rfl
  · left; rw [hcard]; norm_num
  · right; rw [hcard]; norm_num

private theorem card_eq_nine_of_dvd_of_ne {H D : Subgroup PSp43}
    (hHD : H ≤ D) (hD : Nat.card D = 27) (h9 : 9 ∣ Nat.card H) (hne : H ≠ D) : Nat.card H = 9 := by
  rcases card_eq_nine_or_twenty_seven hHD hD h9 with h | h
  · exact h
  · exfalso
    apply hne
    exact Subgroup.eq_of_le_of_card_ge hHD (by rw [h, hD])

private theorem card_eq_three_or_nine_of_dvd_nine {H : Subgroup PSp43}
    (hdiv : Nat.card H ∣ 3 ^ 2) (h1 : 1 < Nat.card H) : Nat.card H = 3 ∨ Nat.card H = 9 := by
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow (p := 3) (m := 2) (by norm_num : Nat.Prime 3)).mp hdiv
  have hk1 : 1 ≤ k := by
    by_contra h
    interval_cases k
    rw [hcard] at h1
    norm_num at h1
  rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
  · left; rw [hcard]; norm_num
  · right; rw [hcard]; norm_num

private theorem closure_pspA_pspB_pspT_eq_of_sylow_three {D : Subgroup PSp43}
    (hDQ : D ≤ sylowQ0) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1)
    (hnc : ¬ IsMulCommutative D) : Subgroup.closure ({pspA, pspB, pspT} : Set PSp43) = D := by
  obtain ⟨haD, hbD, htD⟩ := mem_pspA_pspB_pspT_of_sylow_three hDQ hD h3 hnc
  have hHD : Subgroup.closure ({pspA, pspB, pspT} : Set PSp43) ≤ D := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl) <;> assumption
  have hKH : Subgroup.closure ({pspA, pspB} : Set PSp43) ≤
      Subgroup.closure ({pspA, pspB, pspT} : Set PSp43) := by
    apply Subgroup.closure_mono
    rintro x (rfl | rfl) <;> simp
  have hKE0 : Subgroup.closure ({pspA, pspB} : Set PSp43) ≤ E0 := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact pspA_mem_E0
    · exact pspB_mem_E0
  have h9 : 9 ∣ Nat.card (Subgroup.closure ({pspA, pspB, pspT} : Set PSp43)) := by
    rw [← card_closure_pspA_pspB]
    exact Subgroup.card_dvd_of_le hKH
  have hH9 : Nat.card (Subgroup.closure ({pspA, pspB, pspT} : Set PSp43)) ≠ 9 := by
    intro h
    have hEq : Subgroup.closure ({pspA, pspB, pspT} : Set PSp43) =
        Subgroup.closure ({pspA, pspB} : Set PSp43) :=
      (Subgroup.eq_of_le_of_card_ge hKH (by rw [h, card_closure_pspA_pspB])).symm
    exact levPSp_one_not_mem_E0 (hKE0 (hEq ▸ Subgroup.subset_closure (by simp)))
  rcases card_eq_nine_or_twenty_seven hHD hD h9 with hcard | hcard
  · exact absurd hcard hH9
  · exact Subgroup.eq_of_le_of_card_ge hHD (by rw [hD, hcard])

private theorem card_inf_E0_D_of_sylow_three {D : Subgroup PSp43}
    (hDQ : D ≤ sylowQ0) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1)
    (hnc : ¬ IsMulCommutative D) : Nat.card ↥(E0 ⊓ D) = 9 := by
  obtain ⟨haD, hbD, htD⟩ := mem_pspA_pspB_pspT_of_sylow_three hDQ hD h3 hnc
  have hDH := closure_pspA_pspB_pspT_eq_of_sylow_three hDQ hD h3 hnc
  have hKle : Subgroup.closure ({pspA, pspB} : Set PSp43) ≤ E0 ⊓ D := by
    refine le_inf ?_ ?_
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact pspA_mem_E0
      · exact pspB_mem_E0
    · rw [← hDH]
      exact Subgroup.closure_mono (by rintro x (rfl | rfl) <;> simp)
  have h9 : 9 ∣ Nat.card ↥(E0 ⊓ D) := by
    rw [← card_closure_pspA_pspB]
    exact Subgroup.card_dvd_of_le hKle
  have hproper : E0 ⊓ D ≠ D := fun h =>
    levPSp_one_not_mem_E0 (by rw [← h] at htD; exact htD.1)
  exact card_eq_nine_of_dvd_of_ne inf_le_right hD h9 hproper

private theorem pspA_mem_centerIn_of_sylow_three {D : Subgroup PSp43}
    (hDQ : D ≤ sylowQ0) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1)
    (hnc : ¬ IsMulCommutative D) : pspA ∈ CFSG.centerIn D := by
  obtain ⟨haD, hbD, htD⟩ := mem_pspA_pspB_pspT_of_sylow_three hDQ hD h3 hnc
  have hDH := closure_pspA_pspB_pspT_eq_of_sylow_three hDQ hD h3 hnc
  have hDle : D ≤ Subgroup.centralizer ({pspA} : Set PSp43) := by
    rw [← hDH, Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr pspA_mul_pspB.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr pspA_mul_pspT.symm
  refine ⟨haD, ?_⟩
  change pspA ∈ Subgroup.centralizer (D : Set PSp43)
  rw [Subgroup.mem_centralizer_iff]
  exact fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hDle hy)

private theorem centerIn_eq_zpowers_pspA_of_sylow_three {D : Subgroup PSp43}
    (hDQ : D ≤ sylowQ0) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1)
    (hnc : ¬ IsMulCommutative D) : CFSG.centerIn D = Subgroup.zpowers pspA := by
  obtain ⟨haD, hbD, htD⟩ := mem_pspA_pspB_pspT_of_sylow_three hDQ hD h3 hnc
  have hDH := closure_pspA_pspB_pspT_eq_of_sylow_three hDQ hD h3 hnc
  have hleA : Subgroup.zpowers pspA ≤ CFSG.centerIn D :=
    Subgroup.zpowers_le.mpr (pspA_mem_centerIn_of_sylow_three hDQ hD h3 hnc)
  have hKle : Subgroup.closure ({pspA, pspT} : Set PSp43) ≤
      D ⊓ Subgroup.centralizer ({pspT} : Set PSp43) := by
    refine le_inf ?_ ?_
    · rw [← hDH]
      exact Subgroup.closure_mono (by rintro x (rfl | rfl) <;> simp)
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr pspA_mul_pspT
      · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hproper : D ⊓ Subgroup.centralizer ({pspT} : Set PSp43) ≠ D := by
    intro h
    exact levPSp_one_mul_b_ne (Subgroup.mem_centralizer_singleton_iff.mp
      ((show D ≤ Subgroup.centralizer ({pspT} : Set PSp43) by rw [← h]; exact inf_le_right)
        hbD)).symm
  have h9 : 9 ∣ Nat.card ↥(D ⊓ Subgroup.centralizer ({pspT} : Set PSp43)) := by
    rw [← card_closure_pspA_pspT]
    exact Subgroup.card_dvd_of_le hKle
  have hC9 : Nat.card ↥(D ⊓ Subgroup.centralizer ({pspT} : Set PSp43)) = 9 :=
    card_eq_nine_of_dvd_of_ne inf_le_left hD h9 hproper
  have hCentLe : CFSG.centerIn D ≤ D ⊓ Subgroup.centralizer ({pspT} : Set PSp43) := by
    refine le_inf inf_le_left ?_
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (D : Set PSp43) := hz.2
    rw [Subgroup.mem_centralizer_iff] at hzC ⊢
    rintro y rfl
    exact hzC pspT htD
  have hdiv : Nat.card ↥(CFSG.centerIn D) ∣ 3 ^ 2 := by
    have h := Subgroup.card_dvd_of_le hCentLe
    rw [hC9] at h
    simpa using h
  have h3le : 3 ≤ Nat.card ↥(CFSG.centerIn D) := by
    have := Subgroup.card_le_of_le hleA
    rwa [card_zpowers_pspA] at this
  have hne : Nat.card ↥(CFSG.centerIn D) ≠ 9 := by
    intro hcard
    have heq : CFSG.centerIn D = D ⊓ Subgroup.centralizer ({pspT} : Set PSp43) :=
      Subgroup.eq_of_le_of_card_ge hCentLe (by rw [hcard, hC9])
    have ht : pspT ∈ CFSG.centerIn D := by
      rw [heq]
      exact ⟨htD, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    exact levPSp_one_mul_b_ne
      (Subgroup.mem_centralizer_iff.mp ht.2 pspB hbD).symm
  have hcard : Nat.card ↥(CFSG.centerIn D) = 3 := by
    rcases card_eq_three_or_nine_of_dvd_nine hdiv (by omega) with h | h
    · exact h
    · exact absurd h hne
  exact (Subgroup.eq_of_le_of_card_ge hleA (by rw [hcard, card_zpowers_pspA])).symm

private theorem centralizer_inf_eq_E0_of_sylow_three {D : Subgroup PSp43}
    (hDQ : D ≤ sylowQ0) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1)
    (hnc : ¬ IsMulCommutative D) :
    Subgroup.centralizer ((E0 ⊓ D : Subgroup PSp43) : Set PSp43) = E0 := by
  obtain ⟨haD, hbD, htD⟩ := mem_pspA_pspB_pspT_of_sylow_three hDQ hD h3 hnc
  refine le_antisymm ?_ ?_
  · intro z hz
    apply centralizer_a_b_le_E0
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    rintro y (rfl | rfl)
    · exact hz pspA ⟨pspA_mem_E0, haD⟩
    · exact hz pspB ⟨pspB_mem_E0, hbD⟩
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨hyE, -⟩
    exact (E0_comm hz hyE).symm

private theorem normalizer_inf_le_normalizer_E0_of_sylow_three {D : Subgroup PSp43}
    (hDQ : D ≤ sylowQ0) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1)
    (hnc : ¬ IsMulCommutative D) : Subgroup.normalizer ((E0 ⊓ D : Subgroup PSp43) : Set PSp43) ≤
      Subgroup.normalizer (E0 : Set PSp43) := by
  set K : Subgroup PSp43 := E0 ⊓ D with hK
  have hcent := centralizer_inf_eq_E0_of_sylow_three hDQ hD h3 hnc
  intro x hx
  have hmap : K.map (MulAut.conj x).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have hcentmap : (Subgroup.centralizer (K : Set PSp43)).map
      (MulAut.conj x).toMonoidHom = Subgroup.centralizer (K : Set PSp43) := by
    rw [map_centralizer_mulEquiv (MulAut.conj x) K, hmap]
  have hE0map : (E0 : Subgroup PSp43).map (MulAut.conj x).toMonoidHom = E0 := by
    rw [← hcent]
    exact hcentmap
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hE0map

private theorem not_normalizer_le_normalizer_E0_of_sylow_three {D : Subgroup PSp43}
    (hDQ : D ≤ sylowQ0) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1)
    (hnc : ¬ IsMulCommutative D) :
    ¬ Subgroup.normalizer (D : Set PSp43) ≤ Subgroup.normalizer (E0 : Set PSp43) := by
  have hDH := closure_pspA_pspB_pspT_eq_of_sylow_three hDQ hD h3 hnc
  have hxN : xPSp ∈ Subgroup.normalizer (D : Set PSp43) := by
    have hmaple : D.map (MulAut.conj xPSp).toMonoidHom ≤ D := by
      rw [← hDH, MonoidHom.map_closure, Subgroup.closure_le]
      rintro y ⟨z, (rfl | rfl | rfl), rfl⟩
      · rw [show (MulAut.conj xPSp).toMonoidHom pspA = pspA by
          simpa [MulAut.conj_apply] using xPSp_conj_a]
        exact Subgroup.subset_closure (by simp)
      · rw [show (MulAut.conj xPSp).toMonoidHom pspB = pspT⁻¹ by
          simpa [MulAut.conj_apply] using xPSp_conj_b]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
      · rw [show (MulAut.conj xPSp).toMonoidHom pspT = pspB by
          simpa [MulAut.conj_apply] using xPSp_conj_t]
        exact Subgroup.subset_closure (by simp)
    have hcard := Subgroup.card_map_of_injective (K := D)
      (f := (MulAut.conj xPSp).toMonoidHom) (MulAut.conj xPSp).injective
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm))
  intro hle
  exact xPSp_not_mem_normalizer_E0 (hle hxN)

private theorem mem_normalizer_E0_of_map_conj_le_of_sylow_three {D B : Subgroup PSp43}
    (hDQ : D ≤ sylowQ0) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1)
    (hnc : ¬ IsMulCommutative D) (hB : B ≤ E0 ⊓ D) (hBZ : ¬ B ≤ CFSG.centerIn D) {x : PSp43}
    (hx : x ∈ Subgroup.normalizer (D : Set PSp43)) (hxB : B.map (MulAut.conj x).toMonoidHom ≤ E0) :
    x ∈ Subgroup.normalizer (E0 : Set PSp43) := by
  obtain ⟨haD, hbD, htD⟩ := mem_pspA_pspB_pspT_of_sylow_three hDQ hD h3 hnc
  have hD9 := card_inf_E0_D_of_sylow_three hDQ hD h3 hnc
  have hZ := centerIn_eq_zpowers_pspA_of_sylow_three hDQ hD h3 hnc
  have hDmap : D.map (MulAut.conj x).toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have hZle : CFSG.centerIn D ≤ E0 ⊓ D := by
    rw [hZ]
    exact le_inf (Subgroup.zpowers_le.mpr pspA_mem_E0) (Subgroup.zpowers_le.mpr haD)
  have hBZle : B ⊔ CFSG.centerIn D ≤ E0 ⊓ D := sup_le hB hZle
  have hstrict : CFSG.centerIn D < B ⊔ CFSG.centerIn D :=
    lt_of_le_of_ne le_sup_right fun h => hBZ (by rw [h]; exact le_sup_left)
  have hcardZ : Nat.card ↥(CFSG.centerIn D) = 3 := by rw [hZ, card_zpowers_pspA]
  have hcard : Nat.card ↥(B ⊔ CFSG.centerIn D) = 9 := by
    have hdiv : Nat.card ↥(B ⊔ CFSG.centerIn D) ∣ 3 ^ 2 := by
      have h := Subgroup.card_dvd_of_le hBZle
      rwa [hD9] at h
    have hgt : 3 < Nat.card ↥(B ⊔ CFSG.centerIn D) := by
      have := Subgroup.card_lt_of_lt hstrict
      rwa [hcardZ] at this
    rcases card_eq_three_or_nine_of_dvd_nine hdiv (by omega) with h | h
    · omega
    · exact h
  have heq : B ⊔ CFSG.centerIn D = E0 ⊓ D := Subgroup.eq_of_le_of_card_ge hBZle (by rw [hD9, hcard])
  have hZmap : (CFSG.centerIn D).map (MulAut.conj x).toMonoidHom = CFSG.centerIn D := by
    rw [centerIn_map_mulEquiv' (MulAut.conj x) D, hDmap]
  have hE0Dmap : ((E0 ⊓ D : Subgroup PSp43).map (MulAut.conj x).toMonoidHom) ≤ E0 ⊓ D := by
    rw [← heq, Subgroup.map_sup, hZmap]
    refine sup_le ?_ le_sup_right
    refine (le_inf hxB ?_).trans (le_of_eq heq.symm)
    calc B.map (MulAut.conj x).toMonoidHom ≤ D.map (MulAut.conj x).toMonoidHom :=
          Subgroup.map_mono (hB.trans inf_le_right)
      _ = D := hDmap
  have hcardmap : Nat.card ↥((E0 ⊓ D).map (MulAut.conj x).toMonoidHom) = Nat.card ↥(E0 ⊓ D) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom)
      (MulAut.conj x).injective
  have hE0Deq : (E0 ⊓ D).map (MulAut.conj x).toMonoidHom = E0 ⊓ D :=
    Subgroup.eq_of_le_of_card_ge hE0Dmap (le_of_eq hcardmap.symm)
  exact normalizer_inf_le_normalizer_E0_of_sylow_three hDQ hD h3 hnc
    (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hE0Deq)

private theorem exists_conj_map_eq_sylowQ0 (Q : Sylow 3 PSp43) :
    ∃ g : PSp43, (Q : Subgroup PSp43).map (MulAut.conj g).toMonoidHom = sylowQ0 := by
  obtain ⟨Q0, hQ0⟩ := exists_sylow_eq_sylowQ0
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSp43 Q Q0
  refine ⟨g, ?_⟩
  have h := congrArg (fun S : Sylow 3 PSp43 => (S : Subgroup PSp43)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  rw [hQ0] at h
  convert h using 2 <;> ext x <;> rfl

private theorem exists_conj_data (Q : Sylow 3 PSp43) {D : Subgroup PSp43}
    (hDQ : D ≤ Q) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1) (hnc : ¬ IsMulCommutative D) :
    ∃ g : PSp43, (Q : Subgroup PSp43).map (MulAut.conj g).toMonoidHom = sylowQ0 ∧
      D.map (MulAut.conj g).toMonoidHom ≤ sylowQ0 ∧
      Nat.card (D.map (MulAut.conj g).toMonoidHom) = 27 ∧
      (∀ x ∈ D.map (MulAut.conj g).toMonoidHom, x ^ 3 = 1) ∧
      ¬ IsMulCommutative (D.map (MulAut.conj g).toMonoidHom) ∧
      (CFSG.Open.thompsonSubgroup (Q : Subgroup PSp43)).map (MulAut.conj g).toMonoidHom = E0 := by
  obtain ⟨g, hg⟩ := exists_conj_map_eq_sylowQ0 Q
  refine ⟨g, hg, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hg]
    exact Subgroup.map_mono hDQ
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, hD]
  · rintro _ ⟨d, hd, rfl⟩
    rw [← map_pow, h3 d hd, map_one]
  · intro h0
    haveI : IsMulCommutative (D.map (MulAut.conj g).toMonoidHom) := h0
    exact hnc (by
      have h := Subgroup.comap_injective_isMulCommutative
        (H := D.map (MulAut.conj g).toMonoidHom) (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective
      rwa [Subgroup.comap_map_eq_self_of_injective (MulAut.conj g).injective D] at h)
  · rw [CFSG.map_ambientMaxCardThompson_of_injective (MulAut.conj g).toMonoidHom
      (Q : Subgroup PSp43)
      ((MulAut.conj g).injective.comp (Q : Subgroup PSp43).subtype_injective), hg]
    exact thompsonSubgroup_sylowQ0

private theorem map_conj_le_and_not_centerIn_of_sylow_three (Q : Sylow 3 PSp43)
    {D B : Subgroup PSp43} (hB : B ≤ CFSG.Open.thompsonSubgroup (Q : Subgroup PSp43) ⊓ D)
    (hBZ : ¬ B ≤ CFSG.centerIn D) {g : PSp43}
    (hJmap : (CFSG.Open.thompsonSubgroup (Q : Subgroup PSp43)).map
      (MulAut.conj g).toMonoidHom = E0) :
    (B.map (MulAut.conj g).toMonoidHom ≤ E0 ⊓ D.map (MulAut.conj g).toMonoidHom) ∧
      ¬ B.map (MulAut.conj g).toMonoidHom ≤ CFSG.centerIn (D.map (MulAut.conj g).toMonoidHom) := by
  have hB0 : B.map (MulAut.conj g).toMonoidHom ≤ E0 ⊓ D.map (MulAut.conj g).toMonoidHom := by
    rw [← hJmap, ← Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
    exact Subgroup.map_mono hB
  have hcomp : (MulAut.conj g).symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id PSp43 := by ext y; simp
  have hBmap : (B.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g).symm.toMonoidHom = B := by rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hZmap : (CFSG.centerIn (D.map (MulAut.conj g).toMonoidHom)).map
      (MulAut.conj g).symm.toMonoidHom = CFSG.centerIn D := by
    simpa [Subgroup.map_map, hcomp, Subgroup.map_id] using
      centerIn_map_mulEquiv' (MulAut.conj g).symm (D.map (MulAut.conj g).toMonoidHom)
  refine ⟨hB0, ?_⟩
  intro h
  apply hBZ
  have h' : (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).symm.toMonoidHom ≤
      (CFSG.centerIn (D.map (MulAut.conj g).toMonoidHom)).map
        (MulAut.conj g).symm.toMonoidHom := Subgroup.map_mono h
  rwa [hBmap, hZmap] at h'

theorem not_normalizer_le_normalizer_thompsonSubgroup (Q : Sylow 3 PSp43)
    {D : Subgroup PSp43} (hDQ : D ≤ Q) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1)
    (hnc : ¬ IsMulCommutative D) :
    ¬ Subgroup.normalizer (D : Set PSp43) ≤
      Subgroup.normalizer (CFSG.Open.thompsonSubgroup (Q : Subgroup PSp43) : Set PSp43) := by
  obtain ⟨g, hQ, hD0le, hD0card, hD0three, hD0nc, hJmap⟩ := exists_conj_data Q hDQ hD h3 hnc
  have h0 := not_normalizer_le_normalizer_E0_of_sylow_three hD0le hD0card hD0three hD0nc
  intro hle
  apply h0
  have hle' := Subgroup.map_mono hle (f := (MulAut.conj g).toMonoidHom)
  rwa [Subgroup.map_equiv_normalizer_eq, Subgroup.map_equiv_normalizer_eq, hJmap] at hle'

theorem mem_normalizer_thompsonSubgroup_of_map_conj_le (Q : Sylow 3 PSp43)
    {D B : Subgroup PSp43} (hDQ : D ≤ Q) (hD : Nat.card D = 27) (h3 : ∀ x ∈ D, x ^ 3 = 1)
    (hnc : ¬ IsMulCommutative D)
    (hB : B ≤ CFSG.Open.thompsonSubgroup (Q : Subgroup PSp43) ⊓ D)
    (hBZ : ¬ B ≤ CFSG.centerIn D) {x : PSp43} (hx : x ∈ Subgroup.normalizer (D : Set PSp43))
    (hxB : B.map (MulAut.conj x).toMonoidHom ≤ CFSG.Open.thompsonSubgroup (Q : Subgroup PSp43)) :
    x ∈ Subgroup.normalizer (CFSG.Open.thompsonSubgroup (Q : Subgroup PSp43) : Set PSp43) := by
  obtain ⟨g, hQ, hD0le, hD0card, hD0three, hD0nc, hJmap⟩ := exists_conj_data Q hDQ hD h3 hnc
  obtain ⟨hB0, hBZ0⟩ := map_conj_le_and_not_centerIn_of_sylow_three Q hB hBZ hJmap
  have hx0 : (MulAut.conj g) x ∈
      Subgroup.normalizer ((D.map (MulAut.conj g).toMonoidHom : Subgroup PSp43) :
        Set PSp43) := by
    have hx' : (MulAut.conj g) x ∈
        (Subgroup.normalizer (D : Set PSp43)).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    rwa [Subgroup.map_equiv_normalizer_eq] at hx'
  have hxB0 : (B.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj ((MulAut.conj g) x)).toMonoidHom ≤ E0 := by
    have hmap : (B.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj ((MulAut.conj g) x)).toMonoidHom =
        (B.map (MulAut.conj x).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      apply congrArg (fun f : PSp43 →* PSp43 => Subgroup.map f B)
      ext y
      simp [MulAut.conj_apply, map_mul, map_inv]
      group
    rw [hmap]
    exact (Subgroup.map_mono hxB).trans (le_of_eq hJmap)
  have hxE0 : (MulAut.conj g) x ∈ Subgroup.normalizer (E0 : Set PSp43) :=
    mem_normalizer_E0_of_map_conj_le_of_sylow_three hD0le hD0card hD0three hD0nc
      hB0 hBZ0 hx0 hxB0
  have hxN : (MulAut.conj g) x ∈
      (Subgroup.normalizer
        (CFSG.Open.thompsonSubgroup (Q : Subgroup PSp43) : Set PSp43)).map
        (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_equiv_normalizer_eq, hJmap]
    exact hxE0
  exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).mp hxN

end CFSG.LieType.PSp43Local
