module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenRoot
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEightPerm

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

section Twelve

@[expose] def zTw : Perm (Fin 12) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

@[expose] def cycTw : Fin 4 → Perm (Fin 12) :=
  ![swap 8 9 * swap 8 10, swap 9 10 * swap 9 11, swap 0 2 * swap 0 4 * (swap 1 3 * swap 1 5),
    swap 2 4 * swap 2 6 * (swap 3 5 * swap 3 7)]

theorem zTw_mul_self : zTw * zTw = 1 := by decide

theorem zTw_ne_one : zTw ≠ 1 := by decide

theorem sign_zTw : sign zTw = 1 := by decide

theorem cycTw_commute : ∀ i, cycTw i * zTw = zTw * cycTw i := by decide

theorem cycTw_pow_three : ∀ i, cycTw i ^ 3 = 1 := by decide

theorem sign_cycTw : ∀ i, sign (cycTw i) = 1 := by decide

theorem cycleType_zTw : zTw.cycleType = Multiset.replicate 4 2 := by
  rw [cycleType_eq_replicate_of_mul_self zTw_mul_self, show zTw.support.card = 8 by decide]

theorem apply_eq_iff_of_commute {v w : Perm (Fin 12)} (h : v * w = w * v) (j : Fin 12) :
    w j = j ↔ w (v j) = v j := by
  rw [← Perm.mul_apply w v, ← h, Perm.mul_apply]
  exact v.injective.eq_iff.symm

theorem apply_mem_zero_one_of_commute {v : Perm (Fin 12)} (hv : ∀ i, v * cycTw i = cycTw i * v)
    {j : Fin 12} (hj : j = 0 ∨ j = 1) : v j = 0 ∨ v j = 1 := by
  have h01 : ∀ k, (cycTw 0 k = k ∧ cycTw 1 k = k ∧ cycTw 2 k ≠ k ∧ cycTw 3 k = k) →
      k = 0 ∨ k = 1 := by decide
  have hm := fun i => apply_eq_iff_of_commute (hv i) j
  rcases hj with rfl | rfl
  · exact h01 _ ⟨(hm 0).mp (by decide), (hm 1).mp (by decide),
      fun h => absurd ((hm 2).mpr h) (by decide), (hm 3).mp (by decide)⟩
  · exact h01 _ ⟨(hm 0).mp (by decide), (hm 1).mp (by decide),
      fun h => absurd ((hm 2).mpr h) (by decide), (hm 3).mp (by decide)⟩

theorem eq_one_of_commute_cycTw {v : Perm (Fin 12)} (hv : ∀ i, v * cycTw i = cycTw i * v)
    (h0 : v 0 = 0) : v = 1 := by
  have hc : ∀ i j, v (cycTw i j) = cycTw i (v j) := fun i j => by
    rw [← Perm.mul_apply, hv i, Perm.mul_apply]
  have h8 : ∀ k, (cycTw 0 k ≠ k ∧ cycTw 1 k = k ∧ cycTw 2 k = k ∧ cycTw 3 k = k) → k = 8 := by
    decide
  have hm := fun i => apply_eq_iff_of_commute (hv i) 8
  have hv8 : v 8 = 8 :=
    h8 _ ⟨fun h => absurd ((hm 0).mpr h) (by decide), (hm 1).mp (by decide),
      (hm 2).mp (by decide), (hm 3).mp (by decide)⟩
  have h1 : v 1 = 1 := by
    rcases apply_mem_zero_one_of_commute hv (Or.inr rfl) with h1 | h1
    · exact absurd (v.injective (h1.trans h0.symm)) (by decide)
    · exact h1
  have e10 : v 10 = 10 := by have h := hc 0 8; rw [hv8] at h; exact h
  have e9 : v 9 = 9 := by have h := hc 0 10; rw [e10] at h; exact h
  have e11 : v 11 = 11 := by have h := hc 1 9; rw [e9] at h; exact h
  have e4 : v 4 = 4 := by have h := hc 2 0; rw [h0] at h; exact h
  have e2 : v 2 = 2 := by have h := hc 2 4; rw [e4] at h; exact h
  have e6 : v 6 = 6 := by have h := hc 3 2; rw [e2] at h; exact h
  have e5 : v 5 = 5 := by have h := hc 2 1; rw [h1] at h; exact h
  have e3 : v 3 = 3 := by have h := hc 2 5; rw [e5] at h; exact h
  have e7 : v 7 = 7 := by have h := hc 3 3; rw [e3] at h; exact h
  refine Equiv.ext fun j => ?_
  fin_cases j
  · exact h0
  · exact h1
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6
  · exact e7
  · exact hv8
  · exact e9
  · exact e10
  · exact e11

theorem eq_one_or_eq_zTw_of_commute {v : Perm (Fin 12)} (hv : ∀ i, v * cycTw i = cycTw i * v) :
    v = 1 ∨ v = zTw := by
  rcases apply_mem_zero_one_of_commute hv (Or.inl rfl) with h0 | h0
  · exact Or.inl (eq_one_of_commute_cycTw hv h0)
  · right
    have h1 : v 1 = 0 := by
      rcases apply_mem_zero_one_of_commute hv (Or.inr rfl) with h1 | h1
      · exact h1
      · exact absurd (v.injective (h1.trans h0.symm)) (by decide)
    have hw : ∀ i, v * zTw * cycTw i = cycTw i * (v * zTw) := fun i => by
      rw [mul_assoc, ← cycTw_commute i, ← mul_assoc, hv i, mul_assoc]
    have hw0 : (v * zTw) 0 = 0 := by
      rw [Perm.mul_apply, show zTw 0 = 1 by decide, h1]
    have h := eq_one_of_commute_cycTw hw hw0
    calc v = v * zTw * zTw := by rw [mul_assoc, zTw_mul_self, mul_one]
      _ = zTw := by rw [h, one_mul]

@[expose] def zTwA : alternatingGroup (Fin 12) := ⟨zTw, mem_alternatingGroup.mpr sign_zTw⟩

@[expose] def cycTwA (i : Fin 4) : alternatingGroup (Fin 12) :=
  ⟨cycTw i, mem_alternatingGroup.mpr (sign_cycTw i)⟩

theorem zTwA_mul_self : zTwA * zTwA = 1 := Subtype.ext zTw_mul_self

theorem zTwA_ne_one : zTwA ≠ 1 := fun h => zTw_ne_one (congrArg Subtype.val h)

theorem two_pow_nine_dvd_card_centralizer_zTwA :
    2 ^ 9 ∣ Nat.card (centralizer ({zTwA} : Set (alternatingGroup (Fin 12)))) := by
  have h := card_centralizer_dvd_two_mul_card_centralizer zTwA
  have hC : Nat.card (centralizer ({(zTwA : Perm (Fin 12))} : Set (Perm (Fin 12)))) = 9216 := by
    rw [Perm.nat_card_centralizer]
    change (Fintype.card (Fin 12) - zTw.cycleType.sum).factorial * zTw.cycleType.prod *
      (∏ n ∈ zTw.cycleType.toFinset, (zTw.cycleType.count n).factorial) = 9216
    rw [cycleType_zTw, Fintype.card_fin]
    decide
  rw [hC] at h
  omega

end Twelve

namespace AltGenSetting

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {Φ : alternatingGroup (Fin (8 + 4)) →* G} (s : AltGenSetting A R T g 8 Φ)
include s

theorem false_of_conj_mem_zTw {x : G} (hx : x * Φ zTwA * x⁻¹ ∈ centralizer (A : Set G)) :
    False := by
  classical
  have h7 : 7 ≤ 8 := by norm_num
  set u := Φ zTwA with hu
  have hu2 : u * u = 1 := by rw [hu, ← map_mul, zTwA_mul_self, map_one]
  have hu1 : u ≠ 1 := fun h1 => zTwA_ne_one (s.injective (h1.trans (map_one Φ).symm))
  have hT1 : ∀ y ∈ centralizer ({u} : Set G), x * y * x⁻¹ ∈ normalizer (A : Set G) := by
    have h := Lemma39.centralizer_le_normalizer_rightConjugate s.sec3.hyp 1
      (t := x * u * x⁻¹) (by rw [AschbacherTightEmbedding.rightConjugate_one]; exact hx)
      (fun h => hu1 (by
        have h' : u = x⁻¹ * (x * u * x⁻¹) * x := by group
        rw [h', h]
        group))
      (by rw [sq]; calc x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
                      _ = 1 := by rw [hu2, mul_one, mul_inv_cancel])
    rw [AschbacherTightEmbedding.rightConjugate_one] at h
    intro y hy
    apply h
    rw [mem_centralizer_singleton_iff] at hy ⊢
    calc x * y * x⁻¹ * (x * u * x⁻¹) = x * (y * u) * x⁻¹ := by group
      _ = x * (u * y) * x⁻¹ := by rw [hy]
      _ = x * u * x⁻¹ * (x * y * x⁻¹) := by group
  set act := actPerm s.psiA.symm (Or.inr h7) with hact
  set Cz : Subgroup (alternatingGroup (Fin 12)) := centralizer ({zTwA} : Set _) with hCz
  have hηmem : ∀ a : Cz, x * Φ a * x⁻¹ ∈ normalizer (A : Set G) := by
    intro a
    apply hT1
    rw [mem_centralizer_singleton_iff, hu, ← map_mul, ← map_mul]
    congr 1
    exact mem_centralizer_singleton_iff.mp a.2
  let η₀ : Cz →* normalizer (A : Set G) :=
    ((MulAut.conj x).toMonoidHom.comp (Φ.comp Cz.subtype)).codRestrict _ hηmem
  let η : Cz →* Perm (Fin 8) := act.comp η₀
  have hη1 : ∀ a : Cz, η a = 1 ↔ x * Φ a * x⁻¹ ∈ centralizer (A : Set G) := fun a =>
    actPerm_eq_one_iff s.psiA.symm (Or.inr h7) ⟨_, hηmem a⟩
  set kf : Cz → G := fun a => x * Φ (a : alternatingGroup (Fin 12)) * x⁻¹ with hkf
  have hkf_inj : Function.Injective kf := by
    intro a b h
    apply Subtype.ext
    apply s.injective
    simpa [hkf] using h
  set W : Finset Cz := Finset.univ.filter fun a => η a = 1 ∧ a ^ 4 = 1 with hW
  have hWcard : W.card ≤ 4 := by
    have h := s.card_le_four_of_pow_four (S := W.image kf) (by
      intro k hk
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      rw [hW, Finset.mem_filter] at ha
      refine ⟨(hη1 a).mp ha.2.1, ?_⟩
      show (x * Φ (a : alternatingGroup (Fin 12)) * x⁻¹) ^ 4 = 1
      rw [conj_pow, ← map_pow, ← Subgroup.coe_pow, ha.2.2, Subgroup.coe_one, map_one,
        mul_one, mul_inv_cancel])
    rwa [Finset.card_image_of_injective _ hkf_inj] at h
  set zC : Cz := ⟨zTwA, mem_centralizer_singleton_iff.mpr rfl⟩ with hzC
  have hzC1 : η zC = 1 := (hη1 zC).mpr hx
  have hzC2 : zC * zC = 1 := Subtype.ext zTwA_mul_self
  have hzCne : zC ≠ 1 := fun h => zTwA_ne_one (congrArg Subtype.val h)
  have hzcomm : ∀ a : Cz, a * zC = zC * a := fun a =>
    Subtype.ext (mem_centralizer_singleton_iff.mp a.2)
  set cC : Fin 4 → Cz := fun i => ⟨cycTwA i, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (cycTw_commute i))⟩ with hcC
  have hcC3 : ∀ i, cC i ^ 3 = 1 := fun i =>
    Subtype.ext (Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_pow]
      exact cycTw_pow_three i))
  have hV : ∀ V : Subgroup Cz, V ≤ η.ker → Nat.card V = 4 → False := by
    intro V hVker hV4
    have hVW : ∀ v ∈ V, v ∈ W := by
      intro v hv
      rw [hW, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hVker hv, ?_⟩
      have h := pow_card_eq_one' (G := V) (x := ⟨v, hv⟩)
      rw [hV4] at h
      exact congrArg Subtype.val h
    set VF : Finset Cz := Finset.univ.filter (· ∈ V) with hVF
    have hVFcard : VF.card = 4 := by
      rw [← hV4, hVF, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    have hWV : W = VF :=
      (Finset.eq_of_subset_of_card_le (fun v hv => hVW v (Finset.mem_filter.mp hv).2)
        (hWcard.trans hVFcard.symm.le)).symm
    have hWsub : ∀ a, η a = 1 → a ^ 4 = 1 → a ∈ V := by
      intro a h1 h4
      have ha : a ∈ W := by
        rw [hW, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, h1, h4⟩
      rw [hWV, hVF, Finset.mem_filter] at ha
      exact ha.2
    have hzV : zC ∈ V :=
      hWsub zC hzC1 (by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq zC, hzC2, one_pow])
    have hVn : ∀ c v : Cz, v ∈ V → c * v * c⁻¹ ∈ V := by
      intro c v hv
      have hv1 : η v = 1 := hVker hv
      have hv4 : v ^ 4 = 1 := by
        have h := hVW v hv
        rw [hW, Finset.mem_filter] at h
        exact h.2.2
      apply hWsub
      · rw [map_mul, map_mul, hv1, mul_one, map_inv, mul_inv_cancel]
      · rw [conj_pow, hv4, mul_one, mul_inv_cancel]
    obtain ⟨v, hvV, hv1, hvz⟩ : ∃ v ∈ V, v ≠ 1 ∧ v ≠ zC := by
      by_contra hno
      push Not at hno
      have hsub : VF ⊆ {1, zC} := by
        intro w hw
        have hwV := (Finset.mem_filter.mp hw).2
        by_cases hw1 : w = 1
        · rw [hw1]
          exact Finset.mem_insert_self _ _
        · rw [hno w hwV hw1]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have h2 := Finset.card_le_card hsub
      have h3 : ({1, zC} : Finset Cz).card ≤ 2 := Finset.card_le_two
      omega
    have hzv1 : zC * v ≠ 1 := fun h => hvz (by
      rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hzC2])
    have hzvz : zC * v ≠ zC := fun h => hv1 (mul_left_cancel (h.trans (mul_one zC).symm))
    have hzvv : zC * v ≠ v := fun h => hzCne (mul_right_cancel (h.trans (one_mul v).symm))
    have hV4' : ∀ w ∈ V, w = 1 ∨ w = zC ∨ w = v ∨ w = zC * v := by
      set F4 : Finset Cz := {1, zC, v, zC * v} with hF4
      have c1 : v ∉ ({zC * v} : Finset Cz) := by
        rw [Finset.mem_singleton]
        exact hzvv.symm
      have c2 : zC ∉ ({v, zC * v} : Finset Cz) := by
        rw [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hvz.symm, hzvz.symm⟩
      have c3 : (1 : Cz) ∉ ({zC, v, zC * v} : Finset Cz) := by
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or]
        exact ⟨hzCne.symm, hv1.symm, hzv1.symm⟩
      have hF4card : F4.card = 4 := by
        rw [hF4, Finset.card_insert_of_notMem c3, Finset.card_insert_of_notMem c2,
          Finset.card_insert_of_notMem c1, Finset.card_singleton]
      have hF4V : F4 ⊆ VF := by
        intro w hw
        rw [hVF, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [hF4, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact V.one_mem
        · exact hzV
        · exact hvV
        · exact V.mul_mem hzV hvV
      have hEq := Finset.eq_of_subset_of_card_le hF4V (by omega)
      intro w hw
      have hw' : w ∈ VF := by
        rw [hVF, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hw⟩
      rw [← hEq, hF4] at hw'
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hw'
    have hcomm : ∀ c : Cz, c ^ 3 = 1 → c * v = v * c := by
      intro c hc3
      rcases hV4' (c * v * c⁻¹) (hVn c v hvV) with h | h | h | h
      · exfalso
        apply hv1
        have h' : v = c⁻¹ * (c * v * c⁻¹) * c := by group
        rw [h', h]
        group
      · exfalso
        apply hvz
        have h' : v = c⁻¹ * (c * v * c⁻¹) * c := by group
        rw [h', h, mul_assoc, ← hzcomm c, ← mul_assoc, inv_mul_cancel, one_mul]
      · calc c * v = c * v * c⁻¹ * c := by group
          _ = v * c := by rw [h]
      · exfalso
        have hcz : c * zC * c⁻¹ = zC := by rw [hzcomm c, mul_inv_cancel_right]
        have e2 : c * (c * v * c⁻¹) * c⁻¹ = v := by
          rw [h]
          calc c * (zC * v) * c⁻¹ = c * zC * c⁻¹ * (c * v * c⁻¹) := by group
            _ = zC * (zC * v) := by rw [hcz, h]
            _ = v := by rw [← mul_assoc, hzC2, one_mul]
        have hc3' : c * (c * c) = 1 := by rw [← pow_three]; exact hc3
        have e3 : c * (c * c) * v * (c * (c * c))⁻¹ = zC * v := by
          calc c * (c * c) * v * (c * (c * c))⁻¹ = c * (c * (c * v * c⁻¹) * c⁻¹) * c⁻¹ := by
                group
            _ = zC * v := by rw [e2, h]
        rw [hc3', one_mul, inv_one, mul_one] at e3
        exact hzvv e3.symm
    have hv : ∀ i, (v : Perm (Fin 12)) * cycTw i = cycTw i * (v : Perm (Fin 12)) := by
      intro i
      have h := congrArg (fun w : Cz => ((w : alternatingGroup (Fin 12)) : Perm (Fin 12)))
        (hcomm (cC i) (hcC3 i))
      exact h.symm
    rcases eq_one_or_eq_zTw_of_commute hv with h | h
    · exact hv1 (Subtype.ext (Subtype.ext h))
    · exact hvz (Subtype.ext (Subtype.ext h))
  have hD9 : 2 ^ 9 ∣ Nat.card Cz := two_pow_nine_dvd_card_centralizer_zTwA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hD⟩ := Sylow.exists_subgroup_card_pow_prime 2 hD9
  have hKD : Nat.card (η.ker ⊓ D : Subgroup Cz) ≤ 2 := by
    by_contra hlt
    have hdvd : Nat.card (η.ker ⊓ D : Subgroup Cz) ∣ 2 ^ 9 :=
      hD ▸ Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, hk9, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk2 : 2 ≤ k := by
      by_contra hk2
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> rw [hk] at hlt <;> norm_num at hlt
    have h4 : 2 ^ 2 ∣ Nat.card (η.ker ⊓ D : Subgroup Cz) := by
      rw [hk]
      exact pow_dvd_pow 2 hk2
    obtain ⟨V₀, hV₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
    refine hV (V₀.map (η.ker ⊓ D).subtype) ?_ ?_
    · exact (map_subtype_le V₀).trans inf_le_left
    · rw [card_map_of_injective (η.ker ⊓ D).subtype_injective, hV₀]
      rfl
  have hprod : Nat.card (D.map η) * Nat.card (η.ker ⊓ D : Subgroup Cz) = 2 ^ 9 := by
    rw [← relIndex_ker, relIndex_mul_card, hD]
  have hdvd8 : Nat.card (D.map η) ∣ 40320 := by
    have h := Subgroup.card_subgroup_dvd_card (D.map η)
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 8), Fintype.card_fin] at h
    exact h
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (Dvd.intro _ hprod : Nat.card (D.map η) ∣ 2 ^ 9)
  have ha7 : a ≤ 7 := by
    by_contra ha7
    have h8 : 2 ^ 8 ∣ 40320 :=
      (pow_dvd_pow 2 (by omega : 8 ≤ a)).trans (ha ▸ hdvd8)
    norm_num at h8
  rw [ha] at hprod
  have hle : 2 ^ a * Nat.card (η.ker ⊓ D : Subgroup Cz) ≤ 2 ^ 7 * 2 :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) ha7) hKD
  rw [hprod] at hle
  norm_num at hle

theorem false_of_conj_mem_four_eight (h8 : 2 * 4 ≤ 8 + 4) {x : G}
    (hx : x * Φ (pairAlt h8 (zAlt (m := 4) ⟨2, rfl⟩)) * x⁻¹ ∈ centralizer (A : Set G)) :
    False := by
  set z := pairAlt h8 (zAlt (m := 4) ⟨2, rfl⟩) with hz
  have hzc : (zTwA : Perm (Fin 12)).cycleType = (z : Perm (Fin (8 + 4))).cycleType := by
    rw [hz, coe_pairAlt, cycleType_viaEmbeddingHom']
    exact cycleType_zTw.trans cycleType_zPair.symm
  obtain ⟨β, hβ⟩ := exists_conj_eq_of_cycleType_eq hzc zTwA_mul_self zTwA_ne_one
  refine s.false_of_conj_mem_zTw (x := x * Φ β) ?_
  have h1 : x * Φ β * Φ zTwA * (x * Φ β)⁻¹ = x * Φ z * x⁻¹ := by
    rw [← hβ, map_mul, map_mul, map_inv]
    group
  rw [h1]
  exact hx

theorem rootFusionAt_eight : RootFusionAt A Φ :=
  s.rootFusionAt_of_four (by norm_num) fun h8 _ hx => s.false_of_conj_mem_four_eight h8 hx

end AltGenSetting

end CFSG.ComponentClassification.RankTwoAlt
