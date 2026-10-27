module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveB
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveConj

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G] {z : G}

theorem isSylowOf_of_forall_card_le {C P : Subgroup G} {p : ℕ} [Fact p.Prime] (hPC : P ≤ C)
    (hP : IsPGroup p P) (hmax : ∀ B : Subgroup G, B ≤ C → IsPGroup p B → Nat.card B ≤ Nat.card P) :
    IsSylowOf C p P := by
  obtain ⟨Q⟩ : Nonempty (Sylow p C) := inferInstance
  have hQ : IsSylowOf C p ((Q : Subgroup C).map C.subtype) := ⟨Q, rfl⟩
  have h1 := hmax _ (Subgroup.map_subtype_le _) (Q.isPGroup'.map _)
  have h2 := card_le_of_isSylowOf hQ hP hPC
  exact isSylowOf_of_card_eq hQ hPC (le_antisymm h2 h1)

omit [Finite G] in
theorem conj_mul_comm {a b : G} (c : G) (hab : a * b = b * a) :
    c * a * c⁻¹ * (c * b * c⁻¹) = c * b * c⁻¹ * (c * a * c⁻¹) := by
  calc c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
    _ = c * (b * a) * c⁻¹ := by rw [hab]
    _ = _ := by group

namespace Hyp

variable {fr : JankoFrame G z}

theorem card_centralizer_eq_two_mul (h : Hyp fr) {y u : G} (hy : IsConj y fr.s₃)
    (hu : orderOf u = 2) (huy : u ∈ centralizer ({y} : Set G)) :
    Nat.card (centralizer ({y} : Set G)) =
      2 * Nat.card (oddCoreOf (centralizer ({y} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : Nat.card (zpowers u) = 2 := by rw [Nat.card_zpowers, hu]
  have hPC : zpowers u ≤ centralizer ({y} : Set G) := Subgroup.zpowers_le.mpr huy
  have hPp : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := 1) (by rw [hP2, pow_one])
  have hsyl : IsSylowOf (centralizer ({y} : Set G)) 2 (zpowers u) :=
    isSylowOf_of_forall_card_le hPC hPp fun B hB hBp => hP2 ▸ h.p7.card_le_two y hy B hB hBp
  have := card_oddCoreOf_mul_of_isCyclic hsyl inferInstance (by rw [hP2]; norm_num)
  rw [hP2] at this
  omega

theorem card_le_of_isConj_s₃ (h : Hyp fr) {y : G} (hy : IsConj y fr.s₃) {B : Subgroup G}
    (hB : B ≤ normalizer (zpowers y : Set G)) (hB3 : IsPGroup 3 B) : Nat.card B ≤ 3 ^ 10 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp hy.symm
  subst hc
  have hs₃H : fr.s₃ ∈ centralizer ({z} : Set G) := fr.E_le fr.s₃_mem_E
  have hs₃3 : fr.s₃ ^ 3 = 1 := by rw [← fr.orderOf_s₃, pow_orderOf_eq_one]
  obtain ⟨b, hbH, hb2, hbs⟩ := fr.exists_invert fr.s₃
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h6 := fr.card_centralizer_inv fr.s₃ hs₃H hs₃3 fr.card_centralizer_s₃ b hbH hb2 hbs
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := (centralizer ({fr.s₃} : Set G) ⊓
    centralizer ({b} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G)) 3 (by rw [h6]; norm_num)
  rw [← Subgroup.orderOf_coe] at hw
  obtain ⟨⟨hws, hwb⟩, hwz⟩ := w.2
  set w₀ : G := w.1
  set y := c * fr.s₃ * c⁻¹ with hy_def
  set z' := c * z * c⁻¹ with hz'_def
  set b' := c * b * c⁻¹ with hb'_def
  set w' := c * w₀ * c⁻¹ with hw'_def
  have hzs : z * fr.s₃ = fr.s₃ * z := (Subgroup.mem_centralizer_singleton_iff.mp hs₃H).symm
  have hz'2 : orderOf z' = 2 := by rw [orderOf_conj_eq, h.set.orderOf_z]
  have hb'2 : orderOf b' = 2 := by rw [orderOf_conj_eq, hb2]
  have hy3 : orderOf y = 3 := by rw [orderOf_conj_eq, fr.orderOf_s₃]
  have hz'y : z' ∈ centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (conj_mul_comm c hzs)
  have hb'y : b' * y * b'⁻¹ = y⁻¹ := by
    calc b' * y * b'⁻¹ = c * (b * fr.s₃ * b⁻¹) * c⁻¹ := by
          rw [hb'_def, hy_def]; group
      _ = y⁻¹ := by rw [hbs, hy_def]; group
  have hbz : b * z = z * b := Subgroup.mem_centralizer_singleton_iff.mp hbH
  have hcomm : Commute z' b' := (conj_mul_comm c hbz).symm
  have hw'y : w' ∈ centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (conj_mul_comm c (Subgroup.mem_centralizer_singleton_iff.mp hws))
  have hw'b : w' ∈ centralizer ({b'} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (conj_mul_comm c (Subgroup.mem_centralizer_singleton_iff.mp hwb))
  have hw'z : w' ∈ centralizer ({z'} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (conj_mul_comm c (Subgroup.mem_centralizer_singleton_iff.mp hwz))
  have hw'3 : orderOf w' = 3 := by rw [orderOf_conj_eq]; exact hw
  set C := centralizer ({y} : Set G)
  set O := oddCoreOf C
  have hC : Nat.card C = 2 * Nat.card O := h.card_centralizer_eq_two_mul hy hz'2 hz'y
  have hBC : B ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hodd : Odd (orderOf x) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB3
      have hd := Subgroup.orderOf_dvd_natCard B hx
      rw [hk] at hd
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
      rw [hm]
      exact Odd.pow (by decide)
    have := conj_eq_of_odd hy3 (hB hx) hodd
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [this]
  have hBodd : Odd (Nat.card B) := odd_card_of_isPGroup (by norm_num) hB3
  have hBO : B ≤ O := le_oddCoreOf_of_card hC hBC hBodd
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreOf C
  have hz'O : z' ∈ normalizer (O : Set G) := le_normalizer_oddCoreOf C hz'y
  have hb'O : b' ∈ normalizer (O : Set G) := by
    refine mem_normalizer_oddCoreOf ?_
    have hn : b' ∈ normalizer ((zpowers y : Subgroup G) : Set G) := by
      refine CFSG.Walter.J1.mem_normalizer_of_conj_mem fun x hx => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← conj_zpow, hb'y]
      exact zpow_mem (inv_mem (Subgroup.mem_zpowers y)) k
    have := mem_normalizer_centralizer hn
    rwa [centralizer_zpowers] at this
  have hz'z' : z' * z' = 1 := (CFSG.Walter.J1.orderOf_eq_two_iff.mp hz'2).1
  have hb'b' : b' * b' = 1 := (CFSG.Walter.J1.orderOf_eq_two_iff.mp hb'2).1
  have hz'1 : z' ≠ 1 := (CFSG.Walter.J1.orderOf_eq_two_iff.mp hz'2).2
  have hb'1 : b' ≠ 1 := (CFSG.Walter.J1.orderOf_eq_two_iff.mp hb'2).2
  have hyy : y ≠ y⁻¹ := by
    intro he
    have h2 : y ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [he]
      exact mul_inv_cancel y
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hy3] at this
    exact absurd this (by norm_num)
  have hz'b' : z' ≠ b' := by
    intro he
    apply hyy
    rw [← hb'y, ← he, Subgroup.mem_centralizer_singleton_iff.mp hz'y, mul_inv_cancel_right]
  have hBW := CFSG.Walter.J1.card_mul_card_sq_eq_mul hz'z' hb'b' hz'1 hb'1 hz'b' hcomm O hz'O
    hb'O hOodd
  have hzb2 : orderOf (z' * b') = 2 := by
    refine CFSG.Walter.J1.orderOf_eq_two_iff.mpr ⟨?_, ?_⟩
    · calc z' * b' * (z' * b') = z' * (b' * z') * b' := by group
        _ = z' * (z' * b') * b' := by rw [hcomm.eq]
        _ = (z' * z') * (b' * b') := by group
        _ = 1 := by rw [hz'z', hb'b', one_mul]
    · intro h1
      apply hz'b'
      rw [← mul_one z', ← hb'b', ← mul_assoc, h1, one_mul]
  have hdvd : ∀ v : G, orderOf v = 2 →
      Nat.card (O ⊓ centralizer ({v} : Set G) : Subgroup G) ∣ 362880 := fun v hv =>
    (h.set.twoANine_centralizer v hv).card_eq ▸ Subgroup.card_dvd_of_le inf_le_right
  have h3 : 3 ∣ Nat.card (O ⊓ centralizer ({z'} : Set G) ⊓ centralizer ({b'} : Set G) :
      Subgroup G) := by
    have hw'O : w' ∈ O := by
      have hle := le_oddCoreOf_of_card hC (Subgroup.zpowers_le.mpr hw'y)
        (by rw [Nat.card_zpowers, hw'3]; decide)
      exact hle (Subgroup.mem_zpowers w')
    have := Subgroup.orderOf_dvd_natCard _
      (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hw'O, hw'z⟩, hw'b⟩)
    rwa [hw'3] at this
  have hne : ∀ K : Subgroup G, Nat.card K ≠ 0 := fun K => Nat.card_pos.ne'
  have key := congrArg (fun n => n.factorization 3) hBW
  rw [Nat.factorization_mul (hne _) (pow_ne_zero _ (hne _)), Nat.factorization_pow,
    Nat.factorization_mul (mul_ne_zero (hne _) (hne _)) (hne _),
    Nat.factorization_mul (hne _) (hne _)] at key
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at key
  have b1 := factorization_le_of_dvd (by norm_num) (hdvd z' hz'2) 3
  have b2 := factorization_le_of_dvd (by norm_num) (hdvd b' hb'2) 3
  have b3 := factorization_le_of_dvd (by norm_num) (hdvd _ hzb2) 3
  rw [factorization_card_twoANine] at b1 b2 b3
  have b0 : 1 ≤ (Nat.card (O ⊓ centralizer ({z'} : Set G) ⊓ centralizer ({b'} : Set G) :
      Subgroup G)).factorization 3 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three (hne _)).mp h3
  have hO10 : (Nat.card O).factorization 3 ≤ 10 := by omega
  calc Nat.card B ≤ 3 ^ (Nat.card O).factorization 3 := card_le_of_isPGroup_le hB3 hBO
    _ ≤ 3 ^ 10 := Nat.pow_le_pow_right (by norm_num) hO10

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve
