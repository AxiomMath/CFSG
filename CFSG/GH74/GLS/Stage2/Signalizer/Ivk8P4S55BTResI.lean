module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResC
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResH3
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoDih

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
  CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem isConj_map' {A B : Type*} [Group A] [Group B] (f : A →* B) {a b : A} (h : IsConj a b) :
    IsConj (f a) (f b) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨f c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩

theorem sq_eq_one_of_orderOf {A : Type*} [Group A] {a : A} (ha : orderOf a = 2) : a ^ 2 = 1 := by
  rw [← ha, pow_orderOf_eq_one]

theorem eq_of_mul_eq_one_of_orderOf {A : Type*} [Group A] {a b : A} (hb : orderOf b = 2)
    (h : a * b = 1) : a = b :=
  (eq_inv_of_mul_eq_one_left h).trans
    (inv_eq_of_mul_eq_one_right (by rw [← sq]; exact sq_eq_one_of_orderOf hb))

theorem false_of_mem_J_a7 (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hIJ : barIn H I ≤ centralizer (J : Set (HBar H)))
    (e7 : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 7))
    (hDW : ∀ {w : G}, (w = z ∨ w = t) → ∀ {y : G}, y ∈ H → orderOf y = 2 → IsConj z y →
      y * w = w * y → y ≠ w →
      barIn H (zpowers y) ≤ centralizer (barIn H I : Set (HBar H)) → ¬ IsConj z (y * w))
    {w : G} (hw : w = z ∨ w = t) (hwH : w ∈ H)
    (hwJ : QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨w, hwH⟩ ∈ J)
    (hw1 : QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨w, hwH⟩ ≠ 1) : False := by
  set ν : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hν
  have hZJ := odd_card_center hL31 h hd hJ hIJ
  have hO : Odd (Nat.card (pPrimeCore 2 ↥H)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hww : w * w = 1 := by
    rcases hw with rfl | rfl
    · exact hd.u.udata.z_sq
    · exact hd.u.udata.t_sq
  set w₀ : ↥H := ⟨w, hwH⟩ with hw₀
  have hw₀2 : orderOf w₀ = 2 := orderOf_eq_prime (by rw [sq]; exact Subtype.ext hww)
    (fun h1 => hw1 (by rw [h1, map_one]))
  set j₀ : ↥J := ⟨ν w₀, hwJ⟩ with hj₀
  have hj₀2 : orderOf j₀ = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_mk_eq_two hO hw₀2
  set yb₀ : ↥J ⧸ center ↥J := QuotientGroup.mk' (center ↥J) j₀ with hyb₀
  have hy₀ : orderOf yb₀ = 2 := orderOf_mk_eq_two hZJ hj₀2
  obtain ⟨y₁, c, h11, h01, hne, hc0, hc1⟩ := ResA7.klein_of_involution e7 hy₀
  have hy₁2 : orderOf y₁ = 2 := by
    refine orderOf_eq_prime (by rw [sq]; exact h11) (fun h1 => ?_)
    rw [h1] at hc0
    have : yb₀ = 1 :=
      calc yb₀ = c⁻¹ * (c * yb₀ * c⁻¹) * c := by group
        _ = 1 := by rw [hc0]; group
    rw [this, orderOf_one] at hy₀
    exact absurd hy₀ (by norm_num)
  obtain ⟨j₁, hj₁2, hj₁c, hj₁y⟩ := exists_commuting_involution_lift hZJ hj₀2 hy₁2 h01.symm
  have hj₁j₀ : j₁ ≠ j₀ := fun h1 => hne (by rw [← hj₁y, h1])
  have hconj₁ : IsConj j₁ j₀ := isConj_of_isConj_mk hZJ hj₁2 hj₀2
    (by rw [hj₁y]; exact (isConj_iff.mpr ⟨c, hc0⟩).symm)
  have hj₁₀2 : orderOf (j₁ * j₀) = 2 :=
    orderOf_eq_prime
      (by rw [hj₁c.mul_pow, sq_eq_one_of_orderOf hj₁2, sq_eq_one_of_orderOf hj₀2, one_mul])
      (fun h1 => hj₁j₀ (eq_of_mul_eq_one_of_orderOf hj₀2 h1))
  have hconj₁₀ : IsConj (j₁ * j₀) j₀ := by
    refine isConj_of_isConj_mk hZJ hj₁₀2 hj₀2 ?_
    rw [map_mul, hj₁y, ← hyb₀, ← h01]
    exact ((isConj_iff.mpr ⟨c, hc0⟩).trans (isConj_iff.mpr ⟨c, hc1⟩)).symm
  have hx₁2 : orderOf (j₁ : HBar H) = 2 := by rw [Subgroup.orderOf_coe]; exact hj₁2
  have hx₁c : Commute (j₁ : HBar H) (ν w₀) := by
    have := congrArg Subtype.val hj₁c.eq
    exact this
  obtain ⟨y, hy2, hyc, hyν⟩ := exists_commuting_involution_lift hO hw₀2 hx₁2 hx₁c
  have hyw : IsConj y w₀ := isConj_of_isConj_mk hO hy2 hw₀2
    (by rw [hyν]; exact isConj_map' J.subtype hconj₁)
  have hyw₀ : y ≠ w₀ := by
    intro h1
    apply hj₁j₀
    apply Subtype.ext
    show (j₁ : HBar H) = ν w₀
    rw [← hyν, h1]
  have hyw2 : orderOf (y * w₀) = 2 :=
    orderOf_eq_prime
      (by rw [hyc.mul_pow, sq_eq_one_of_orderOf hy2, sq_eq_one_of_orderOf hw₀2, one_mul])
      (fun h1 => hyw₀ (eq_of_mul_eq_one_of_orderOf hw₀2 h1))
  have hyw' : IsConj (y * w₀) w₀ := isConj_of_isConj_mk hO hyw2 hw₀2
    (by rw [map_mul, hyν]; exact isConj_map' J.subtype hconj₁₀)
  have hzw : IsConj z w := by
    rcases hw with rfl | rfl
    · exact IsConj.refl _
    · exact hd.u.udata.conj_zt
  have hzy : IsConj z (y : G) := hzw.trans (isConj_map' H.subtype hyw).symm
  have hzyw : IsConj z ((y : G) * w) := hzw.trans (isConj_map' H.subtype hyw').symm
  refine hDW hw y.2 (by rw [Subgroup.orderOf_coe]; exact hy2) hzy
    (congrArg Subtype.val hyc.eq) (fun h1 => hyw₀ (Subtype.ext h1)) ?_ hzyw
  rw [L52Two.barIn_zpowers_eq H y.2, zpowers_le, Subgroup.mem_centralizer_iff]
  intro i hi
  have hyJ : P34.mkH H ⟨(y : G), y.2⟩ ∈ J := by
    show ν y ∈ J
    rw [hyν]
    exact j₁.2
  exact ((Subgroup.mem_centralizer_iff.mp (hIJ hi)) _ hyJ).symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
