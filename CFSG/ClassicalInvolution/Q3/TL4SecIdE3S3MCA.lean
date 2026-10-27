module

public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoM12A
public import Certificates.Certificate55124
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLiftClasses

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3MC

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.ComponentClassification.M12Cover CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12

variable {Y : Type} [Group Y]

theorem eq_one_or_eq_of_mem_zpowers {c x : Y} (hc : orderOf c = 2)
    (hx : x ∈ Subgroup.zpowers c) : x = 1 ∨ x = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hc]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show k % ((2 : ℕ) : ℤ) = 0 from h, zpow_zero]
  · right
    rw [show k % ((2 : ℕ) : ℤ) = 1 from h, zpow_one]

theorem q8_six : (∀ w ∈ six (QuaternionGroup.a 1 : QuaternionGroup 2) (QuaternionGroup.xa 0),
    w * w = QuaternionGroup.a 2) ∧
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  decide

theorem six_mem_qL {b : Bool} {u v : Equiv.Perm (Fin 12)}
    (hu : u ∈ qL b) (hv : v ∈ qL b) : ∀ w ∈ six u v, w ∈ qL b := by
  intro w hw
  simp only [six, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | assumption
    | repeat (first | apply qL_mul | assumption)

theorem quatOK_qL (b : Bool) :
    quatOK m12Rep1 ((qL (!b)).getD 1 1) (qL b) = true := by
  obtain ⟨h0, h1, -⟩ := Certificates.certificate55124
  cases b
  · exact h0
  · exact h1

theorem fix12_rep2 : fix12 m12Rep2 = 0 := by
  have h := Certificates.certificate55124.2.2
  simp only [chkFix2, beq_iff_eq] at h
  exact h

variable [Finite Y]

theorem false_of_rep1 {R : Subgroup Y} {S : Sylow 2 R} {t c : Y} (hd : TightDatum R S t)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) (hc : orderOf c = 2)
    (hcZ : c ∈ Subgroup.center Y) (π : Y →* ↥NativeSporadic.M12) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers c)
    (h4 : ∀ v : Y, orderOf (π v) = 2 → fixedCount (π v) = 4 → orderOf v = 2)
    (h0 : ∀ v : Y, orderOf (π v) = 2 → fixedCount (π v) = 0 → v ^ 2 = c)
    (htc : t ∉ Subgroup.zpowers c)
    (ht1 : ((π t : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = m12Rep1) : False := by
  classical
  obtain ⟨e⟩ := hq
  set φ : QuaternionGroup 2 →* Y :=
    R.subtype.comp ((S : Subgroup R).subtype.comp e.symm.toMonoidHom) with hφ
  have hφi : Function.Injective φ :=
    R.subtype_injective.comp ((S : Subgroup R).subtype_injective.comp e.symm.injective)
  have hφR : ∀ q, φ q ∈ R := fun q => ((e.symm q : ↥(S : Subgroup R)) : ↥R).2
  have ha2 : orderOf (QuaternionGroup.a 2 : QuaternionGroup 2) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  have hφt : φ (QuaternionGroup.a 2) = t :=
    hd.eq_of_orderOf_eq_two (hφR _) (by rw [orderOf_injective φ hφi, ha2])
  obtain ⟨hQsq, hQnc⟩ := q8_six
  set i := φ (QuaternionGroup.a 1) with hi
  set j := φ (QuaternionGroup.xa 0) with hj
  have hsix : six i j = (six (QuaternionGroup.a 1) (QuaternionGroup.xa 0)).map φ := by
    simp only [six, List.map_cons, List.map_nil, map_mul, hi, hj]
  have hsixsq : ∀ w ∈ six i j, w * w = t := by
    intro w hw
    rw [hsix] at hw
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hw
    rw [← map_mul, hQsq q hq, hφt]
  have hsixR : ∀ w ∈ six i j, w ∈ R := by
    intro w hw
    rw [hsix] at hw
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hw
    exact hφR q
  have hij : i * j ≠ j * i := fun h => hQnc (hφi (by rw [map_mul, map_mul]; exact h))
  have hcR : c ∉ R := fun h => htc (by
    rw [← hd.eq_of_orderOf_eq_two h hc]
    exact Subgroup.mem_zpowers c)
  have hkerc : ∀ x, π x = 1 → x = 1 ∨ x = c := fun x hx =>
    eq_one_or_eq_of_mem_zpowers hc (hker ▸ MonoidHom.mem_ker.mpr hx)
  have hcomm_of : ∀ y w : Y, w ∈ R → y * w * y⁻¹ ∈ R → π (y * w * y⁻¹ * w⁻¹) = 1 →
      y * w = w * y := by
    intro y w hw hyw h
    rcases hkerc _ h with h1 | h1
    · calc y * w = y * w * y⁻¹ * w⁻¹ * (w * y) := by group
        _ = w * y := by rw [h1, one_mul]
    · exact absurd (h1 ▸ R.mul_mem hyw (R.inv_mem hw)) hcR
  set u : Equiv.Perm (Fin 12) := ((π i : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) with hu
  set v : Equiv.Perm (Fin 12) := ((π j : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) with hv
  have hu2 : u * u = m12Rep1 := by
    rw [hu, ← Subgroup.coe_mul, ← map_mul, hsixsq i (by simp [six]), ht1]
  have hv2 : v * v = m12Rep1 := by
    rw [hv, ← Subgroup.coe_mul, ← map_mul, hsixsq j (by simp [six]), ht1]
  have huv : u * v ≠ v * u := by
    intro h
    apply hij
    have hk : π (i * j * i⁻¹ * j⁻¹) = 1 := by
      apply Subtype.ext
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
      rw [← hu, ← hv, h]
      group
    have hiR := hsixR i (by simp [six])
    have hjR := hsixR j (by simp [six])
    rcases hkerc _ hk with h1 | h1
    · calc i * j = i * j * i⁻¹ * j⁻¹ * (j * i) := by group
        _ = j * i := by rw [h1, one_mul]
    · exact absurd (h1 ▸ R.mul_mem (R.mul_mem (R.mul_mem hiR hjR) (R.inv_mem hiR))
        (R.inv_mem hjR)) hcR
  obtain ⟨b, hub, hvb⟩ := qL_same (π i).2 hu2 (π j).2 hv2 huv
  have hchk := quatOK_qL b
  set ybar := (qL (!b)).getD 1 1 with hybar
  simp only [quatOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨hy2, hycomm⟩, hpairs⟩ := hchk
  have hpair := hpairs u hub v hvb
  simp only [pairOK, hu2, hv2, ne_eq, huv, not_false_eq_true, and_self, ↓reduceIte,
    Bool.and_eq_true, List.any_eq_true] at hpair
  obtain ⟨⟨w₀, hw₀, hw₀ok⟩, ⟨w₄, hw₄, hw₄ok⟩⟩ := hpair
  simp only [wOK, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, beq_iff_eq] at hw₀ok hw₄ok
  obtain ⟨⟨⟨-, hne₀⟩, hinv₀⟩, hfix₀⟩ := hw₀ok
  obtain ⟨⟨⟨-, hne₄⟩, hinv₄⟩, hfix₄⟩ := hw₄ok
  have hsixuv : six u v = (six i j).map fun w => ((π w : ↥NativeSporadic.M12) :
      Equiv.Perm (Fin 12)) := by
    simp [six, hu, hv, map_mul]
  have hsix_qL := six_mem_qL hub hvb
  rw [hsixuv] at hw₀ hw₄ hsix_qL
  obtain ⟨ŵ₀, hŵ₀, rfl⟩ := List.mem_map.1 hw₀
  obtain ⟨ŵ₄, hŵ₄, rfl⟩ := List.mem_map.1 hw₄
  have hymem : ybar ∈ qL (!b) := by
    rw [hybar, List.getD_eq_getElem _ _ (by rw [qL_length]; norm_num)]
    exact List.getElem_mem _
  obtain ⟨y, hy⟩ := hπ ⟨ybar, (qL_memC hymem).1⟩
  have hyt : y * t = t * y := by
    have hk : π ((y * y)⁻¹ * t) = 1 := by
      apply Subtype.ext
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one, hy]
      rw [ht1, hy2, inv_mul_cancel]
    rcases hkerc _ hk with h1 | h1
    · have ht : t = y * y := by
        rw [inv_mul_eq_one] at h1
        exact h1.symm
      rw [ht]
      group
    · have ht : t = y * y * c := by
        rw [← h1]
        group
      have hcy : c * y = y * c := (Subgroup.mem_center_iff.mp hcZ y).symm
      rw [ht]
      calc y * (y * y * c) = y * y * (y * c) := by group
        _ = y * y * (c * y) := by rw [hcy]
        _ = y * y * c * y := by group
  have hyN : y ∈ Subgroup.normalizer (R : Set Y) :=
    hd.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hyt)
  have hyw : ∀ w ∈ six i j, y * w = w * y := by
    intro w hw
    have hwR := hsixR w hw
    refine hcomm_of y w hwR ((Subgroup.mem_normalizer_iff.mp hyN w).mp hwR) ?_
    have hmem := hsix_qL _ (List.mem_map_of_mem hw)
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one, hy]
    rw [← hycomm _ hmem]
    group
  have hsq : ∀ w ∈ six i j, (w * y) ^ 2 = t * (y * y) := by
    intro w hw
    calc (w * y) ^ 2 = w * (y * w) * y := by rw [sq]; group
      _ = w * (w * y) * y := by rw [hyw w hw]
      _ = w * w * (y * y) := by group
      _ = t * (y * y) := by rw [hsixsq w hw]
  have hord : ∀ w : Y, ((π w : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) * ybar ≠ 1 →
      ((π w : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) * ybar *
        (((π w : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) * ybar) = 1 →
      orderOf (π (w * y)) = 2 := by
    intro w hne hinv
    rw [← Subgroup.orderOf_coe, map_mul, hy, Subgroup.coe_mul]
    exact orderOf_eq_prime (by rw [sq]; exact hinv) hne
  have hc0 := h0 _ (hord ŵ₀ hne₀ hinv₀) (by
    rw [fixedCount, map_mul, hy]
    exact hfix₀)
  have hc4 := h4 _ (hord ŵ₄ hne₄ hinv₄) (by
    rw [fixedCount, map_mul, hy]
    exact hfix₄)
  have hc1 : c = 1 := by
    rw [← hc0, hsq ŵ₀ hŵ₀, ← hsq ŵ₄ hŵ₄, ← hc4, pow_orderOf_eq_one]
  rw [hc1, orderOf_one] at hc
  exact absurd hc (by norm_num)

end CFSG.ClassicalInvolution.Q3.TL4.E3S3MC
