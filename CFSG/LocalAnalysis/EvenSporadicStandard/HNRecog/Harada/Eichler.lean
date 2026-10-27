module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.EichlerDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.OrthData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

private theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  have hval : c.val ≠ 0 := fun hv => h ((ZMod.val_eq_zero c).1 hv)
  have h1 : c.val = 1 := by have := ZMod.val_lt c; omega
  exact (ZMod.val_eq_one (by norm_num : 1 < 2) c).1 h1

private theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  by_cases h : c = 0
  · exact Or.inl h
  · exact Or.inr (zmod2_eq_one_of_ne_zero h)

private theorem zmod2_mul_self (c : ZMod 2) : c * c = c := by
  rcases zmod2_eq_zero_or_one c with h | h <;> simp [h]

private theorem zmod2_add_self_self (p a : ZMod 2) : p + a + a = p := by
  revert p a
  decide +kernel

private theorem add_self_eq_zero_V6 (x : V6) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

private theorem qm_zero : qm (0 : V6) = 0 := by decide

private theorem bil_comm_zero {x y : V6} (h : bil x y = 0) : bil y x = 0 := by
  rwa [bil_comm]

private theorem perm_zero {g : Equiv.Perm V6} (hg : IsAddPerm g) : g 0 = 0 := by
  have h : g 0 = g 0 + g 0 := by simpa using hg 0 0
  rwa [add_self_eq_zero_V6] at h

private theorem perm_smul {g : Equiv.Perm V6} (hg : IsAddPerm g) (c : ZMod 2) (v : V6) :
    g (c • v) = c • g v := by
  rcases zmod2_eq_zero_or_one c with h | h
  · rw [h, zero_smul, zero_smul]; exact perm_zero hg
  · rw [h, one_smul, one_smul]

private theorem zmod2_swap {a b c d : ZMod 2} (h : a + b = c + d) : a + c = b + d := by
  revert h
  revert a b c d
  decide +kernel

private theorem add_eq_add_iff_V6 {a b c d : V6} : a + b = c + d ↔ a + c = b + d := by
  constructor
  · intro h
    funext i
    exact zmod2_swap (congrFun h i)
  · intro h
    funext i
    exact zmod2_swap (a := a i) (b := c i) (c := b i) (d := d i) (congrFun h i)

set_option maxRecDepth 100000 in
private theorem exists_bil_eq_one_of_ne_zero (w : V6) (hw : w ≠ 0) : ∃ x, bil x w = 1 := by
  revert hw
  revert w
  decide +kernel

private theorem eichF_add_self_aux (w u a : V6) :
    eichF w u a + a = bil a w • u + (bil a u + qm u * bil a w) • w := by
  rw [eichF]
  rw [show a + bil a w • u + (bil a u + qm u * bil a w) • w + a
        = (a + a) + (bil a w • u + (bil a u + qm u * bil a w) • w) by abel]
  rw [add_self_eq_zero_V6, zero_add]

theorem bil_zero_left (x : V6) : bil 0 x = 0 := by
  simp [bil]

theorem bil_zero_right (x : V6) : bil x 0 = 0 := by
  simp [bil]

theorem bil_smul_right (c : ZMod 2) (x y : V6) : bil x (c • y) = c * bil x y := by
  simp only [bil, Pi.smul_apply, smul_eq_mul]; ring

theorem eichF_zero (w x : V6) : eichF w 0 x = x := by
  rw [eichF]
  simp only [bil_zero_right, qm_zero, zero_mul, add_zero, smul_zero, zero_smul]

theorem eichF_comp {w u u' : V6} (hu : bil u w = 0) (hu' : bil u' w = 0) (x : V6) :
    eichF w u (eichF w u' x) = eichF w (u + u') x := by
  funext i
  simp only [eichF, Pi.add_apply, Pi.smul_apply, smul_eq_mul, bil_add_left, bil_add_right,
    bil_smul_left, bil_smul_right, bil_self, qm_add, bil_comm_zero hu, bil_comm_zero hu',
    bil_comm u' u, hu, hu']
  ring_nf
  try (simp only [pow_two, zmod2_mul_self, zmod2_add_self_self, CharTwo.add_self_eq_zero,
    CharTwo.two_eq_zero, mul_zero, zero_mul, add_zero, zero_add])

theorem eichF_self {w u : V6} (hu : bil u w = 0) (x : V6) :
    eichF w u (eichF w u x) = x := by
  rw [eichF_comp hu hu, add_self_eq_zero_V6, eichF_zero]

theorem eichF_apply_w {w u : V6} (hu : bil u w = 0) : eichF w u w = w := by
  rw [eichF, bil_self, bil_comm_zero hu]
  simp only [zero_smul, mul_zero, add_zero]

theorem eichF_add_w {w u : V6} (hw : qm w = 0) (hu : bil u w = 0) (x : V6) :
    eichF w (u + w) x = eichF w u x := by
  funext i
  simp only [eichF, Pi.add_apply, Pi.smul_apply, smul_eq_mul, bil_add_left, bil_add_right,
    bil_smul_left, bil_smul_right, bil_self, qm_add, bil_comm_zero hu, hu, hw]
  ring_nf
  try (simp only [pow_two, zmod2_mul_self, zmod2_add_self_self, CharTwo.add_self_eq_zero,
    CharTwo.two_eq_zero, mul_zero, zero_mul, add_zero, zero_add])

theorem eichF_conj {g : Equiv.Perm V6} (hg : g ∈ OrthMinus) {w u : V6} (hgw : g w = w) (x : V6) :
    g (eichF w u x) = eichF w (g u) (g x) := by
  have hbw : bil (g x) w = bil x w := by
    have h1 : bil (g x) (g w) = bil x w := bil_apply_of_mem_orthOf isQF_qm hg x w
    rwa [hgw] at h1
  have hbu : bil (g x) (g u) = bil x u := bil_apply_of_mem_orthOf isQF_qm hg x u
  have hqu : qm (g u) = qm u := hg.2 u
  simp only [eichF]
  rw [hg.1, hg.1, perm_smul hg.1, perm_smul hg.1, hgw, hbw, hbu, hqu]

theorem eichF_eq_iff {w u u' : V6} (hw : qm w = 0) (hw0 : w ≠ 0) (hu : bil u w = 0)
    (hu' : bil u' w = 0) :
    (∀ x, eichF w u x = eichF w u' x) ↔ (u + u' = 0 ∨ u + u' = w) := by
  constructor
  · intro hP
    obtain ⟨x₀, hx₀⟩ := exists_bil_eq_one_of_ne_zero w hw0
    have hEq : eichF w u x₀ + x₀ = eichF w u' x₀ + x₀ := by rw [hP x₀]
    rw [eichF_add_self_aux, eichF_add_self_aux] at hEq
    simp only [hx₀, one_smul, mul_one] at hEq
    have h2 : u + u' = ((bil x₀ u + qm u) + (bil x₀ u' + qm u')) • w := by
      rw [add_eq_add_iff_V6.mp hEq, ← add_smul]
    rcases zmod2_eq_zero_or_one ((bil x₀ u + qm u) + (bil x₀ u' + qm u')) with hc | hc
    · left; rw [h2, hc, zero_smul]
    · right; rw [h2, hc, one_smul]
  · rintro (h0 | hw')
    · intro x
      have hu'_eq : u' = u := by
        have h2 : u + 0 = u' := by rw [← h0, ← add_assoc, add_self_eq_zero_V6, zero_add]
        rw [add_zero] at h2
        exact h2.symm
      rw [hu'_eq]
    · intro x
      have hu'_eq : u' = u + w := by
        have h2 : u + w = u' := by rw [← hw', ← add_assoc, add_self_eq_zero_V6, zero_add]
        exact h2.symm
      rw [hu'_eq, eichF_add_w hw hu]

theorem eichF_add_self (w u a : V6) :
    eichF w u a + a = bil a w • u + (bil a u + qm u * bil a w) • w :=
  eichF_add_self_aux w u a

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
