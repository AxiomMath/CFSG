module

public import CFSG.ClassicalGroups.Unitary.Transitivity

public section

namespace CFSG.ClassicalGroups.Unitary

open Matrix CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem herm_smul_sub_self_right (hσ : ∀ c, σ (σ c) = c) {t : SUid σ n} (ht : t * t = 1)
    (x y : Fin n → K) :
    herm σ x (t • y - y) = herm σ (t • x - x) y := by
  have h1 : t • (t • x) = x := by rw [smul_smul, ht, one_smul]
  have h : herm σ x (t • y) = herm σ (t • x) y := by
    conv_lhs => rw [← h1]
    exact herm_smul_smul σ t (t • x) y
  rw [herm_sub_right, herm_sub_left, h]

theorem smul_sub_self_smul_sub_self [CharP K 2] {t : SUid σ n} (ht : t * t = 1)
    (x : Fin n → K) :
    t • (t • x - x) - (t • x - x) = 0 := by
  have h1 : t • (t • x) = x := by rw [smul_smul, ht, one_smul]
  rw [smul_sub, h1]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  funext i
  simp only [Pi.sub_apply, Pi.zero_apply]
  linear_combination (x i - (t • x) i) * h2

theorem herm_smul_sub_self_self [CharP K 2] (hσ : ∀ c, σ (σ c) = c) {t : SUid σ n}
    (ht : t * t = 1) (x y : Fin n → K) :
    herm σ (t • x - x) (t • y - y) = 0 := by
  rw [herm_smul_sub_self_right (σ := σ) (n := n) hσ (t := t) ht
    (x := t • x - x) (y := y),
    smul_sub_self_smul_sub_self (σ := σ) (n := n) (t := t) ht (x := x), herm_zero_left]

theorem exists_herm_smul_sub_self_ne_zero (hσ : IsUnitaryInvolution σ) {t : SUid σ n}
    (ht : t * t = 1) (ht1 : t ≠ 1) : ∃ u : Fin n → K, herm σ (t • u - u) u ≠ 0 := by
  by_contra! h
  have hNadd : ∀ u v : Fin n → K,
      t • (u + v) - (u + v) = (t • u - u) + (t • v - v) := by
    intro u v
    rw [smul_add]
    abel
  have hb : ∀ (u v : Fin n → K),
      herm σ (t • u - u) v + σ (herm σ (t • u - u) v) = 0 := by
    intro u v
    have h0 : herm σ (t • (u + v) - (u + v)) (u + v) = 0 := h (u + v)
    simp only [hNadd u v, herm_add_left, herm_add_right, h u, h v, add_zero,
      zero_add] at h0
    have hvu : herm σ (t • v - v) u = σ (herm σ (t • u - u) v) := by
      rw [← herm_smul_sub_self_right hσ.invol ht (x := v) (y := u), herm_conj σ hσ.invol]
    rw [hvu] at h0
    simpa only [add_comm] using h0
  obtain ⟨lam, hlam⟩ := hσ.exists_ne
  have hlam' : lam - σ lam ≠ 0 := by
    rw [sub_ne_zero]
    exact Ne.symm hlam
  have hzero : ∀ (u v : Fin n → K), herm σ (t • u - u) v = 0 := by
    intro u v
    have h1 := hb u (lam • v)
    rw [herm_smul_right, map_mul] at h1
    have hneg : σ (herm σ (t • u - u) v) = -herm σ (t • u - u) v := by
      linear_combination hb u v
    have hlam_b : (lam - σ lam) * herm σ (t • u - u) v = 0 := by
      rw [hneg] at h1
      linear_combination h1
    exact (mul_eq_zero.mp hlam_b).resolve_left hlam'
  have hNu : ∀ u : Fin n → K, t • u - u = 0 := fun u => eq_zero_of_herm σ (hzero u)
  apply ht1
  exact ext_smul σ fun v => by rw [sub_eq_zero.mp (hNu v), one_smul]

theorem herm_smul_sub_self_fixed (hσ : IsUnitaryInvolution σ) {t : SUid σ n}
    (ht : t * t = 1) (u : Fin n → K) :
    σ (herm σ (t • u - u) u) = herm σ (t • u - u) u := by
  rw [← herm_conj σ hσ.invol (x := t • u - u) (y := u)]
  exact herm_smul_sub_self_right hσ.invol ht u u

theorem eichler_smul_smul_sub_self [CharP K 2] (hσ : IsUnitaryInvolution σ) {t : SUid σ n}
    (ht : t * t = 1) {u y : Fin n → K} (hy : herm σ (t • u - u) y = 0) {c : K}
    (hc : c + σ c = -herm σ y y) (x : Fin n → K) :
    eichler hσ.invol (herm_smul_sub_self_self hσ.invol ht u u) hy hc • (t • x - x) =
      t • (x - herm σ y (t • x - x) • u) - (x - herm σ y (t • x - x) • u) := by
  set a := t • u - u with hadef
  have haa : herm σ a a = 0 := herm_smul_sub_self_self hσ.invol ht u u
  have haN : herm σ a (t • x - x) = 0 := herm_smul_sub_self_self hσ.invol ht u x
  rw [eichler_smul hσ.invol haa hy hc, haN, zero_smul, add_zero]
  have hlin : t • (x - herm σ y (t • x - x) • u) -
      (x - herm σ y (t • x - x) • u) =
      (t • x - x) - herm σ y (t • x - x) • a := by
    rw [hadef, smul_sub, smul_comm t (herm σ y (t • x - x)) u, smul_sub]
    abel
  rw [hlin]

theorem eichler_maps_smul_sub_self_image [CharP K 2] (hσ : IsUnitaryInvolution σ)
    {t : SUid σ n} (ht : t * t = 1) {u y : Fin n → K}
    (hy : herm σ (t • u - u) y = 0) {c : K} (hc : c + σ c = -herm σ y y) :
    ∀ x : Fin n → K, ∃ z : Fin n → K,
      eichler hσ.invol (herm_smul_sub_self_self hσ.invol ht u u) hy hc • (t • x - x) =
        t • z - z :=
  fun x => ⟨x - herm σ y (t • x - x) • u, eichler_smul_smul_sub_self hσ ht hy hc x⟩

theorem eq_transvection_of_forall_commute_eichler [CharP K 2] (hσ : IsUnitaryInvolution σ)
    {t : SUid σ n} (ht : t * t = 1) {u : Fin n → K}
    (hd : herm σ (t • u - u) u ≠ 0)
    (hE : ∀ (y : Fin n → K) (hy : herm σ (t • u - u) y = 0) (c : K)
      (hc : c + σ c = -herm σ y y),
      eichler hσ.invol (herm_smul_sub_self_self hσ.invol ht u u) hy hc * t =
        t * eichler hσ.invol (herm_smul_sub_self_self hσ.invol ht u u) hy hc)
    (x : Fin n → K) :
    t • x = x + ((herm σ (t • u - u) u)⁻¹ * herm σ (t • u - u) x) • (t • u - u) := by
  set a := t • u - u with hadef
  have haa : herm σ a a = 0 := herm_smul_sub_self_self hσ.invol ht u u
  have hta : t • a = a := by
    rw [hadef]
    exact sub_eq_zero.mp (smul_sub_self_smul_sub_self (σ := σ) (t := t) ht u)
  have hherm : ∀ v : Fin n → K, herm σ a (t • v) = herm σ a v := by
    intro v
    simpa [hta] using herm_smul_smul σ t a v
  have hkey : ∀ (y : Fin n → K), herm σ a y = 0 → ∀ x : Fin n → K,
      -(herm σ y (t • x - x)) • a = herm σ a x • (t • y - y) := by
    intro y hy x
    obtain ⟨c, hc⟩ := hσ.trace_surj (-herm σ y y)
      (by rw [map_neg, herm_self_fixed σ hσ.invol])
    have hcomm := hE y hy c hc
    have hcomm' : eichler hσ.invol haa hy hc * t =
        t * eichler hσ.invol haa hy hc := by
      simpa only [hadef] using hcomm
    have h1 : eichler hσ.invol haa hy hc • (t • x) =
        t • (eichler hσ.invol haa hy hc • x) := by
      rw [← mul_smul, hcomm', mul_smul]
    rw [eichler_smul hσ.invol haa hy hc (x := t • x)] at h1
    rw [eichler_smul hσ.invol haa hy hc (x := x)] at h1
    conv at h1 =>
      rhs
      rw [smul_sub]
      rw [smul_add t x (herm σ a x • (y + c • a))]
      rw [smul_comm t (herm σ a x) (y + c • a)]
      rw [smul_comm t (herm σ y x) a]
      rw [smul_add t y (c • a)]
      rw [smul_comm t c a]
      rw [hta]
    rw [hherm x] at h1
    rw [herm_sub_right]
    funext i
    have h1i := congrFun h1 i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      neg_mul] at h1i ⊢
    linear_combination h1i
  have hNy : ∀ y : Fin n → K, herm σ a y = 0 → t • y - y = 0 := by
    intro y hy
    have h := hkey y hy u
    have hyA : herm σ y a = 0 := herm_eq_zero_comm σ hσ.invol hy
    rw [hyA, neg_zero, zero_smul] at h
    exact (smul_eq_zero.mp h.symm).resolve_left hd
  set k := (herm σ a u)⁻¹ * herm σ a x with hkdef
  have hay : herm σ a (x - k • u) = 0 := by
    rw [herm_sub_right, herm_smul_right, hkdef]
    field_simp [hd]
    ring
  have hlin : t • (x - k • u) - (x - k • u) = (t • x - x) - k • a := by
    rw [hadef, smul_sub, smul_comm t k u, smul_sub]
    abel
  have hNx : t • x - x = k • a := by
    have h := hNy (x - k • u) hay
    rw [hlin] at h
    exact sub_eq_zero.mp h
  rw [hkdef]
  exact sub_eq_iff_eq_add'.mp hNx

theorem exists_conj_smul_eq_of_transvection (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n)
    {t : SUid σ n} {a : Fin n → K} {c : K} (ha0 : a ≠ 0) (ha : herm σ a a = 0)
    (hc0 : c ≠ 0) (hcσ : σ c = c)
    (ht : ∀ x, t • x = x + (c * herm σ a x) • a) {e : Fin n → K} (he0 : e ≠ 0)
    (he : herm σ e e = 0) :
    ∃ g : SUid σ n, ∀ x, (g * t * g⁻¹) • x = x + herm σ e x • e := by
  obtain ⟨lam, hlam⟩ := hσ.exists_norm (d := c⁻¹)
    (by simpa only [map_inv₀] using congrArg Inv.inv hcσ)
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hlam
    exact (inv_ne_zero hc0) hlam.symm
  have hlam_e0 : lam • e ≠ 0 := smul_ne_zero hlam0 he0
  have hlam_e : herm σ (lam • e) (lam • e) = 0 := by
    rw [herm_smul_left, herm_smul_right, he]
    ring
  obtain ⟨g, -, hga⟩ := exists_mem_T_smul_eq_of_iso hσ hn ha0 ha hlam_e0 hlam_e
  refine ⟨g, fun x => ?_⟩
  rw [conj_smul_of_tv g t ht x, hga]
  rw [herm_smul_left, smul_smul]
  have hscalar : c * (σ lam * herm σ e x) * lam = herm σ e x := by
    have hc_inv : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
    linear_combination (c * herm σ e x) * hlam + herm σ e x * hc_inv
  rw [hscalar]

theorem exists_conj_smul_eq_of_forall_commute [CharP K 2] (hσ : IsUnitaryInvolution σ)
    (hn : 3 ≤ n) {t : SUid σ n} (ht : t * t = 1) (ht1 : t ≠ 1)
    (hW : ∀ g : SUid σ n,
      (∀ x : Fin n → K, ∃ y : Fin n → K, g • (t • x - x) = t • y - y) →
        g * t = t * g)
    {e : Fin n → K} (he0 : e ≠ 0) (he : herm σ e e = 0) :
    ∃ g : SUid σ n, ∀ x, (g * t * g⁻¹) • x = x + herm σ e x • e := by
  obtain ⟨u, hd⟩ := exists_herm_smul_sub_self_ne_zero hσ ht ht1
  have ha0 : t • u - u ≠ 0 := by
    intro h
    exact hd (by rw [h, herm_zero_left])
  have haa : herm σ (t • u - u) (t • u - u) = 0 :=
    herm_smul_sub_self_self hσ.invol ht u u
  have hdσ : σ (herm σ (t • u - u) u) = herm σ (t • u - u) u :=
    herm_smul_sub_self_fixed hσ ht u
  have hE : ∀ (y : Fin n → K) (hy : herm σ (t • u - u) y = 0) (c : K)
      (hc : c + σ c = -herm σ y y),
      eichler hσ.invol (herm_smul_sub_self_self hσ.invol ht u u) hy hc * t =
        t * eichler hσ.invol (herm_smul_sub_self_self hσ.invol ht u u) hy hc := by
    intro y hy c hc
    apply hW
    exact eichler_maps_smul_sub_self_image hσ ht hy hc
  have htx := eq_transvection_of_forall_commute_eichler hσ ht hd hE
  have hc0 : (herm σ (t • u - u) u)⁻¹ ≠ 0 := inv_ne_zero hd
  have hcσ : σ ((herm σ (t • u - u) u)⁻¹) = (herm σ (t • u - u) u)⁻¹ := by
    simpa only [map_inv₀] using congrArg Inv.inv hdσ
  exact exists_conj_smul_eq_of_transvection hσ hn ha0 haa hc0 hcσ htx he0 he

end CFSG.ClassicalGroups.Unitary
