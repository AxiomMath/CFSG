module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12PrinceCentral
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12PrinceBil

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped commutatorElement

variable {G : Type} [Group G]

private lemma pi_zmod_two_add_self {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private lemma isEvenVec_add {n : ℕ} {v w : Fin n → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) : IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hv, hw, add_zero]

private lemma isEvenVec_zero {n : ℕ} : IsEvenVec (0 : Fin n → ZMod 2) := by
  simp [IsEvenVec]

private lemma permVec_even {n : ℕ} (σ : Equiv.Perm (Fin n)) {v : Fin n → ZMod 2}
    (hv : IsEvenVec v) : IsEvenVec (permVec σ v) := by
  show ∑ i, v (σ.symm i) = 0
  rw [Equiv.sum_comp σ.symm v]
  exact hv

private lemma phiZero_zero_eq_one {n : ℕ} (φ₀ : (Fin n → ZMod 2) → G)
    (hadd : ∀ v w, IsEvenVec v → IsEvenVec w → φ₀ (v + w) = φ₀ v * φ₀ w) :
    φ₀ 0 = 1 := by
  have h0 : IsEvenVec (0 : Fin n → ZMod 2) := isEvenVec_zero
  have h := hadd 0 0 h0 h0
  rw [add_zero] at h
  have h2 : φ₀ 0 * φ₀ 0 = φ₀ 0 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

private lemma sq_mul_central {x b : G} (hb1 : b * b = 1) (hcomm : x * b = b * x) :
    (x * b) * (x * b) = x * x := by
  calc (x * b) * (x * b) = x * (b * x) * b := by group
    _ = x * (x * b) * b := by rw [← hcomm]
    _ = x * x * (b * b) := by group
    _ = x * x := by rw [hb1, mul_one]

private lemma commutatorElement_mul_left_central {x b z : G} (hbz : b * z = z * b) :
    ⁅x * b, z⁆ = ⁅x, z⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul x b z]
  have h1 : ⁅b, z⁆ = 1 := by
    rw [commutatorElement_def, hbz]
    group
  rw [h1]
  group

private lemma commutatorElement_mul_right_central {x y b : G} (hbx : x * b = b * x) :
    ⁅x, y * b⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj x y b]
  have h1 : ⁅x, b⁆ = 1 := by
    rw [commutatorElement_def, hbx]
    group
  rw [h1]
  group

private lemma commutatorElement_mul_central {a b c : G}
    (h : a * ⁅b, c⁆ = ⁅b, c⁆ * a) :
    ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul a b c, h]
  group

private lemma commutatorElement_mul_central_right {a b c : G}
    (h : b * ⁅a, c⁆ = ⁅a, c⁆ * b) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj a b c]
  have e : ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆) * b⁻¹ := by group
  rw [e, h]
  group

namespace PrinceData

variable {B V H : Subgroup G} {φ φ₀ : (Fin 5 → ZMod 2) → G}

theorem abelian [Finite G] (hP : PrinceData B V H φ φ₀) {x y : G} (hx : x ∈ V)
    (hy : y ∈ V) : x * y = y * x := by
  classical
  obtain ⟨hBleV, _, hHV, _, hφmemV, hφadd, _, hsurj, _, hmodAlt⟩ := hP.mod
  obtain ⟨hφ₀add, hφ₀inj, hφ₀mem, _, _⟩ := hP.via
  have hφ₀0 : φ₀ 0 = 1 := phiZero_zero_eq_one φ₀ hφ₀add
  have hex : ∀ v w : Fin 5 → ZMod 2, IsEvenVec v → IsEvenVec w →
      ∃ u, IsEvenVec u ∧ φ₀ u = ⁅φ v, φ w⁆ := by
    intro v w hv hw
    exact (hφ₀mem ⁅φ v, φ w⁆).mp (comm_mem hP (hφmemV v hv) (hφmemV w hw))
  have hex2 : ∀ v w, ∃ u, IsEvenVec v → IsEvenVec w →
      IsEvenVec u ∧ φ₀ u = ⁅φ v, φ w⁆ := by
    intro v w
    by_cases hv : IsEvenVec v
    · by_cases hw : IsEvenVec w
      · obtain ⟨u, hu, heq⟩ := hex v w hv hw
        exact ⟨u, fun _ _ => ⟨hu, heq⟩⟩
      · exact ⟨0, fun _ hw' => absurd hw' hw⟩
    · exact ⟨0, fun hv' _ => absurd hv' hv⟩
  choose k hk using hex2
  have hk_even : ∀ v w, IsEvenVec v → IsEvenVec w → IsEvenVec (k v w) :=
    fun v w hv hw => (hk v w hv hw).1
  have hk_eq : ∀ v w, IsEvenVec v → IsEvenVec w → φ₀ (k v w) = ⁅φ v, φ w⁆ :=
    fun v w hv hw => (hk v w hv hw).2
  have hadd₁ : ∀ v v' w, IsEvenVec v → IsEvenVec v' → IsEvenVec w →
      k (v + v') w = k v w + k v' w := by
    intro v v' w hv hv' hw
    have hvv' : IsEvenVec (v + v') := isEvenVec_add hv hv'
    have hbB : (φ v * φ v')⁻¹ * φ (v + v') ∈ B := hφadd v v' hv hv'
    have hbz : ((φ v * φ v')⁻¹ * φ (v + v')) * φ w =
        φ w * ((φ v * φ v')⁻¹ * φ (v + v')) :=
      (B_central hP hbB (hφmemV w hw)).symm
    have hφsum : φ (v + v') = (φ v * φ v') * ((φ v * φ v')⁻¹ * φ (v + v')) := by
      group
    have hpB : ⁅φ v', φ w⁆ ∈ B := comm_mem hP (hφmemV v' hv') (hφmemV w hw)
    have hstep1 : ⁅φ (v + v'), φ w⁆ = ⁅φ v * φ v', φ w⁆ := by
      rw [hφsum]
      exact commutatorElement_mul_left_central hbz
    have hstep2 : ⁅φ v * φ v', φ w⁆ = ⁅φ v', φ w⁆ * ⁅φ v, φ w⁆ :=
      commutatorElement_mul_central (B_central hP hpB (hφmemV v hv))
    have hcommute : ⁅φ v', φ w⁆ * ⁅φ v, φ w⁆ = ⁅φ v, φ w⁆ * ⁅φ v', φ w⁆ :=
      B_central hP (comm_mem hP (hφmemV v hv) (hφmemV w hw)) (hBleV hpB)
    refine hφ₀inj (k (v + v') w) (k v w + k v' w) (hk_even (v + v') w hvv' hw)
      (isEvenVec_add (hk_even v w hv hw) (hk_even v' w hv' hw)) ?_
    rw [hk_eq (v + v') w hvv' hw,
      hφ₀add (k v w) (k v' w) (hk_even v w hv hw) (hk_even v' w hv' hw),
      hk_eq v w hv hw, hk_eq v' w hv' hw]
    exact hstep1.trans (hstep2.trans hcommute)
  have hadd₂ : ∀ v w w', IsEvenVec v → IsEvenVec w → IsEvenVec w' →
      k v (w + w') = k v w + k v w' := by
    intro v w w' hv hw hw'
    have hww' : IsEvenVec (w + w') := isEvenVec_add hw hw'
    have hbB : (φ w * φ w')⁻¹ * φ (w + w') ∈ B := hφadd w w' hw hw'
    have hbx : φ v * ((φ w * φ w')⁻¹ * φ (w + w')) =
        ((φ w * φ w')⁻¹ * φ (w + w')) * φ v :=
      B_central hP hbB (hφmemV v hv)
    have hφsum : φ (w + w') = (φ w * φ w') * ((φ w * φ w')⁻¹ * φ (w + w')) := by
      group
    have hpB : ⁅φ v, φ w'⁆ ∈ B := comm_mem hP (hφmemV v hv) (hφmemV w' hw')
    have hstep1 : ⁅φ v, φ (w + w')⁆ = ⁅φ v, φ w * φ w'⁆ := by
      rw [hφsum]
      exact commutatorElement_mul_right_central hbx
    have hstep2 : ⁅φ v, φ w * φ w'⁆ = ⁅φ v, φ w⁆ * ⁅φ v, φ w'⁆ :=
      commutatorElement_mul_central_right (B_central hP hpB (hφmemV w hw))
    refine hφ₀inj (k v (w + w')) (k v w + k v w') (hk_even v (w + w') hv hww')
      (isEvenVec_add (hk_even v w hv hw) (hk_even v w' hv hw')) ?_
    rw [hk_eq v (w + w') hv hww',
      hφ₀add (k v w) (k v w') (hk_even v w hv hw) (hk_even v w' hv hw'),
      hk_eq v w hv hw, hk_eq v w' hv hw']
    exact hstep1.trans hstep2
  have halt : ∀ v, IsEvenVec v → k v v = 0 := by
    intro v hv
    refine hφ₀inj (k v v) 0 (hk_even v v hv hv) isEvenVec_zero ?_
    rw [hk_eq v v hv hv, hφ₀0, commutatorElement_def]
    group
  have hequi : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v w, IsEvenVec v → IsEvenVec w →
      k (permVec σ v) (permVec σ w) = permVec σ (k v w) := by
    intro σ hσ v w hv hw
    obtain ⟨h, hhH, hact⟩ := hmodAlt σ hσ
    have hhv : h ∈ normalizer (V : Set G) := hHV hhH
    have hconjv : h * φ v * h⁻¹ ∈ V :=
      (Subgroup.mem_set_normalizer_iff.mp hhv (φ v)).mp (hφmemV v hv)
    have hconjw : h * φ w * h⁻¹ ∈ V :=
      (Subgroup.mem_set_normalizer_iff.mp hhv (φ w)).mp (hφmemV w hw)
    set bv : G := (h * φ v * h⁻¹)⁻¹ * φ (permVec σ v) with hbvdef
    set bw : G := (h * φ w * h⁻¹)⁻¹ * φ (permVec σ w) with hbwdef
    have hbvB : bv ∈ B := by rw [hbvdef]; exact hact v hv
    have hbwB : bw ∈ B := by rw [hbwdef]; exact hact w hw
    have hφv' : φ (permVec σ v) = (h * φ v * h⁻¹) * bv := by rw [hbvdef]; group
    have hφw' : φ (permVec σ w) = (h * φ w * h⁻¹) * bw := by rw [hbwdef]; group
    have hzV : (h * φ w * h⁻¹) * bw ∈ V := V.mul_mem hconjw (hBleV hbwB)
    have hbz : bv * ((h * φ w * h⁻¹) * bw) = ((h * φ w * h⁻¹) * bw) * bv :=
      (B_central hP hbvB hzV).symm
    have hbx : (h * φ v * h⁻¹) * bw = bw * (h * φ v * h⁻¹) :=
      B_central hP hbwB hconjv
    have hdrop : ⁅φ (permVec σ v), φ (permVec σ w)⁆ =
        ⁅h * φ v * h⁻¹, h * φ w * h⁻¹⁆ := by
      rw [hφv', hφw', commutatorElement_mul_left_central hbz]
      exact commutatorElement_mul_right_central hbx
    have hevenv : IsEvenVec (permVec σ v) := permVec_even σ hv
    have hevenw : IsEvenVec (permVec σ w) := permVec_even σ hw
    have hfin : ⁅φ (permVec σ v), φ (permVec σ w)⁆ = φ₀ (permVec σ (k v w)) := by
      rw [hdrop, (conjugate_commutatorElement (φ v) (φ w) h).symm, ← hk_eq v w hv hw]
      exact hP.compat h hhH σ hσ hact (k v w) (hk_even v w hv hw)
    refine hφ₀inj (k (permVec σ v) (permVec σ w)) (permVec σ (k v w))
      (hk_even (permVec σ v) (permVec σ w) hevenv hevenw)
      (permVec_even σ (hk_even v w hv hw)) ?_
    rw [hk_eq (permVec σ v) (permVec σ w) hevenv hevenw]
    exact hfin
  have hkzero : ∀ v w, IsEvenVec v → IsEvenVec w → k v w = 0 :=
    prince_bilinear_zero k hk_even hadd₁ hadd₂ halt hequi
  have hφcomm : ∀ v w, IsEvenVec v → IsEvenVec w → φ v * φ w = φ w * φ v := by
    intro v w hv hw
    have h1 : ⁅φ v, φ w⁆ = 1 := by
      rw [← hk_eq v w hv hw, hkzero v w hv hw, hφ₀0]
    exact (commutatorElement_eq_one_iff_mul_comm (g₁ := φ v) (g₂ := φ w)).mp h1
  obtain ⟨v, hv, hbv⟩ := hsurj x hx
  obtain ⟨w, hw, hbw⟩ := hsurj y hy
  set b₁ : G := (φ v)⁻¹ * x with hb1def
  set b₂ : G := (φ w)⁻¹ * y with hb2def
  have hb1B : b₁ ∈ B := by rw [hb1def]; exact hbv
  have hb2B : b₂ ∈ B := by rw [hb2def]; exact hbw
  have hx_eq : x = φ v * b₁ := by
    rw [hb1def]; exact (mul_inv_cancel_left (φ v) x).symm
  have hy_eq : y = φ w * b₂ := by
    rw [hb2def]; exact (mul_inv_cancel_left (φ w) y).symm
  have hb1_φw : b₁ * φ w = φ w * b₁ := (B_central hP hb1B (hφmemV w hw)).symm
  have hb2_φv : b₂ * φ v = φ v * b₂ := (B_central hP hb2B (hφmemV v hv)).symm
  have hb1b2 : b₁ * b₂ = b₂ * b₁ := (B_central hP hb1B (hBleV hb2B)).symm
  calc x * y = (φ v * b₁) * (φ w * b₂) := by rw [hx_eq, hy_eq]
    _ = (φ w * b₂) * (φ v * b₁) := by
          calc (φ v * b₁) * (φ w * b₂)
              = φ v * (b₁ * φ w) * b₂ := by group
            _ = φ v * (φ w * b₁) * b₂ := by rw [hb1_φw]
            _ = φ v * φ w * (b₁ * b₂) := by group
            _ = φ w * φ v * (b₁ * b₂) := by rw [hφcomm v w hv hw]
            _ = φ w * φ v * (b₂ * b₁) := by rw [hb1b2]
            _ = φ w * (φ v * b₂) * b₁ := by group
            _ = φ w * (b₂ * φ v) * b₁ := by rw [← hb2_φv]
            _ = (φ w * b₂) * (φ v * b₁) := by group
    _ = y * x := by rw [hx_eq, hy_eq]

theorem sq_dichotomy [Finite G] (hP : PrinceData B V H φ φ₀) :
    (∀ x ∈ V, x * x = 1) ∨ (∀ v, IsEvenVec v → φ v * φ v = φ₀ v) := by
  classical
  obtain ⟨hBleV, _, hHV, _, hφmemV, hφadd, _, hsurj, _, hmodAlt⟩ := hP.mod
  obtain ⟨hφ₀add, hφ₀inj, hφ₀mem, _, _⟩ := hP.via
  have hφ₀0 : φ₀ 0 = 1 := phiZero_zero_eq_one φ₀ hφ₀add
  have hcommV : ∀ a b : G, a ∈ V → b ∈ V → a * b = b * a :=
    fun a b ha hb => abelian hP ha hb
  have hex : ∀ v, IsEvenVec v → ∃ u, IsEvenVec u ∧ φ₀ u = φ v * φ v := by
    intro v hv
    exact (hφ₀mem (φ v * φ v)).mp (sq_mem hP (hφmemV v hv))
  have hex2 : ∀ v, ∃ u, IsEvenVec v → IsEvenVec u ∧ φ₀ u = φ v * φ v := by
    intro v
    by_cases hv : IsEvenVec v
    · obtain ⟨u, hu, heq⟩ := hex v hv
      exact ⟨u, fun _ => ⟨hu, heq⟩⟩
    · exact ⟨0, fun hv' => absurd hv' hv⟩
  choose s hs using hex2
  have hs_even : ∀ v, IsEvenVec v → IsEvenVec (s v) := fun v hv => (hs v hv).1
  have hs_eq : ∀ v, IsEvenVec v → φ₀ (s v) = φ v * φ v := fun v hv => (hs v hv).2
  have hsadd : ∀ v w, IsEvenVec v → IsEvenVec w → s (v + w) = s v + s w := by
    intro v w hv hw
    have hvw : IsEvenVec (v + w) := isEvenVec_add hv hw
    have hbB : (φ v * φ w)⁻¹ * φ (v + w) ∈ B := hφadd v w hv hw
    have hAb : (φ v * φ w) * ((φ v * φ w)⁻¹ * φ (v + w)) =
        ((φ v * φ w)⁻¹ * φ (v + w)) * (φ v * φ w) :=
      B_central hP hbB (V.mul_mem (hφmemV v hv) (hφmemV w hw))
    have hφsum : φ (v + w) = (φ v * φ w) * ((φ v * φ w)⁻¹ * φ (v + w)) := by group
    have hsq : φ (v + w) * φ (v + w) = (φ v * φ v) * (φ w * φ w) := by
      rw [hφsum, sq_mul_central (B_sq hP hbB) hAb]
      calc (φ v * φ w) * (φ v * φ w)
          = φ v * (φ w * φ v) * φ w := by group
        _ = φ v * (φ v * φ w) * φ w := by
              rw [hcommV _ _ (hφmemV w hw) (hφmemV v hv)]
        _ = (φ v * φ v) * (φ w * φ w) := by group
    refine hφ₀inj (s (v + w)) (s v + s w) (hs_even (v + w) hvw)
      (isEvenVec_add (hs_even v hv) (hs_even w hw)) ?_
    rw [hs_eq (v + w) hvw, hφ₀add (s v) (s w) (hs_even v hv) (hs_even w hw),
      hs_eq v hv, hs_eq w hw]
    exact hsq
  have hsequi : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v, IsEvenVec v →
      s (permVec σ v) = permVec σ (s v) := by
    intro σ hσ v hv
    obtain ⟨h, hhH, hact⟩ := hmodAlt σ hσ
    have hhv : h ∈ normalizer (V : Set G) := hHV hhH
    have hconjv : h * φ v * h⁻¹ ∈ V :=
      (Subgroup.mem_set_normalizer_iff.mp hhv (φ v)).mp (hφmemV v hv)
    set bv : G := (h * φ v * h⁻¹)⁻¹ * φ (permVec σ v) with hbvdef
    have hbvB : bv ∈ B := by rw [hbvdef]; exact hact v hv
    have hφv' : φ (permVec σ v) = (h * φ v * h⁻¹) * bv := by rw [hbvdef]; group
    have hevenv : IsEvenVec (permVec σ v) := permVec_even σ hv
    have hcomp : φ (permVec σ v) * φ (permVec σ v) = φ₀ (permVec σ (s v)) := by
      rw [hφv', sq_mul_central (B_sq hP hbvB) (B_central hP hbvB hconjv),
        show (h * φ v * h⁻¹) * (h * φ v * h⁻¹) = h * (φ v * φ v) * h⁻¹ by group,
        ← hs_eq v hv]
      exact hP.compat h hhH σ hσ hact (s v) (hs_even v hv)
    refine hφ₀inj (s (permVec σ v)) (permVec σ (s v))
      (hs_even (permVec σ v) hevenv) (permVec_even σ (hs_even v hv)) ?_
    rw [hs_eq (permVec σ v) hevenv]
    exact hcomp
  rcases prince_endo s hs_even hsadd hsequi with hzero | hid
  · left
    intro x hx
    obtain ⟨v, hv, hbv⟩ := hsurj x hx
    set b : G := (φ v)⁻¹ * x with hbdef
    have hbB : b ∈ B := by rw [hbdef]; exact hbv
    have hx_eq : x = φ v * b := by
      rw [hbdef]; exact (mul_inv_cancel_left (φ v) x).symm
    have hbb : b * b = 1 := B_sq hP hbB
    have hbcomm : φ v * b = b * φ v := B_central hP hbB (hφmemV v hv)
    calc x * x = (φ v * b) * (φ v * b) := by rw [hx_eq]
      _ = φ v * φ v := sq_mul_central hbb hbcomm
      _ = φ₀ (s v) := (hs_eq v hv).symm
      _ = φ₀ 0 := by rw [hzero v hv]
      _ = 1 := hφ₀0
  · right
    intro v hv
    rw [← hs_eq v hv, hid v hv]

end PrinceData

end CFSG.OddStandard.SmallF3.Omega
