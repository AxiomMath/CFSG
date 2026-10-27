module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddBigCell
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddTwist
public import CFSG.RankThree.PartOne.SEITZ8.D4Fin

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ8
  CFSG.RankThree.PartOne.SEITZ3 CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem

variable {K : Type} [Field K]

section Prelim

variable (σ : K →+* K)

@[expose] noncomputable def tAB (x : K) : adjointGroup d4 K :=
  xd 5 (-x) * xd 7 (-σ x) * xd 9 (σ (σ x))

theorem tAB_add (x y : K) : tAB σ (x + y) = tAB σ x * tAB σ y := by
  unfold tAB
  simp only [map_add]
  d4collO
  d4finO

theorem tAB_zero : tAB σ (0 : K) = 1 := by
  simp [tAB, xd_zero]

theorem tAB_neg (x : K) : tAB σ (-x) = (tAB σ x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← tAB_add, neg_add_cancel, tAB_zero])

end Prelim

section Torus

variable (σ : K →+* K)

@[expose] noncomputable def aW (u a : K) : adjointGroup d4 K :=
  xd 5 (-(a * u)) * xd 7 (-(σ a * u)) * xd 9 (σ (σ a) * u)

@[expose] noncomputable def bW (u a : K) : adjointGroup d4 K :=
  xd 12 (-(a * σ a * u)) * xd 15 (-(σ a * σ (σ a) * u)) * xd 13 (-(a * σ (σ a) * u))

theorem aW_eq_tAB (d a : K) (hd : σ d = d) : aW σ d a = tAB σ (d * a) := by
  have e1 : -(a * d) = -(d * a) := by ring
  have e2 : -(σ a * d) = -σ (d * a) := by rw [map_mul, hd]; ring
  have e3 : σ (σ a) * d = σ (σ (d * a)) := by simp only [map_mul, hd]; ring
  unfold aW tAB
  rw [e1, e2, e3]

theorem torus_aW_bW (t : Kˣ) (s : K) (hts : (t : K) = s) (d a : K) :
    torusElement d4 K (nd 2) t * (aW σ d a * bW σ d a) * (torusElement d4 K (nd 2) t)⁻¹ *
        (aW σ d a * bW σ d a)⁻¹ = aW σ ((s - 1) * d) a := by
  obtain ⟨h5, h7, h9, h12, h15, h13⟩ := cartan_AB_check
  have e5 := torusElement_conj_xd (K := K) (nd 2) (p := 5) (by norm_num) t
  have e7 := torusElement_conj_xd (K := K) (nd 2) (p := 7) (by norm_num) t
  have e9 := torusElement_conj_xd (K := K) (nd 2) (p := 9) (by norm_num) t
  have e12 := torusElement_conj_xd (K := K) (nd 2) (p := 12) (by norm_num) t
  have e15 := torusElement_conj_xd (K := K) (nd 2) (p := 15) (by norm_num) t
  have e13 := torusElement_conj_xd (K := K) (nd 2) (p := 13) (by norm_num) t
  simp only [h5, zpow_one, hts] at e5
  simp only [h7, zpow_one, hts] at e7
  simp only [h9, zpow_one, hts] at e9
  simp only [h12, zpow_zero, Units.val_one, one_mul] at e12
  simp only [h15, zpow_zero, Units.val_one, one_mul] at e15
  simp only [h13, zpow_zero, Units.val_one, one_mul] at e13
  have key : ∀ (n x y z : adjointGroup d4 K), n * (x * y * z) * n⁻¹ =
      (n * x * n⁻¹) * (n * y * n⁻¹) * (n * z * n⁻¹) := fun n x y z => by group
  have hA : torusElement d4 K (nd 2) t * aW σ d a * (torusElement d4 K (nd 2) t)⁻¹ =
      xd 5 (s * -(a * d)) * xd 7 (s * -(σ a * d)) * xd 9 (s * (σ (σ a) * d)) := by
    unfold aW
    rw [key, e5, e7, e9]
  have hB : torusElement d4 K (nd 2) t * bW σ d a * (torusElement d4 K (nd 2) t)⁻¹ =
      bW σ d a := by
    unfold bW
    rw [key, e12, e15, e13]
  have e : torusElement d4 K (nd 2) t * (aW σ d a * bW σ d a) * (torusElement d4 K (nd 2) t)⁻¹ =
      (torusElement d4 K (nd 2) t * aW σ d a * (torusElement d4 K (nd 2) t)⁻¹) *
        (torusElement d4 K (nd 2) t * bW σ d a * (torusElement d4 K (nd 2) t)⁻¹) := by group
  rw [e, hA, hB]
  have e2 : ∀ (X B A : adjointGroup d4 K), X * B * (A * B)⁻¹ = X * A⁻¹ := fun X B A => by group
  rw [e2]
  unfold aW
  d4collO
  d4finO

end Torus

section Twist

variable (σ : K →+* K)

theorem twistC_xd5 (c : K) : twistC .D4 K σ (xd 5 c) = xd 7 (σ c) := by
  have := twistC_xPar σ (SEITZ8.isRoot_d4 (by norm_num : 5 < 24)) c
  rw [rho_dict.2.2.2.2.2.1, twistSign_5, one_mul] at this
  exact this

theorem twistC_xd7 (c : K) : twistC .D4 K σ (xd 7 c) = xd 9 (-(σ c)) := by
  have := twistC_xPar σ (SEITZ8.isRoot_d4 (by norm_num : 7 < 24)) c
  rw [rho_dict.2.2.2.2.2.2.1, twistSign_7, neg_one_mul] at this
  exact this

theorem n0_tAB (hF : twistC .D4 K σ (weylElement d4 K (nd 2)) = weylElement d4 K (nd 2)) (a : K) :
    ∃ x : K, weylElement d4 K (nd 2) * tAB σ x * (weylElement d4 K (nd 2))⁻¹ =
      xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a)) := by
  obtain ⟨h5, h7, h9, -⟩ := reflect_AB_check
  obtain ⟨ε5, hε5, e5⟩ := weylElement_conj_xd_odd (K := K) (nd 2) (p := 5) (q := 0)
    (by norm_num) h5
  obtain ⟨ε7, hε7, e7⟩ := weylElement_conj_xd_odd (K := K) (nd 2) (p := 7) (q := 1)
    (by norm_num) h7
  obtain ⟨ε9, hε9, e9⟩ := weylElement_conj_xd_odd (K := K) (nd 2) (p := 9) (q := 3)
    (by norm_num) h9
  have r57 : ε7 = ε5 := by
    have h := congrArg (twistC .D4 K σ) (e5 1)
    rw [map_mul, map_mul, map_inv, hF, twistC_xd5, twistC_xd0, map_one] at h
    have h' := h.symm.trans (e7 1)
    have h'' := xPar_injective (SEITZ8.isRoot_d4 (by norm_num : 1 < 24)) (by
      simpa [xd, map_mul, map_one, pmone_sigma hε5] using h'.symm)
    simpa using h''
  have r79 : ε9 = -ε7 := by
    have h := congrArg (twistC .D4 K σ) (e7 1)
    rw [map_mul, map_mul, map_inv, hF, twistC_xd7, twistC_xd1, map_one] at h
    have h' := h.symm.trans (e9 (-(1 : K)))
    have h'' := xPar_injective (SEITZ8.isRoot_d4 (by norm_num : 3 < 24)) (by
      simpa [xd, map_mul, map_one, pmone_sigma hε7] using h'.symm)
    have h3 : -ε9 = ε7 := by simpa using h''
    exact neg_eq_iff_eq_neg.1 h3
  refine ⟨-(ε5 * a), ?_⟩
  have key : ∀ (n x y z : adjointGroup d4 K), n * (x * y * z) * n⁻¹ =
      (n * x * n⁻¹) * (n * y * n⁻¹) * (n * z * n⁻¹) := fun n x y z => by group
  unfold tAB
  rw [key, e5, e7, e9, r79, r57]
  have s1 : σ (ε5 * a) = ε5 * σ a := by rw [map_mul, pmone_sigma hε5]
  have hσx : σ (-(ε5 * a)) = -(ε5 * σ a) := by rw [map_neg, s1]
  have hσσx : σ (-(ε5 * σ a)) = -(ε5 * σ (σ a)) := by
    rw [map_neg, map_mul, pmone_sigma hε5]
  have q := hε5.sq
  have c0 : ε5 * -(-(ε5 * a)) = a := by
    calc ε5 * -(-(ε5 * a)) = (ε5 * ε5) * a := by ring
      _ = a := by rw [q, one_mul]
  have c1 : ε5 * -(-(ε5 * σ a)) = σ a := by
    calc ε5 * -(-(ε5 * σ a)) = (ε5 * ε5) * σ a := by ring
      _ = σ a := by rw [q, one_mul]
  have c3 : -ε5 * -(ε5 * σ (σ a)) = σ (σ a) := by
    calc -ε5 * -(ε5 * σ (σ a)) = (ε5 * ε5) * σ (σ a) := by ring
      _ = σ (σ a) := by rw [q, one_mul]
  rw [hσx, hσσx, c0, c1, c3]

end Twist

section Closing

variable (σ : K →+* K)

theorem pmone_mem_fixed {ε c : K} (hε : PMOne ε) (hc : σ c = c) :
    σ (ε * c) = ε * c := by
  rw [map_mul, pmone_sigma hε, hc]

theorem long_closing_odd (hσ : ∀ c, σ (σ (σ c)) = c) (k : Subfield K)
    (Hs : Subgroup (adjointGroup d4 K)) (hn0 : weylElement d4 K (nd 2) ∈ Hs)
    (hn1 : weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) ∈ Hs)
    (hF : twistC .D4 K σ (weylElement d4 K (nd 2)) = weylElement d4 K (nd 2))
    (hH : ∀ c : K, σ c = c → xd 22 c ∈ Hs)
    (hA : ∀ a ∈ k, xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a)) ∈ Hs)
    (s : K) (hsσ : σ s = s) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hspan : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ d : K, σ d = d ∧ ∃ a ∈ k, y = d * a}) :
    (∀ c : K, σ c = c → xd 2 c ∈ Hs) ∧
      (∀ a : K, xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a)) ∈ Hs) := by
  have hWt : (Wt : adjointGroup d4 K) ∈ Hs := Hs.mul_mem hn0 hn1
  have hB : ∀ c : K, σ c = c → xd 2 c ∈ Hs := by
    intro c hc
    obtain ⟨-, εw, hεw, hW⟩ := Wt_rootMove_B (K := K)
    have h := hW c
    have e : xd 2 c = (Wt : adjointGroup d4 K)⁻¹ * xd 22 (εw * c) * Wt := by
      calc xd 2 c = (Wt : adjointGroup d4 K)⁻¹ * (Wt * xd 2 c * (Wt : adjointGroup d4 K)⁻¹) * Wt := by
            group
        _ = _ := by rw [h]
    rw [e]
    exact Hs.mul_mem (Hs.mul_mem (Hs.inv_mem hWt) (hH _ (pmone_mem_fixed σ hεw hc))) hWt
  have hBm : ∀ c : K, σ c = c → xd 8 c ∈ Hs := by
    intro c hc
    obtain ⟨-, -, -, h8⟩ := reflect_AB_check
    obtain ⟨ε8, hε8, e8⟩ := weylElement_conj_xd_odd (K := K) (nd 2) (p := 2) (q := 8)
      (by norm_num) h8
    have e : xd 8 c = weylElement d4 K (nd 2) * xd 2 (ε8 * c) * (weylElement d4 K (nd 2))⁻¹ := by
      rw [e8, ← mul_assoc, hε8.sq, one_mul]
    rw [e]
    exact Hs.mul_mem (Hs.mul_mem hn0 (hB _ (pmone_mem_fixed σ hε8 hc))) (Hs.inv_mem hn0)
  have hN : ∀ c : K, σ c = c → xd 19 c ∈ Hs := by
    intro c hc
    obtain ⟨-, -, -, a1, a2, a3, -, -, -⟩ := reflect_facts
    have hm := ((weylElement_rootMove (K := K) (nd 3) (p := 19) (by norm_num) a1).comp
      (weylElement_rootMove (K := K) (nd 1) (p := 12) (by norm_num) a2)).comp
      (weylElement_rootMove (K := K) (nd 0) (p := 5) (by norm_num) a3)
    obtain ⟨-, εn, hεn, hN⟩ := hm
    have hn1' : (weylElement d4 K (nd 0) * (weylElement d4 K (nd 1) * weylElement d4 K (nd 3))) ∈
        Hs := by simpa only [mul_assoc] using hn1
    generalize (weylElement d4 K (nd 0) * (weylElement d4 K (nd 1) * weylElement d4 K (nd 3))) = N
      at hn1' hN
    have h := hN c
    have e : xd 19 c = N⁻¹ * (N * xd 19 c * N⁻¹) * N := by group
    rw [e, h]
    exact Hs.mul_mem (Hs.mul_mem (Hs.inv_mem hn1') (hB _ (pmone_mem_fixed σ hεn hc))) hn1'
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (fixedField σ)ˣ,
      ((Units.map (fixedField σ).subtype.toMonoidHom ρ : Kˣ) : K) = s :=
    ⟨Units.mk0 ⟨s, hsσ⟩ (fun h => hs0 (congrArg Subtype.val h)), rfl⟩
  set t : Kˣ := Units.map (fixedField σ).subtype.toMonoidHom ρ with ht
  have htH : torusElement d4 K (nd 2) t ∈ Hs :=
    torus_mem σ Hs (fun c => hB c c.2) (fun c => hBm c c.2) ρ
  have hE : ∀ d : K, σ d = d → ∀ a ∈ k, aW σ d a * bW σ d a ∈ Hs := by
    intro d hd a ha
    have hconj : (xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a))) * xd 2 d *
        (xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a)))⁻¹ =
        xd 2 d * aW σ d a * bW σ d a * xd 19 (-(a * σ a * σ (σ a) * d)) *
          xd 22 (-(a * σ a * σ (σ a) * d ^ 2)) := conj_xA_xB_odd σ a d
    have hNσ : σ (a * σ a * σ (σ a)) = a * σ a * σ (σ a) := by
      simp only [map_mul, hσ]
      ring
    have h1 : xd 19 (-(a * σ a * σ (σ a) * d)) ∈ Hs := hN _ (by
      rw [map_neg, map_mul, hd, hNσ])
    have h2 : xd 22 (-(a * σ a * σ (σ a) * d ^ 2)) ∈ Hs := hH _ (by
      rw [map_neg, map_mul, map_pow, hd, hNσ])
    have h3 : (xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a))) * xd 2 d *
        (xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a)))⁻¹ ∈ Hs :=
      Hs.mul_mem (Hs.mul_mem (hA a ha) (hB d hd)) (Hs.inv_mem (hA a ha))
    have e : aW σ d a * bW σ d a = (xd 2 d)⁻¹ * ((xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a))) *
        xd 2 d * (xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a)))⁻¹) *
          (xd 22 (-(a * σ a * σ (σ a) * d ^ 2)))⁻¹ *
            (xd 19 (-(a * σ a * σ (σ a) * d)))⁻¹ := by
      rw [hconj]
      group
    rw [e]
    exact Hs.mul_mem (Hs.mul_mem (Hs.mul_mem (Hs.inv_mem (hB d hd)) h3) (Hs.inv_mem h2))
      (Hs.inv_mem h1)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hAu : ∀ u : K, σ u = u → ∀ a ∈ k, aW σ u a ∈ Hs := by
    intro u hu a ha
    set d : K := u / (s - 1) with hd
    have hdσ : σ d = d := by rw [hd, map_div₀, hu, map_sub, hsσ, map_one]
    have hq := Hs.mul_mem (Hs.mul_mem (Hs.mul_mem htH (hE d hdσ a ha)) (Hs.inv_mem htH))
      (Hs.inv_mem (hE d hdσ a ha))
    rw [torus_aW_bW σ t s (by rw [ht]; exact hρ) d a] at hq
    rwa [show (s - 1) * d = u by rw [hd]; field_simp] at hq
  let Ξ : AddSubgroup K :=
    { carrier := {x | tAB σ x ∈ Hs}
      zero_mem' := by
        show tAB σ 0 ∈ Hs
        rw [tAB_zero]
        exact Hs.one_mem
      add_mem' := fun {x y} hx hy => by
        show tAB σ (x + y) ∈ Hs
        rw [tAB_add]
        exact Hs.mul_mem hx hy
      neg_mem' := fun {x} hx => by
        show tAB σ (-x) ∈ Hs
        rw [tAB_neg]
        exact Hs.inv_mem hx }
  have hall : ∀ x : K, tAB σ x ∈ Hs := fun x =>
    (AddSubgroup.closure_le Ξ).2 (fun y hy => by
      obtain ⟨d, hd, a, ha, rfl⟩ := hy
      show tAB σ (d * a) ∈ Hs
      rw [← aW_eq_tAB σ d a hd]
      exact hAu d hd a ha) (hspan x)
  refine ⟨hB, fun a => ?_⟩
  obtain ⟨x, hx⟩ := n0_tAB σ hF a
  rw [← hx]
  exact Hs.mul_mem (Hs.mul_mem hn0 (hall x)) (Hs.inv_mem hn0)

end Closing

end CFSG.HardMathSupport.Seitz.TrialityOdd
